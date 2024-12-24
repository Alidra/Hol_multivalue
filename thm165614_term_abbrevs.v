Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term146 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term103 (x0 : nat) := exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0)).
Definition term161 (x0 : nat) := (~ (Peano.lt (Nat.modulo x0 (NUMERAL 0)) (NUMERAL 0))) -> Peano.lt (Nat.modulo x0 (NUMERAL 0)) (NUMERAL 0).
Definition term154 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term71 (x0 : nat -> Prop) := ~ (all x0).
Definition term167 := (~ False) -> False.
Definition term95 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) x1).
Definition term165 (x0 : nat) := (Peano.lt (Nat.modulo x0 (NUMERAL 0)) (NUMERAL 0)) -> False.
Definition term157 (x0 : nat) := (fun y0 : nat => Peano.lt (Nat.modulo x0 y0) y0) (NUMERAL 0).
Definition term142 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term54 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))))).
Definition term22 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term114 := fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0)).
Definition term84 := fun y0 : nat => exists y1 : nat, ((Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) \/ ((~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term105 (x0 : nat) := or (exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))).
Definition term166 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term147 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term109 (x0 : nat) := (exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) \/ (exists y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term62 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) /\ (~ (x1 = (NUMERAL 0))).
Definition term148 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term65 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) /\ (x1 = (NUMERAL 0)).
Definition term16 := imp ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))).
Definition term168 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term162 (x0 : nat) := ~ (Peano.lt (Nat.modulo x0 (NUMERAL 0)) (NUMERAL 0)).
Definition term171 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term73 (x0 : nat) := ~ (forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0)))).
Definition term14 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term0 := ~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))).
Definition term136 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term52 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term47 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term11 := imp (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False).
Definition term163 (x0 : Prop) := (~ x0) -> x0.
Definition term153 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term141 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term119 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) x0) \/ ((fun y0 : nat => exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) x0).
Definition term9 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term31 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term174 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term115 := fun y0 : nat => exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0))).
Definition term118 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) x0.
Definition term116 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) x0.
Definition term51 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0.
Definition term128 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (~ (y2 = (NUMERAL 0)))) y0.
Definition term123 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0.
Definition term57 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term56 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term139 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term8 := fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0)).
Definition term122 := @eq Prop (exists y0 : nat, (exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) \/ (exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term121 := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (~ (y2 = (NUMERAL 0)))) y0)).
Definition term100 (x0 : nat) := @eq Prop (exists y0 : nat, ((Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) \/ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0))))).
Definition term99 (x0 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0) \/ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) y0)).
Definition term79 (x0 : nat) := exists y0 : nat, ((Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) \/ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term10 := forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0)).
Definition term151 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 (NUMERAL 0))) x0.
Definition term113 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (~ (y2 = (NUMERAL 0)))) y0).
Definition term91 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) y0).
Definition term13 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term106 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) y0.
Definition term173 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term4 := (((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term70 (x0 : nat) (x1 : nat) := ~ ((Peano.lt (Nat.modulo x0 x1) x1) = (~ (x1 = (NUMERAL 0)))).
Definition term53 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0).
Definition term48 := and (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term43 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term38 := and (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0).
Definition term33 := and (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0).
Definition term12 := imp (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))).
Definition term6 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL 0)).
Definition term2 := ((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term39 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))).
Definition term46 := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term137 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term108 (x0 : nat) := exists y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0))).
Definition term92 (x0 : nat) := fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0)).
Definition term20 := (forall y0 : nat, ~ (Peano.lt y0 (NUMERAL 0))) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term24 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term138 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term150 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term144 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term60 := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))).
Definition term15 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term64 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (~ (x1 = (NUMERAL 0)))).
Definition term63 (x0 : nat) (x1 : nat) := and (Peano.lt (Nat.modulo x0 x1) x1).
Definition term19 := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term3 := (((~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term111 := exists y0 : nat, (exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) \/ (exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term112 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (~ (y2 = (NUMERAL 0)))) y0).
Definition term90 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0) \/ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) y0).
Definition term159 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt (Nat.modulo x0 y0) y0) x1).
Definition term23 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term41 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term127 := or (exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))).
Definition term175 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> False.
Definition term83 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) = (~ (y2 = (NUMERAL 0)))) y0).
Definition term50 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) x0.
Definition term36 := fun y0 : nat => (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term172 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> x1 = (NUMERAL 0).
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0)))) x1.
Definition term107 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) y0.
Definition term102 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0.
Definition term93 (x0 : nat) := fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0))).
Definition term158 (x0 : nat) := Peano.lt (Nat.modulo x0 (NUMERAL 0)) (NUMERAL 0).
Definition term110 := fun y0 : nat => (exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) \/ (exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term34 := (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))).
Definition term42 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term29 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term5 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term120 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0) \/ ((fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (~ (y2 = (NUMERAL 0)))) y0).
Definition term82 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) x0).
Definition term58 (x0 : nat) := forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term117 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) x0).
Definition term152 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term81 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) x0.
Definition term44 := (forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0))))).
Definition term37 := forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0.
Definition term32 := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0.
Definition term78 (x0 : nat) := fun y0 : nat => ((Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) \/ ((~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0)))).
Definition term96 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0)))) x1.
Definition term155 (x0 : nat) := fun y0 : nat => Peano.lt (Nat.modulo x0 y0) y0.
Definition term7 := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False.
Definition term1 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) -> ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term145 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term80 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) = (~ (y2 = (NUMERAL 0)))) y0).
Definition term74 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) = (~ (y1 = (NUMERAL 0)))) y0).
Definition term131 := (exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) \/ (exists y0 : nat, exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term101 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0.
Definition term160 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (Nat.modulo x0 x1) x1).
Definition term55 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term30 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.lt (NUMERAL 0) x0.
Definition term17 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term66 (x0 : nat) (x1 : nat) := or ((Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (~ (x1 = (NUMERAL 0))))).
Definition term68 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (~ (x1 = (NUMERAL 0))))) \/ ((~ (Peano.lt (Nat.modulo x0 x1) x1)) /\ (~ (x1 = (NUMERAL 0)))).
Definition term94 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) x1.
Definition term156 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt (Nat.modulo x0 y0) y0) x1.
Definition term59 := fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))).
Definition term129 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (~ (y2 = (NUMERAL 0)))) y0.
Definition term124 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0.
Definition term35 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term130 := exists y0 : nat, exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0))).
Definition term125 := exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0)).
Definition term85 := exists y0 : nat, exists y1 : nat, ((Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) \/ ((~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))).
Definition term88 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term77 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) = (~ (y1 = (NUMERAL 0)))) y0).
Definition term76 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0)))) x1).
Definition term27 (x0 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term45 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) x0.
Definition term140 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term67 (x0 : nat) (x1 : nat) := or ((Peano.lt (Nat.modulo x0 x1) x1) /\ (x1 = (NUMERAL 0))).
Definition term18 := ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.lt (NUMERAL 0) y0) /\ ((forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))))) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term98 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0) \/ ((fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) y0).
Definition term126 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0).
Definition term104 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0).
Definition term61 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term97 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) x1) \/ ((fun y0 : nat => (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0)))) x1).
Definition term164 (x0 : nat) := (Peano.lt x0 (NUMERAL 0)) -> False.
Definition term25 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term49 := (forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> ~ (y0 = (NUMERAL 0))) /\ ((forall y0 : nat, (Peano.lt (NUMERAL 0) y0) -> Peano.le (NUMERAL (BIT1 0)) y0) /\ ((forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.lt (NUMERAL 0) y0) /\ (forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)))))).
Definition term28 := fun y0 : nat => (Peano.le (NUMERAL (BIT1 0)) y0) -> ~ (y0 = (NUMERAL 0)).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term72 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term69 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) /\ (x1 = (NUMERAL 0))) \/ ((~ (Peano.lt (Nat.modulo x0 x1) x1)) /\ (~ (x1 = (NUMERAL 0)))).
Definition term149 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term143 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term26 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term40 (x0 : nat) := (Peano.lt (NUMERAL 0) x0) -> ~ (x0 = (NUMERAL 0)).
Definition term89 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term21 := imp (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))).
Definition term170 (x0 : Prop) := x0 -> ~ x0.
Definition term169 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) -> ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term135 (x0 : nat) := @eq Prop ((exists y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) /\ (y0 = (NUMERAL 0))) \/ (exists y0 : nat, (~ (Peano.lt (Nat.modulo x0 y0) y0)) /\ (~ (y0 = (NUMERAL 0))))).
Definition term134 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.lt (Nat.modulo x0 y1) y1) /\ (y1 = (NUMERAL 0))) y0) \/ (exists y0 : nat, (fun y1 : nat => (~ (Peano.lt (Nat.modulo x0 y1) y1)) /\ (~ (y1 = (NUMERAL 0)))) y0)).
Definition term133 := @eq Prop ((exists y0 : nat, exists y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) /\ (y1 = (NUMERAL 0))) \/ (exists y0 : nat, exists y1 : nat, (~ (Peano.lt (Nat.modulo y0 y1) y1)) /\ (~ (y1 = (NUMERAL 0))))).
Definition term132 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (Peano.lt (Nat.modulo y1 y2) y2) /\ (y2 = (NUMERAL 0))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (~ (Peano.lt (Nat.modulo y1 y2) y2)) /\ (~ (y2 = (NUMERAL 0)))) y0)).
