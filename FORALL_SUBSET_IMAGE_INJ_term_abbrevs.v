Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) x1) \/ ((fun y0 : a0 => (~ (x0 y0)) /\ (forall y1 : a0, x0 y1)) x1).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, x0 y0) /\ (~ (x0 x1)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := exists y0 : a1 -> Prop, (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) /\ (x2 y0).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or ((forall y0 : a0, x0 y0) /\ (~ (x0 x1))).
Definition term125 := (~ False) -> False.
Definition term175 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := @eq Prop (exists y0 : a1 -> Prop, (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) /\ (~ (x2 y0))).
Definition term181 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 x0 x1).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ ((fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0).
Definition term38 (x0 : Prop) := ~ (~ x0).
Definition term163 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @SUBSET a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term19 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (exists y2 : a1 -> Prop, (@SUBSET a1 y2 (@IMAGE a0 a1 y0 y1)) /\ (x0 y2)) = (exists y2 : a0 -> Prop, (@SUBSET a0 y2 y1) /\ ((forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ (@IN a0 y4 y2)) -> ((y0 y3) = (y0 y4)) = (y3 = y4)) /\ (x0 (@IMAGE a0 a1 y0 y2))))) x1.
Definition term149 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0)) x3.
Definition term160 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := exists y0 : a0 -> Prop, ~ (((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0)).
Definition term188 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := @eq Prop (~ (exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2)) /\ (~ (x1 (@IMAGE a0 a1 x2 y0)))))).
Definition term145 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := @eq Prop (~ (exists y0 : a1 -> Prop, ~ ((@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0))).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term190 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (@SUBSET a0 x1 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ (@IN a0 y1 x1)) -> ((x2 y0) = (x2 y1)) = (y0 = y1)).
Definition term4 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 /\ (x1 /\ y0)) = ((x0 /\ x1) /\ y0).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (~ (x0 y0)) /\ (forall y1 : a0, x0 y1)) x1.
Definition term176 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (fun y0 : a1 -> Prop => ~ (x0 y0)) (@IMAGE a0 a1 x1 x2).
Definition term143 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := exists y0 : a1 -> Prop, ~ ((@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0).
Definition term6 (x0 : Prop) := fun y0 : Prop => forall y1 : Prop, (x0 /\ (y0 /\ y1)) = ((x0 /\ y0) /\ y1).
Definition term74 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term29 (x0 : Prop) := (~ x0) -> False.
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) x1.
Definition term156 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := ~ (((@SUBSET a0 x3 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x3) /\ (@IN a0 y1 x3)) -> ((x2 y0) = (x2 y1)) = (y0 = y1))) -> x1 (@IMAGE a0 a1 x2 x3)).
Definition term166 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := exists y0 : a1 -> Prop, (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) /\ ((fun y1 : a1 -> Prop => ~ (x2 y1)) y0).
Definition term25 (x0 : Prop) := forall y0 : Prop, (~ (x0 -> y0)) = (x0 /\ (~ y0)).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, x0 y0.
Definition term64 (a0 : Type') (x0 : a0 -> Prop) := (~ (forall y0 : a0, x0 y0)) /\ (~ (exists y0 : a0, ~ (x0 y0))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0).
Definition term164 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := fun y0 : a1 -> Prop => (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) /\ (~ (x2 y0)).
Definition term161 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := ~ (exists y0 : a0 -> Prop, ~ (((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0))).
Definition term147 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := ~ (exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => ((@SUBSET a0 y1 x0) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x2 y2) = (x2 y3)) = (y2 = y3))) -> x1 (@IMAGE a0 a1 x2 y1)) y0)).
Definition term144 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := ~ (exists y0 : a1 -> Prop, ~ ((@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0)).
Definition term130 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := ~ (exists y0 : a1 -> Prop, ~ ((fun y1 : a1 -> Prop => (@SUBSET a1 y1 (@IMAGE a0 a1 x0 x1)) -> x2 y1) y0)).
Definition term128 (a0 : Type') (x0 : type686 a0) := ~ (exists y0 : a0 -> Prop, ~ (x0 y0)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (~ (~ (exists y0 : a0, ~ (x0 y0)))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term195 (a0 : Type') (a1 : Type') := forall y0 : type686 a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a1 -> Prop, (@SUBSET a1 y3 (@IMAGE a0 a1 y1 y2)) -> y0 y3) = (forall y3 : a0 -> Prop, ((@SUBSET a0 y3 y2) /\ (forall y4 : a0, forall y5 : a0, ((@IN a0 y4 y3) /\ (@IN a0 y5 y3)) -> ((y1 y4) = (y1 y5)) = (y4 = y5))) -> y0 (@IMAGE a0 a1 y1 y3)).
Definition term134 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := fun y0 : a1 -> Prop => (fun y1 : a1 -> Prop => (@SUBSET a1 y1 (@IMAGE a0 a1 x0 x1)) -> x2 y1) y0.
Definition term73 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term123 (x0 : Prop) := (~ x0) -> x0.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ (exists y0 : a0, (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => x0 y1) y0).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (~ (x0 y0)) /\ (forall y1 : a0, x0 y1).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) := and (exists y0 : a0, ~ (x0 y0)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, (exists y1 : a1 -> Prop, (@SUBSET a1 y1 (@IMAGE a0 a1 x1 y0)) /\ (x0 y1)) = (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x1 y2) = (x1 y3)) = (y2 = y3)) /\ (x0 (@IMAGE a0 a1 x1 y1)))).
Definition term11 := fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2)).
Definition term10 := fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 /\ (y1 /\ y2)) = ((y0 /\ y1) /\ y2).
Definition term24 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (~ (y0 -> y1)) = (y0 /\ (~ y1))) x0.
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, x0 y0) /\ ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (x1 x0)) /\ (forall y0 : a0, x1 y0).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term7 (x0 : Prop) := fun y0 : Prop => forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a1 -> Prop, (@SUBSET a1 y1 (@IMAGE a0 a1 x1 y0)) /\ (x0 y1)) = (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ ((forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x1 y2) = (x1 y3)) = (y2 = y3)) /\ (x0 (@IMAGE a0 a1 x1 y1))))) x2.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0.
Definition term108 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0.
Definition term193 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, (forall y1 : a1 -> Prop, (@SUBSET a1 y1 (@IMAGE a0 a1 x1 y0)) -> x0 y1) = (forall y1 : a0 -> Prop, ((@SUBSET a0 y1 y0) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x1 y2) = (x1 y3)) = (y2 = y3))) -> x0 (@IMAGE a0 a1 x1 y1)).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0)).
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 /\ x2).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := ~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0)))).
Definition term158 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => ~ (((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0)).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, x0 y1) /\ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y1 : a0, x0 y1).
Definition term42 (a0 : Type') := forall y0 : a0 -> Prop, (forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))).
Definition term191 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := x0 (@IMAGE a0 a1 x1 x2).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) := and (forall y0 : a0, x0 y0).
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0))) x2.
Definition term179 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x2) /\ (@IN a0 y1 x2)) -> ((x1 y0) = (x1 y1)) = (y0 = y1)) /\ ((fun y0 : a1 -> Prop => ~ (x0 y0)) (@IMAGE a0 a1 x1 x2)).
Definition term5 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0)).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) := or ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0))).
Definition term132 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) (x3 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0) x3.
Definition term159 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => ((@SUBSET a0 y1 x0) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x2 y2) = (x2 y3)) = (y2 = y3))) -> x1 (@IMAGE a0 a1 x2 y1)) y0).
Definition term142 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := exists y0 : a1 -> Prop, ~ ((fun y1 : a1 -> Prop => (@SUBSET a1 y1 (@IMAGE a0 a1 x0 x1)) -> x2 y1) y0).
Definition term14 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2))) x0.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := ((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term185 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2)) /\ (~ (x1 (@IMAGE a0 a1 x2 y0)))).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ((forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ ((~ (x0 y0)) /\ (forall y1 : a0, x0 y1)).
Definition term139 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) (x3 : a1 -> Prop) := ~ ((@SUBSET a1 x3 (@IMAGE a0 a1 x0 x1)) -> x2 x3).
Definition term153 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := @eq Prop (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((@SUBSET a0 y1 x0) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x2 y2) = (x2 y3)) = (y2 = y3))) -> x1 (@IMAGE a0 a1 x2 y1)) y0).
Definition term136 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := @eq Prop (forall y0 : a1 -> Prop, (fun y1 : a1 -> Prop => (@SUBSET a1 y1 (@IMAGE a0 a1 x0 x1)) -> x2 y1) y0).
Definition term146 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((@SUBSET a0 y1 x0) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x2 y2) = (x2 y3)) = (y2 = y3))) -> x1 (@IMAGE a0 a1 x2 y1)) y0.
Definition term129 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := forall y0 : a1 -> Prop, (fun y1 : a1 -> Prop => (@SUBSET a1 y1 (@IMAGE a0 a1 x0 x1)) -> x2 y1) y0.
Definition term157 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => ((@SUBSET a0 y1 x0) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x2 y2) = (x2 y3)) = (y2 = y3))) -> x1 (@IMAGE a0 a1 x2 y1)) y0).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) /\ x2.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) := ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0))) \/ ((exists y0 : a0, ~ (x0 y0)) /\ (forall y0 : a0, x0 y0)).
Definition term155 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => ((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0)) x3).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0, x0 y0).
Definition term133 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) (x3 : a1 -> Prop) := (@SUBSET a1 x3 (@IMAGE a0 a1 x0 x1)) -> x2 x3.
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) := or ((forall y0 : a0, x0 y0) /\ (~ (~ (exists y0 : a0, ~ (x0 y0))))).
Definition term152 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := forall y0 : a0 -> Prop, ((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0).
Definition term165 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := exists y0 : a1 -> Prop, (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) /\ (~ (x2 y0)).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term151 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => ((@SUBSET a0 y1 x0) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ (@IN a0 y3 y1)) -> ((x2 y2) = (x2 y3)) = (y2 = y3))) -> x1 (@IMAGE a0 a1 x2 y1)) y0.
Definition term137 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := @eq Prop (forall y0 : a1 -> Prop, (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, x0 y1) /\ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))).
Definition term167 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2)) /\ ((fun y1 : a1 -> Prop => ~ (x1 y1)) (@IMAGE a0 a1 x2 y0))).
Definition term187 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := ~ (exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2)) /\ (~ (x1 (@IMAGE a0 a1 x2 y0))))).
Definition term178 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := and (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ (@IN a0 y1 x0)) -> ((x1 y0) = (x1 y1)) = (y0 = y1)).
Definition term40 (a0 : Type') := fun y0 : a0 -> Prop => (forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))).
Definition term186 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2)) /\ (~ (x1 (@IMAGE a0 a1 x2 y0)))).
Definition term96 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((fun y0 : a0 => ~ (x1 y0)) x0) /\ (forall y0 : a0, x1 y0).
Definition term135 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := forall y0 : a1 -> Prop, (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := (((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term41 (a0 : Type') := forall y0 : a0 -> Prop, (~ ((forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))))) -> False.
Definition term13 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, ((y0 /\ y1) /\ y2) = (y0 /\ (y1 /\ y2)).
Definition term12 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (y0 /\ (y1 /\ y2)) = ((y0 /\ y1) /\ y2).
Definition term9 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1)).
Definition term8 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 /\ (y0 /\ y1)) = ((x0 /\ y0) /\ y1).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0.
Definition term140 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := fun y0 : a1 -> Prop => ~ ((fun y1 : a1 -> Prop => (@SUBSET a1 y1 (@IMAGE a0 a1 x0 x1)) -> x2 y1) y0).
Definition term194 (a0 : Type') (a1 : Type') (x0 : type686 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a1 -> Prop, (@SUBSET a1 y2 (@IMAGE a0 a1 y0 y1)) -> x0 y2) = (forall y2 : a0 -> Prop, ((@SUBSET a0 y2 y1) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ (@IN a0 y4 y2)) -> ((y0 y3) = (y0 y4)) = (y3 = y4))) -> x0 (@IMAGE a0 a1 y0 y2)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type686 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (exists y2 : a1 -> Prop, (@SUBSET a1 y2 (@IMAGE a0 a1 y0 y1)) /\ (x0 y2)) = (exists y2 : a0 -> Prop, (@SUBSET a0 y2 y1) /\ ((forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ (@IN a0 y4 y2)) -> ((y0 y3) = (y0 y4)) = (y3 = y4)) /\ (x0 (@IMAGE a0 a1 y0 y2)))).
Definition term3 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((x0 /\ x1) /\ y0) = (x0 /\ (x1 /\ y0)).
Definition term26 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (x0 -> y0)) = (x0 /\ (~ y0))) x1.
Definition term154 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := @eq Prop (forall y0 : a0 -> Prop, ((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0)).
Definition term182 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (@SUBSET a0 x3 x0) /\ ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x3) /\ (@IN a0 y1 x3)) -> ((x2 y0) = (x2 y1)) = (y0 = y1)) /\ ((fun y0 : a1 -> Prop => ~ (x1 y0)) (@IMAGE a0 a1 x2 x3))).
Definition term174 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := @eq Prop (exists y0 : a1 -> Prop, (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) /\ ((fun y1 : a1 -> Prop => ~ (x2 y1)) y0)).
Definition term171 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> a1) (x2 : a0 -> Prop) := and (@SUBSET a1 x0 (@IMAGE a0 a1 x1 x2)).
Definition term180 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x2) /\ (@IN a0 y1 x2)) -> ((x1 y0) = (x1 y1)) = (y0 = y1)) /\ (~ (x0 (@IMAGE a0 a1 x1 x2))).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))))) -> False) x0.
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or ((fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) x1).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) := ((forall y0 : a0, x0 y0) /\ (~ (~ (exists y0 : a0, ~ (x0 y0))))) \/ ((~ (forall y0 : a0, x0 y0)) /\ (~ (exists y0 : a0, ~ (x0 y0)))).
Definition term138 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) (x3 : a1 -> Prop) := ~ ((fun y0 : a1 -> Prop => (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0) x3).
Definition term173 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := fun y0 : a1 -> Prop => (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) /\ ((fun y1 : a1 -> Prop => ~ (x2 y1)) y0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => x0 y1) y0).
Definition term148 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => ((@SUBSET a0 y0 x0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2))) -> x1 (@IMAGE a0 a1 x2 y0).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ (exists y0 : a0, (~ (x0 y0)) /\ (forall y1 : a0, x0 y1)).
Definition term169 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ~ (x0 y0)) x1.
Definition term177 (a0 : Type') (a1 : Type') (x0 : type686 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := ~ (x0 (@IMAGE a0 a1 x1 x2)).
Definition term183 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (@SUBSET a0 x3 x0) /\ ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x3) /\ (@IN a0 y1 x3)) -> ((x2 y0) = (x2 y1)) = (y0 = y1)) /\ (~ (x1 (@IMAGE a0 a1 x2 x3)))).
Definition term172 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) (x3 : a1 -> Prop) := (@SUBSET a1 x3 (@IMAGE a0 a1 x0 x1)) /\ ((fun y0 : a1 -> Prop => ~ (x2 y0)) x3).
Definition term192 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ (@IN a0 y1 x0)) -> ((x1 y0) = (x1 y1)) = (y0 = y1).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ ((fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2)) /\ (x1 (@IMAGE a0 a1 x2 y0))).
Definition term184 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ ((forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ (@IN a0 y2 y0)) -> ((x2 y1) = (x2 y2)) = (y1 = y2)) /\ ((fun y1 : a1 -> Prop => ~ (x1 y1)) (@IMAGE a0 a1 x2 y0))).
Definition term168 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => ~ (x0 y0).
Definition term127 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, x0 y0.
Definition term150 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := ((@SUBSET a0 x3 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x3) /\ (@IN a0 y1 x3)) -> ((x2 y0) = (x2 y1)) = (y0 = y1))) -> x1 (@IMAGE a0 a1 x2 x3).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term15 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 /\ y0) /\ y1) = (x0 /\ (y0 /\ y1))) x1.
Definition term162 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) (x3 : a1 -> Prop) := (@SUBSET a1 x3 (@IMAGE a0 a1 x0 x1)) /\ (~ (x2 x3)).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ((forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ ((~ (x0 y0)) /\ (forall y1 : a0, x0 y1)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) := and (~ (forall y0 : a0, x0 y0)).
Definition term28 (x0 : Prop) (x1 : Prop) := x0 /\ (~ x1).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, ~ (x0 y0))).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((forall y0 : a0, x0 y0) /\ (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0)).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, ~ (x0 y0)) /\ (forall y0 : a0, x0 y0)).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y0 : a0, x0 y0)).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := (((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> ((~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False) -> (~ ((forall y0 : a0, x0 y0) = (~ (exists y0 : a0, ~ (x0 y0))))) -> False.
Definition term27 (x0 : Prop) (x1 : Prop) := ~ (x0 -> x1).
Definition term170 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term39 (a0 : Type') := fun y0 : a0 -> Prop => (~ ((forall y1 : a0, y0 y1) = (~ (exists y1 : a0, ~ (y0 y1))))) -> False.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, ~ (x0 y0)).
Definition term141 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := fun y0 : a1 -> Prop => ~ ((@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) := and (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (exists y0 : a0, ~ (x0 y0))).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y1 : a0, x0 y1).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term189 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := ((@SUBSET a0 x3 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x3) /\ (@IN a0 y1 x3)) -> ((x2 y0) = (x2 y1)) = (y0 = y1))) /\ (~ (x1 (@IMAGE a0 a1 x2 x3))).
Definition term118 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((forall y0 : a0, x1 y0) /\ (~ (x1 x0))) \/ ((~ (x1 x0)) /\ (forall y0 : a0, x1 y0)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, ~ (x0 y0)) /\ (forall y0 : a0, x0 y0).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) := or (exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0))).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) /\ (forall y1 : a0, x0 y1).
Definition term131 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type686 a1) := fun y0 : a1 -> Prop => (@SUBSET a1 y0 (@IMAGE a0 a1 x0 x1)) -> x2 y0.
Definition term2 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (x0 /\ (x1 /\ y0)) = ((x0 /\ x1) /\ y0).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => x0 y0) x1).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, x0 y1) /\ (~ (x0 y0)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0) /\ (forall y0 : a0, x0 y0).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (forall y1 : a0, x0 y1) /\ (~ (x0 y0))) \/ (exists y0 : a0, (~ (x0 y0)) /\ (forall y1 : a0, x0 y1))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, x0 y2) /\ (~ (x0 y1))) y0) \/ (exists y0 : a0, (fun y1 : a0 => (~ (x0 y1)) /\ (forall y2 : a0, x0 y2)) y0)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : type686 a1) := (fun y0 : type686 a1 => forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (exists y3 : a1 -> Prop, (@SUBSET a1 y3 (@IMAGE a0 a1 y1 y2)) /\ (y0 y3)) = (exists y3 : a0 -> Prop, (@SUBSET a0 y3 y2) /\ ((forall y4 : a0, forall y5 : a0, ((@IN a0 y4 y3) /\ (@IN a0 y5 y3)) -> ((y1 y4) = (y1 y5)) = (y4 = y5)) /\ (y0 (@IMAGE a0 a1 y1 y3))))) x0.
