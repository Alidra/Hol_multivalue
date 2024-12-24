Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 x0 x1)) = (@IN a0 y0 (@EMPTY a0)).
Definition term130 := (~ False) -> False.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 x1 x2)).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0)).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0) \/ ((fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0).
Definition term41 (x0 : Prop) := ~ (~ x0).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) \/ (((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (x1 x2).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (exists y0 : a0, (x0 y0) /\ (x1 y0)).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term75 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term34 (x0 : Prop) := (~ x0) -> False.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@DISJOINT a0 x0 y0) = (~ (exists y1 : a0, (@IN a0 y1 x0) /\ (@IN a0 y1 y0))).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ ((x0 y0) /\ (x1 y0)))) /\ (~ (exists y0 : a0, (x0 y0) /\ (x1 y0))).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 x0 x1)) = (@IN a0 y0 (@EMPTY a0)).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ (x0 y0)) \/ (~ (x1 y0))) x2.
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((fun y0 : a0 => (x1 y0) /\ (x2 y0)) x0) /\ (forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 y0))).
Definition term74 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term36 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2)))).
Definition term127 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term126 (x0 : Prop) := (~ x0) -> x0.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0) \/ (exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))).
Definition term128 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x2).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => ~ ((x0 y0) /\ (x1 y0))) x2).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0.
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (exists y0 : a0, (x0 y0) /\ (x1 y0)).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))) = (~ (exists y0 : a0, (x0 y0) /\ (x1 y0)))).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, ~ ((x0 y1) /\ (y0 y1))) = (~ (exists y1 : a0, (x0 y1) /\ (y0 y1))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 (@INTER a0 x0 y0)) = (@IN a0 y1 (@EMPTY a0))) = (~ (exists y1 : a0, (@IN a0 y1 x0) /\ (@IN a0 y1 y0))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (x0 y0) /\ (x1 y0))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (x0 y0) /\ (x1 y0)).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@DISJOINT a0 x0 y0) = (~ (exists y1 : a0, (@IN a0 y1 x0) /\ (@IN a0 y1 y0))).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term37 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False.
Definition term119 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 y0))) /\ ((x1 x0) /\ (x2 x0))) \/ (((x1 x0) /\ (x2 x0)) /\ (forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 y0)))).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) /\ (x1 x2)).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) \/ (((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (@DISJOINT a0 x0 x1).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (x0 y0) /\ (x1 y0))) \/ ((exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (exists y0 : a0, (@IN a0 y0 x0) /\ (@IN a0 y0 x1)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ ((x0 x2) /\ (x1 x2))).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))) /\ (~ (~ (exists y0 : a0, (x0 y0) /\ (x1 y0))))).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) x2.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => ~ ((x0 y0) /\ (x1 y0))) x2.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, (@IN a0 y0 (@INTER a0 x0 x1)) = (@IN a0 y0 (@EMPTY a0))).
Definition term40 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((x0 y0) /\ (x1 y0)).
Definition term35 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ ((fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (forall y1 : a0, ~ ((x0 y1) /\ (y0 y1))) = (~ (exists y1 : a0, (x0 y1) /\ (y0 y1))).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 (@INTER a0 x0 y0)) = (@IN a0 y1 (@EMPTY a0))) = (~ (exists y1 : a0, (@IN a0 y1 x0) /\ (@IN a0 y1 y0))).
Definition term38 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False.
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) /\ (@IN a0 y0 x1).
Definition term33 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 (@INTER a0 y0 y1)) = (@IN a0 y2 (@EMPTY a0))) = (~ (exists y2 : a0, (@IN a0 y2 y0) /\ (@IN a0 y2 y1))).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@DISJOINT a0 y0 y1) = (~ (exists y2 : a0, (@IN a0 y2 y0) /\ (@IN a0 y2 y1))).
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((x1 x0) /\ (x2 x0)) /\ (forall y0 : a0, (~ (x1 y0)) \/ (~ (x2 y0))).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (x1 x2)) -> False.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) x2.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x0 x2) /\ (x1 x2)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((fun y0 : a0 => (x0 y0) /\ (x1 y0)) x2).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 x2).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))) /\ (~ (~ (exists y0 : a0, (x0 y0) /\ (x1 y0))))) \/ ((~ (forall y0 : a0, ~ ((x0 y0) /\ (x1 y0)))) /\ (~ (exists y0 : a0, (x0 y0) /\ (x1 y0)))).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ~ ((fun y1 : a0 => ~ ((x0 y1) /\ (x1 y1))) y0).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (@IN a0 y0 x0) /\ (@IN a0 y0 x1).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))) = (~ (exists y0 : a0, (x0 y0) /\ (x1 y0))))) -> False.
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) \/ (exists y0 : a0, ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (x1 x2)).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0) \/ ((fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0)).
Definition term32 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))).
Definition term10 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 (@INTER a0 y0 y1)) = (@IN a0 y2 (@EMPTY a0))) = (~ (exists y2 : a0, (@IN a0 y2 y0) /\ (@IN a0 y2 y1))).
Definition term9 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@DISJOINT a0 y0 y1) = (~ (exists y2 : a0, (@IN a0 y2 y0) /\ (@IN a0 y2 y1))).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (forall y0 : a0, ~ ((x0 y0) /\ (x1 y0)))).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (x0 y0) /\ (x1 y0))).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) /\ (x1 y0).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (x0 y0) /\ (x1 y0)) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0) /\ (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0)))).
Definition term39 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, ~ ((y0 y2) /\ (y1 y2))) = (~ (exists y2 : a0, (y0 y2) /\ (y1 y2))))) -> False.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ ((x0 y0) /\ (x1 y0)).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0.
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) x2).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) \/ (~ (x1 y0)).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ~ ((x0 y1) /\ (x1 y1))) y0).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (exists y0 : a0, (fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (exists y0 : a0, (x0 y0) /\ (x1 y0))).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => (x0 y1) /\ (x1 y1)) y0).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (~ ((x0 x2) /\ (x1 x2))).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (x1 x2)).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((fun y0 : a0 => (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) x2) \/ ((fun y0 : a0 => ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1)))) x2).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) /\ (x1 y0).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, ~ ((x0 y0) /\ (x1 y0))) /\ (~ (~ (exists y0 : a0, (x0 y0) /\ (x1 y0)))).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (forall y0 : a0, (~ (x0 y0)) \/ (~ (x1 y0))) /\ ((x0 x2) /\ (x1 x2)).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))) /\ ((x0 y0) /\ (x1 y0))) \/ (exists y0 : a0, ((x0 y0) /\ (x1 y0)) /\ (forall y1 : a0, (~ (x0 y1)) \/ (~ (x1 y1))))).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2))) /\ ((x0 y1) /\ (x1 y1))) y0) \/ (exists y0 : a0, (fun y1 : a0 => ((x0 y1) /\ (x1 y1)) /\ (forall y2 : a0, (~ (x0 y2)) \/ (~ (x1 y2)))) y0)).
