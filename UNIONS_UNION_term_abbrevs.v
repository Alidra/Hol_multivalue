Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : type686 a0) := fun y0 : type686 a0 => (@UNIONS a0 (@UNION (a0 -> Prop) x0 y0)) = (@UNION a0 (@UNIONS a0 x0) (@UNIONS a0 y0)).
Definition term113 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x2))))).
Definition term112 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0) /\ ((forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x2))))).
Definition term119 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2)))).
Definition term70 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ~ (x0 y0).
Definition term219 := (~ False) -> False.
Definition term22 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (x0 x2) \/ (x1 x2).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type686 a0) (x3 : a0) := (((@I ((a0 -> Prop) -> Prop) x1 x0) \/ (@I ((a0 -> Prop) -> Prop) x2 x0)) /\ (@I (a0 -> Prop) x0 x3)) /\ ((forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x1 y0)) \/ (~ (@I (a0 -> Prop) y0 x3))) /\ (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x2 y0)) \/ (~ (@I (a0 -> Prop) y0 x3)))).
Definition term138 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)).
Definition term177 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2).
Definition term58 (x0 : Prop) := ~ (~ x0).
Definition term154 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ ((fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2))) y0).
Definition term206 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((((@I ((a0 -> Prop) -> Prop) x0 x2) \/ (@I ((a0 -> Prop) -> Prop) x1 x2)) /\ (@I (a0 -> Prop) x2 x3)) /\ ((forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x3))) /\ (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x1 y0)) \/ (~ (@I (a0 -> Prop) y0 x3))))) \/ ((forall y0 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 y0))) \/ (~ (@I (a0 -> Prop) y0 x3))) /\ (((@I ((a0 -> Prop) -> Prop) x0 x2) /\ (@I (a0 -> Prop) x2 x3)) \/ ((@I ((a0 -> Prop) -> Prop) x1 x2) /\ (@I (a0 -> Prop) x2 x3)))).
Definition term13 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term8 (a0 : Type') := fun y0 : type686 a0 => forall y1 : type686 a0, (@UNIONS a0 (@UNION (a0 -> Prop) y0 y1)) = (@UNION a0 (@UNIONS a0 y0) (@UNIONS a0 y1)).
Definition term193 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term41 (a0 : Type') (x0 : a0) (x1 : type686 a0) := or (@IN a0 x0 (@UNIONS a0 x1)).
Definition term120 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2)))).
Definition term97 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ (~ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2)))).
Definition term92 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := and (~ (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2))).
Definition term87 (a0 : Type') (x0 : type686 a0) (x1 : a0) := and (~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1))).
Definition term165 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (forall y2 : a0 -> Prop, ((~ (x0 y2)) /\ (~ (x1 y2))) \/ (~ (y2 x2))) /\ (((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2)))) y0.
Definition term161 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (((x0 y1) \/ (x1 y1)) /\ (y1 x2)) /\ ((forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 x2))) /\ (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 x2))))) y0.
Definition term148 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2))) y0.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term203 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := and (((@I ((a0 -> Prop) -> Prop) x0 x2) \/ (@I ((a0 -> Prop) -> Prop) x1 x2)) /\ (@I (a0 -> Prop) x2 x3)).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term100 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := or ((exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x2))))).
Definition term12 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@UNIONS a0 x1).
Definition term83 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2).
Definition term98 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x2)))).
Definition term142 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term51 (x0 : Prop) := (~ x0) -> False.
Definition term59 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (~ ((exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) = ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))))) -> False.
Definition term31 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)).
Definition term25 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := (@IN (a0 -> Prop) x3 (@UNION (a0 -> Prop) x0 x1)) /\ (@IN a0 x2 x3).
Definition term101 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := ((exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ (~ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))))) \/ ((~ (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2))) /\ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2)))).
Definition term209 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := forall y0 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) /\ ((~ (@I ((a0 -> Prop) -> Prop) x1 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))).
Definition term143 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := x0 /\ (exists y0 : a0 -> Prop, x1 y0).
Definition term36 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) /\ (@IN a0 x1 x2).
Definition term169 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := or ((fun y0 : a0 -> Prop => (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))) x3).
Definition term50 (a0 : Type') := forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))).
Definition term11 (a0 : Type') := forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (@IN a0 y2 (@UNIONS a0 (@UNION (a0 -> Prop) y0 y1))) = (@IN a0 y2 (@UNION a0 (@UNIONS a0 y0) (@UNIONS a0 y1))).
Definition term141 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term153 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := (forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x3))) /\ (((x0 x2) /\ (x2 x3)) \/ ((x1 x2) /\ (x2 x3))).
Definition term1 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @UNIONS a0 (@UNION (a0 -> Prop) x0 x1).
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@I (a0 -> Prop) x0 x1)) -> @I (a0 -> Prop) x0 x1.
Definition term60 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := ~ ((exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) = ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2)))).
Definition term115 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := and (((x0 x2) \/ (x1 x2)) /\ (x2 x3)).
Definition term38 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term2 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := @UNION a0 (@UNIONS a0 x0) (@UNIONS a0 x1).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term32 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : type686 a0) := @IN a0 x0 (@UNION a0 (@UNIONS a0 x1) (@UNIONS a0 x2)).
Definition term43 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2)).
Definition term189 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := forall y0 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 y0))) \/ (~ (@I (a0 -> Prop) y0 x2)).
Definition term62 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (~ (x0 x2)) /\ (~ (x1 x2)).
Definition term53 (a0 : Type') := ~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2)))).
Definition term215 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type686 a0) (x3 : a0) := (((x1 x0) \/ (x2 x0)) /\ (x0 x3)) /\ ((forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x3))) /\ (forall y0 : a0 -> Prop, (~ (x2 y0)) \/ (~ (y0 x3)))).
Definition term213 (x0 : Prop) := (~ x0) -> x0.
Definition term197 (a0 : Type') (x0 : type686 a0) (x1 : a0) := and (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1))).
Definition term190 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := and (forall y0 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 y0))) \/ (~ (@I (a0 -> Prop) y0 x2))).
Definition term93 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := and (forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))).
Definition term88 (a0 : Type') (x0 : type686 a0) (x1 : a0) := and (forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x1))).
Definition term79 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x1)) \/ (~ (x1 x2)).
Definition term85 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (x0 y0)) \/ (~ (y0 x1)).
Definition term49 (a0 : Type') := fun y0 : type686 a0 => forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))).
Definition term9 (a0 : Type') := fun y0 : type686 a0 => forall y1 : type686 a0, forall y2 : a0, (@IN a0 y2 (@UNIONS a0 (@UNION (a0 -> Prop) y0 y1))) = (@IN a0 y2 (@UNION a0 (@UNIONS a0 y0) (@UNIONS a0 y1))).
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((x0 y0) \/ (x1 y0)) /\ (y0 x2).
Definition term21 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (x0 x1).
Definition term45 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 => (exists y1 : a0 -> Prop, ((x0 y1) \/ (x1 y1)) /\ (y1 y0)) = ((exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) \/ (exists y1 : a0 -> Prop, (x1 y1) /\ (y1 y0))).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type686 a0) := @IN (a0 -> Prop) x0 (@UNION (a0 -> Prop) x1 x2).
Definition term15 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@UNION (a0 -> Prop) x0 x1)) /\ (@IN a0 x2 y0).
Definition term216 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term188 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 y0))) \/ (~ (@I (a0 -> Prop) y0 x2)).
Definition term157 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (exists y0 : a0 -> Prop, (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))) \/ (exists y0 : a0 -> Prop, (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)))).
Definition term114 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) x3).
Definition term108 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2)))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type686 a0) := and (@IN (a0 -> Prop) x0 (@UNION (a0 -> Prop) x1 x2)).
Definition term86 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x1)).
Definition term48 (a0 : Type') (x0 : type686 a0) := forall y0 : type686 a0, forall y1 : a0, (exists y2 : a0 -> Prop, ((x0 y2) \/ (y0 y2)) /\ (y2 y1)) = ((exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1)) \/ (exists y2 : a0 -> Prop, (y0 y2) /\ (y2 y1))).
Definition term7 (a0 : Type') (x0 : type686 a0) := forall y0 : type686 a0, forall y1 : a0, (@IN a0 y1 (@UNIONS a0 (@UNION (a0 -> Prop) x0 y0))) = (@IN a0 y1 (@UNION a0 (@UNIONS a0 x0) (@UNIONS a0 y0))).
Definition term135 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x2)) x3) \/ ((fun y0 : a0 -> Prop => (x1 y0) /\ (y0 x2)) x3).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := or (@IN (a0 -> Prop) x0 x1).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type686 a0) (x3 : a0) := or ((((x1 x0) \/ (x2 x0)) /\ (x0 x3)) /\ ((forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x3))) /\ (forall y0 : a0 -> Prop, (~ (x2 y0)) \/ (~ (y0 x3))))).
Definition term125 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := exists y0 : a0 -> Prop, (x0 y0) \/ (x1 y0).
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := or ((~ (x0 x2)) /\ (~ (x1 x2))).
Definition term156 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2))).
Definition term198 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x1 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))).
Definition term90 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x2))).
Definition term178 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := or ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2)).
Definition term183 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (~ (x0 x1)).
Definition term133 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := or ((fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2).
Definition term218 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2)) -> False.
Definition term173 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (((x0 y1) \/ (x1 y1)) /\ (y1 x2)) /\ ((forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 x2))) /\ (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 x2))))) y0) \/ ((fun y1 : a0 -> Prop => (forall y2 : a0 -> Prop, ((~ (x0 y2)) /\ (~ (x1 y2))) \/ (~ (y2 x2))) /\ (((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2)))) y0).
Definition term137 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) \/ ((fun y1 : a0 -> Prop => (x1 y1) /\ (y1 x2)) y0).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type686 a0) (x3 : a0) := ((fun y0 : a0 -> Prop => ((x1 y0) \/ (x2 y0)) /\ (y0 x3)) x0) /\ ((forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x3))) /\ (forall y0 : a0 -> Prop, (~ (x2 y0)) \/ (~ (y0 x3)))).
Definition term212 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) -> @I ((a0 -> Prop) -> Prop) x0 x1.
Definition term35 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (x0 x1).
Definition term155 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2))).
Definition term134 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x1) /\ (x1 x2)).
Definition term77 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2)).
Definition term54 (a0 : Type') := ((~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False.
Definition term192 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (x0 x1)).
Definition term47 (a0 : Type') (x0 : type686 a0) := fun y0 : type686 a0 => forall y1 : a0, (exists y2 : a0 -> Prop, ((x0 y2) \/ (y0 y2)) /\ (y2 y1)) = ((exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1)) \/ (exists y2 : a0 -> Prop, (y0 y2) /\ (y2 y1))).
Definition term5 (a0 : Type') (x0 : type686 a0) := fun y0 : type686 a0 => forall y1 : a0, (@IN a0 y1 (@UNIONS a0 (@UNION (a0 -> Prop) x0 y0))) = (@IN a0 y1 (@UNION a0 (@UNIONS a0 x0) (@UNIONS a0 y0))).
Definition term174 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))) \/ ((forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)))).
Definition term81 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term72 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := forall y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0).
Definition term145 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))) /\ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2))) y0).
Definition term44 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := fun y0 : a0 => (@IN a0 y0 (@UNIONS a0 (@UNION (a0 -> Prop) x0 x1))) = (@IN a0 y0 (@UNION a0 (@UNIONS a0 x0) (@UNIONS a0 x1))).
Definition term158 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (((x0 y1) \/ (x1 y1)) /\ (y1 x2)) /\ ((forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 x2))) /\ (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 x2))))) y0) \/ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (forall y2 : a0 -> Prop, ((~ (x0 y2)) /\ (~ (x1 y2))) \/ (~ (y2 x2))) /\ (((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2)))) y0).
Definition term126 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) \/ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x1 y1) /\ (y1 x2)) y0).
Definition term84 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term75 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0).
Definition term111 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := and (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0).
Definition term200 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (@I ((a0 -> Prop) -> Prop) x0 x2) \/ (@I ((a0 -> Prop) -> Prop) x1 x2).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term118 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2)))).
Definition term211 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) /\ ((~ (@I ((a0 -> Prop) -> Prop) x1 y0)) \/ (~ (@I (a0 -> Prop) y0 x2)))) x3.
Definition term69 (a0 : Type') (x0 : type686 a0) := ~ (ex x0).
Definition term66 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x0 x2) \/ (x1 x2))) \/ (~ (x2 x3)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := and (@IN (a0 -> Prop) x0 x1).
Definition term191 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := (forall y0 : a0 -> Prop, ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 y0))) \/ (~ (@I (a0 -> Prop) y0 x3))) /\ (((@I ((a0 -> Prop) -> Prop) x0 x2) /\ (@I (a0 -> Prop) x2 x3)) \/ ((@I ((a0 -> Prop) -> Prop) x1 x2) /\ (@I (a0 -> Prop) x2 x3))).
Definition term124 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (exists y0 : a0 -> Prop, x0 y0) \/ (exists y0 : a0 -> Prop, x1 y0).
Definition term42 (a0 : Type') (x0 : type686 a0) (x1 : a0) := or (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1)).
Definition term202 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((@I ((a0 -> Prop) -> Prop) x0 x2) \/ (@I ((a0 -> Prop) -> Prop) x1 x2)) /\ (@I (a0 -> Prop) x2 x3).
Definition term27 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@UNION (a0 -> Prop) x0 x1)) /\ (@IN a0 x2 y0).
Definition term187 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((~ (@I ((a0 -> Prop) -> Prop) x0 x2)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 x2))) \/ (~ (@I (a0 -> Prop) x2 x3)).
Definition term46 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0, (exists y1 : a0 -> Prop, ((x0 y1) \/ (x1 y1)) /\ (y1 y0)) = ((exists y1 : a0 -> Prop, (x0 y1) /\ (y1 y0)) \/ (exists y1 : a0 -> Prop, (x1 y1) /\ (y1 y0))).
Definition term140 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))) /\ (exists y0 : a0 -> Prop, ((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2))).
Definition term3 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0, (@IN a0 y0 (@UNIONS a0 (@UNION (a0 -> Prop) x0 x1))) = (@IN a0 y0 (@UNION a0 (@UNIONS a0 x0) (@UNIONS a0 x1))).
Definition term33 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : type686 a0) := (@IN a0 x1 (@UNIONS a0 x0)) \/ (@IN a0 x1 (@UNIONS a0 x2)).
Definition term207 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((~ (@I ((a0 -> Prop) -> Prop) x0 x2)) \/ (~ (@I (a0 -> Prop) x2 x3))) /\ ((~ (@I ((a0 -> Prop) -> Prop) x1 x2)) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term37 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 x1) /\ (x1 x2).
Definition term146 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ ((fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2))) y0).
Definition term175 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, ((((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))) \/ ((forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)))).
Definition term57 (a0 : Type') := ~ (~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))).
Definition term52 (a0 : Type') := (~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False.
Definition term95 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))) /\ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))).
Definition term106 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := exists y0 : a0 -> Prop, (x0 y0) /\ x1.
Definition term94 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (~ (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2))) /\ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))).
Definition term176 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term55 (a0 : Type') := (((~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False.
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (@I (a0 -> Prop) x0 x1).
Definition term172 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((((x0 x2) \/ (x1 x2)) /\ (x2 x3)) /\ ((forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x3))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x3))))) \/ ((forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x3))) /\ (((x0 x2) /\ (x2 x3)) \/ ((x1 x2) /\ (x2 x3)))).
Definition term152 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := (forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))) /\ ((fun y0 : a0 -> Prop => ((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2))) x3).
Definition term208 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))) /\ ((~ (@I ((a0 -> Prop) -> Prop) x1 y0)) \/ (~ (@I (a0 -> Prop) y0 x2))).
Definition term99 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := or ((exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ (~ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))))).
Definition term19 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : type686 a0) := (@IN (a0 -> Prop) x1 x0) \/ (@IN (a0 -> Prop) x1 x2).
Definition term195 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1)).
Definition term160 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))) x3.
Definition term10 (a0 : Type') := forall y0 : type686 a0, forall y1 : type686 a0, (@UNIONS a0 (@UNION (a0 -> Prop) y0 y1)) = (@UNION a0 (@UNIONS a0 y0) (@UNIONS a0 y1)).
Definition term105 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := (exists y0 : a0 -> Prop, x0 y0) /\ x1.
Definition term186 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := or ((~ (@I ((a0 -> Prop) -> Prop) x0 x2)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 x2))).
Definition term194 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term74 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) x3).
Definition term185 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (~ (@I ((a0 -> Prop) -> Prop) x0 x2)) /\ (~ (@I ((a0 -> Prop) -> Prop) x1 x2)).
Definition term73 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) x3.
Definition term82 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2.
Definition term210 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1))) x2.
Definition term201 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := and ((@I ((a0 -> Prop) -> Prop) x0 x2) \/ (@I ((a0 -> Prop) -> Prop) x1 x2)).
Definition term91 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := ~ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))).
Definition term64 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := or (~ ((x0 x2) \/ (x1 x2))).
Definition term163 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := or (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (((x0 y1) \/ (x1 y1)) /\ (y1 x2)) /\ ((forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 x2))) /\ (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 x2))))) y0).
Definition term130 (a0 : Type') (x0 : type686 a0) (x1 : a0) := or (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term144 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := exists y0 : a0 -> Prop, x0 /\ (x1 y0).
Definition term14 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : type686 a0) := @IN a0 x0 (@UNIONS a0 (@UNION (a0 -> Prop) x1 x2)).
Definition term67 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x0 x2)) /\ (~ (x1 x2))) \/ (~ (x2 x3)).
Definition term199 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x2) \/ (x1 x2)) /\ (x2 x3).
Definition term196 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1)).
Definition term179 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((@I ((a0 -> Prop) -> Prop) x0 x2) /\ (@I (a0 -> Prop) x2 x3)) \/ ((@I ((a0 -> Prop) -> Prop) x1 x2) /\ (@I (a0 -> Prop) x2 x3)).
Definition term121 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := or (exists y0 : a0 -> Prop, (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))).
Definition term128 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0.
Definition term109 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0.
Definition term151 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))) /\ (exists y0 : a0 -> Prop, ((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)))).
Definition term150 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))) /\ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2))) y0)).
Definition term61 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := ~ ((x0 x2) \/ (x1 x2)).
Definition term56 (a0 : Type') := (((~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False) -> ((~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False) -> (~ (forall y0 : type686 a0, forall y1 : type686 a0, forall y2 : a0, (exists y3 : a0 -> Prop, ((y0 y3) \/ (y1 y3)) /\ (y3 y2)) = ((exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2)) \/ (exists y3 : a0 -> Prop, (y1 y3) /\ (y3 y2))))) -> False.
Definition term139 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, ((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)).
Definition term181 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term89 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2))) /\ (~ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))).
Definition term159 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (((x0 y1) \/ (x1 y1)) /\ (y1 x2)) /\ ((forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 x2))) /\ (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 x2))))) y0) \/ ((fun y1 : a0 -> Prop => (forall y2 : a0 -> Prop, ((~ (x0 y2)) /\ (~ (x1 y2))) \/ (~ (y2 x2))) /\ (((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2)))) y0).
Definition term127 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) \/ ((fun y1 : a0 -> Prop => (x1 y1) /\ (y1 x2)) y0).
Definition term80 (a0 : Type') (x0 : type686 a0) (x1 : a0) := ~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1)).
Definition term71 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := ~ (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term24 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) := and ((x0 x2) \/ (x1 x2)).
Definition term39 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1).
Definition term6 (a0 : Type') (x0 : type686 a0) := forall y0 : type686 a0, (@UNIONS a0 (@UNION (a0 -> Prop) x0 y0)) = (@UNION a0 (@UNIONS a0 x0) (@UNIONS a0 y0)).
Definition term30 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : type686 a0) := @eq Prop (@IN a0 x0 (@UNIONS a0 (@UNION (a0 -> Prop) x1 x2))).
Definition term102 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := ((exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x2))))) \/ ((forall y0 : a0 -> Prop, ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2))) /\ ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2)))).
Definition term164 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)))) x3.
Definition term76 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := fun y0 : a0 -> Prop => ((~ (x0 y0)) /\ (~ (x1 y0))) \/ (~ (y0 x2)).
Definition term205 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type686 a0) (x3 : a0) := or ((((@I ((a0 -> Prop) -> Prop) x1 x0) \/ (@I ((a0 -> Prop) -> Prop) x2 x0)) /\ (@I (a0 -> Prop) x0 x3)) /\ ((forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x1 y0)) \/ (~ (@I (a0 -> Prop) y0 x3))) /\ (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x2 y0)) \/ (~ (@I (a0 -> Prop) y0 x3))))).
Definition term29 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term78 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x1) /\ (x1 x2)).
Definition term166 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (forall y2 : a0 -> Prop, ((~ (x0 y2)) /\ (~ (x1 y2))) \/ (~ (y2 x2))) /\ (((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2)))) y0.
Definition term162 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (((x0 y1) \/ (x1 y1)) /\ (y1 x2)) /\ ((forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 x2))) /\ (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 x2))))) y0.
Definition term149 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2))) y0.
Definition term129 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0.
Definition term110 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0.
Definition term40 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1).
Definition term147 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2))) x3.
Definition term182 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term107 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => ((x0 y1) \/ (x1 y1)) /\ (y1 x2)) y0) /\ ((forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x2))) /\ (forall y0 : a0 -> Prop, (~ (x1 y0)) \/ (~ (y0 x2)))).
Definition term171 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) (x3 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))) x3) \/ ((fun y0 : a0 -> Prop => (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2)))) x3).
Definition term96 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := and (exists y0 : a0 -> Prop, ((x0 y0) \/ (x1 y0)) /\ (y0 x2)).
Definition term68 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x0 x2) \/ (x1 x2)) /\ (x2 x3)).
Definition term136 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x2) /\ (x2 x3)) \/ ((x1 x2) /\ (x2 x3)).
Definition term217 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2)).
Definition term184 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term168 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, (((x0 y0) \/ (x1 y0)) /\ (y0 x2)) /\ ((forall y1 : a0 -> Prop, (~ (x0 y1)) \/ (~ (y1 x2))) /\ (forall y1 : a0 -> Prop, (~ (x1 y1)) \/ (~ (y1 x2))))) \/ (exists y0 : a0 -> Prop, (forall y1 : a0 -> Prop, ((~ (x0 y1)) /\ (~ (x1 y1))) \/ (~ (y1 x2))) /\ (((x0 y0) /\ (y0 x2)) \/ ((x1 y0) /\ (y0 x2))))).
Definition term167 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (((x0 y1) \/ (x1 y1)) /\ (y1 x2)) /\ ((forall y2 : a0 -> Prop, (~ (x0 y2)) \/ (~ (y2 x2))) /\ (forall y2 : a0 -> Prop, (~ (x1 y2)) \/ (~ (y2 x2))))) y0) \/ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (forall y2 : a0 -> Prop, ((~ (x0 y2)) /\ (~ (x1 y2))) \/ (~ (y2 x2))) /\ (((x0 y1) /\ (y1 x2)) \/ ((x1 y1) /\ (y1 x2)))) y0)).
Definition term132 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x2)) \/ (exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2))).
Definition term131 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) (x2 : a0) := @eq Prop ((exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x2)) y0) \/ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (x1 y1) /\ (y1 x2)) y0)).
