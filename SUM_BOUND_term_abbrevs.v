Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') := fun y0 : real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (real_mul (real_of_num (@CARD a0 y1)) y0) = (@sum a0 y1 (fun y2 : a0 => y0)).
Definition term9 (a0 : Type') := fun y0 : real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 y1 (fun y2 : a0 => y0)) = (real_mul (real_of_num (@CARD a0 y1)) y0).
Definition term63 (a0 : Type') (x0 : a0 -> real) (x1 : real) (x2 : a0) (x3 : a0 -> Prop) := ((@IN a0 x2 x3) -> (real_le (x0 x2) ((fun y0 : a0 => x1) x2)) = True) -> ((@IN a0 x2 x3) -> real_le (x0 x2) ((fun y0 : a0 => x1) x2)) = ((@IN a0 x2 x3) -> True).
Definition term5 (a0 : Type') (x0 : real) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => x0)) = (real_mul (real_of_num (@CARD a0 y0)) x0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := real_mul (real_of_num (@CARD a0 x0)) x1.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> True.
Definition term70 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term88 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> real, forall y2 : real, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> real_le (y1 y3) y2)) -> real_le (@sum a0 y0 y1) (real_mul (real_of_num (@CARD a0 y0)) y2).
Definition term52 (a0 : Type') (x0 : a0 -> real) (x1 : real) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) -> (real_le (x0 x2) ((fun y0 : a0 => x1) x2)) = x4) -> ((@IN a0 x2 x3) -> real_le (x0 x2) ((fun y0 : a0 => x1) x2)) = ((@IN a0 x2 x3) -> x4).
Definition term77 := fun y0 : real => True.
Definition term58 (a0 : Type') (x0 : real) (x1 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => x0) y0) x1).
Definition term69 (a0 : Type') := forall y0 : a0, True.
Definition term13 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) x0.
Definition term17 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1)) x2.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) ((fun y1 : a0 => x2) y0).
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term90 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term85 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> real, x0.
Definition term8 (a0 : Type') (x0 : real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (real_mul (real_of_num (@CARD a0 y0)) x0) = (@sum a0 y0 (fun y1 : a0 => x0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : Prop) := (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> (real_le (@sum a0 x0 x1) (real_mul (real_of_num (@CARD a0 x0)) x2)) = x3) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> real_le (@sum a0 x0 x1) (real_mul (real_of_num (@CARD a0 x0)) x2)) = (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> x3).
Definition term79 := forall y0 : real, True.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) (x4 : Prop) (x5 : Prop) := ((@IN a0 x3 x0) = x4) -> (x4 -> (real_le (x1 x3) ((fun y0 : a0 => x2) x3)) = x5) -> ((@IN a0 x3 x0) -> real_le (x1 x3) ((fun y0 : a0 => x2) x3)) = (x4 -> x5).
Definition term80 (x0 : Prop) := forall y0 : real, x0.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_le (@sum a0 x0 x1).
Definition term56 (a0 : Type') (x0 : real) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term57 (a0 : Type') (x0 : real) := fun y0 : a0 => (fun y1 : a0 => x0) y0.
Definition term12 (a0 : Type') := forall y0 : real, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (real_mul (real_of_num (@CARD a0 y1)) y0) = (@sum a0 y1 (fun y2 : a0 => y0)).
Definition term11 (a0 : Type') := forall y0 : real, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 y1 (fun y2 : a0 => y0)) = (real_mul (real_of_num (@CARD a0 y1)) y0).
Definition term29 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> real_le (x0 y2) x2)) = y0) -> (y0 -> (real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = y1) -> (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> real_le (x0 y2) x2)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = (y0 -> y1)) x3.
Definition term42 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) ((fun y1 : a0 => x2) y0))) -> (real_le (@sum a0 x1 x0) (@sum a0 x1 (fun y0 : a0 => x2))) = True.
Definition term51 (a0 : Type') (x0 : a0 -> real) (x1 : real) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) = (@IN a0 x2 x3)) -> ((@IN a0 x2 x3) -> (real_le (x0 x2) ((fun y0 : a0 => x1) x2)) = x4) -> ((@IN a0 x2 x3) -> real_le (x0 x2) ((fun y0 : a0 => x1) x2)) = ((@IN a0 x2 x3) -> x4).
Definition term7 (a0 : Type') (x0 : real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => x0)) = (real_mul (real_of_num (@CARD a0 y0)) x0).
Definition term15 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0)) x1.
Definition term78 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := forall y0 : real, ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) y0)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) y0).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) := (@IN a0 x2 x0) -> (real_le (x1 x2) x3) = True.
Definition term38 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : real) := real_le (x0 x1) x2.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term23 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := (@FINITE a0 x0) -> (real_mul (real_of_num (@CARD a0 x0)) x1) = (@sum a0 x0 (fun y0 : a0 => x1)).
Definition term6 (a0 : Type') (x0 : real) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (real_mul (real_of_num (@CARD a0 y0)) x0) = (@sum a0 y0 (fun y1 : a0 => x0)).
Definition term59 (a0 : Type') (x0 : real) (x1 : a0) := @eq real ((fun y0 : a0 => x0) x1).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term32 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) (x3 : Prop) (x4 : Prop) := (((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) x2)) = x3) -> (x3 -> (real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = x4) -> (((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) x2)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = (x3 -> x4).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> (real_le (@sum a0 x0 x1) (real_mul (real_of_num (@CARD a0 x0)) x2)) = True) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> real_le (@sum a0 x0 x1) (real_mul (real_of_num (@CARD a0 x0)) x2)) = (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> True).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) := (@IN a0 x3 x0) -> real_le (x1 x3) ((fun y0 : a0 => x2) x3).
Definition term67 (a0 : Type') := fun y0 : a0 => True.
Definition term54 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : real) := (@IN a0 x2 x0) -> real_le (x1 x2) x3.
Definition term76 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := fun y0 : real => ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) y0)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) y0).
Definition term20 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> real_le (x1 y0) x2) x3.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := @sum a0 x0 (fun y0 : a0 => x1).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) (x4 : Prop) := forall y0 : Prop, ((@IN a0 x3 x0) = x4) -> (x4 -> (real_le (x1 x3) ((fun y1 : a0 => x2) x3)) = y0) -> ((@IN a0 x3 x0) -> real_le (x1 x3) ((fun y1 : a0 => x2) x3)) = (x4 -> y0).
Definition term30 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) (x3 : Prop) := forall y0 : Prop, (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) x2)) = x3) -> (x3 -> (real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = y0) -> (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) x2)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = (x3 -> y0).
Definition term24 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term22 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (real_mul (real_of_num (@CARD a0 y0)) x0) = (@sum a0 y0 (fun y1 : a0 => x0))) x1.
Definition term87 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term74 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) x2)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2).
Definition term82 (a0 : Type') := fun y0 : a0 -> real => True.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := fun y0 : a0 => (@IN a0 y0 x0) -> real_le (x1 y0) ((fun y1 : a0 => x2) y0).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x3 x0) = y0) -> (y0 -> (real_le (x1 x3) ((fun y2 : a0 => x2) x3)) = y1) -> ((@IN a0 x3 x0) -> real_le (x1 x3) ((fun y2 : a0 => x2) x3)) = (y0 -> y1).
Definition term26 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := forall y0 : Prop, forall y1 : Prop, (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> real_le (x0 y2) x2)) = y0) -> (y0 -> (real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = y1) -> (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> real_le (x0 y2) x2)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = (y0 -> y1).
Definition term25 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := (@FINITE a0 x0) -> (@sum a0 x0 (fun y0 : a0 => x1)) = (real_mul (real_of_num (@CARD a0 x0)) x1).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> real, forall y1 : real, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> real_le (y0 y2) y1)) -> real_le (@sum a0 x0 y0) (real_mul (real_of_num (@CARD a0 x0)) y1).
Definition term14 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0).
Definition term28 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2).
Definition term31 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) x2)) = x3) -> (x3 -> (real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = y0) -> (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> real_le (x0 y1) x2)) -> real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = (x3 -> y0)) x4.
Definition term55 (a0 : Type') (x0 : real) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0) y0) x1.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@IN a0 x3 x0) = x4) -> (x4 -> (real_le (x1 x3) ((fun y1 : a0 => x2) x3)) = y0) -> ((@IN a0 x3 x0) -> real_le (x1 x3) ((fun y1 : a0 => x2) x3)) = (x4 -> y0)) x5.
Definition term18 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) (x2 y0))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> real => forall y1 : real, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> real_le (y0 y2) y1)) -> real_le (@sum a0 x0 y0) (real_mul (real_of_num (@CARD a0 x0)) y1).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) ((fun y1 : a0 => x2) y0)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) (x2 y0)).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : Prop) := (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) = ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2))) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> (real_le (@sum a0 x0 x1) (real_mul (real_of_num (@CARD a0 x0)) x2)) = x3) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> real_le (@sum a0 x0 x1) (real_mul (real_of_num (@CARD a0 x0)) x2)) = (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) x2)) -> x3).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) := (@IN a0 x3 x0) -> (real_le (x1 x3) ((fun y0 : a0 => x2) x3)) = True.
Definition term46 (a0 : Type') (x0 : a0 -> real) (x1 : real) (x2 : a0) := real_le (x0 x2) ((fun y0 : a0 => x1) x2).
Definition term72 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) x2)) -> (real_le (@sum a0 x1 x0) (real_mul (real_of_num (@CARD a0 x1)) x2)) = True.
Definition term41 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) (x2 y0))) -> (real_le (@sum a0 x1 x0) (@sum a0 x1 x2)) = True.
Definition term86 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> real, forall y2 : real, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> real_le (y1 y3) y2)) -> real_le (@sum a0 y0 y1) (real_mul (real_of_num (@CARD a0 y0)) y2).
Definition term16 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1).
Definition term43 (a0 : Type') (x0 : real) := fun y0 : a0 => x0.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x3 x0) = y0) -> (y0 -> (real_le (x1 x3) ((fun y2 : a0 => x2) x3)) = y1) -> ((@IN a0 x3 x0) -> real_le (x1 x3) ((fun y2 : a0 => x2) x3)) = (y0 -> y1)) x4.
Definition term40 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : real) := real_le (@sum a0 x1 x0) (@sum a0 x1 (fun y0 : a0 => x2)).
Definition term21 (a0 : Type') (x0 : real) := (fun y0 : real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (real_mul (real_of_num (@CARD a0 y1)) y0) = (@sum a0 y1 (fun y2 : a0 => y0))) x0.
Definition term60 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := real_le (x0 x1).
Definition term89 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term84 (a0 : Type') := forall y0 : a0 -> real, True.