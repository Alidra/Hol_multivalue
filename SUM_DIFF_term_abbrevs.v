Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (@sum a0 (@DIFF a0 x0 x1) x2).
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y2 y1)) -> (x0 (@iterate a1 a0 x0 (@DIFF a0 y1 y2) y0) (@iterate a1 a0 x0 y2 y0)) = (@iterate a1 a0 x0 y1 y0).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (@iterate real a0 real_add (@DIFF a0 x0 x1) x2).
Definition term54 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term60 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y2 y1)) -> (@sum a0 (@DIFF a0 y1 y2) y0) = (real_sub (@sum a0 y1 y0) (@sum a0 y2 y0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y2 y1)) -> (x0 (@iterate a1 a0 x0 (@DIFF a0 y1 y2) y0) (@iterate a1 a0 x0 y2 y0)) = (@iterate a1 a0 x0 y1 y0).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@monoidal real real_add) /\ ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1))) -> (real_add (@iterate real a0 real_add (@DIFF a0 x1 x0) x2) (@iterate real a0 real_add x0 x2)) = (@iterate real a0 real_add x1 x2).
Definition term41 := and (@monoidal real real_add).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := @iterate real a0 real_add (@DIFF a0 x0 x1) x2.
Definition term62 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> real, x0.
Definition term55 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term31 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : Prop) := (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> ((@sum a0 (@DIFF a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (@sum a0 x1 x0))) = x3) -> (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> (@sum a0 (@DIFF a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (@sum a0 x1 x0))) = (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> x3).
Definition term19 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (x0 = (real_sub x1 y0)) = ((real_add x0 y0) = x1)) x2.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ (@SUBSET a0 y0 x0)) -> (@sum a0 (@DIFF a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (@sum a0 y0 x1)).
Definition term56 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 y1 y0)) -> (@sum a0 (@DIFF a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (@sum a0 y1 x0)).
Definition term16 (x0 : real) := forall y0 : real, forall y1 : real, (x0 = (real_sub y0 y1)) = ((real_add x0 y1) = y0).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) = y0) -> (y0 -> ((@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = y1) -> (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> (@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = (y0 -> y1)) x3.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@monoidal real real_add) /\ ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> (@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2)).
Definition term30 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : Prop) := (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) = ((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2))) -> (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> ((@sum a0 (@DIFF a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (@sum a0 x1 x0))) = x3) -> (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> (@sum a0 (@DIFF a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (@sum a0 x1 x0))) = (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> x3).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 y1 y0)) -> (x0 (@iterate a1 a0 x0 (@DIFF a0 y0 y1) x1) (@iterate a1 a0 x0 y1 x1)) = (@iterate a1 a0 x0 y0 x1)) x2.
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_sub (@sum a0 x0 x2) (@sum a0 x1 x2).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x1) /\ (@SUBSET a0 y0 x1)) -> (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 y0) x2) (@iterate a1 a0 x0 y0 x2)) = (@iterate a1 a0 x0 x1 x2)) x3.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @sum a0 (@DIFF a0 x0 x1).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> ((@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = True.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := @eq real (real_add (@sum a0 (@DIFF a0 x0 x1) x2) (@sum a0 x1 x2)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) -> True.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) (x4 : Prop) := (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) = x3) -> (x3 -> ((@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = x4) -> (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> (@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = (x3 -> x4).
Definition term47 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> ((@sum a0 (@DIFF a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (@sum a0 x1 x0))) = True) -> (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> (@sum a0 (@DIFF a0 x2 x1) x0) = (real_sub (@sum a0 x2 x0) (@sum a0 x1 x0))) = (((@FINITE a0 x2) /\ (@SUBSET a0 x1 x2)) -> True).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @iterate real a0 real_add (@DIFF a0 x0 x1).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := (@monoidal a1 x1) -> ((@FINITE a0 x2) /\ (@SUBSET a0 x0 x2)) -> (x1 (@iterate a1 a0 x1 (@DIFF a0 x2 x0) x3) (@iterate a1 a0 x1 x0 x3)) = (@iterate a1 a0 x1 x2 x3).
Definition term58 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y2 y1)) -> (@sum a0 (@DIFF a0 y1 y2) y0) = (real_sub (@sum a0 y1 y0) (@sum a0 y2 y0)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) := forall y0 : Prop, (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) = x3) -> (x3 -> ((@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = y0) -> (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> (@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = (x3 -> y0).
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term18 (x0 : real) (x1 : real) := forall y0 : real, (x0 = (real_sub x1 y0)) = ((real_add x0 y0) = x1).
Definition term51 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term59 (a0 : Type') := fun y0 : a0 -> real => True.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ (@SUBSET a0 y0 x0)) -> (@sum a0 (@DIFF a0 x0 y0) x1) = (real_sub (@sum a0 x0 x1) (@sum a0 y0 x1)).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1627) (x2 : a0 -> Prop) (x3 : a0 -> real) := ((@monoidal real x1) /\ ((@FINITE a0 x2) /\ (@SUBSET a0 x0 x2))) -> (x1 (@iterate real a0 x1 (@DIFF a0 x2 x0) x3) (@iterate real a0 x1 x0 x3)) = (@iterate real a0 x1 x2 x3).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@monoidal a1 x1) /\ ((@FINITE a0 x2) /\ (@SUBSET a0 x0 x2))) -> (x1 (@iterate a1 a0 x1 (@DIFF a0 x2 x0) x3) (@iterate a1 a0 x1 x0 x3)) = (@iterate a1 a0 x1 x2 x3).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := forall y0 : Prop, forall y1 : Prop, (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) = y0) -> (y0 -> ((@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = y1) -> (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> (@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = (y0 -> y1).
Definition term22 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term17 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (x0 = (real_sub y0 y1)) = ((real_add x0 y1) = y0)) x1.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y2 y1)) -> (x0 (@iterate a1 a0 x0 (@DIFF a0 y1 y2) y0) (@iterate a1 a0 x0 y2 y0)) = (@iterate a1 a0 x0 y1 y0)) x1.
Definition term57 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 y1 y0)) -> (@sum a0 (@DIFF a0 y0 y1) x0) = (real_sub (@sum a0 y0 x0) (@sum a0 y1 x0)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 y1 y0)) -> (x0 (@iterate a1 a0 x0 (@DIFF a0 y0 y1) x1) (@iterate a1 a0 x0 y1 x1)) = (@iterate a1 a0 x0 y0 x1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) = x3) -> (x3 -> ((@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = y0) -> (((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> (@sum a0 (@DIFF a0 x0 x1) x2) = (real_sub (@sum a0 x0 x2) (@sum a0 x1 x2))) = (x3 -> y0)) x4.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x1 (@iterate a1 a0 x1 (@DIFF a0 x0 x2) x3) (@iterate a1 a0 x1 x2 x3).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (@sum a0 (@DIFF a0 x0 x1) x2) (@sum a0 x1 x2).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := @sum a0 (@DIFF a0 x0 x1) x2.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@FINITE a0 x2) /\ (@SUBSET a0 x0 x2)) -> (x1 (@iterate a1 a0 x1 (@DIFF a0 x2 x0) x3) (@iterate a1 a0 x1 x0 x3)) = (@iterate a1 a0 x1 x2 x3).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@iterate real a0 real_add x0 x1).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@FINITE a0 y2) /\ (@SUBSET a0 y3 y2)) -> (y0 (@iterate a1 a0 y0 (@DIFF a0 y2 y3) y1) (@iterate a1 a0 y0 y3 y1)) = (@iterate a1 a0 y0 y2 y1)) x0.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (@iterate real a0 real_add (@DIFF a0 x0 x1) x2) (@iterate real a0 real_add x1 x2).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) := forall y0 : a0 -> Prop, ((@FINITE a0 x1) /\ (@SUBSET a0 y0 x1)) -> (x0 (@iterate a1 a0 x0 (@DIFF a0 x1 y0) x2) (@iterate a1 a0 x0 y0 x2)) = (@iterate a1 a0 x0 x1 x2).
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (y0 = (real_sub y1 y2)) = ((real_add y0 y2) = y1)) x0.
Definition term61 (a0 : Type') := forall y0 : a0 -> real, True.
Definition term53 (a0 : Type') := forall y0 : a0 -> Prop, True.
