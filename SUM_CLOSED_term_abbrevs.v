Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term126 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((x0 (real_of_num (NUMERAL 0))) /\ ((forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2)) /\ (forall y1 : a0, (@IN a0 y1 y0) -> x0 (x1 y1)))) -> x0 (@sum a0 y0 x1).
Definition term56 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1).
Definition term97 (a0 : Type') (x0 : real -> Prop) := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0).
Definition term96 (a0 : Type') (x0 : real -> Prop) := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) = x4) -> (x4 -> (x1 (x2 x3)) = x5) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x1 (x2 x3)) = (x4 -> x5).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) = x4) -> (x4 -> (x1 (x2 x3)) = x5) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x1 (x2 x3)) = (x4 -> x5).
Definition term14 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => ((x0 x1) /\ (x0 y0)) -> x0 (real_add x1 y0)) x2.
Definition term92 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) := fun y0 : a0 -> Prop => (forall y1 : a0, ((@IN a0 y1 y0) /\ (~ ((x1 y1) = (@neutral real real_add)))) -> x0 (x1 y1)) -> x0 (@iterate real a0 real_add y0 x1).
Definition term105 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, ((@IN a0 y1 y0) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) -> x0 (x1 y1)) -> x0 (@sum a0 y0 x1)) x2.
Definition term57 (a0 : Type') (x0 : real -> Prop) (x1 : Prop) := (((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) = True) -> (True -> (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = x1) -> (((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = (True -> x1).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> x1 (x2 y0).
Definition term116 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x0 (x2 x3)) = True) -> (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x0 (x2 x3)) = (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> True).
Definition term49 (x0 : real) (x1 : real -> Prop) (x2 : real) := (((x1 x0) /\ (x1 x2)) -> (x1 (real_add x0 x2)) = True) -> (((x1 x0) /\ (x1 x2)) -> x1 (real_add x0 x2)) = (((x1 x0) /\ (x1 x2)) -> True).
Definition term37 := real_of_num (NUMERAL 0).
Definition term48 (x0 : real -> Prop) (x1 : real) := and (x0 x1).
Definition term95 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, ((@IN a0 y1 y0) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) -> x0 (x1 y1)) -> x0 (@sum a0 y0 x1).
Definition term94 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, ((@IN a0 y1 y0) /\ (~ ((x1 y1) = (@neutral real real_add)))) -> x0 (x1 y1)) -> x0 (@iterate real a0 real_add y0 x1).
Definition term99 (a0 : Type') (x0 : real -> Prop) := True -> (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0)).
Definition term120 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0)) -> (x0 (@sum a0 x1 x2)) = True.
Definition term15 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((x0 x1) /\ (x0 x2)) -> x0 (real_add x1 x2).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real -> Prop) (x3 : Prop) := ((forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x2 (y0 y2)) -> x2 (@sum a0 y1 y0)) -> (x2 (@sum a0 x0 x1)) = x3) -> ((((x2 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x2 y0) /\ (x2 y1)) -> x2 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x2 (y0 y2)) -> x2 (@iterate real a0 real_add y1 y0)) -> x2 (@sum a0 x0 x1)) = ((forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x2 (y0 y2)) -> x2 (@sum a0 y1 y0)) -> x3).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : Prop) := ((forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x1 (x2 y0)) -> (x1 (@iterate real a0 real_add x0 x2)) = x3) -> ((forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x1 (x2 y0)) -> x1 (@iterate real a0 real_add x0 x2)) = ((forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x1 (x2 y0)) -> x3).
Definition term54 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term124 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : real -> Prop, ((y0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((y0 y1) /\ (y0 y2)) -> y0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> y0 (y1 y3)) -> y0 (@iterate real a0 real_add y2 y1)) -> x0 (@sum a0 x1 x2).
Definition term50 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((x1 x0) /\ (x1 x2)) -> True.
Definition term91 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x0 (x2 y0)) -> x0 (@sum a0 x1 x2).
Definition term52 := fun y0 : real => True.
Definition term72 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real (x0 x1).
Definition term38 (x0 : real -> Prop) := x0 (@neutral real real_add).
Definition term25 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := x0 (@sum a0 x1 x2).
Definition term119 (a0 : Type') := forall y0 : a0, True.
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := ((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x1 (x2 x3)) = True.
Definition term58 (a0 : Type') (x0 : real -> Prop) (x1 : Prop) := (True -> (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = x1) -> (((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = (True -> x1).
Definition term128 (a0 : Type') := forall y0 : real -> Prop, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((y0 (real_of_num (NUMERAL 0))) /\ ((forall y3 : real, forall y4 : real, ((y0 y3) /\ (y0 y4)) -> y0 (real_add y3 y4)) /\ (forall y3 : a0, (@IN a0 y3 y2) -> y0 (y1 y3)))) -> y0 (@sum a0 y2 y1).
Definition term53 := forall y0 : real, True.
Definition term93 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) := fun y0 : a0 -> Prop => (forall y1 : a0, ((@IN a0 y1 y0) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) -> x0 (x1 y1)) -> x0 (@sum a0 y0 x1).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> x1 (x2 x3).
Definition term123 (a0 : Type') (x0 : real -> Prop) := (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0)) -> True.
Definition term55 (x0 : Prop) := forall y0 : real, x0.
Definition term7 (x0 : real -> Prop) := x0 (real_of_num (NUMERAL 0)).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x1 (x2 x3)) = (x1 (x2 x3))) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x1 (x2 x3)) = (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x1 (x2 x3)).
Definition term122 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) -> x0 (@sum a0 x1 x2).
Definition term9 (x0 : real -> Prop) := forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := ((@IN a0 x2 x0) /\ (~ ((x1 x2) = (real_of_num (NUMERAL 0))))) -> True.
Definition term62 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : a0, ((@IN a0 y2 x1) /\ (~ ((x2 y2) = (@neutral real real_add)))) -> x0 (x2 y2)) = y0) -> (y0 -> (x0 (@iterate real a0 real_add x1 x2)) = y1) -> ((forall y2 : a0, ((@IN a0 y2 x1) /\ (~ ((x2 y2) = (@neutral real real_add)))) -> x0 (x2 y2)) -> x0 (@iterate real a0 real_add x1 x2)) = (y0 -> y1)) x3.
Definition term41 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((x0 x1) /\ (x0 x2)) = y0) -> (y0 -> (x0 (real_add x1 x2)) = y1) -> (((x0 x1) /\ (x0 x2)) -> x0 (real_add x1 x2)) = (y0 -> y1)) x3.
Definition term26 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) -> forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) = y0) -> (y0 -> (x0 (@sum a0 x1 x2)) = y1) -> ((((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) -> forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) -> x0 (@sum a0 x1 x2)) = (y0 -> y1)) x3.
Definition term17 (x0 : real -> Prop) (x1 : real) (x2 : real) := x0 (real_add x1 x2).
Definition term45 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : Prop) := (((x1 x0) /\ (x1 x2)) = ((x1 x0) /\ (x1 x2))) -> (((x1 x0) /\ (x1 x2)) -> (x1 (real_add x0 x2)) = x3) -> (((x1 x0) /\ (x1 x2)) -> x1 (real_add x0 x2)) = (((x1 x0) /\ (x1 x2)) -> x3).
Definition term104 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0)) x1.
Definition term65 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) (x4 : Prop) := ((forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x0 (x2 y0)) = x3) -> (x3 -> (x0 (@iterate real a0 real_add x1 x2)) = x4) -> ((forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x0 (x2 y0)) -> x0 (@iterate real a0 real_add x1 x2)) = (x3 -> x4).
Definition term11 (a0 : Type') (x0 : real -> Prop) := ((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0).
Definition term35 (a0 : Type') (x0 : real -> Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) = x1) -> (x1 -> (forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) = y0) -> (((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) = (x1 -> y0)) x2.
Definition term106 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x0 (x2 y0)) -> (x0 (@sum a0 x1 x2)) = True.
Definition term100 (a0 : Type') (x0 : real -> Prop) := (True -> (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0))) -> (((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = (True -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0)).
Definition term112 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) = ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0)))))) -> (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x0 (x2 x3)) = x4) -> (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x0 (x2 x3)) = (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x4).
Definition term77 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (@neutral real real_add)))) = ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0)))))) -> (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x0 (x2 x3)) = x4) -> (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x0 (x2 x3)) = (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x4).
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((x1 x2) = (@neutral real real_add))).
Definition term74 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ~ ((x0 x1) = (real_of_num (NUMERAL 0))).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) := forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x1 (x2 y0).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) := forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x1 (x2 y0).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term10 (a0 : Type') (x0 : real -> Prop) := (fun y0 : real -> Prop => ((y0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((y0 y1) /\ (y0 y2)) -> y0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> y0 (y1 y3)) -> y0 (@iterate real a0 real_add y2 y1)) x0.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := ((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x1 (x2 x3)) = (x1 (x2 x3)).
Definition term44 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := (((x0 x1) /\ (x0 x2)) = x3) -> (x3 -> (x0 (real_add x1 x2)) = x4) -> (((x0 x1) /\ (x0 x2)) -> x0 (real_add x1 x2)) = (x3 -> x4).
Definition term29 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) (x4 : Prop) := ((((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = x3) -> (x3 -> (x0 (@sum a0 x1 x2)) = x4) -> ((((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) -> x0 (@sum a0 x1 x2)) = (x3 -> x4).
Definition term118 (a0 : Type') := fun y0 : a0 => True.
Definition term101 (a0 : Type') (x0 : real -> Prop) := True -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0).
Definition term16 (x0 : real) (x1 : real -> Prop) (x2 : real) := (x1 x0) /\ (x1 x2).
Definition term51 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((x0 x1) /\ (x0 y0)) -> x0 (real_add x1 y0).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((x1 x2) = (real_of_num (NUMERAL 0)))).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) := fun y0 : a0 => ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x1 (x2 y0).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) := fun y0 : a0 => ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x1 (x2 y0).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) := (x1 (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, ((x1 y0) /\ (x1 y1)) -> x1 (real_add y0 y1)) /\ (forall y0 : a0, (@IN a0 y0 x0) -> x1 (x2 y0))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := forall y0 : Prop, (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) = x4) -> (x4 -> (x1 (x2 x3)) = y0) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x1 (x2 x3)) = (x4 -> y0).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := forall y0 : Prop, (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) = x4) -> (x4 -> (x1 (x2 x3)) = y0) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x1 (x2 x3)) = (x4 -> y0).
Definition term63 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) := forall y0 : Prop, ((forall y1 : a0, ((@IN a0 y1 x1) /\ (~ ((x2 y1) = (@neutral real real_add)))) -> x0 (x2 y1)) = x3) -> (x3 -> (x0 (@iterate real a0 real_add x1 x2)) = y0) -> ((forall y1 : a0, ((@IN a0 y1 x1) /\ (~ ((x2 y1) = (@neutral real real_add)))) -> x0 (x2 y1)) -> x0 (@iterate real a0 real_add x1 x2)) = (x3 -> y0).
Definition term42 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) := forall y0 : Prop, (((x0 x1) /\ (x0 x2)) = x3) -> (x3 -> (x0 (real_add x1 x2)) = y0) -> (((x0 x1) /\ (x0 x2)) -> x0 (real_add x1 x2)) = (x3 -> y0).
Definition term34 (a0 : Type') (x0 : real -> Prop) (x1 : Prop) := forall y0 : Prop, (((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) = x1) -> (x1 -> (forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) = y0) -> (((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) = (x1 -> y0).
Definition term27 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) := forall y0 : Prop, ((((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) = x3) -> (x3 -> (x0 (@sum a0 x1 x2)) = y0) -> ((((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) -> x0 (@sum a0 x1 x2)) = (x3 -> y0).
Definition term22 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term113 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x0 (x2 x3)) = x4) -> (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x0 (x2 x3)) = (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x4).
Definition term78 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> (x0 (x2 x3)) = x4) -> (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x0 (x2 x3)) = (((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x4).
Definition term90 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x0 (x2 y0)) -> x0 (@iterate real a0 real_add x1 x2).
Definition term46 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : Prop) := (((x1 x0) /\ (x1 x2)) -> (x1 (real_add x0 x2)) = x3) -> (((x1 x0) /\ (x1 x2)) -> x1 (real_add x0 x2)) = (((x1 x0) /\ (x1 x2)) -> x3).
Definition term13 (x0 : real -> Prop) (x1 : real) := forall y0 : real, ((x0 x1) /\ (x0 y0)) -> x0 (real_add x1 y0).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> (x1 (x2 x3)) = y1) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x1 (x2 x3)) = (y0 -> y1).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) = y0) -> (y0 -> (x1 (x2 x3)) = y1) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x1 (x2 x3)) = (y0 -> y1).
Definition term59 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : a0, ((@IN a0 y2 x1) /\ (~ ((x2 y2) = (@neutral real real_add)))) -> x0 (x2 y2)) = y0) -> (y0 -> (x0 (@iterate real a0 real_add x1 x2)) = y1) -> ((forall y2 : a0, ((@IN a0 y2 x1) /\ (~ ((x2 y2) = (@neutral real real_add)))) -> x0 (x2 y2)) -> x0 (@iterate real a0 real_add x1 x2)) = (y0 -> y1).
Definition term40 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : Prop, (((x0 x1) /\ (x0 x2)) = y0) -> (y0 -> (x0 (real_add x1 x2)) = y1) -> (((x0 x1) /\ (x0 x2)) -> x0 (real_add x1 x2)) = (y0 -> y1).
Definition term30 (a0 : Type') (x0 : real -> Prop) := forall y0 : Prop, forall y1 : Prop, (((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) = y0) -> (y0 -> (forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) = y1) -> (((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) -> forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) = (y0 -> y1).
Definition term24 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := forall y0 : Prop, forall y1 : Prop, ((((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) -> forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) = y0) -> (y0 -> (x0 (@sum a0 x1 x2)) = y1) -> ((((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) -> forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) -> x0 (@sum a0 x1 x2)) = (y0 -> y1).
Definition term23 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term12 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1)) x1.
Definition term88 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x0 (x2 y0)) -> (x0 (@iterate real a0 real_add x1 x2)) = (x0 (@sum a0 x1 x2)).
Definition term4 (a0 : Type') := forall y0 : real -> Prop, ((y0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((y0 y1) /\ (y0 y2)) -> y0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> y0 (y1 y3)) -> y0 (@iterate real a0 real_add y2 y1).
Definition term127 (a0 : Type') (x0 : real -> Prop) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((x0 (real_of_num (NUMERAL 0))) /\ ((forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3)) /\ (forall y2 : a0, (@IN a0 y2 y1) -> x0 (y0 y2)))) -> x0 (@sum a0 y1 y0).
Definition term98 (a0 : Type') (x0 : real -> Prop) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x0 (y0 y2)) -> x0 (@sum a0 y1 y0).
Definition term32 (a0 : Type') (x0 : real -> Prop) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> x1 (x2 y0)) x3.
Definition term64 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((forall y1 : a0, ((@IN a0 y1 x1) /\ (~ ((x2 y1) = (@neutral real real_add)))) -> x0 (x2 y1)) = x3) -> (x3 -> (x0 (@iterate real a0 real_add x1 x2)) = y0) -> ((forall y1 : a0, ((@IN a0 y1 x1) /\ (~ ((x2 y1) = (@neutral real real_add)))) -> x0 (x2 y1)) -> x0 (@iterate real a0 real_add x1 x2)) = (x3 -> y0)) x4.
Definition term43 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((x0 x1) /\ (x0 x2)) = x3) -> (x3 -> (x0 (real_add x1 x2)) = y0) -> (((x0 x1) /\ (x0 x2)) -> x0 (real_add x1 x2)) = (x3 -> y0)) x4.
Definition term28 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) = x3) -> (x3 -> (x0 (@sum a0 x1 x2)) = y0) -> ((((x0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((x0 y1) /\ (x0 y2)) -> x0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> x0 (y1 y3)) -> x0 (@iterate real a0 real_add y2 y1)) -> x0 (@sum a0 x1 x2)) = (x3 -> y0)) x4.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) = x4) -> (x4 -> (x1 (x2 x3)) = y0) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x1 (x2 x3)) = (x4 -> y0)) x5.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) = x4) -> (x4 -> (x1 (x2 x3)) = y0) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x1 (x2 x3)) = (x4 -> y0)) x5.
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real -> Prop) (x3 : Prop) := ((((x2 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x2 y0) /\ (x2 y1)) -> x2 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x2 (y0 y2)) -> x2 (@iterate real a0 real_add y1 y0)) = (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x2 (y0 y2)) -> x2 (@sum a0 y1 y0))) -> ((forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x2 (y0 y2)) -> x2 (@sum a0 y1 y0)) -> (x2 (@sum a0 x0 x1)) = x3) -> ((((x2 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x2 y0) /\ (x2 y1)) -> x2 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x2 (y0 y2)) -> x2 (@iterate real a0 real_add y1 y0)) -> x2 (@sum a0 x0 x1)) = ((forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x2 (y0 y2)) -> x2 (@sum a0 y1 y0)) -> x3).
Definition term125 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((x0 (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1)) /\ (forall y0 : a0, (@IN a0 y0 x1) -> x0 (x2 y0)))) -> x0 (@sum a0 x1 x2).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real -> Prop) := ((forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x2 (y0 y2)) -> x2 (@sum a0 y1 y0)) -> (x2 (@sum a0 x0 x1)) = True) -> ((((x2 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x2 y0) /\ (x2 y1)) -> x2 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x2 (y0 y2)) -> x2 (@iterate real a0 real_add y1 y0)) -> x2 (@sum a0 x0 x1)) = ((forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (real_of_num (NUMERAL 0))))) -> x2 (y0 y2)) -> x2 (@sum a0 y1 y0)) -> True).
Definition term89 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x0 (x2 y0)) -> (x0 (@iterate real a0 real_add x1 x2)) = (x0 (@sum a0 x1 x2))) -> ((forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x0 (x2 y0)) -> x0 (@iterate real a0 real_add x1 x2)) = ((forall y0 : a0, ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x0 (x2 y0)) -> x0 (@sum a0 x1 x2)).
Definition term61 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := x0 (@iterate real a0 real_add x1 x2).
Definition term2 (a0 : Type') (x0 : type1627) := (@monoidal real x0) -> forall y0 : real -> Prop, ((y0 (@neutral real x0)) /\ (forall y1 : real, forall y2 : real, ((y0 y1) /\ (y0 y2)) -> y0 (x0 y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real x0)))) -> y0 (y1 y3)) -> y0 (@iterate real a0 x0 y2 y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a1 -> Prop, ((y0 (@neutral a1 x0)) /\ (forall y1 : a1, forall y2 : a1, ((y0 y1) /\ (y0 y2)) -> y0 (x0 y1 y2))) -> forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral a1 x0)))) -> y0 (y1 y3)) -> y0 (@iterate a1 a0 x0 y2 y1).
Definition term3 (a0 : Type') := (@monoidal real real_add) -> forall y0 : real -> Prop, ((y0 (@neutral real real_add)) /\ (forall y1 : real, forall y2 : real, ((y0 y1) /\ (y0 y2)) -> y0 (real_add y1 y2))) -> forall y1 : a0 -> real, forall y2 : a0 -> Prop, (forall y3 : a0, ((@IN a0 y3 y2) /\ (~ ((y1 y3) = (@neutral real real_add)))) -> y0 (y1 y3)) -> y0 (@iterate real a0 real_add y2 y1).
Definition term73 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ~ ((x0 x1) = (@neutral real real_add)).
Definition term33 (a0 : Type') (x0 : real -> Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) = y0) -> (y0 -> (forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) = y1) -> (((x0 (@neutral real real_add)) /\ (forall y2 : real, forall y3 : real, ((x0 y2) /\ (x0 y3)) -> x0 (real_add y2 y3))) -> forall y2 : a0 -> real, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral real real_add)))) -> x0 (y2 y4)) -> x0 (@iterate real a0 real_add y3 y2)) = (y0 -> y1)) x1.
Definition term36 (a0 : Type') (x0 : real -> Prop) (x1 : Prop) (x2 : Prop) := (((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) = x1) -> (x1 -> (forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = x2) -> (((x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1))) -> forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, ((@IN a0 y2 y1) /\ (~ ((y0 y2) = (@neutral real real_add)))) -> x0 (y0 y2)) -> x0 (@iterate real a0 real_add y1 y0)) = (x1 -> x2).
Definition term31 (x0 : real -> Prop) := (x0 (@neutral real real_add)) /\ (forall y0 : real, forall y1 : real, ((x0 y0) /\ (x0 y1)) -> x0 (real_add y0 y1)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a1 -> Prop, ((y1 (@neutral a1 y0)) /\ (forall y2 : a1, forall y3 : a1, ((y1 y2) /\ (y1 y3)) -> y1 (y0 y2 y3))) -> forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (forall y4 : a0, ((@IN a0 y4 y3) /\ (~ ((y2 y4) = (@neutral a1 y0)))) -> y1 (y2 y4)) -> y1 (@iterate a1 a0 y0 y3 y2)) x0.
Definition term20 (a0 : Type') (x0 : real -> Prop) (x1 : a0 -> real) (x2 : a0) := x0 (x1 x2).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := ((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x1 (x2 x3).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := ((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x1 (x2 x3).
Definition term39 (x0 : real -> Prop) := and (x0 (@neutral real real_add)).
Definition term47 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((x0 x1) /\ (x0 x2)) -> (x0 (real_add x1 x2)) = True.
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> (x1 (x2 x3)) = y1) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) -> x1 (x2 x3)) = (y0 -> y1)) x4.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) = y0) -> (y0 -> (x1 (x2 x3)) = y1) -> (((@IN a0 x3 x0) /\ (~ ((x2 x3) = (@neutral real real_add)))) -> x1 (x2 x3)) = (y0 -> y1)) x4.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> (x1 (x2 x3)) = True.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) := (forall y0 : real, forall y1 : real, ((x1 y0) /\ (x1 y1)) -> x1 (real_add y0 y1)) /\ (forall y0 : a0, (@IN a0 y0 x0) -> x1 (x2 y0)).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : real -> Prop) (x2 : a0 -> real) (x3 : Prop) := ((forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x1 (x2 y0)) = (forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x1 (x2 y0))) -> ((forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x1 (x2 y0)) -> (x1 (@iterate real a0 real_add x0 x2)) = x3) -> ((forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (@neutral real real_add)))) -> x1 (x2 y0)) -> x1 (@iterate real a0 real_add x0 x2)) = ((forall y0 : a0, ((@IN a0 y0 x0) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) -> x1 (x2 y0)) -> x3).