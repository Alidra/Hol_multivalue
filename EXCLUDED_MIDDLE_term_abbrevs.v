Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : Prop) := ~ ((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0))).
Definition term14 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ x0) (@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)).
Definition term8 (x0 : Prop) := (fun y0 : Prop => (y0 = False) \/ x0) (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)).
Definition term39 (x0 : Prop) := (~ ((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)))) -> @ε Prop (fun y0 : Prop => (y0 = False) \/ x0).
Definition term24 (x0 : Prop) := or (False = (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0))).
Definition term0 := (True = False) -> False -> True.
Definition term10 (x0 : Prop) := fun y0 : Prop => (y0 = False) \/ x0.
Definition term33 (x0 : Prop) := x0 \/ (~ x0).
Definition term17 (x0 : Prop) := ((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = True) \/ x0.
Definition term2 := (True -> False) -> False.
Definition term6 (x0 : Prop) := (((@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)) = False) \/ x0) /\ (((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = True) \/ x0).
Definition term41 (x0 : Prop) (x1 : Prop) := (x0 = True) \/ x1.
Definition term7 (x0 : Prop -> Prop) := x0 (@ε Prop x0).
Definition term3 := (False -> True) -> (True -> False) -> False.
Definition term40 (x0 : Prop) := or (x0 = True).
Definition term5 := ~ (True = False).
Definition term38 := (~ (True = False)) -> False.
Definition term23 (x0 : Prop) := or ((@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)) = False).
Definition term27 (x0 : Prop) := and ((False = (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0))) \/ x0).
Definition term28 (x0 : Prop) := @ε Prop (fun y0 : Prop => (y0 = True) \/ x0).
Definition term22 (x0 : Prop) := @ε Prop (fun y0 : Prop => (y0 = False) \/ x0).
Definition term48 (x0 : Prop) := (~ x0) \/ True.
Definition term20 (x0 : Prop) := (True = True) \/ x0.
Definition term19 (x0 : Prop) := @eq Prop (((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = True) \/ x0).
Definition term13 (x0 : Prop) := @eq Prop (((@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)) = False) \/ x0).
Definition term42 := fun y0 : Prop => True.
Definition term36 := imp (~ (True = False)).
Definition term31 (x0 : Prop) := (True = (@ε Prop (fun y0 : Prop => (y0 = True) \/ x0))) \/ x0.
Definition term4 := (True = False) -> False.
Definition term18 (x0 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = True) \/ x0) (@ε Prop (fun y0 : Prop => (y0 = True) \/ x0))).
Definition term12 (x0 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = False) \/ x0) (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0))).
Definition term34 (x0 : Prop) := @eq Prop (@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)).
Definition term25 (x0 : Prop) := (False = (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0))) \/ x0.
Definition term11 (x0 : Prop) := ((@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)) = False) \/ x0.
Definition term45 (x0 : Prop) := or (x0 = False).
Definition term49 := False -> @ε Prop (fun y0 : Prop => True).
Definition term37 (x0 : Prop) := imp (~ ((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)))).
Definition term50 (x0 : Prop) := ((((@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)) = False) \/ x0) /\ (((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = True) \/ x0)) -> x0 \/ (~ x0).
Definition term1 := (True = False) -> True -> False.
Definition term47 (x0 : Prop) (x1 : Prop) := (x0 = False) \/ x1.
Definition term29 (x0 : Prop) := or ((@ε Prop (fun y0 : Prop => (y0 = True) \/ x0)) = True).
Definition term21 (x0 : Prop) := (False = False) \/ x0.
Definition term32 (x0 : Prop) := ((False = (@ε Prop (fun y0 : Prop => (y0 = False) \/ x0))) \/ x0) /\ ((True = (@ε Prop (fun y0 : Prop => (y0 = True) \/ x0))) \/ x0).
Definition term16 (x0 : Prop) := fun y0 : Prop => (y0 = True) \/ x0.
Definition term46 (x0 : Prop) := or (~ x0).
Definition term44 := @eq Prop (@ε Prop (fun y0 : Prop => True)).
Definition term26 (x0 : Prop) := and (((@ε Prop (fun y0 : Prop => (y0 = False) \/ x0)) = False) \/ x0).
Definition term51 := forall y0 : Prop, y0 \/ (~ y0).
Definition term30 (x0 : Prop) := or (True = (@ε Prop (fun y0 : Prop => (y0 = True) \/ x0))).
Definition term43 := @ε Prop (fun y0 : Prop => True).
Definition term15 (x0 : Prop) := exists y0 : Prop, (y0 = True) \/ x0.
Definition term9 (x0 : Prop) := exists y0 : Prop, (y0 = False) \/ x0.
