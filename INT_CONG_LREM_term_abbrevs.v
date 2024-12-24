Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : int) (x1 : int) := forall y0 : int, (@eq2 int (rem x0 y0) x1 (int_mod y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term23 (x0 : int) (x1 : int) (x2 : int) := @eq Prop (@eq2 int (rem x0 x2) x1 (int_mod x2)).
Definition term31 (x0 : int) := fun y0 : int => forall y1 : int, (@eq2 int (rem x0 y1) y0 (int_mod y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term6 (x0 : int) := fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1)).
Definition term5 (x0 : int) := fun y0 : int => forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term18 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1))) x1.
Definition term33 := fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int (rem y0 y2) y1 (int_mod y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term10 := fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2)).
Definition term9 := fun y0 : int => forall y1 : int, forall y2 : int, ((rem y0 y2) = (rem y1 y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 := fun y0 : int => True.
Definition term13 (x0 : int) := (fun y0 : int => forall y1 : int, (rem (rem y0 y1) y1) = (rem y0 y1)) x0.
Definition term16 (x0 : int) (x1 : int) := rem (rem x0 x1) x1.
Definition term17 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2))) x0.
Definition term25 (x0 : int) (x1 : int) := fun y0 : int => (@eq2 int (rem x0 y0) x1 (int_mod y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term19 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0))) x2.
Definition term2 (x0 : int) (x1 : int) := fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0)).
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0)).
Definition term1 (x0 : int) (x1 : int) := fun y0 : int => ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term15 (x0 : int) (x1 : int) := (fun y0 : int => (rem (rem x0 y0) y0) = (rem x0 y0)) x1.
Definition term30 (x0 : Prop) := forall y0 : int, x0.
Definition term34 := forall y0 : int, forall y1 : int, forall y2 : int, (@eq2 int (rem y0 y2) y1 (int_mod y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term32 (x0 : int) := forall y0 : int, forall y1 : int, (@eq2 int (rem x0 y1) y0 (int_mod y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term12 := forall y0 : int, forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2)).
Definition term11 := forall y0 : int, forall y1 : int, forall y2 : int, ((rem y0 y2) = (rem y1 y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term8 (x0 : int) := forall y0 : int, forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1)).
Definition term7 (x0 : int) := forall y0 : int, forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term0 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
Definition term21 (x0 : int) (x1 : int) := @eq int (rem (rem x0 x1) x1).
Definition term22 (x0 : int) (x1 : int) := @eq int (rem x0 x1).
Definition term20 (x0 : int) (x1 : int) (x2 : int) := @eq2 int (rem x0 x2) x1 (int_mod x2).
Definition term28 := forall y0 : int, True.
Definition term24 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((rem x0 x2) = (rem x1 x2)).
Definition term14 (x0 : int) := forall y0 : int, (rem (rem x0 y0) y0) = (rem x0 y0).
