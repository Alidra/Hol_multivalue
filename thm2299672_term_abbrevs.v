Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : Prop) (x2 : Prop) (x3 : int) (x4 : int) (x5 : int) := (x1 -> (fun y0 : int => (real_of_int y0) = (@COND real x2 (real_of_int x3) (real_of_int x4))) x0) /\ ((~ x1) -> (fun y0 : int => (real_of_int y0) = (@COND real x2 (real_of_int x3) (real_of_int x4))) x5).
Definition term9 (x0 : Prop) := imp (~ x0).
Definition term4 (x0 : Prop) (x1 : int) (x2 : int) := fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2)).
Definition term30 (x0 : int) (x1 : int) := (fun y0 : Prop => (real_of_int x1) = (@COND real y0 (real_of_int x0) (real_of_int x1))) False.
Definition term10 (x0 : Prop) (x1 : int) (x2 : int) := (~ x0) -> (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2))) x2.
Definition term18 (x0 : Prop) (x1 : int) (x2 : int) := real_of_int (@COND int x0 x1 x2).
Definition term6 (x0 : Prop) (x1 : int) (x2 : int) := (x0 -> (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2))) x1) /\ ((~ x0) -> (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2))) x2).
Definition term16 (x0 : Prop) (x1 : int) (x2 : int) := and (x0 -> (real_of_int x1) = (@COND real x0 (real_of_int x1) (real_of_int x2))).
Definition term1 (x0 : int) (x1 : Prop) (x2 : int -> Prop) (x3 : int) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term28 (x0 : int) (x1 : int) := fun y0 : Prop => (real_of_int x1) = (@COND real y0 (real_of_int x0) (real_of_int x1)).
Definition term2 (x0 : Prop) (x1 : int) (x2 : int) (x3 : Prop) (x4 : int) (x5 : int) := (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2))) (@COND int x3 x4 x5).
Definition term11 (x0 : Prop) (x1 : int) (x2 : int) := (~ x0) -> (real_of_int x2) = (@COND real x0 (real_of_int x1) (real_of_int x2)).
Definition term20 (x0 : Prop) (x1 : int) (x2 : int) := @eq Prop ((real_of_int (@COND int x0 x1 x2)) = (@COND real x0 (real_of_int x1) (real_of_int x2))).
Definition term24 (x0 : int) (x1 : int) := @COND real True (real_of_int x0) (real_of_int x1).
Definition term14 (x0 : Prop) (x1 : int) (x2 : int) := x0 -> (real_of_int x1) = (@COND real x0 (real_of_int x1) (real_of_int x2)).
Definition term13 (x0 : Prop) (x1 : int) (x2 : int) := x0 -> (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x2) (real_of_int x1))) x2.
Definition term26 (x0 : Prop) (x1 : int) (x2 : int) := @eq Prop ((real_of_int x1) = (@COND real x0 (real_of_int x1) (real_of_int x2))).
Definition term21 (x0 : int) (x1 : int) := fun y0 : Prop => (real_of_int x0) = (@COND real y0 (real_of_int x0) (real_of_int x1)).
Definition term19 (x0 : Prop) (x1 : int) (x2 : int) := @eq Prop ((fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2))) (@COND int x0 x1 x2)).
Definition term15 (x0 : Prop) (x1 : int) (x2 : int) := and (x0 -> (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x2) (real_of_int x1))) x2).
Definition term17 (x0 : Prop) (x1 : int) (x2 : int) := (x0 -> (real_of_int x1) = (@COND real x0 (real_of_int x1) (real_of_int x2))) /\ ((~ x0) -> (real_of_int x2) = (@COND real x0 (real_of_int x1) (real_of_int x2))).
Definition term5 (x0 : Prop) (x1 : int) (x2 : int) := (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2))) (@COND int x0 x1 x2).
Definition term12 (x0 : Prop) (x1 : int) (x2 : int) := (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x2) (real_of_int x1))) x2.
Definition term7 (x0 : Prop) (x1 : int) (x2 : int) := (fun y0 : int => (real_of_int y0) = (@COND real x0 (real_of_int x1) (real_of_int x2))) x2.
Definition term31 (x0 : int) (x1 : int) := @COND real False (real_of_int x0) (real_of_int x1).
Definition term8 (x0 : Prop) (x1 : int) (x2 : int) := @COND real x0 (real_of_int x1) (real_of_int x2).
Definition term33 (x0 : Prop) (x1 : int) (x2 : int) := @eq Prop ((real_of_int x2) = (@COND real x0 (real_of_int x1) (real_of_int x2))).
Definition term22 (x0 : int) (x1 : int) (x2 : Prop) := (fun y0 : Prop => (real_of_int x0) = (@COND real y0 (real_of_int x0) (real_of_int x1))) x2.
Definition term27 (x0 : Prop) := (~ x0) -> x0 = False.
Definition term23 (x0 : int) (x1 : int) := (fun y0 : Prop => (real_of_int x0) = (@COND real y0 (real_of_int x0) (real_of_int x1))) True.
Definition term34 (x0 : int) := @eq real (real_of_int x0).
Definition term29 (x0 : int) (x1 : int) (x2 : Prop) := (fun y0 : Prop => (real_of_int x1) = (@COND real y0 (real_of_int x0) (real_of_int x1))) x2.
Definition term0 (x0 : int -> Prop) (x1 : Prop) (x2 : int) (x3 : int) := x0 (@COND int x1 x2 x3).
Definition term32 (x0 : int) (x1 : int) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (real_of_int x1) = (@COND real y0 (real_of_int x0) (real_of_int x1))) x2).
Definition term25 (x0 : int) (x1 : int) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (real_of_int x0) = (@COND real y0 (real_of_int x0) (real_of_int x1))) x2).
