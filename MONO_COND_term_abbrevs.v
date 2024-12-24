Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) (x4 : Prop) := @eq Prop ((@COND Prop x2 x0 x1) -> @COND Prop x2 x3 x4).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (@COND Prop y0 x0 x1) -> @COND Prop y0 x2 x3) True.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (@COND Prop y0 x0 x1) -> @COND Prop y0 x2 x3) x4.
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) (x4 : Prop) := (@COND Prop x2 x0 x1) -> @COND Prop x2 x3 x4.
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (@COND Prop y0 x0 x1) -> @COND Prop y0 x2 x3) False.
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := fun y0 : Prop => (@COND Prop y0 x0 x1) -> @COND Prop y0 x2 x3.
Definition term2 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 -> x1) /\ (x2 -> x3).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (@COND Prop False x0 x1) -> @COND Prop False x2 x3.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (@COND Prop True x0 x1) -> @COND Prop True x2 x3.
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) (x4 : Prop) := @eq Prop ((fun y0 : Prop => (@COND Prop y0 x0 x1) -> @COND Prop y0 x2 x3) x4).
Definition term13 (x0 : Prop) (x1 : Prop) := imp (@COND Prop False x0 x1).
Definition term12 (x0 : Prop) (x1 : Prop) := imp (@COND Prop True x0 x1).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) (x4 : Prop) := ((x0 -> x3) /\ (x1 -> x4)) -> (@COND Prop x2 x0 x1) -> @COND Prop x2 x3 x4.
