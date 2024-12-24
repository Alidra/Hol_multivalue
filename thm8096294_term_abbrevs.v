Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term50 (a0 : Type') := @ε a0 (fun y0 : a0 => False).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @ex1 a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => fun y2 : a1 => @COND (a0 -> Prop) (exists y3 : a0, x0 y2 y3) (x0 y2) (y1 y2)) y0) x1.
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @ex1 a0 ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) := @eq ((a1 -> a0 -> Prop) -> a0) ((fun y0 : a1 => fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 y0)) (@ε a0 (y1 y0)) (@ε a0 (fun y2 : a0 => False))) x0).
Definition term61 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND a0 (exists y0 : a0, x0 x2 y0) (@COND a0 (@ex1 a0 (x0 x2)) (@ε a0 (x0 x2)) (@ε a0 (fun y0 : a0 => False))) (@COND a0 (@ex1 a0 (x1 x2)) (@ε a0 (x1 x2)) (@ε a0 (fun y0 : a0 => False))).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => fun y1 : a1 => @COND (a0 -> Prop) (exists y2 : a0, x0 y1 y2) (x0 y1) (y0 y1)) x1.
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq ((a1 -> a0 -> Prop) -> a1 -> a0 -> Prop) ((fun y0 : type1470 a0 a1 => fun y1 : type1470 a0 a1 => fun y2 : a1 => @COND (a0 -> Prop) (exists y3 : a0, y0 y2 y3) (y0 y2) (y1 y2)) x0).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y0 x0)) (@ε a0 (y0 x0)) (@ε a0 (fun y1 : a0 => False))) x1.
Definition term53 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @eq a0 (@COND a0 (@ex1 a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2))) (@ε a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2))) (@ε a0 (fun y0 : a0 => False))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := @eq (a1 -> a0 -> Prop) ((fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => fun y2 : a1 => @COND (a0 -> Prop) (exists y3 : a0, x0 y2 y3) (x0 y2) (y1 y2)) y0) x1).
Definition term58 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) := @COND a0 (exists y0 : a0, x1 x0 y0) (@_MATCH a1 a0 x0 x1).
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : type1470 a0 a1 => fun y1 : a1 => @COND (a0 -> Prop) (exists y2 : a0, x0 y1 y2) (x0 y1) (y0 y1).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => (fun y1 : a1 => fun y2 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y2 y1)) (@ε a0 (y2 y1)) (@ε a0 (fun y3 : a0 => False))) y0) x0.
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := (fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1) := fun y0 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y0 x0)) (@ε a0 (y0 x0)) (@ε a0 (fun y1 : a0 => False)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := @eq ((a1 -> a0 -> Prop) -> a1 -> a0 -> Prop) ((fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => fun y2 : type1470 a0 a1 => fun y3 : a1 => @COND (a0 -> Prop) (exists y4 : a0, y1 y3 y4) (y1 y3) (y2 y3)) y0) x0).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @ε a0 ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2).
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => fun y2 : type1470 a0 a1 => fun y3 : a1 => @COND (a0 -> Prop) (exists y4 : a0, y1 y3 y4) (y1 y3) (y2 y3)) y0) x0.
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 x0)) (@ε a0 (y1 x0)) (@ε a0 (fun y2 : a0 => False))) y0) (fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x1 y0 y1) (x1 y0) (x2 y0)).
Definition term60 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : type1470 a0 a1) := @COND a0 (exists y0 : a0, x0 x1 y0) (@_MATCH a1 a0 x1 x0) (@_MATCH a1 a0 x1 x2).
Definition term44 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND a0 (@ex1 a0 ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2)).
Definition term51 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND a0 (@ex1 a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2))) (@ε a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2))) (@ε a0 (fun y0 : a0 => False)).
Definition term1 (a0 : Type') (a1 : Type') := fun y0 : a1 => fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 y0)) (@ε a0 (y1 y0)) (@ε a0 (fun y2 : a0 => False)).
Definition term7 (a0 : Type') (a1 : Type') := fun y0 : a1 => (fun y1 : a1 => fun y2 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y2 y1)) (@ε a0 (y2 y1)) (@ε a0 (fun y3 : a0 => False))) y0.
Definition term54 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 x0)) (@ε a0 (y1 x0)) (@ε a0 (fun y2 : a0 => False))) y0) x1.
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @COND a0 (exists y0 : a0, x0 x1 y0).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1) := @eq ((a1 -> a0 -> Prop) -> a0) ((fun y0 : a1 => (fun y1 : a1 => fun y2 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y2 y1)) (@ε a0 (y2 y1)) (@ε a0 (fun y3 : a0 => False))) y0) x0).
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @ε a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2)).
Definition term52 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @eq a0 (@_MATCH a1 a0 x0 (@_SEQPATTERN a0 a1 x1 x2)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @eq a0 ((fun y0 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y0 x0)) (@ε a0 (y0 x0)) (@ε a0 (fun y1 : a0 => False))) (fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x1 y0 y1) (x1 y0) (x2 y0))).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @eq a0 ((fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 x0)) (@ε a0 (y1 x0)) (@ε a0 (fun y2 : a0 => False))) y0) (fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x1 y0 y1) (x1 y0) (x2 y0))).
Definition term49 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND a0 (@ex1 a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2))) (@ε a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2))).
Definition term15 (a0 : Type') (a1 : Type') := fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => fun y2 : type1470 a0 a1 => fun y3 : a1 => @COND (a0 -> Prop) (exists y4 : a0, y1 y3 y4) (y1 y3) (y2 y3)) y0.
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := @eq (a1 -> a0 -> Prop) ((fun y0 : type1470 a0 a1 => fun y1 : a1 => @COND (a0 -> Prop) (exists y2 : a0, x0 y1 y2) (x0 y1) (y0 y1)) x1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1) := fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 x0)) (@ε a0 (y1 x0)) (@ε a0 (fun y2 : a0 => False))) y0.
Definition term55 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) := @eq a0 ((fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 x0)) (@ε a0 (y1 x0)) (@ε a0 (fun y2 : a0 => False))) y0) x1).
Definition term10 (a0 : Type') (a1 : Type') := fun y0 : type1470 a0 a1 => fun y1 : type1470 a0 a1 => fun y2 : a1 => @COND (a0 -> Prop) (exists y3 : a0, y0 y2 y3) (y0 y2) (y1 y2).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type743 a0 a1) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => x0 y0) x1.
Definition term19 (a0 : Type') (a1 : Type') (x0 : type741 a0 a1) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => x0 y0) x1.
Definition term12 (a0 : Type') (a1 : Type') (x0 : type731 a0 a1) (x1 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => x0 y0) x1.
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := (fun y0 : a1 => (fun y1 : a1 => @COND (a0 -> Prop) (exists y2 : a0, x0 y1 y2) (x0 y1) (x1 y1)) y0) x2.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => fun y1 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y1 y0)) (@ε a0 (y1 y0)) (@ε a0 (fun y2 : a0 => False))) x0.
Definition term39 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => (fun y1 : a1 => @COND (a0 -> Prop) (exists y2 : a0, x0 y1 y2) (x0 y1) (x1 y1)) y0.
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND a0 (@ex1 a0 (@COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => x0 y0) x1.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1450 a0 a1) (x1 : a1) := (fun y0 : a1 => x0 y0) x1.
Definition term48 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND a0 (@ex1 a0 ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2)) (@ε a0 ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND a0 (@ex1 a0 ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2)) (@ε a0 ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2)) (@ε a0 (fun y0 : a0 => False)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @COND (a0 -> Prop) (exists y0 : a0, x0 x2 y0) (x0 x2) (x1 x2).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => fun y1 : type1470 a0 a1 => fun y2 : a1 => @COND (a0 -> Prop) (exists y3 : a0, y0 y2 y3) (y0 y2) (y1 y2)) x0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y0 x0)) (@ε a0 (y0 x0)) (@ε a0 (fun y1 : a0 => False))) (fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x1 y0 y1) (x1 y0) (x2 y0)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := fun y0 : type1470 a0 a1 => (fun y1 : type1470 a0 a1 => fun y2 : a1 => @COND (a0 -> Prop) (exists y3 : a0, x0 y2 y3) (x0 y2) (y1 y2)) y0.
Definition term56 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) := @eq a0 ((fun y0 : type1470 a0 a1 => @COND a0 (@ex1 a0 (y0 x0)) (@ε a0 (y0 x0)) (@ε a0 (fun y1 : a0 => False))) x1).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @COND a0 (@ex1 a0 (x0 x1)) (@ε a0 (x0 x1)) (@ε a0 (fun y0 : a0 => False)).
Definition term59 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := @COND a0 (exists y0 : a0, x0 x1 y0) (@COND a0 (@ex1 a0 (x0 x1)) (@ε a0 (x0 x1)) (@ε a0 (fun y0 : a0 => False))).
Definition term40 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @eq (a0 -> Prop) ((fun y0 : a1 => (fun y1 : a1 => @COND (a0 -> Prop) (exists y2 : a0, x0 y1 y2) (x0 y1) (x1 y1)) y0) x2).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) := fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : type1470 a0 a1) (x2 : a1) := @eq (a0 -> Prop) ((fun y0 : a1 => @COND (a0 -> Prop) (exists y1 : a0, x0 y0 y1) (x0 y0) (x1 y0)) x2).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 => fun y1 : type1413 a0 a1 => @COND a1 (@ex1 a1 (y1 y0)) (@ε a1 (y1 y0)) (@ε a1 (fun y2 : a1 => False)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @_MATCH a1 a0 x0 (@_SEQPATTERN a0 a1 x1 x2).
