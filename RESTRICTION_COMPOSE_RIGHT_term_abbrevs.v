Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term55 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) := fun y0 : a1 -> a2 => forall y1 : a0 -> Prop, (@RESTRICTION a0 a2 y1 (@o a0 a1 a2 y0 (@RESTRICTION a0 a1 y1 x0))) = (@RESTRICTION a0 a2 y1 (@o a0 a1 a2 y0 x0)).
Definition term20 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) := fun y0 : a0 => x0 (@RESTRICTION a0 a1 x1 x2 y0).
Definition term25 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (fun y0 : a0 => x0 (@COND a1 (@IN a0 y0 x1) (x2 y0) (@ARB a1))) x3.
Definition term29 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq a2 ((fun y0 : a0 => (fun y1 : a0 => x0 (@COND a1 (@IN a0 y1 x1) (x2 y1) (@ARB a1))) y0) x3).
Definition term43 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) := @eq a2 ((fun y0 : a0 => (fun y1 : a0 => x0 (x1 y1)) y0) x2).
Definition term79 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) := (fun y0 : a1 => forall y1 : a1, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((~ x3) -> (@ARB a1) = y1) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 y0 y1)) x4.
Definition term28 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) := fun y0 : a0 => (fun y1 : a0 => x0 (@COND a1 (@IN a0 y1 x1) (x2 y1) (@ARB a1))) y0.
Definition term96 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := ((~ (@IN a0 x3 x0)) -> (@ARB a2) = (@ARB a2)) -> (@COND a2 (@IN a0 x3 x0) (x1 (@COND a1 (@IN a0 x3 x0) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 x3 x0) (x1 (x2 x3)) (@ARB a2)).
Definition term36 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq a2 (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)).
Definition term73 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) (x4 : Prop) (x5 : a2) (x6 : a2) := ((@IN a0 x3 x1) = x4) -> (x4 -> (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) = x5) -> ((~ x4) -> (@ARB a2) = x6) -> (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 x4 x5 x6).
Definition term30 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq a2 ((fun y0 : a0 => x0 (@COND a1 (@IN a0 y0 x1) (x2 y0) (@ARB a1))) x3).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1))) x1.
Definition term24 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @o a0 a1 a2 x0 (@RESTRICTION a0 a1 x1 x2) x3.
Definition term100 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1))) x2.
Definition term62 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : a0 -> a1, forall y1 : a1 -> a2, forall y2 : a0 -> Prop, forall y3 : a0, (@COND a2 (@IN a0 y3 y2) (y1 (@COND a1 (@IN a0 y3 y2) (y0 y3) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y3 y2) (y1 (y0 y3)) (@ARB a2)).
Definition term61 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : a0 -> a1, forall y1 : a1 -> a2, forall y2 : a0 -> Prop, (@RESTRICTION a0 a2 y2 (@o a0 a1 a2 y1 (@RESTRICTION a0 a1 y2 y0))) = (@RESTRICTION a0 a2 y2 (@o a0 a1 a2 y1 y0)).
Definition term58 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) := forall y0 : a1 -> a2, forall y1 : a0 -> Prop, forall y2 : a0, (@COND a2 (@IN a0 y2 y1) (y0 (@COND a1 (@IN a0 y2 y1) (x0 y2) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y2 y1) (y0 (x0 y2)) (@ARB a2)).
Definition term85 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := True -> (x0 x1) = (x0 x1).
Definition term68 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : a2, forall y2 : a2, ((@IN a0 x3 x1) = y0) -> (y0 -> (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) = y1) -> ((~ y0) -> (@ARB a2) = y2) -> (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 y0 y1 y2)) x4.
Definition term72 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) (x4 : Prop) (x5 : a2) (x6 : a2) := (fun y0 : a2 => ((@IN a0 x3 x1) = x4) -> (x4 -> (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) = x5) -> ((~ x4) -> (@ARB a2) = y0) -> (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 x4 x5 y0)) x6.
Definition term99 (a0 : Type') := forall y0 : a0, True.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, (@RESTRICTION a0 a1 y0 y1 y2) = (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1))) x0.
Definition term64 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term56 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) := fun y0 : a1 -> a2 => forall y1 : a0 -> Prop, forall y2 : a0, (@COND a2 (@IN a0 y2 y1) (y0 (@COND a1 (@IN a0 y2 y1) (x0 y2) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y2 y1) (y0 (x0 y2)) (@ARB a2)).
Definition term106 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term103 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term84 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : a1) := (True -> (x1 x2) = x3) -> ((~ True) -> (@ARB a1) = x4) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 True x3 x4).
Definition term70 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) (x4 : Prop) (x5 : a2) := (fun y0 : a2 => forall y1 : a2, ((@IN a0 x3 x1) = x4) -> (x4 -> (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) = y0) -> ((~ x4) -> (@ARB a2) = y1) -> (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 x4 y0 y1)) x5.
Definition term95 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term80 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) := forall y0 : a1, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (@ARB a1) = y0) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 x4 y0).
Definition term48 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) := fun y0 : a0 => (@RESTRICTION a0 a2 x0 (@o a0 a1 a2 x1 (@RESTRICTION a0 a1 x0 x2)) y0) = (@RESTRICTION a0 a2 x0 (@o a0 a1 a2 x1 x2) y0).
Definition term81 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) (x5 : a1) := (fun y0 : a1 => ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (@ARB a1) = y0) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 x4 y0)) x5.
Definition term47 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x0) (x1 (x2 x3)) (@ARB a2).
Definition term51 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := fun y0 : a0 -> Prop => (@RESTRICTION a0 a2 y0 (@o a0 a1 a2 x0 (@RESTRICTION a0 a1 y0 x1))) = (@RESTRICTION a0 a2 y0 (@o a0 a1 a2 x0 x1)).
Definition term53 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, (@RESTRICTION a0 a2 y0 (@o a0 a1 a2 x0 (@RESTRICTION a0 a1 y0 x1))) = (@RESTRICTION a0 a2 y0 (@o a0 a1 a2 x0 x1)).
Definition term21 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := x0 (@RESTRICTION a0 a1 x1 x2 x3).
Definition term97 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := @eq a2 (@COND a2 (@IN a0 x3 x0) (x1 (x2 x3)) (@ARB a2)).
Definition term44 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) := @eq a2 ((fun y0 : a0 => x0 (x1 y0)) x2).
Definition term89 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := ((~ True) -> (@ARB a1) = (@ARB a1)) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 True (x1 x2) (@ARB a1)).
Definition term88 (a0 : Type') := (~ True) -> (@ARB a0) = (@ARB a0).
Definition term23 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) := fun y0 : a0 => x0 (@COND a1 (@IN a0 y0 x1) (x2 y0) (@ARB a1)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1).
Definition term52 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := fun y0 : a0 -> Prop => forall y1 : a0, (@COND a2 (@IN a0 y1 y0) (x0 (@COND a1 (@IN a0 y1 y0) (x1 y1) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y1 y0) (x0 (x1 y1)) (@ARB a2)).
Definition term42 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := fun y0 : a0 => (fun y1 : a0 => x0 (x1 y1)) y0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term71 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) (x4 : Prop) (x5 : a2) := forall y0 : a2, ((@IN a0 x3 x1) = x4) -> (x4 -> (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) = x5) -> ((~ x4) -> (@ARB a2) = y0) -> (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 x4 x5 y0).
Definition term98 (a0 : Type') := fun y0 : a0 => True.
Definition term75 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) (x4 : a2) (x5 : a2) := ((@IN a0 x2 x3) -> (x0 (@COND a1 (@IN a0 x2 x3) (x1 x2) (@ARB a1))) = x4) -> ((~ (@IN a0 x2 x3)) -> (@ARB a2) = x5) -> (@COND a2 (@IN a0 x2 x3) (x0 (@COND a1 (@IN a0 x2 x3) (x1 x2) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 x2 x3) x4 x5).
Definition term83 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : a1) := ((@IN a0 x2 x0) = True) -> (True -> (x1 x2) = x3) -> ((~ True) -> (@ARB a1) = x4) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 True x3 x4).
Definition term35 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @eq a2 (@RESTRICTION a0 a2 x1 (@o a0 a1 a2 x0 (@RESTRICTION a0 a1 x1 x2)) x3).
Definition term22 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1)).
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) := forall y0 : a0, (@RESTRICTION a0 a2 x0 (@o a0 a1 a2 x1 (@RESTRICTION a0 a1 x0 x2)) y0) = (@RESTRICTION a0 a2 x0 (@o a0 a1 a2 x1 x2) y0).
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @RESTRICTION a0 a2 x1 (@o a0 a1 a2 x0 (@RESTRICTION a0 a1 x1 x2)) x3.
Definition term41 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) := x0 (x1 x2).
Definition term74 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) (x4 : a2) (x5 : a2) := ((@IN a0 x2 x3) = (@IN a0 x2 x3)) -> ((@IN a0 x2 x3) -> (x0 (@COND a1 (@IN a0 x2 x3) (x1 x2) (@ARB a1))) = x4) -> ((~ (@IN a0 x2 x3)) -> (@ARB a2) = x5) -> (@COND a2 (@IN a0 x2 x3) (x0 (@COND a1 (@IN a0 x2 x3) (x1 x2) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 x2 x3) x4 x5).
Definition term104 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term101 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := (fun y0 : a1 -> a2 => forall y1 : a0 -> a1, (@o a0 a1 a2 y0 y1) = (fun y2 : a0 => y0 (y1 y2))) x0.
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : a1, forall y2 : a1, ((@IN a0 x2 x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((~ y0) -> (@ARB a1) = y2) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 y0 y1 y2)) x3.
Definition term39 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => x0 (x1 y0)) x2.
Definition term76 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := forall y0 : Prop, forall y1 : a1, forall y2 : a1, ((@IN a0 x2 x0) = y0) -> (y0 -> (x1 x2) = y1) -> ((~ y0) -> (@ARB a1) = y2) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 y0 y1 y2).
Definition term67 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := forall y0 : Prop, forall y1 : a2, forall y2 : a2, ((@IN a0 x3 x1) = y0) -> (y0 -> (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) = y1) -> ((~ y0) -> (@ARB a2) = y2) -> (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 y0 y1 y2).
Definition term66 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term57 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) := forall y0 : a1 -> a2, forall y1 : a0 -> Prop, (@RESTRICTION a0 a2 y1 (@o a0 a1 a2 y0 (@RESTRICTION a0 a1 y1 x0))) = (@RESTRICTION a0 a2 y1 (@o a0 a1 a2 y0 x0)).
Definition term87 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := ((~ True) -> (@ARB a1) = x3) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 True (x1 x2) x3).
Definition term50 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) := forall y0 : a0, (@COND a2 (@IN a0 y0 x0) (x1 (@COND a1 (@IN a0 y0 x0) (x2 y0) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y0 x0) (x1 (x2 y0)) (@ARB a2)).
Definition term34 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2).
Definition term82 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) (x4 : a1) (x5 : a1) := ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = x4) -> ((~ x3) -> (@ARB a1) = x5) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 x4 x5).
Definition term18 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x1) (@o a0 a1 a2 x0 (@RESTRICTION a0 a1 x1 x2) x3) (@ARB a2).
Definition term93 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) (x4 : a2) := ((~ (@IN a0 x3 x0)) -> (@ARB a2) = x4) -> (@COND a2 (@IN a0 x3 x0) (x1 (@COND a1 (@IN a0 x3 x0) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 x3 x0) (x1 (x2 x3)) x4).
Definition term65 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term46 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x0) (x1 (x2 x3)).
Definition term60 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : a0 -> a1 => forall y1 : a1 -> a2, forall y2 : a0 -> Prop, forall y3 : a0, (@COND a2 (@IN a0 y3 y2) (y1 (@COND a1 (@IN a0 y3 y2) (y0 y3) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y3 y2) (y1 (y0 y3)) (@ARB a2)).
Definition term59 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : a0 -> a1 => forall y1 : a1 -> a2, forall y2 : a0 -> Prop, (@RESTRICTION a0 a2 y2 (@o a0 a1 a2 y1 (@RESTRICTION a0 a1 y2 y0))) = (@RESTRICTION a0 a2 y2 (@o a0 a1 a2 y1 y0)).
Definition term78 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := forall y0 : a1, forall y1 : a1, ((@IN a0 x2 x0) = x3) -> (x3 -> (x1 x2) = y0) -> ((~ x3) -> (@ARB a1) = y1) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 x3 y0 y1).
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) := @RESTRICTION a0 a2 x0 (@o a0 a1 a2 x1 x2).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := forall y0 : a0 -> a1, (@o a0 a1 a2 x0 y0) = (fun y1 : a0 => x0 (y0 y1)).
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@o a0 a1 a2 x0 y0) = (fun y1 : a0 => x0 (y0 y1))) x1.
Definition term27 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0 (@COND a1 (@IN a0 y1 x1) (x2 y1) (@ARB a1))) y0) x3.
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) := @o a0 a1 a2 x0 (@RESTRICTION a0 a1 x1 x2).
Definition term86 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := (True -> (x1 x2) = (x1 x2)) -> ((~ True) -> (@ARB a1) = x3) -> (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)) = (@COND a1 True (x1 x2) x3).
Definition term69 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) (x4 : Prop) := forall y0 : a2, forall y1 : a2, ((@IN a0 x3 x1) = x4) -> (x4 -> (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) = y0) -> ((~ x4) -> (@ARB a2) = y1) -> (@COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 x4 y0 y1).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) := @RESTRICTION a0 a2 x1 (@o a0 a1 a2 x0 (@RESTRICTION a0 a1 x1 x2)).
Definition term91 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := (@IN a0 x3 x0) -> (x1 (@COND a1 (@IN a0 x3 x0) (x2 x3) (@ARB a1))) = (x1 (x2 x3)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term38 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x0) (@o a0 a1 a2 x1 x2 x3) (@ARB a2).
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := fun y0 : a0 => x0 (x1 y0).
Definition term92 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) (x4 : a2) := ((@IN a0 x3 x0) -> (x1 (@COND a1 (@IN a0 x3 x0) (x2 x3) (@ARB a1))) = (x1 (x2 x3))) -> ((~ (@IN a0 x3 x0)) -> (@ARB a2) = x4) -> (@COND a2 (@IN a0 x3 x0) (x1 (@COND a1 (@IN a0 x3 x0) (x2 x3) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 x3 x0) (x1 (x2 x3)) x4).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term49 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) := fun y0 : a0 => (@COND a2 (@IN a0 y0 x0) (x1 (@COND a1 (@IN a0 y0 x0) (x2 y0) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y0 x0) (x1 (x2 y0)) (@ARB a2)).
Definition term33 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x1) (x0 (@COND a1 (@IN a0 x3 x1) (x2 x3) (@ARB a1))).
Definition term94 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@ARB a1) = (@ARB a1).
Definition term90 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @COND a1 True (x0 x1) (@ARB a1).
Definition term63 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term54 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, forall y1 : a0, (@COND a2 (@IN a0 y1 y0) (x0 (@COND a1 (@IN a0 y1 y0) (x1 y1) (@ARB a1))) (@ARB a2)) = (@COND a2 (@IN a0 y1 y0) (x0 (x1 y1)) (@ARB a2)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND a1 (@IN a0 x0 x1).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term37 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := @RESTRICTION a0 a2 x0 (@o a0 a1 a2 x1 x2) x3.
Definition term40 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0 (x1 y1)) y0) x2.
Definition term32 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> Prop) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x1) (@o a0 a1 a2 x0 (@RESTRICTION a0 a1 x1 x2) x3).
Definition term105 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
Definition term102 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1)).
Definition term45 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a2) (x2 : a0 -> a1) (x3 : a0) := @COND a2 (@IN a0 x3 x0) (@o a0 a1 a2 x1 x2 x3).
