Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term91 := (~ False) -> False.
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x1 = x0)) /\ (x0 = x1).
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => x1 = y0) x2) x2.
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => y0 = x1) x2) x2.
Definition term62 (a0 : Type') (x0 : a0) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 = y2) y2))) = (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))).
Definition term42 (a0 : Type') (x0 : a0) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = x0) y2))) = (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))).
Definition term64 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term75 (x0 : Prop) := ~ (~ x0).
Definition term12 (a0 : Type') := fun y0 : a0 => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 = y3) y3))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0))).
Definition term4 (a0 : Type') := fun y0 : a0 => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y3 = y0) y3))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => y0 = x1) x2).
Definition term11 (a0 : Type') := fun y0 : a0 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y0 = y2) y2)) = (@INSERT a0 y0 (@EMPTY a0)).
Definition term3 (a0 : Type') := fun y0 : a0 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = y0) y2)) = (@INSERT a0 y0 (@EMPTY a0)).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term45 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => x1 = y1) y0) y0.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => y1 = x1) y0) y0.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term68 (x0 : Prop) := (~ x0) -> False.
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ False.
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => x0 = y0) x1.
Definition term44 (a0 : Type') := forall y0 : a0, True.
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => @SETSPEC a0 x0 (y0 = x1) y0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term89 (x0 : Prop) := (~ x0) -> x0.
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => x1 = y0) x2).
Definition term56 (a0 : Type') (x0 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => x0 = y2) y1) y1.
Definition term29 (a0 : Type') (x0 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => y2 = x0) y1) y1.
Definition term10 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 = y2) y2))) = (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))).
Definition term2 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = x0) y2))) = (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 = y1) y1)).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => x1 = y2) y1) y1)).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (y1 = x1) y1)).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => y2 = x1) y1) y1)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term63 (a0 : Type') (x0 : a0) := fun y0 : a0 => (x0 = y0) = (y0 = x0).
Definition term85 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x0) /\ (~ (x0 = x1)).
Definition term61 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 = y1) y1))).
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => x1 = y2) y1) y1))).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (y1 = x1) y1))).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => y2 = x1) y1) y1))).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @SETSPEC a0 x0 (x1 = x2).
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (x0 = y0)) x1.
Definition term77 (a0 : Type') (x0 : a0) (x1 : a0) := ~ ((x1 = x0) = (x0 = x1)).
Definition term13 (a0 : Type') := forall y0 : a0, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y0 = y2) y2)) = (@INSERT a0 y0 (@EMPTY a0)).
Definition term5 (a0 : Type') := forall y0 : a0, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = y0) y2)) = (@INSERT a0 y0 (@EMPTY a0)).
Definition term71 (a0 : Type') := ((~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False.
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => @SETSPEC a0 x0 (x1 = y0) y0.
Definition term58 (a0 : Type') (x0 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => x0 = y2) y1) y1).
Definition term31 (a0 : Type') (x0 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => y2 = x0) y1) y1).
Definition term9 (a0 : Type') (x0 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x0 = y1) y1).
Definition term1 (a0 : Type') (x0 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (y1 = x0) y1).
Definition term43 (a0 : Type') := fun y0 : a0 => True.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => x1 = y1) y0) y0.
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => y1 = x1) y0) y0.
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 = y0)) x1).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @SETSPEC a0 x0 (x2 = x1) x2.
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0) := exists y0 : a0, @SETSPEC a0 x0 (x1 = y0) y0.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0) := exists y0 : a0, @SETSPEC a0 x0 (y0 = x1) y0.
Definition term67 (a0 : Type') := True /\ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0)).
Definition term74 (a0 : Type') := ~ (~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))).
Definition term69 (a0 : Type') := (~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False.
Definition term8 (a0 : Type') := and (forall y0 : a0, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y3 = y0) y3))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0)))).
Definition term7 (a0 : Type') := and (forall y0 : a0, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = y0) y2)) = (@INSERT a0 y0 (@EMPTY a0))).
Definition term72 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False.
Definition term20 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (x0 = x1).
Definition term82 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (x0 = y0).
Definition term16 (a0 : Type') (a1 : Type') := (forall y0 : a0, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y3 = y0) y3))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0)))) /\ (forall y0 : a1, forall y1 : a1, (@IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (y0 = y3) y3))) = (@IN a1 y1 (@INSERT a1 y0 (@EMPTY a1)))).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x0) \/ (@IN a0 x1 (@EMPTY a0)).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term66 (a0 : Type') := forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0).
Definition term14 (a0 : Type') := forall y0 : a0, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 = y3) y3))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0))).
Definition term6 (a0 : Type') := forall y0 : a0, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y3 = y0) y3))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0))).
Definition term88 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term84 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (x0 = y0)) x0.
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0) := ((x1 = x0) /\ (~ (x0 = x1))) \/ ((~ (x1 = x0)) /\ (x0 = x1)).
Definition term70 (a0 : Type') := ~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0)).
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0) := (~ ((x1 = x0) = (x0 = x1))) -> False.
Definition term15 (a0 : Type') (a1 : Type') := (forall y0 : a0, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (y2 = y0) y2)) = (@INSERT a0 y0 (@EMPTY a0))) /\ (forall y0 : a1, (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (y0 = y2) y2)) = (@INSERT a1 y0 (@EMPTY a1))).
Definition term73 (a0 : Type') := (((~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False) -> ((~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False) -> (~ (forall y0 : a0, forall y1 : a0, (y0 = y1) = (y1 = y0))) -> False.
Definition term48 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term57 (a0 : Type') (x0 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x0 = y1) y1.
Definition term30 (a0 : Type') (x0 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (y1 = x0) y1.
Definition term65 (a0 : Type') := fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => y0 = x0) x1.
Definition term90 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @SETSPEC a0 x0 (x1 = x2) x2.
