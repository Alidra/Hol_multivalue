Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term82 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : type686 a0 => forall y1 : a1, (exists y2 : a0, (y1 = (x0 y2)) /\ (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2)) -> forall y2 : a0 -> Prop, (y0 y2) -> exists y3 : a0, (y1 = (x0 y3)) /\ (y2 y3).
Definition term159 := (~ False) -> False.
Definition term110 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (~ (x0 = (x1 y0))) \/ (~ (x2 y0)).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := @eq Prop (@IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) -> @IN a1 y1 (@IMAGE a0 a1 x2 y2)) y1))).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := @eq Prop (@IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x1) -> @IN a1 y2 (@IMAGE a0 a1 x2 y3)) y1) y1))).
Definition term116 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := or (~ (x0 = (x1 x2))).
Definition term136 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := @eq Prop ((fun y0 : a1 => (~ (y0 = (@I (a0 -> a1) x0 x2))) \/ (~ (@I (a0 -> Prop) x1 x2))) x3).
Definition term93 (x0 : Prop) := ~ (~ x0).
Definition term156 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ((@I (a0 -> a1) x1 x0) = (@I (a0 -> a1) x1 x3)) /\ (@I (a0 -> Prop) x2 x3).
Definition term124 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type686 a0) := @INTERS a1 (@IMAGE (a0 -> Prop) (a1 -> Prop) (@IMAGE a0 a1 x0) x1).
Definition term32 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term61 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x0) -> @IN a1 y2 (@IMAGE a0 a1 x1 y3)) y1) y1.
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term85 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4).
Definition term26 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (@IN a1 y2 (@IMAGE a0 a1 y0 (@INTERS a0 y1))) -> @IN a1 y2 (@GSPEC a1 (fun y3 : a1 => exists y4 : a1, @SETSPEC a1 y3 (forall y5 : a0 -> Prop, (@IN (a0 -> Prop) y5 y1) -> @IN a1 y4 (@IMAGE a0 a1 y0 y5)) y4)).
Definition term72 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (@IN (a0 -> Prop) x3 x0) -> @IN a1 x1 (@IMAGE a0 a1 x2 x3).
Definition term74 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN a1 x1 (@IMAGE a0 a1 x2 y0).
Definition term125 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (@I (a0 -> Prop) x1 x2).
Definition term86 (x0 : Prop) := (~ x0) -> False.
Definition term127 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I (a0 -> Prop) y0 x1).
Definition term137 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((~ (x0 = (@I (a0 -> a1) x1 x3))) \/ (~ (@I (a0 -> Prop) x2 x3))).
Definition term134 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> a1) (x3 : a0) := (fun y0 : a1 => (~ (y0 = (@I (a0 -> a1) x2 x1))) \/ (~ (@I (a0 -> Prop) x0 x1))) (@I (a0 -> a1) x2 x3).
Definition term144 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := @eq Prop ((@I (a0 -> Prop) x2 x0) \/ (~ (@I ((a0 -> Prop) -> Prop) x1 x2))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : type686 a0 => @SUBSET a1 (@IMAGE a0 a1 x0 (@INTERS a0 y0)) (@INTERS a1 (@IMAGE (a0 -> Prop) (a1 -> Prop) (@IMAGE a0 a1 x0) y0)).
Definition term131 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I (a0 -> Prop) y0 x1)) x2.
Definition term128 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := and (x0 = (@I (a0 -> a1) x1 x2)).
Definition term56 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) (x3 : a1) := @SETSPEC a1 x0 (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) -> @IN a1 x3 (@IMAGE a0 a1 x2 y0)) x3.
Definition term53 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) (x3 : a1) := @SETSPEC a1 x0 ((fun y0 : a1 => forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) -> @IN a1 y0 (@IMAGE a0 a1 x2 y1)) x3).
Definition term39 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (x0 y0) -> y0 x1.
Definition term145 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term150 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (@I ((a0 -> Prop) -> Prop) x0 x1) -> @I (a0 -> Prop) x1 x2.
Definition term64 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := @IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) -> @IN a1 y1 (@IMAGE a0 a1 x2 y2)) y1)).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := @IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x1) -> @IN a1 y2 (@IMAGE a0 a1 x2 y3)) y1) y1)).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@I (a0 -> Prop) x0 x1)) -> @I (a0 -> Prop) x0 x1.
Definition term38 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (x0 y0) -> y0 x1.
Definition term88 (a0 : Type') (a1 : Type') := ~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4)).
Definition term152 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term140 (x0 : Prop) := (~ x0) -> x0.
Definition term103 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (~ (x0 = (x1 x3))) \/ (~ (x2 x3)).
Definition term34 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (x0 x1).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : type686 a0, @SUBSET a1 (@IMAGE a0 a1 x0 (@INTERS a0 y0)) (@INTERS a1 (@IMAGE (a0 -> Prop) (a1 -> Prop) (@IMAGE a0 a1 x0) y0)).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : type686 a0 => forall y1 : a1, (@IN a1 y1 (@IMAGE a0 a1 x0 (@INTERS a0 y0))) -> @IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y0) -> @IN a1 y3 (@IMAGE a0 a1 x0 y4)) y3)).
Definition term97 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (x0 y0)) \/ (y0 x1).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (x0 = (x1 x3)) /\ (x2 x3).
Definition term63 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := @GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x0) -> @IN a1 y2 (@IMAGE a0 a1 x1 y3)) y1) y1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := @GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) -> @IN a1 y1 (@IMAGE a0 a1 x1 y2)) y1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : type678 a0 a1) := @GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) -> @IN a1 y1 (x1 y2)) y1).
Definition term94 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := (~ (exists y0 : a0, (x0 = (x1 y0)) /\ (x2 y0))) -> False.
Definition term153 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1 -> Prop, (@INTERS a0 (@IMAGE a1 (a0 -> Prop) x0 y0)) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a1, (@IN a1 y3 y0) -> @IN a0 y2 (x0 y3)) y2)).
Definition term146 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1))) -> @I (a0 -> Prop) x1 x2.
Definition term83 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : type686 a0, forall y1 : a1, (exists y2 : a0, (y1 = (x0 y2)) /\ (forall y3 : a0 -> Prop, (y0 y3) -> y3 y2)) -> forall y2 : a0 -> Prop, (y0 y2) -> exists y3 : a0, (y1 = (x0 y3)) /\ (y2 y3).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : type686 a0, forall y1 : a1, (@IN a1 y1 (@IMAGE a0 a1 x0 (@INTERS a0 y0))) -> @IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y0) -> @IN a1 y3 (@IMAGE a0 a1 x0 y4)) y3)).
Definition term147 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term115 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := ~ (x0 = (@I (a0 -> a1) x1 x2)).
Definition term80 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := fun y0 : a1 => (exists y1 : a0, (y0 = (x1 y1)) /\ (forall y2 : a0 -> Prop, (x0 y2) -> y2 y1)) -> forall y1 : a0 -> Prop, (x0 y1) -> exists y2 : a0, (y0 = (x1 y2)) /\ (y1 y2).
Definition term50 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) (x2 : a1) := (fun y0 : a1 => forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) -> @IN a1 y0 (@IMAGE a0 a1 x1 y1)) x2.
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type686 a0) := @IMAGE a0 a1 x0 (@INTERS a0 x1).
Definition term100 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := fun y0 : a0 => (x0 = (x1 y0)) /\ (forall y1 : a0 -> Prop, (~ (x2 y1)) \/ (y1 y0)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := fun y0 : a0 => (x0 = (x1 y0)) /\ (forall y1 : a0 -> Prop, (x2 y1) -> y1 y0).
Definition term77 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := (@IN a1 x0 (@IMAGE a0 a1 x2 (@INTERS a0 x1))) -> @IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) -> @IN a1 y1 (@IMAGE a0 a1 x2 y2)) y1)).
Definition term109 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 = (x1 y1)) /\ (x2 y1)) y0).
Definition term95 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := ~ (exists y0 : a0, (x0 = (x1 y0)) /\ (x2 y0)).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) (x3 : a1) := @SETSPEC a1 x0 ((fun y0 : a1 => forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) -> @IN a1 y0 (@IMAGE a0 a1 x2 y1)) x3) x3.
Definition term96 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x1)) \/ (x1 x2).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := imp (exists y0 : a0, (x0 = (x1 y0)) /\ (forall y1 : a0 -> Prop, (x2 y1) -> y1 y0)).
Definition term129 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) (x3 : a0) := (x0 = (@I (a0 -> a1) x1 x3)) /\ (forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x2 y0)) \/ (@I (a0 -> Prop) y0 x3)).
Definition term141 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) -> @I ((a0 -> Prop) -> Prop) x0 x1.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term89 (a0 : Type') (a1 : Type') := ((~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False.
Definition term123 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (x0 x1)).
Definition term158 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := (((@I (a0 -> a1) x0 x2) = (@I (a0 -> a1) x0 x2)) /\ (@I (a0 -> Prop) x1 x2)) -> False.
Definition term58 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := fun y0 : a1 => @SETSPEC a1 x0 (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) -> @IN a1 y0 (@IMAGE a0 a1 x2 y1)) y0.
Definition term43 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := fun y0 : a0 => (x0 = (x1 y0)) /\ (@IN a0 y0 (@INTERS a0 x2)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (forall y2 : a1, (@IN a1 y2 x0) -> @IN a0 y1 (x1 y2)) y1).
Definition term133 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) (x3 : a1) := (fun y0 : a1 => (~ (y0 = (@I (a0 -> a1) x0 x2))) \/ (~ (@I (a0 -> Prop) x1 x2))) x3.
Definition term57 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := fun y0 : a1 => @SETSPEC a1 x0 ((fun y1 : a1 => forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) -> @IN a1 y1 (@IMAGE a0 a1 x2 y2)) y0) y0.
Definition term155 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (((@I (a0 -> a1) x1 x0) = (@I (a0 -> a1) x1 x3)) /\ (@I (a0 -> Prop) x2 x3)) -> False.
Definition term154 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ (((@I (a0 -> a1) x1 x0) = (@I (a0 -> a1) x1 x3)) /\ (@I (a0 -> Prop) x2 x3)).
Definition term70 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (x0 = (x1 y0)) /\ (x2 y0).
Definition term111 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, (~ (x0 = (x1 y0))) \/ (~ (x2 y0)).
Definition term132 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a1 => (~ (y0 = (@I (a0 -> a1) x0 x2))) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term62 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) -> @IN a1 y1 (@IMAGE a0 a1 x1 y2)) y1.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 (@INTERS a0 x2)).
Definition term118 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (~ (x0 = (@I (a0 -> a1) x1 x3))) \/ (~ (@I (a0 -> Prop) x2 x3)).
Definition term73 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (x0 x3) -> exists y0 : a0, (x1 = (x2 y0)) /\ (x3 y0).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := imp (@IN (a0 -> Prop) x0 x1).
Definition term138 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (~ ((@I (a0 -> a1) x0 x1) = (@I (a0 -> a1) x0 x1))) -> (@I (a0 -> a1) x0 x1) = (@I (a0 -> a1) x0 x1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type686 a0) := @SUBSET a1 (@IMAGE a0 a1 x0 (@INTERS a0 x1)).
Definition term31 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term92 (a0 : Type') (a1 : Type') := ~ (~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))).
Definition term81 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := forall y0 : a1, (exists y1 : a0, (y0 = (x1 y1)) /\ (forall y2 : a0 -> Prop, (x0 y2) -> y2 y1)) -> forall y1 : a0 -> Prop, (x0 y1) -> exists y2 : a0, (y0 = (x1 y2)) /\ (y1 y2).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type686 a0) := @SUBSET a1 (@IMAGE a0 a1 x0 (@INTERS a0 x1)) (@INTERS a1 (@IMAGE (a0 -> Prop) (a1 -> Prop) (@IMAGE a0 a1 x0) x1)).
Definition term87 (a0 : Type') (a1 : Type') := (~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False.
Definition term51 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := fun y0 : a1 => forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) -> @IN a1 y0 (@IMAGE a0 a1 x1 y1).
Definition term16 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : type686 a0, @SUBSET a1 (@IMAGE a0 a1 y0 (@INTERS a0 y1)) (@INTERS a1 (@IMAGE (a0 -> Prop) (a1 -> Prop) (@IMAGE a0 a1 y0) y1)).
Definition term90 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False.
Definition term78 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1) (x2 : a0 -> a1) := (exists y0 : a0, (x1 = (x2 y0)) /\ (forall y1 : a0 -> Prop, (x0 y1) -> y1 y0)) -> forall y0 : a0 -> Prop, (x0 y0) -> exists y1 : a0, (x1 = (x2 y1)) /\ (y0 y1).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (@I (a0 -> Prop) x0 x1).
Definition term120 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, (~ (x0 = (@I (a0 -> a1) x1 y0))) \/ (~ (@I (a0 -> Prop) x2 y0)).
Definition term19 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : type686 a0, @SUBSET a1 (@IMAGE a0 a1 y0 (@INTERS a0 y1)) (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y1) -> @IN a1 y3 (@IMAGE a0 a1 y0 y4)) y3)).
Definition term18 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : type686 a0, @SUBSET a1 (@IMAGE a0 a1 y0 (@INTERS a0 y1)) (@INTERS a1 (@IMAGE (a0 -> Prop) (a1 -> Prop) (@IMAGE a0 a1 y0) y1)).
Definition term102 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ ((x0 = (x1 x3)) /\ (x2 x3)).
Definition term157 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a0) := ((@I (a0 -> a1) x0 x2) = (@I (a0 -> a1) x0 x2)) /\ (@I (a0 -> Prop) x1 x2).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := and (x0 = (x1 x2)).
Definition term69 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := @SUBSET a1 (@IMAGE a0 a1 x1 (@INTERS a0 x0)) (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) -> @IN a1 y1 (@IMAGE a0 a1 x1 y2)) y1)).
Definition term76 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1) (x2 : a0 -> a1) := forall y0 : a0 -> Prop, (x0 y0) -> exists y1 : a0, (x1 = (x2 y1)) /\ (y0 y1).
Definition term142 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) := (@I (a0 -> Prop) x2 x0) \/ (~ (@I ((a0 -> Prop) -> Prop) x1 x2)).
Definition term79 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := fun y0 : a1 => (@IN a1 y0 (@IMAGE a0 a1 x1 (@INTERS a0 x0))) -> @IN a1 y0 (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x0) -> @IN a1 y2 (@IMAGE a0 a1 x1 y3)) y2)).
Definition term60 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := exists y0 : a1, @SETSPEC a1 x0 (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) -> @IN a1 y0 (@IMAGE a0 a1 x2 y1)) y0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a0 -> a1) := forall y0 : a1, (@IN a1 y0 (@IMAGE a0 a1 x1 (@INTERS a0 x0))) -> @IN a1 y0 (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x0) -> @IN a1 y2 (@IMAGE a0 a1 x1 y3)) y2)).
Definition term71 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (x2 y0).
Definition term99 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) (x3 : a0) := (x0 = (x1 x3)) /\ (forall y0 : a0 -> Prop, (~ (x2 y0)) \/ (y0 x3)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) (x3 : a0) := (x0 = (x1 x3)) /\ (forall y0 : a0 -> Prop, (x2 y0) -> y0 x3).
Definition term117 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := or (~ (x0 = (@I (a0 -> a1) x1 x2))).
Definition term108 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := ~ ((fun y0 : a0 => (x0 = (x1 y0)) /\ (x2 y0)) x3).
Definition term84 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4).
Definition term25 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : type686 a0, forall y2 : a1, (@IN a1 y2 (@IMAGE a0 a1 y0 (@INTERS a0 y1))) -> @IN a1 y2 (@GSPEC a1 (fun y3 : a1 => exists y4 : a1, @SETSPEC a1 y3 (forall y5 : a0 -> Prop, (@IN (a0 -> Prop) y5 y1) -> @IN a1 y4 (@IMAGE a0 a1 y0 y5)) y4)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : type686 a0, @SUBSET a1 (@IMAGE a0 a1 x0 (@INTERS a0 y0)) (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y0) -> @IN a1 y2 (@IMAGE a0 a1 x0 y3)) y2)).
Definition term143 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (@I (a0 -> Prop) x1 x2)).
Definition term75 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1) (x2 : a0 -> a1) := fun y0 : a0 -> Prop => (x0 y0) -> exists y1 : a0, (x1 = (x2 y1)) /\ (y0 y1).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => forall y1 : a1 -> Prop, (@INTERS a0 (@IMAGE a1 (a0 -> Prop) y0 y1)) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (forall y4 : a1, (@IN a1 y4 y1) -> @IN a0 y3 (y0 y4)) y3))) x0.
Definition term52 (a0 : Type') (a1 : Type') (x0 : type686 a0) (x1 : a1) (x2 : a0 -> a1) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a1 x1 (@IMAGE a0 a1 x2 y0).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := @IN a1 x0 (@IMAGE a0 a1 x1 (@INTERS a0 x2)).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) (x3 : a0 -> Prop) := (x0 = (x1 x2)) /\ (@IN a0 x2 x3).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term91 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False) -> ((~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False) -> (~ (forall y0 : a0 -> a1, forall y1 : type686 a0, forall y2 : a1, (exists y3 : a0, (y2 = (y0 y3)) /\ (forall y4 : a0 -> Prop, (y1 y4) -> y4 y3)) -> forall y3 : a0 -> Prop, (y1 y3) -> exists y4 : a0, (y2 = (y0 y4)) /\ (y3 y4))) -> False.
Definition term107 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (x0 = (x1 y0)) /\ (x2 y0)) x3.
Definition term149 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term121 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) (x3 : type686 a0) := (x0 = (x1 x2)) /\ (@IN a0 x2 (@INTERS a0 x3)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@INTERS a0 (@IMAGE a1 (a0 -> Prop) x0 y0)) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a1, (@IN a1 y3 y0) -> @IN a0 y2 (x0 y3)) y2))) x1.
Definition term119 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := fun y0 : a0 => (~ (x0 = (@I (a0 -> a1) x1 y0))) \/ (~ (@I (a0 -> Prop) x2 y0)).
Definition term46 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := imp (@IN a1 x0 (@IMAGE a0 a1 x1 (@INTERS a0 x2))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : type678 a0 a1) (x1 : type686 a0) := @INTERS a1 (@IMAGE (a0 -> Prop) (a1 -> Prop) x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1 -> Prop) := @INTERS a0 (@IMAGE a1 (a0 -> Prop) x0 x1).
Definition term139 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := ~ ((@I (a0 -> a1) x0 x1) = (@I (a0 -> a1) x0 x1)).
Definition term98 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (y0 x1).
Definition term54 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a1) (x3 : a0 -> a1) := @SETSPEC a1 x0 (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) -> @IN a1 x2 (@IMAGE a0 a1 x3 y0)).
Definition term114 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := ~ (x0 = (x1 x2)).
Definition term36 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 x1) -> x1 x2.
Definition term106 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => (x0 = (x1 y1)) /\ (x2 y1)) y0).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : type686 a0 => @SUBSET a1 (@IMAGE a0 a1 x0 (@INTERS a0 y0)) (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y0) -> @IN a1 y2 (@IMAGE a0 a1 x0 y3)) y2)).
Definition term17 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : type686 a0, @SUBSET a1 (@IMAGE a0 a1 y0 (@INTERS a0 y1)) (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (forall y4 : a0 -> Prop, (@IN (a0 -> Prop) y4 y1) -> @IN a1 y3 (@IMAGE a0 a1 y0 y4)) y3)).
Definition term122 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term135 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (~ ((@I (a0 -> a1) x1 x0) = (@I (a0 -> a1) x1 x3))) \/ (~ (@I (a0 -> Prop) x2 x3)).
Definition term126 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (@I (a0 -> Prop) y0 x1).
Definition term101 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := exists y0 : a0, (x0 = (x1 y0)) /\ (forall y1 : a0 -> Prop, (~ (x2 y1)) \/ (y1 y0)).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type686 a0) := exists y0 : a0, (x0 = (x1 y0)) /\ (forall y1 : a0 -> Prop, (x2 y1) -> y1 y0).
Definition term35 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) -> @IN a0 x1 x2.
Definition term130 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (~ (x0 = (@I (a0 -> a1) x1 y0))) \/ (~ (@I (a0 -> Prop) x2 y0))) x3.
Definition term59 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type686 a0) (x2 : a0 -> a1) := exists y0 : a1, @SETSPEC a1 x0 ((fun y1 : a1 => forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) -> @IN a1 y1 (@IMAGE a0 a1 x2 y2)) y0) y0.
Definition term37 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term148 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (~ (~ (@I ((a0 -> Prop) -> Prop) x0 x1))).
