Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1606) := (@monoidal nat x0) -> forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : type1415 a0 a1, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@iterate nat a0 x0 y0 (fun y3 : a0 => @iterate nat a1 x0 (y1 y3) (y2 y3))) = (@iterate nat (prod a0 a1) x0 (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> nat) (fun y3 : type1212 a0 a1 => forall y4 : a0, forall y5 : a1, @GEQ nat (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := (@monoidal a2 x0) -> forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : type1412 a0 a1 a2, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@iterate a2 a0 x0 y0 (fun y3 : a0 => @iterate a2 a1 x0 (y1 y3) (y2 y3))) = (@iterate a2 (prod a0 a1) x0 (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> a2) (fun y3 : type1209 a0 a1 a2 => forall y4 : a0, forall y5 : a1, @GEQ a2 (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> @FINITE a1 (x1 y0))) -> (@nsum a0 x0 (fun y0 : a0 => @nsum a1 (x1 y0) (x2 y0))) = (@nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 (x1 y1))) (@pair a0 a1 y1 y2))) (@GABS ((prod a0 a1) -> nat) (fun y0 : type1212 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ nat (y0 (@pair a0 a1 y1 y2)) (x2 y1 y2)))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : type1415 a0 a1) := fun y0 : a0 => @nsum a1 (x0 y0) (x1 y0).
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1415 a0 a1) := @GABS ((prod a0 a1) -> nat) (fun y0 : type1212 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ nat (y0 (@pair a0 a1 y1 y2)) (x0 y1 y2)).
Definition term36 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : type1415 a0 a1, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@iterate nat a0 Nat.add y0 (fun y3 : a0 => @iterate nat a1 Nat.add (y1 y3) (y2 y3))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> nat) (fun y3 : type1212 a0 a1 => forall y4 : a0, forall y5 : a1, @GEQ nat (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term35 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : type1415 a0 a1, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@nsum a0 y0 (fun y3 : a0 => @nsum a1 (y1 y3) (y2 y3))) = (@nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> nat) (fun y3 : type1212 a0 a1 => forall y4 : a0, forall y5 : a1, @GEQ nat (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : type1412 a0 a1 a2, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@iterate a2 a0 x0 y0 (fun y3 : a0 => @iterate a2 a1 x0 (y1 y3) (y2 y3))) = (@iterate a2 (prod a0 a1) x0 (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> a2) (fun y3 : type1209 a0 a1 a2 => forall y4 : a0, forall y5 : a1, @GEQ a2 (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : type1415 a0 a1 => ((@FINITE a0 x0) /\ (forall y1 : a0, (@IN a0 y1 x0) -> @FINITE a1 (x1 y1))) -> (@nsum a0 x0 (fun y1 : a0 => @nsum a1 (x1 y1) (y0 y1))) = (@nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y1 : prod a0 a1 => exists y2 : a0, exists y3 : a1, @SETSPEC (prod a0 a1) y1 ((@IN a0 y2 x0) /\ (@IN a1 y3 (x1 y2))) (@pair a0 a1 y2 y3))) (@GABS ((prod a0 a1) -> nat) (fun y1 : type1212 a0 a1 => forall y2 : a0, forall y3 : a1, @GEQ nat (y1 (@pair a0 a1 y2 y3)) (y0 y2 y3)))).
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : type1415 a0 a1 => ((@FINITE a0 x0) /\ (forall y1 : a0, (@IN a0 y1 x0) -> @FINITE a1 (x1 y1))) -> (@iterate nat a0 Nat.add x0 (fun y1 : a0 => @iterate nat a1 Nat.add (x1 y1) (y0 y1))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y1 : prod a0 a1 => exists y2 : a0, exists y3 : a1, @SETSPEC (prod a0 a1) y1 ((@IN a0 y2 x0) /\ (@IN a1 y3 (x1 y2))) (@pair a0 a1 y2 y3))) (@GABS ((prod a0 a1) -> nat) (fun y1 : type1212 a0 a1 => forall y2 : a0, forall y3 : a1, @GEQ nat (y1 (@pair a0 a1 y2 y3)) (y0 y2 y3)))).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a0 -> Prop, forall y2 : type1413 a0 a1, forall y3 : type1412 a0 a1 a2, ((@FINITE a0 y1) /\ (forall y4 : a0, (@IN a0 y4 y1) -> @FINITE a1 (y2 y4))) -> (@iterate a2 a0 y0 y1 (fun y4 : a0 => @iterate a2 a1 y0 (y2 y4) (y3 y4))) = (@iterate a2 (prod a0 a1) y0 (@GSPEC (prod a0 a1) (fun y4 : prod a0 a1 => exists y5 : a0, exists y6 : a1, @SETSPEC (prod a0 a1) y4 ((@IN a0 y5 y1) /\ (@IN a1 y6 (y2 y5))) (@pair a0 a1 y5 y6))) (@GABS ((prod a0 a1) -> a2) (fun y4 : type1209 a0 a1 a2 => forall y5 : a0, forall y6 : a1, @GEQ a2 (y4 (@pair a0 a1 y5 y6)) (y3 y5 y6)))).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : type1415 a0 a1) (x2 : a0) := @nsum a1 (x0 x2) (x1 x2).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := @iterate nat a1 Nat.add (x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := @iterate nat a0 Nat.add x0 (fun y0 : a0 => @iterate nat a1 Nat.add (x1 y0) (x2 y0)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : type1415 a0 a1, ((@FINITE a0 x0) /\ (forall y1 : a0, (@IN a0 y1 x0) -> @FINITE a1 (x1 y1))) -> (@iterate nat a0 Nat.add x0 (fun y1 : a0 => @iterate nat a1 Nat.add (x1 y1) (y0 y1))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y1 : prod a0 a1 => exists y2 : a0, exists y3 : a1, @SETSPEC (prod a0 a1) y1 ((@IN a0 y2 x0) /\ (@IN a1 y3 (x1 y2))) (@pair a0 a1 y2 y3))) (@GABS ((prod a0 a1) -> nat) (fun y1 : type1212 a0 a1 => forall y2 : a0, forall y3 : a1, @GEQ nat (y1 (@pair a0 a1 y2 y3)) (y0 y2 y3)))).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : type1415 a0 a1, ((@FINITE a0 x0) /\ (forall y1 : a0, (@IN a0 y1 x0) -> @FINITE a1 (x1 y1))) -> (@nsum a0 x0 (fun y1 : a0 => @nsum a1 (x1 y1) (y0 y1))) = (@nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y1 : prod a0 a1 => exists y2 : a0, exists y3 : a1, @SETSPEC (prod a0 a1) y1 ((@IN a0 y2 x0) /\ (@IN a1 y3 (x1 y2))) (@pair a0 a1 y2 y3))) (@GABS ((prod a0 a1) -> nat) (fun y1 : type1212 a0 a1 => forall y2 : a0, forall y3 : a1, @GEQ nat (y1 (@pair a0 a1 y2 y3)) (y0 y2 y3)))).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> @FINITE a1 (x1 y0))) -> (@iterate nat a0 Nat.add x0 (fun y0 : a0 => @iterate nat a1 Nat.add (x1 y0) (x2 y0))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 (x1 y1))) (@pair a0 a1 y1 y2))) (@GABS ((prod a0 a1) -> nat) (fun y0 : type1212 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ nat (y0 (@pair a0 a1 y1 y2)) (x2 y1 y2)))).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 (x1 y1))) (@pair a0 a1 y1 y2))).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := (forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a0 -> Prop, forall y2 : type1413 a0 a1, forall y3 : type1412 a0 a1 a2, ((@FINITE a0 y1) /\ (forall y4 : a0, (@IN a0 y4 y1) -> @FINITE a1 (y2 y4))) -> (@iterate a2 a0 y0 y1 (fun y4 : a0 => @iterate a2 a1 y0 (y2 y4) (y3 y4))) = (@iterate a2 (prod a0 a1) y0 (@GSPEC (prod a0 a1) (fun y4 : prod a0 a1 => exists y5 : a0, exists y6 : a1, @SETSPEC (prod a0 a1) y4 ((@IN a0 y5 y1) /\ (@IN a1 y6 (y2 y5))) (@pair a0 a1 y5 y6))) (@GABS ((prod a0 a1) -> a2) (fun y4 : type1209 a0 a1 a2 => forall y5 : a0, forall y6 : a1, @GEQ a2 (y4 (@pair a0 a1 y5 y6)) (y3 y5 y6))))) -> forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : type1412 a0 a1 a2, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@iterate a2 a0 x0 y0 (fun y3 : a0 => @iterate a2 a1 x0 (y1 y3) (y2 y3))) = (@iterate a2 (prod a0 a1) x0 (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> a2) (fun y3 : type1209 a0 a1 a2 => forall y4 : a0, forall y5 : a1, @GEQ a2 (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := @nsum a0 x0 (fun y0 : a0 => @nsum a1 (x1 y0) (x2 y0)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := imp ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> @FINITE a1 (x1 y0))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := @nsum a1 (x0 x1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := @iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 (x1 y1))) (@pair a0 a1 y1 y2))) (@GABS ((prod a0 a1) -> nat) (fun y0 : type1212 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ nat (y0 (@pair a0 a1 y1 y2)) (x2 y1 y2))).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := @eq nat (@nsum a0 x0 (fun y0 : a0 => @nsum a1 (x1 y0) (x2 y0))).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : type1413 a0 a1 => forall y1 : type1415 a0 a1, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> @FINITE a1 (y0 y2))) -> (@iterate nat a0 Nat.add x0 (fun y2 : a0 => @iterate nat a1 Nat.add (y0 y2) (y1 y2))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y2 : prod a0 a1 => exists y3 : a0, exists y4 : a1, @SETSPEC (prod a0 a1) y2 ((@IN a0 y3 x0) /\ (@IN a1 y4 (y0 y3))) (@pair a0 a1 y3 y4))) (@GABS ((prod a0 a1) -> nat) (fun y2 : type1212 a0 a1 => forall y3 : a0, forall y4 : a1, @GEQ nat (y2 (@pair a0 a1 y3 y4)) (y1 y3 y4)))).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : type1413 a0 a1 => forall y1 : type1415 a0 a1, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> @FINITE a1 (y0 y2))) -> (@nsum a0 x0 (fun y2 : a0 => @nsum a1 (y0 y2) (y1 y2))) = (@nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y2 : prod a0 a1 => exists y3 : a0, exists y4 : a1, @SETSPEC (prod a0 a1) y2 ((@IN a0 y3 x0) /\ (@IN a1 y4 (y0 y3))) (@pair a0 a1 y3 y4))) (@GABS ((prod a0 a1) -> nat) (fun y2 : type1212 a0 a1 => forall y3 : a0, forall y4 : a1, @GEQ nat (y2 (@pair a0 a1 y3 y4)) (y1 y3 y4)))).
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : type1415 a0 a1) (x2 : a0) := @iterate nat a1 Nat.add (x0 x2) (x1 x2).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : type1413 a0 a1, forall y1 : type1415 a0 a1, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> @FINITE a1 (y0 y2))) -> (@iterate nat a0 Nat.add x0 (fun y2 : a0 => @iterate nat a1 Nat.add (y0 y2) (y1 y2))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y2 : prod a0 a1 => exists y3 : a0, exists y4 : a1, @SETSPEC (prod a0 a1) y2 ((@IN a0 y3 x0) /\ (@IN a1 y4 (y0 y3))) (@pair a0 a1 y3 y4))) (@GABS ((prod a0 a1) -> nat) (fun y2 : type1212 a0 a1 => forall y3 : a0, forall y4 : a1, @GEQ nat (y2 (@pair a0 a1 y3 y4)) (y1 y3 y4)))).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : type1413 a0 a1, forall y1 : type1415 a0 a1, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> @FINITE a1 (y0 y2))) -> (@nsum a0 x0 (fun y2 : a0 => @nsum a1 (y0 y2) (y1 y2))) = (@nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y2 : prod a0 a1 => exists y3 : a0, exists y4 : a1, @SETSPEC (prod a0 a1) y2 ((@IN a0 y3 x0) /\ (@IN a1 y4 (y0 y3))) (@pair a0 a1 y3 y4))) (@GABS ((prod a0 a1) -> nat) (fun y2 : type1212 a0 a1 => forall y3 : a0, forall y4 : a1, @GEQ nat (y2 (@pair a0 a1 y3 y4)) (y1 y3 y4)))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : type1415 a0 a1) := fun y0 : a0 => @iterate nat a1 Nat.add (x0 y0) (x1 y0).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 (x1 y1))) (@pair a0 a1 y1 y2)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 (x1 y1))) (@pair a0 a1 y1 y2))).
Definition term38 (a0 : Type') (a1 : Type') := (@monoidal nat Nat.add) -> forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : type1415 a0 a1, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@iterate nat a0 Nat.add y0 (fun y3 : a0 => @iterate nat a1 Nat.add (y1 y3) (y2 y3))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> nat) (fun y3 : type1212 a0 a1 => forall y4 : a0, forall y5 : a1, @GEQ nat (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term34 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : type1413 a0 a1, forall y2 : type1415 a0 a1, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@iterate nat a0 Nat.add y0 (fun y3 : a0 => @iterate nat a1 Nat.add (y1 y3) (y2 y3))) = (@iterate nat (prod a0 a1) Nat.add (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> nat) (fun y3 : type1212 a0 a1 => forall y4 : a0, forall y5 : a1, @GEQ nat (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term33 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : type1413 a0 a1, forall y2 : type1415 a0 a1, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> @FINITE a1 (y1 y3))) -> (@nsum a0 y0 (fun y3 : a0 => @nsum a1 (y1 y3) (y2 y3))) = (@nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y3 : prod a0 a1 => exists y4 : a0, exists y5 : a1, @SETSPEC (prod a0 a1) y3 ((@IN a0 y4 y0) /\ (@IN a1 y5 (y1 y4))) (@pair a0 a1 y4 y5))) (@GABS ((prod a0 a1) -> nat) (fun y3 : type1212 a0 a1 => forall y4 : a0, forall y5 : a1, @GEQ nat (y3 (@pair a0 a1 y4 y5)) (y2 y4 y5)))).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') := (forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a0 -> Prop, forall y2 : type1413 a0 a1, forall y3 : type1412 a0 a1 a2, ((@FINITE a0 y1) /\ (forall y4 : a0, (@IN a0 y4 y1) -> @FINITE a1 (y2 y4))) -> (@iterate a2 a0 y0 y1 (fun y4 : a0 => @iterate a2 a1 y0 (y2 y4) (y3 y4))) = (@iterate a2 (prod a0 a1) y0 (@GSPEC (prod a0 a1) (fun y4 : prod a0 a1 => exists y5 : a0, exists y6 : a1, @SETSPEC (prod a0 a1) y4 ((@IN a0 y5 y1) /\ (@IN a1 y6 (y2 y5))) (@pair a0 a1 y5 y6))) (@GABS ((prod a0 a1) -> a2) (fun y4 : type1209 a0 a1 a2 => forall y5 : a0, forall y6 : a1, @GEQ a2 (y4 (@pair a0 a1 y5 y6)) (y3 y5 y6))))) -> forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a0 -> Prop, forall y2 : type1413 a0 a1, forall y3 : type1412 a0 a1 a2, ((@FINITE a0 y1) /\ (forall y4 : a0, (@IN a0 y4 y1) -> @FINITE a1 (y2 y4))) -> (@iterate a2 a0 y0 y1 (fun y4 : a0 => @iterate a2 a1 y0 (y2 y4) (y3 y4))) = (@iterate a2 (prod a0 a1) y0 (@GSPEC (prod a0 a1) (fun y4 : prod a0 a1 => exists y5 : a0, exists y6 : a1, @SETSPEC (prod a0 a1) y4 ((@IN a0 y5 y1) /\ (@IN a1 y6 (y2 y5))) (@pair a0 a1 y5 y6))) (@GABS ((prod a0 a1) -> a2) (fun y4 : type1209 a0 a1 a2 => forall y5 : a0, forall y6 : a1, @GEQ a2 (y4 (@pair a0 a1 y5 y6)) (y3 y5 y6)))).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := @nsum (prod a0 a1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 (x1 y1))) (@pair a0 a1 y1 y2))) (@GABS ((prod a0 a1) -> nat) (fun y0 : type1212 a0 a1 => forall y1 : a0, forall y2 : a1, @GEQ nat (y0 (@pair a0 a1 y1 y2)) (x2 y1 y2))).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := (fun y0 : type1400 a2 => (@monoidal a2 y0) -> forall y1 : a0 -> Prop, forall y2 : type1413 a0 a1, forall y3 : type1412 a0 a1 a2, ((@FINITE a0 y1) /\ (forall y4 : a0, (@IN a0 y4 y1) -> @FINITE a1 (y2 y4))) -> (@iterate a2 a0 y0 y1 (fun y4 : a0 => @iterate a2 a1 y0 (y2 y4) (y3 y4))) = (@iterate a2 (prod a0 a1) y0 (@GSPEC (prod a0 a1) (fun y4 : prod a0 a1 => exists y5 : a0, exists y6 : a1, @SETSPEC (prod a0 a1) y4 ((@IN a0 y5 y1) /\ (@IN a1 y6 (y2 y5))) (@pair a0 a1 y5 y6))) (@GABS ((prod a0 a1) -> a2) (fun y4 : type1209 a0 a1 a2 => forall y5 : a0, forall y6 : a1, @GEQ a2 (y4 (@pair a0 a1 y5 y6)) (y3 y5 y6))))) x0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type1415 a0 a1) := @eq nat (@iterate nat a0 Nat.add x0 (fun y0 : a0 => @iterate nat a1 Nat.add (x1 y0) (x2 y0))).