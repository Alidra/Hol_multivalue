Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term53 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0).
Definition term64 (a0 : Type') (a1 : Type') (x0 : type1379 a0 a1) (x1 : type1592 a0 a1) (x2 : nat) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) x0 x1 (S x2).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type1337 a0 a1) (x3 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1614 a0, (x2 (@CONSTR a0 y0 y1 y2)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y3 : a0 => fun y4 : type1614 a0 => fun y5 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y3 : a0 => fun y4 : type1614 a0 => fun y5 : nat -> a1 => x1 y3) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) y0 y1 y2 (fun y3 : nat => x2 (y2 y3)))) x3.
Definition term87 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : a1) (x2 : a0 -> a1) (x3 : type1159 a0 a1) := (x3 = (fun y0 : option a0 => x0 (@_dest_option a0 y0))) -> (fun y0 : type1159 a0 a1 => ((y0 (@None a0)) = x1) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x2 y1))) x3.
Definition term42 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type1337 a0 a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM a0) y0)).
Definition term69 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0 y0) x1.
Definition term66 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1)) (NUMERAL 0).
Definition term90 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := fun y0 : type1337 a0 a1 => forall y1 : nat, forall y2 : a0, forall y3 : type1614 a0, (y0 (@CONSTR a0 y1 y2 y3)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y4 : a0 => fun y5 : type1614 a0 => fun y6 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y4 : a0 => fun y5 : type1614 a0 => fun y6 : nat -> a1 => x1 y4) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) y1 y2 y3 (fun y4 : nat => y0 (y3 y4))).
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : type1337 a0 a1) := (fun y0 : nat -> a1 => x0 x1) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM a0) y0)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1338 a0) (x1 : type1159 a0 a1) (x2 : type1337 a0 a1) (x3 : a0) := (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> ((x1 (@None a0)) = (x2 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x1 (@Some a0 x3)) = (x2 (@CONSTR a0 (S (NUMERAL 0)) x3 (fun y0 : nat => @BOTTOM a0)))).
Definition term88 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : a1) (x2 : a0 -> a1) := forall y0 : type1159 a0 a1, (y0 = (fun y1 : option a0 => x0 (@_dest_option a0 y1))) -> (fun y1 : type1159 a0 a1 => ((y1 (@None a0)) = x1) /\ (forall y2 : a0, (y1 (@Some a0 y2)) = (x2 y2))) y0.
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1159 a0 a1) (x1 : type1337 a0 a1) (x2 : a0) := ((fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0) = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> ((x0 (@None a0)) = (x1 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x0 (@Some a0 x2)) = (x1 (@CONSTR a0 (S (NUMERAL 0)) x2 (fun y0 : nat => @BOTTOM a0)))).
Definition term62 := S (NUMERAL 0).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : nat) (x3 : type1337 a0 a1) (x4 : a0) := (fun y0 : a0 => forall y1 : type1614 a0, (x3 (@CONSTR a0 x2 y0 y1)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y2 : a0 => fun y3 : type1614 a0 => fun y4 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y2 : a0 => fun y3 : type1614 a0 => fun y4 : nat -> a1 => x1 y2) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) x2 y0 y1 (fun y2 : nat => x3 (y1 y2)))) x4.
Definition term51 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@ε a0 (fun y0 : a0 => True)).
Definition term18 (a0 : Type') (x0 : type1432 a0) (x1 : a0) := @eq (recspace a0) (x0 x1).
Definition term43 (a0 : Type') := @ε a0 (fun y0 : a0 => True).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) := fun y0 : option a0 => x0 (@_dest_option a0 y0).
Definition term79 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1159 a0 a1) (x2 : a0 -> a1) := ((x1 (@None a0)) = x0) /\ (forall y0 : a0, (x1 (@Some a0 y0)) = (x2 y0)).
Definition term45 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @FCONS a0 x0 x1 (NUMERAL 0).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1159 a0 a1) (x3 : type1337 a0 a1) (x4 : a0) := ((fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0)) = (fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> ((x2 (@None a0)) = (x3 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x2 (@Some a0 x4)) = (x3 (@CONSTR a0 (S (NUMERAL 0)) x4 (fun y0 : nat => @BOTTOM a0)))).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : type1337 a0 a1) := (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0 y0) x1 (fun y0 : nat => @BOTTOM a0) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM a0) y0)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : type1159 a0 a1) (x4 : type1337 a0 a1) (x5 : a0) := (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = (x2 y3))) -> y1 y2) -> y1 y0)) -> ((x3 (@None a0)) = (x4 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x3 (@Some a0 x5)) = (x4 (@CONSTR a0 (S (NUMERAL 0)) x5 (fun y0 : nat => @BOTTOM a0)))).
Definition term30 (a0 : Type') (a1 : Type') := forall y0 : type1592 a0 a1, exists y1 : type1337 a0 a1, forall y2 : nat, forall y3 : a0, forall y4 : type1614 a0, (y1 (@CONSTR a0 y2 y3 y4)) = (y0 y2 y3 y4 (fun y5 : nat => y1 (y4 y5))).
Definition term16 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0)) x0.
Definition term52 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0).
Definition term9 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := forall y0 : a0, x0 (x1 y0).
Definition term60 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1337 a0 a1) := (fun y0 : nat -> a1 => x0) (fun y0 : nat => x1 ((fun y1 : nat => @BOTTOM a0) y0)).
Definition term84 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := forall y0 : type1159 a0 a1, (forall y1 : type1159 a0 a1, (y1 = y0) -> (fun y2 : type1159 a0 a1 => ((y2 (@None a0)) = x0) /\ (forall y3 : a0, (y2 (@Some a0 y3)) = (x1 y3))) y1) -> exists y1 : type1159 a0 a1, ((y1 (@None a0)) = x0) /\ (forall y2 : a0, (y1 (@Some a0 y2)) = (x1 y2)).
Definition term78 (a0 : Type') (a1 : Type') (x0 : type1159 a0 a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 (@Some a0 y0)) = (x1 y0).
Definition term13 (a0 : Type') (x0 : type1432 a0) (x1 : a0) := @_dest_option a0 (@_mk_option a0 (x0 x1)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1159 a0 a1) (x1 : a0) := x0 (@Some a0 x1).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1338 a0) (x1 : type1159 a0 a1) (x2 : type1337 a0 a1) (x3 : a0) := ((@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)) = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> ((x1 (@None a0)) = (x2 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x1 (@Some a0 x3)) = (x2 (@CONSTR a0 (S (NUMERAL 0)) x3 (fun y0 : nat => @BOTTOM a0)))).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) (x3 : type1159 a0 a1) (x4 : type1337 a0 a1) (x5 : a0) := (x2 = (fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = (x2 y3))) -> y1 y2) -> y1 y0)) -> ((x3 (@None a0)) = (x4 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x3 (@Some a0 x5)) = (x4 (@CONSTR a0 (S (NUMERAL 0)) x5 (fun y0 : nat => @BOTTOM a0)))).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1159 a0 a1) (x3 : type1337 a0 a1) (x4 : a0) := (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> ((x2 (@None a0)) = (x3 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x2 (@Some a0 x4)) = (x3 (@CONSTR a0 (S (NUMERAL 0)) x4 (fun y0 : nat => @BOTTOM a0)))).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : nat) (x3 : a0) (x4 : type1337 a0 a1) := forall y0 : type1614 a0, (x4 (@CONSTR a0 x2 x3 y0)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y1 : a0 => fun y2 : type1614 a0 => fun y3 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y1 : a0 => fun y2 : type1614 a0 => fun y3 : nat -> a1 => x1 y1) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) x2 x3 y0 (fun y1 : nat => x4 (y0 y1))).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1337 a0 a1) := (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0) (fun y0 : nat => x1 ((fun y1 : nat => @BOTTOM a0) y0)).
Definition term3 (a0 : Type') := fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (S (NUMERAL 0)) x2.
Definition term11 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := (fun y0 : a0 => x0 (x1 y0)) x2.
Definition term86 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : a1) (x2 : a0 -> a1) := (forall y0 : type1159 a0 a1, (y0 = (fun y1 : option a0 => x0 (@_dest_option a0 y1))) -> (fun y1 : type1159 a0 a1 => ((y1 (@None a0)) = x1) /\ (forall y2 : a0, (y1 (@Some a0 y2)) = (x2 y2))) y0) -> exists y0 : type1159 a0 a1, ((y0 (@None a0)) = x1) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x2 y1)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := (fun y0 : type1592 a0 a1 => exists y1 : type1337 a0 a1, forall y2 : nat, forall y3 : a0, forall y4 : type1614 a0, (y1 (@CONSTR a0 y2 y3 y4)) = (y0 y2 y3 y4 (fun y5 : nat => y1 (y4 y5)))) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1)))).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type1337 a0 a1) := forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, (x2 (@CONSTR a0 y0 y1 y2)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y3 : a0 => fun y4 : type1614 a0 => fun y5 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y3 : a0 => fun y4 : type1614 a0 => fun y5 : nat -> a1 => x1 y3) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) y0 y1 y2 (fun y3 : nat => x2 (y2 y3))).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))).
Definition term82 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := (fun y0 : type279 a0 a1 => forall y1 : type1159 a0 a1, (forall y2 : type1159 a0 a1, (y2 = y1) -> y0 y2) -> ex y0) (fun y0 : type1159 a0 a1 => ((y0 (@None a0)) = x0) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x1 y1))).
Definition term71 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0 y0) x1 (fun y0 : nat => @BOTTOM a0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : type1432 a0) (x2 : a0) := x0 (@_dest_option a0 (@_mk_option a0 (x1 x2))).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1379 a0 a1) (x1 : type1592 a0 a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) x0 x1 (NUMERAL 0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : type1432 a0) (x2 : a0) := (fun y0 : option a0 => x0 (@_dest_option a0 y0)) (@_mk_option a0 (x1 x2)).
Definition term85 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type1337 a0 a1) := (fun y0 : type1159 a0 a1 => (forall y1 : type1159 a0 a1, (y1 = y0) -> (fun y2 : type1159 a0 a1 => ((y2 (@None a0)) = x0) /\ (forall y3 : a0, (y2 (@Some a0 y3)) = (x1 y3))) y1) -> exists y1 : type1159 a0 a1, ((y1 (@None a0)) = x0) /\ (forall y2 : a0, (y1 (@Some a0 y2)) = (x1 y2))) (fun y0 : option a0 => x2 (@_dest_option a0 y0)).
Definition term74 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : type1614 a0 => fun y1 : nat -> a1 => x0 x1) (fun y0 : nat => @BOTTOM a0).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0 y0.
Definition term80 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : type1159 a0 a1) := (fun y0 : type1159 a0 a1 => ((y0 (@None a0)) = x0) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x1 y1))) x2.
Definition term56 (a0 : Type') (a1 : Type') (x0 : a1) := fun y0 : type1614 a0 => fun y1 : nat -> a1 => x0.
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : a0) := x0 (@CONSTR a0 (S (NUMERAL 0)) x1 (fun y0 : nat => @BOTTOM a0)).
Definition term12 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := x0 (x1 x2).
Definition term92 (a0 : Type') (a1 : Type') := forall y0 : a1, forall y1 : a0 -> a1, exists y2 : type1159 a0 a1, ((y2 (@None a0)) = y0) /\ (forall y3 : a0, (y2 (@Some a0 y3)) = (y1 y3)).
Definition term44 (a0 : Type') := fun y0 : nat => @BOTTOM a0.
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1159 a0 a1) (x1 : type1337 a0 a1) (x2 : a0) := ((x0 (@None a0)) = (x1 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x0 (@Some a0 x2)) = (x1 (@CONSTR a0 (S (NUMERAL 0)) x2 (fun y0 : nat => @BOTTOM a0)))).
Definition term50 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)).
Definition term81 (a0 : Type') (a1 : Type') := forall y0 : type279 a0 a1, forall y1 : type1159 a0 a1, (forall y2 : type1159 a0 a1, (y2 = y1) -> y0 y2) -> ex y0.
Definition term58 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1337 a0 a1) := (fun y0 : type1614 a0 => fun y1 : nat -> a1 => x0) (fun y0 : nat => @BOTTOM a0) (fun y0 : nat => x1 ((fun y1 : nat => @BOTTOM a0) y0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : recspace a0) := (fun y0 : option a0 => x0 (@_dest_option a0 y0)) (@_mk_option a0 x1).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (NUMERAL 0).
Definition term40 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : nat) (x2 : a0) (x3 : type1614 a0) := x0 (@CONSTR a0 x1 x2 x3).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a1) := fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0.
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := exists y0 : type1337 a0 a1, forall y1 : nat, forall y2 : a0, forall y3 : type1614 a0, (y0 (@CONSTR a0 y1 y2 y3)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y4 : a0 => fun y5 : type1614 a0 => fun y6 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y4 : a0 => fun y5 : type1614 a0 => fun y6 : nat -> a1 => x1 y4) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) y1 y2 y3 (fun y4 : nat => y0 (y3 y4))).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (S (NUMERAL 0)).
Definition term28 (a0 : Type') := fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0.
Definition term8 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0.
Definition term57 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : type1614 a0 => fun y1 : nat -> a1 => x0) (fun y0 : nat => @BOTTOM a0).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1159 a0 a1) (x3 : type1337 a0 a1) (x4 : a0) := (x1 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> ((x2 (@None a0)) = (x3 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)))) /\ ((x2 (@Some a0 x4)) = (x3 (@CONSTR a0 (S (NUMERAL 0)) x4 (fun y0 : nat => @BOTTOM a0)))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : recspace a0) := x0 (@_dest_option a0 (@_mk_option a0 x1)).
Definition term73 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := fun y0 : type1614 a0 => fun y1 : nat -> a1 => x0 x1.
Definition term54 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) := fun y0 : nat => x0 ((fun y1 : nat => @BOTTOM a0) y0).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : nat) (x3 : a0) (x4 : type1337 a0 a1) (x5 : type1614 a0) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) x2 x3 x5 (fun y0 : nat => x4 (x5 y0)).
Definition term83 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := fun y0 : type1159 a0 a1 => ((y0 (@None a0)) = x0) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x1 y1)).
Definition term91 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : a0 -> a1, exists y1 : type1159 a0 a1, ((y1 (@None a0)) = x0) /\ (forall y2 : a0, (y1 (@Some a0 y2)) = (y0 y2)).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1)).
Definition term1 (a0 : Type') := @CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : nat) (x3 : a0) (x4 : type1337 a0 a1) (x5 : type1614 a0) := (fun y0 : type1614 a0 => (x4 (@CONSTR a0 x2 x3 y0)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y1 : a0 => fun y2 : type1614 a0 => fun y3 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y1 : a0 => fun y2 : type1614 a0 => fun y3 : nat -> a1 => x1 y1) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) x2 x3 y0 (fun y1 : nat => x4 (y0 y1)))) x5.
Definition term10 (a0 : Type') (x0 : recspace a0) := @_dest_option a0 (@_mk_option a0 x0).
Definition term89 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := exists y0 : type1159 a0 a1, ((y0 (@None a0)) = x0) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x1 y1)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) := x0 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : nat) (x3 : type1337 a0 a1) := forall y0 : a0, forall y1 : type1614 a0, (x3 (@CONSTR a0 x2 y0 y1)) = (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y2 : a0 => fun y3 : type1614 a0 => fun y4 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y2 : a0 => fun y3 : type1614 a0 => fun y4 : nat -> a1 => x1 y2) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) x2 y0 y1 (fun y2 : nat => x3 (y1 y2))).
Definition term76 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := fun y0 : nat -> a1 => x0 x1.
Definition term70 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (S (NUMERAL 0)) x2 (fun y0 : nat => @BOTTOM a0).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0) (x3 : type1337 a0 a1) := @FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x0) (@FCONS (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1) (fun y0 : a0 => fun y1 : type1614 a0 => fun y2 : nat -> a1 => x1 y0) (@FNIL (a0 -> (nat -> recspace a0) -> (nat -> a1) -> a1))) (S (NUMERAL 0)) x2 (fun y0 : nat => @BOTTOM a0) (fun y0 : nat => x3 ((fun y1 : nat => @BOTTOM a0) y0)).
Definition term63 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := @FCONS a0 x0 x1 (S x2).
Definition term59 (a0 : Type') (x0 : a0) := fun y0 : nat -> a0 => x0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1337 a0 a1) (x1 : type1432 a0) (x2 : a0) := x0 (x1 x2).
Definition term17 (a0 : Type') (x0 : a0) := @CONSTR a0 (S (NUMERAL 0)) x0 (fun y0 : nat => @BOTTOM a0).
Definition term75 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : type1337 a0 a1) := (fun y0 : type1614 a0 => fun y1 : nat -> a1 => x0 x1) (fun y0 : nat => @BOTTOM a0) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM a0) y0)).