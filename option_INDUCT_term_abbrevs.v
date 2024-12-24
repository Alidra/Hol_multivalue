Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term45 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : option a0) := (x0 (@_dest_option a0 x2)) /\ (x1 (@_mk_option a0 (@_dest_option a0 x2))).
Definition term40 (a0 : Type') (x0 : option a0) := @_mk_option a0 (@_dest_option a0 x0).
Definition term14 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : type1432 a0) (x3 : a0) := (x0 (x2 x3)) /\ (x1 (@_mk_option a0 (x2 x3))).
Definition term21 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := and (x0 (x1 x2)).
Definition term37 (a0 : Type') (x0 : option a0) := imp ((@_dest_option a0 (@_mk_option a0 (@_dest_option a0 x0))) = (@_dest_option a0 x0)).
Definition term35 (a0 : Type') (x0 : option a0) := @_dest_option a0 (@_mk_option a0 (@_dest_option a0 x0)).
Definition term30 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) := forall y0 : recspace a0, (x0 y0) -> (fun y1 : recspace a0 => (x0 y1) /\ (x1 (@_mk_option a0 y1))) y0.
Definition term22 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : type1160 a0) (x3 : a0) := (x0 (x1 x3)) /\ (x2 (@Some a0 x3)).
Definition term6 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : recspace a0) := (x0 x2) /\ (x1 (@_mk_option a0 x2)).
Definition term4 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := forall y0 : a0, x0 (x1 y0).
Definition term46 (a0 : Type') (x0 : type1160 a0) (x1 : option a0) := x0 (@_mk_option a0 (@_dest_option a0 x1)).
Definition term12 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : recspace a0) := (x1 (@None a0)) -> (fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) x2.
Definition term38 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : option a0) := (fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) (@_dest_option a0 x2).
Definition term19 (a0 : Type') (x0 : type1160 a0) (x1 : type1432 a0) (x2 : a0) := x0 (@_mk_option a0 (x1 x2)).
Definition term25 (a0 : Type') (x0 : type1160 a0) (x1 : a0) := (fun y0 : a0 => x0 (@Some a0 y0)) x1.
Definition term11 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : recspace a0) := @eq Prop ((fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) x2).
Definition term3 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : type1160 a0) := (((fun y0 : recspace a0 => (x2 y0) /\ (x3 (@_mk_option a0 y0))) x0) /\ (forall y0 : a0, (fun y1 : recspace a0 => (x2 y1) /\ (x3 (@_mk_option a0 y1))) (x1 y0))) -> forall y0 : recspace a0, (x2 y0) -> (fun y1 : recspace a0 => (x2 y1) /\ (x3 (@_mk_option a0 y1))) y0.
Definition term52 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := ((@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)) = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term42 (a0 : Type') (x0 : option a0) := @eq (recspace a0) (@_dest_option a0 x0).
Definition term39 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : option a0) := ((@_dest_option a0 (@_mk_option a0 (@_dest_option a0 x2))) = (@_dest_option a0 x2)) -> (fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) (@_dest_option a0 x2).
Definition term10 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1160 a0) := (x0 x1) /\ (x2 (@None a0)).
Definition term17 (a0 : Type') := fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0).
Definition term15 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := (fun y0 : a0 => x0 (x1 y0)) x2.
Definition term24 (a0 : Type') (x0 : type1160 a0) := forall y0 : a0, x0 (@Some a0 y0).
Definition term51 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := (x1 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = (x2 y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term36 (a0 : Type') (x0 : type1338 a0) (x1 : option a0) := imp (x0 (@_dest_option a0 x1)).
Definition term43 (a0 : Type') (x0 : option a0) := imp ((@_dest_option a0 x0) = (@_dest_option a0 x0)).
Definition term55 (a0 : Type') (x0 : type1338 a0) := ((fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0)) = (fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term41 (a0 : Type') (x0 : option a0) := @eq (recspace a0) (@_dest_option a0 (@_mk_option a0 (@_dest_option a0 x0))).
Definition term8 (a0 : Type') (x0 : type1160 a0) (x1 : recspace a0) := x0 (@_mk_option a0 x1).
Definition term56 (a0 : Type') (x0 : type1338 a0) := (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term53 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term50 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) (x2 : type1432 a0) := (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x1) \/ (exists y3 : a0, y2 = (x2 y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term54 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) := (x1 = (fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0))) -> (x0 = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term32 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : option a0) := (x0 (@_dest_option a0 x2)) -> (fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) (@_dest_option a0 x2).
Definition term29 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : type1160 a0) (x3 : type1432 a0) := ((fun y0 : recspace a0 => (x1 y0) /\ (x2 (@_mk_option a0 y0))) x0) /\ (forall y0 : a0, (fun y1 : recspace a0 => (x1 y1) /\ (x2 (@_mk_option a0 y1))) (x3 y0)).
Definition term2 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) := fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0)).
Definition term16 (a0 : Type') (x0 : type1338 a0) (x1 : type1432 a0) (x2 : a0) := x0 (x1 x2).
Definition term49 (a0 : Type') := forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term23 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : type1432 a0) (x3 : a0) := @eq Prop ((fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) (x2 x3)).
Definition term58 (a0 : Type') := ((fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0) = (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0)) -> forall y0 : type1160 a0, ((y0 (@None a0)) /\ (forall y1 : a0, y0 (@Some a0 y1))) -> forall y1 : option a0, y0 y1.
Definition term13 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : type1432 a0) (x3 : a0) := (fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) (x2 x3).
Definition term9 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := and (x0 x1).
Definition term5 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : recspace a0) := (fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) x2.
Definition term31 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : option a0) := (fun y0 : recspace a0 => (x0 y0) -> (fun y1 : recspace a0 => (x0 y1) /\ (x1 (@_mk_option a0 y1))) y0) (@_dest_option a0 x2).
Definition term18 (a0 : Type') (x0 : type1432 a0) (x1 : a0) := @_mk_option a0 (x0 x1).
Definition term34 (a0 : Type') (x0 : type1338 a0) (x1 : option a0) := x0 (@_dest_option a0 x1).
Definition term57 (a0 : Type') := fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0.
Definition term0 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0.
Definition term44 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : option a0) := ((@_dest_option a0 x2) = (@_dest_option a0 x2)) -> (fun y0 : recspace a0 => (x0 y0) /\ (x1 (@_mk_option a0 y0))) (@_dest_option a0 x2).
Definition term27 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : type1432 a0) := (forall y0 : a0, x1 (@Some a0 y0)) -> forall y0 : a0, (fun y1 : recspace a0 => (x0 y1) /\ (x1 (@_mk_option a0 y1))) (x2 y0).
Definition term7 (a0 : Type') := @CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0).
Definition term47 (a0 : Type') (x0 : type1160 a0) := forall y0 : option a0, x0 y0.
Definition term33 (a0 : Type') (x0 : recspace a0) := @_dest_option a0 (@_mk_option a0 x0).
Definition term20 (a0 : Type') (x0 : type1160 a0) (x1 : a0) := x0 (@Some a0 x1).
Definition term26 (a0 : Type') (x0 : type1338 a0) (x1 : type1160 a0) (x2 : type1432 a0) := forall y0 : a0, (fun y1 : recspace a0 => (x0 y1) /\ (x1 (@_mk_option a0 y1))) (x2 y0).
Definition term28 (a0 : Type') (x0 : type1160 a0) := (x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0)).
Definition term1 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) (x2 : type1338 a0) (x3 : type1160 a0) := (fun y0 : type1338 a0 => ((y0 x0) /\ (forall y1 : a0, y0 (x1 y1))) -> forall y1 : recspace a0, (x2 y1) -> y0 y1) (fun y0 : recspace a0 => (x2 y0) /\ (x3 (@_mk_option a0 y0))).
Definition term48 (a0 : Type') (x0 : type1160 a0) := ((x0 (@None a0)) /\ (forall y0 : a0, x0 (@Some a0 y0))) -> forall y0 : option a0, x0 y0.
