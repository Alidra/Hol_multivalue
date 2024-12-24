Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term65 (a0 : Type') (x0 : type1597 a0) := imp (@ZRECSPACE a0 x0).
Definition term182 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => x0 y0.
Definition term138 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := (forall y0 : nat, x0 (@_mk_rec a0 (x1 y0))) -> forall y0 : nat, forall y1 : a0, x0 (@CONSTR a0 y0 y1 (fun y2 : nat => @_mk_rec a0 (x1 y2))).
Definition term128 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := (forall y0 : nat, x0 ((fun y1 : nat => @_mk_rec a0 (x1 y1)) y0)) -> forall y0 : nat, forall y1 : a0, x0 (@CONSTR a0 y0 y1 (fun y2 : nat => @_mk_rec a0 (x1 y2))).
Definition term124 (a0 : Type') (x0 : type1338 a0) (x1 : type1614 a0) := (forall y0 : nat, x0 (x1 y0)) -> forall y0 : nat, forall y1 : a0, x0 (@CONSTR a0 y0 y1 x1).
Definition term154 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := x0 (@CONSTR a0 x1 x2 (fun y0 : nat => @_mk_rec a0 (x3 y0))).
Definition term147 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := @_dest_rec a0 ((fun y0 : nat => @_mk_rec a0 (x0 y0)) x1).
Definition term109 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := ((forall y0 : nat, @ZRECSPACE a0 (x3 y0)) /\ (forall y0 : nat, x0 (@_mk_rec a0 (x3 y0)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 x2 x3)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))).
Definition term121 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1614 a0) := x0 (@CONSTR a0 x1 x2 x3).
Definition term196 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, (forall y2 : nat, (@ZRECSPACE a0 (y1 y2)) /\ (x0 (@_mk_rec a0 (y1 y2)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 y0 y1)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 y1)))) x2.
Definition term207 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (@ZRECSPACE a0 (@_dest_rec a0 x1)) -> (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 (@_mk_rec a0 (@_dest_rec a0 x1))).
Definition term62 (a0 : Type') (x0 : type1338 a0) := imp (((@ZRECSPACE a0 (@ZBOT a0)) /\ (x0 (@_mk_rec a0 (@ZBOT a0)))) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2))))).
Definition term86 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, ((fun y1 : nat => @ZRECSPACE a0 (x1 y1)) y0) /\ ((fun y1 : nat => x0 (@_mk_rec a0 (x1 y1))) y0).
Definition term101 (a0 : Type') (x0 : type1600 a0) := forall y0 : nat, (fun y1 : nat => @ZRECSPACE a0 (x0 y1)) y0.
Definition term155 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 (fun y0 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y0))))).
Definition term117 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) := forall y0 : type1614 a0, (forall y1 : nat, x0 (y0 y1)) -> x0 (@CONSTR a0 x1 x2 y0).
Definition term116 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) := (fun y0 : a0 => forall y1 : type1614 a0, (forall y2 : nat, x0 (y1 y2)) -> x0 (@CONSTR a0 x1 y0 y1)) x2.
Definition term33 (a0 : Type') (x0 : type1338 a0) := and ((fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZBOT a0)).
Definition term143 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => @_mk_rec a0 (x0 y1)) y0) x1.
Definition term78 (a0 : Type') (x0 : type1338 a0) := x0 (@_mk_rec a0 (@ZBOT a0)).
Definition term209 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := x0 (@_mk_rec a0 (@_dest_rec a0 x1)).
Definition term172 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term136 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := imp (forall y0 : nat, x0 (@_mk_rec a0 (x1 y0))).
Definition term135 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := imp (forall y0 : nat, x0 ((fun y1 : nat => @_mk_rec a0 (x1 y1)) y0)).
Definition term64 (a0 : Type') (x0 : type1338 a0) (x1 : type1597 a0) := (@ZRECSPACE a0 x1) /\ (x0 (@_mk_rec a0 x1)).
Definition term43 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZCONSTR a0 x1 x2 x3).
Definition term153 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (@_mk_rec a0 (x2 y0)))).
Definition term140 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 ((fun y1 : nat => @_mk_rec a0 (x2 y1)) y0))).
Definition term9 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term27 (a0 : Type') (x0 : type1338 a0) := fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0)).
Definition term60 (a0 : Type') (x0 : type1338 a0) := ((@ZRECSPACE a0 (@ZBOT a0)) /\ (x0 (@_mk_rec a0 (@ZBOT a0)))) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2)))).
Definition term122 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1614 a0) := forall y0 : a0, x0 (@CONSTR a0 x1 y0 x2).
Definition term192 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3))) -> (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = True.
Definition term167 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y2)))))) -> x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3)).
Definition term166 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (forall y0 : nat, forall y1 : a0, x0 (@CONSTR a0 y0 y1 (fun y2 : nat => @_mk_rec a0 (x3 y2)))) -> x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3)).
Definition term20 (a0 : Type') := (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) -> forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2).
Definition term112 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term41 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := imp (forall y0 : nat, (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) (x1 y0)).
Definition term35 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) (x2 : nat) := (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (x1 x2).
Definition term159 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1600 a0) := forall y0 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 (fun y1 : nat => @_dest_rec a0 (@_mk_rec a0 (x2 y1))))).
Definition term118 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1614 a0) := (fun y0 : type1614 a0 => (forall y1 : nat, x0 (y0 y1)) -> x0 (@CONSTR a0 x1 x2 y0)) x3.
Definition term189 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1338 a0) (x3 : type1600 a0) (x4 : Prop) := ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3))) -> (x2 (@_mk_rec a0 (@ZCONSTR a0 x0 x1 x3))) = x4) -> ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y2)))))) -> x2 (@_mk_rec a0 (@ZCONSTR a0 x0 x1 x3))) = ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3))) -> x4).
Definition term87 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := (forall y0 : nat, (fun y1 : nat => @ZRECSPACE a0 (x1 y1)) y0) /\ (forall y0 : nat, (fun y1 : nat => x0 (@_mk_rec a0 (x1 y1))) y0).
Definition term71 (a0 : Type') (x0 : type1338 a0) := forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0)).
Definition term210 (a0 : Type') (x0 : recspace a0) := and (@ZRECSPACE a0 (@_dest_rec a0 x0)).
Definition term202 (a0 : Type') := forall y0 : a0, True.
Definition term96 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) (x2 : nat) := ((fun y0 : nat => @ZRECSPACE a0 (x1 y0)) x2) /\ ((fun y0 : nat => x0 (@_mk_rec a0 (x1 y0))) x2).
Definition term26 (a0 : Type') (x0 : type1338 a0) := (fun y0 : type953 a0 => ((y0 (@ZBOT a0)) /\ (forall y1 : nat, forall y2 : a0, forall y3 : type1600 a0, (forall y4 : nat, y0 (y3 y4)) -> y0 (@ZCONSTR a0 y1 y2 y3))) -> forall y1 : type1597 a0, (@ZRECSPACE a0 y1) -> y0 y1) (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))).
Definition term59 (a0 : Type') (x0 : type1338 a0) := ((fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZBOT a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (fun y4 : type1597 a0 => (@ZRECSPACE a0 y4) /\ (x0 (@_mk_rec a0 y4))) (y2 y3)) -> (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (@ZCONSTR a0 y0 y1 y2)).
Definition term171 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term183 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @_mk_rec a0 (@ZCONSTR a0 x0 x1 x2).
Definition term84 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term63 (a0 : Type') (x0 : type1338 a0) (x1 : type1597 a0) := (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) x1.
Definition term181 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) (x4 : Prop) (x5 : Prop) := ((forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y2)))))) = x4) -> (x4 -> (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = x5) -> ((forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y2)))))) -> x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = (x4 -> x5).
Definition term215 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := imp ((@ZRECSPACE a0 (@_dest_rec a0 x1)) -> (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 (@_mk_rec a0 (@_dest_rec a0 x1)))).
Definition term103 (a0 : Type') (x0 : type1600 a0) := and (forall y0 : nat, @ZRECSPACE a0 (x0 y0)).
Definition term194 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := (forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x1))) -> True.
Definition term151 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 ((fun y1 : nat => @_mk_rec a0 (x2 y1)) y0)).
Definition term56 (a0 : Type') (x0 : type1338 a0) := fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2))).
Definition term55 (a0 : Type') (x0 : type1338 a0) := fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (fun y4 : type1597 a0 => (@ZRECSPACE a0 y4) /\ (x0 (@_mk_rec a0 y4))) (y2 y3)) -> (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (@ZCONSTR a0 y0 y1 y2).
Definition term11 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) x0.
Definition term4 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1614 a0, (@CONSTR a0 y0 y1 y2) = (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y3 : nat => @_dest_rec a0 (y2 y3))))) x0.
Definition term51 (a0 : Type') (x0 : type1338 a0) (x1 : nat) := fun y0 : a0 => forall y1 : type1600 a0, (forall y2 : nat, (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (y1 y2)) -> (fun y2 : type1597 a0 => (@ZRECSPACE a0 y2) /\ (x0 (@_mk_rec a0 y2))) (@ZCONSTR a0 x1 y0 y1).
Definition term3 (x0 : Prop) (x1 : Prop) := ((x0 -> x0 /\ x1) -> x0 -> x1) /\ ((x0 -> x1) -> x0 -> x0 /\ x1).
Definition term149 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => @_dest_rec a0 ((fun y1 : nat => @_mk_rec a0 (x0 y1)) y0).
Definition term212 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 x1).
Definition term198 (a0 : Type') := fun y0 : type1600 a0 => True.
Definition term16 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (forall y0 : nat, @ZRECSPACE a0 (x2 y0)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term99 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := @eq Prop (forall y0 : nat, (@ZRECSPACE a0 (x1 y0)) /\ (x0 (@_mk_rec a0 (x1 y0)))).
Definition term98 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := @eq Prop (forall y0 : nat, ((fun y1 : nat => @ZRECSPACE a0 (x1 y1)) y0) /\ ((fun y1 : nat => x0 (@_mk_rec a0 (x1 y1))) y0)).
Definition term216 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := imp ((@ZRECSPACE a0 (@_dest_rec a0 x1)) -> (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 x1)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term81 (a0 : Type') (x0 : type1338 a0) := (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2)))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0)).
Definition term38 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => (@ZRECSPACE a0 (x1 y0)) /\ (x0 (@_mk_rec a0 (x1 y0))).
Definition term15 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => (forall y1 : nat, @ZRECSPACE a0 (y0 y1)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 y0)) x2.
Definition term208 (a0 : Type') (x0 : recspace a0) := @_mk_rec a0 (@_dest_rec a0 x0).
Definition term90 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := (fun y0 : nat => @ZRECSPACE a0 (x0 y0)) x1.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)).
Definition term52 (a0 : Type') (x0 : type1338 a0) (x1 : nat) := fun y0 : a0 => forall y1 : type1600 a0, (forall y2 : nat, (@ZRECSPACE a0 (y1 y2)) /\ (x0 (@_mk_rec a0 (y1 y2)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 y0 y1)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 y1))).
Definition term36 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) (x2 : nat) := (@ZRECSPACE a0 (x1 x2)) /\ (x0 (@_mk_rec a0 (x1 x2))).
Definition term120 (a0 : Type') (x0 : type1338 a0) (x1 : type1614 a0) := forall y0 : nat, x0 (x1 y0).
Definition term32 (a0 : Type') (x0 : type1338 a0) := (@ZRECSPACE a0 (@ZBOT a0)) /\ (x0 (@_mk_rec a0 (@ZBOT a0))).
Definition term107 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := (forall y0 : nat, @ZRECSPACE a0 (x1 y0)) /\ (forall y0 : nat, x0 (@_mk_rec a0 (x1 y0))).
Definition term174 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term206 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@_dest_rec a0 x1).
Definition term104 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => (fun y1 : nat => x0 (@_mk_rec a0 (x1 y1))) y0.
Definition term28 (a0 : Type') (x0 : type1338 a0) := (((fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZBOT a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (fun y4 : type1597 a0 => (@ZRECSPACE a0 y4) /\ (x0 (@_mk_rec a0 y4))) (y2 y3)) -> (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (@ZCONSTR a0 y0 y1 y2))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) y0.
Definition term68 (a0 : Type') (x0 : type1338 a0) := fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) -> (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) y0.
Definition term76 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((((@ZRECSPACE a0 (@ZBOT a0)) /\ (x0 (@_mk_rec a0 (@ZBOT a0)))) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2))))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) -> x0 x1.
Definition term75 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((((fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZBOT a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (fun y4 : type1597 a0 => (@ZRECSPACE a0 y4) /\ (x0 (@_mk_rec a0 y4))) (y2 y3)) -> (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (@ZCONSTR a0 y0 y1 y2))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) y0) -> x0 x1.
Definition term220 (a0 : Type') (x0 : recspace a0) := @ZRECSPACE a0 (@_dest_rec a0 x0).
Definition term70 (a0 : Type') (x0 : type1338 a0) := forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) y0.
Definition term150 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => @_dest_rec a0 (@_mk_rec a0 (x0 y0)).
Definition term127 (a0 : Type') (x0 : type1338 a0) (x1 : type1614 a0) := (fun y0 : type1614 a0 => (forall y1 : nat, x0 (y0 y1)) -> forall y1 : nat, forall y2 : a0, x0 (@CONSTR a0 y1 y2 y0)) x1.
Definition term42 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := imp (forall y0 : nat, (@ZRECSPACE a0 (x1 y0)) /\ (x0 (@_mk_rec a0 (x1 y0)))).
Definition term97 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => ((fun y1 : nat => @ZRECSPACE a0 (x1 y1)) y0) /\ ((fun y1 : nat => x0 (@_mk_rec a0 (x1 y1))) y0).
Definition term79 (a0 : Type') (x0 : type1338 a0) := True /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2)))).
Definition term48 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) := fun y0 : type1600 a0 => (forall y1 : nat, (@ZRECSPACE a0 (y0 y1)) /\ (x0 (@_mk_rec a0 (y0 y1)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 x2 y0)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 y0))).
Definition term129 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => @_mk_rec a0 (x0 y0).
Definition term74 (a0 : Type') (x0 : type1338 a0) := imp ((((@ZRECSPACE a0 (@ZBOT a0)) /\ (x0 (@_mk_rec a0 (@ZBOT a0)))) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2))))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))).
Definition term73 (a0 : Type') (x0 : type1338 a0) := imp ((((fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZBOT a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (fun y4 : type1597 a0 => (@ZRECSPACE a0 y4) /\ (x0 (@_mk_rec a0 y4))) (y2 y3)) -> (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (@ZCONSTR a0 y0 y1 y2))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) y0).
Definition term108 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := imp ((forall y0 : nat, @ZRECSPACE a0 (x1 y0)) /\ (forall y0 : nat, x0 (@_mk_rec a0 (x1 y0)))).
Definition term141 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term77 (a0 : Type') := and (@ZRECSPACE a0 (@ZBOT a0)).
Definition term72 (a0 : Type') (x0 : type1338 a0) := (((@ZRECSPACE a0 (@ZBOT a0)) /\ (x0 (@_mk_rec a0 (@ZBOT a0)))) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2))))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0)).
Definition term199 (a0 : Type') := forall y0 : type1600 a0, True.
Definition term37 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) (x1 y0).
Definition term186 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x1)).
Definition term161 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x1 y2))))).
Definition term92 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := and ((fun y0 : nat => @ZRECSPACE a0 (x0 y0)) x1).
Definition term187 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x1)).
Definition term162 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x1 y2))))).
Definition term137 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, forall y1 : a0, x0 (@CONSTR a0 y0 y1 (fun y2 : nat => @_mk_rec a0 (x1 y2))).
Definition term123 (a0 : Type') (x0 : type1338 a0) (x1 : type1614 a0) := forall y0 : nat, forall y1 : a0, x0 (@CONSTR a0 y0 y1 x1).
Definition term58 (a0 : Type') (x0 : type1338 a0) := forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2))).
Definition term57 (a0 : Type') (x0 : type1338 a0) := forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (fun y4 : type1597 a0 => (@ZRECSPACE a0 y4) /\ (x0 (@_mk_rec a0 y4))) (y2 y3)) -> (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (@ZCONSTR a0 y0 y1 y2).
Definition term30 (a0 : Type') (x0 : type1338 a0) := forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, (forall y3 : nat, x0 (y2 y3)) -> x0 (@CONSTR a0 y0 y1 y2).
Definition term10 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2).
Definition term201 (a0 : Type') := fun y0 : a0 => True.
Definition term66 (a0 : Type') (x0 : type1338 a0) (x1 : type1597 a0) := (@ZRECSPACE a0 x1) -> (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) x1.
Definition term145 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := @eq (recspace a0) ((fun y0 : nat => (fun y1 : nat => @_mk_rec a0 (x0 y1)) y0) x1).
Definition term219 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (@ZRECSPACE a0 (@_dest_rec a0 x1)) -> x0 x1.
Definition term142 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term173 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := (fun y0 : nat => (@_dest_rec a0 (@_mk_rec a0 (x0 y0))) = (x0 y0)) x1.
Definition term218 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((@ZRECSPACE a0 (@_dest_rec a0 x1)) -> (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 x1)) -> x0 x1.
Definition term222 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((@ZRECSPACE a0 (@_dest_rec a0 x1)) -> x0 x1) -> x0 x1.
Definition term111 := forall y0 : nat, True.
Definition term93 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := and (@ZRECSPACE a0 (x0 x1)).
Definition term132 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) (x2 : nat) := x0 ((fun y0 : nat => @_mk_rec a0 (x1 y0)) x2).
Definition term191 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1600 a0) (x3 : a0) := (fun y0 : a0 => x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 x2))) x3.
Definition term221 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := imp ((@ZRECSPACE a0 (@_dest_rec a0 x1)) -> x0 x1).
Definition term45 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (forall y0 : nat, (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) (x3 y0)) -> (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZCONSTR a0 x1 x2 x3).
Definition term133 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => x0 ((fun y1 : nat => @_mk_rec a0 (x1 y1)) y0).
Definition term228 (a0 : Type') (x0 : type1338 a0) := ((x0 (@BOTTOM a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, (forall y3 : nat, x0 (y2 y3)) -> x0 (@CONSTR a0 y0 y1 y2))) -> forall y0 : recspace a0, x0 y0.
Definition term204 (a0 : Type') (x0 : type1338 a0) := imp (forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))).
Definition term168 (a0 : Type') (x0 : type1597 a0) := @_dest_rec a0 (@_mk_rec a0 x0).
Definition term195 (a0 : Type') (x0 : type1338 a0) (x1 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2)))) x1.
Definition term114 (a0 : Type') (x0 : type1338 a0) (x1 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1614 a0, (forall y3 : nat, x0 (y2 y3)) -> x0 (@CONSTR a0 y0 y1 y2)) x1.
Definition term47 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) := fun y0 : type1600 a0 => (forall y1 : nat, (fun y2 : type1597 a0 => (@ZRECSPACE a0 y2) /\ (x0 (@_mk_rec a0 y2))) (y0 y1)) -> (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) (@ZCONSTR a0 x1 x2 y0).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, (y0 y2) /\ (y1 y2)) = ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2))) x0.
Definition term46 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (forall y0 : nat, (@ZRECSPACE a0 (x3 y0)) /\ (x0 (@_mk_rec a0 (x3 y0)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 x2 x3)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))).
Definition term227 (a0 : Type') (x0 : type1338 a0) := forall y0 : recspace a0, x0 y0.
Definition term148 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := @_dest_rec a0 (@_mk_rec a0 (x0 x1)).
Definition term110 := fun y0 : nat => True.
Definition term67 (a0 : Type') (x0 : type1338 a0) (x1 : type1597 a0) := (@ZRECSPACE a0 x1) -> (@ZRECSPACE a0 x1) /\ (x0 (@_mk_rec a0 x1)).
Definition term1 (x0 : Prop) (x1 : Prop) := (x0 -> x0 /\ x1) -> x0 -> x1.
Definition term100 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => (fun y1 : nat => @ZRECSPACE a0 (x0 y1)) y0.
Definition term205 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) -> x0 x1.
Definition term179 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) (x4 : Prop) := forall y0 : Prop, ((forall y1 : nat, forall y2 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y1 y2 (fun y3 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y3)))))) = x4) -> (x4 -> (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = y0) -> ((forall y1 : nat, forall y2 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y1 y2 (fun y3 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y3)))))) -> x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = (x4 -> y0).
Definition term175 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term214 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (@ZRECSPACE a0 (@_dest_rec a0 x1)) -> (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 x1).
Definition term85 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term157 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1600 a0) := fun y0 : a0 => x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 (fun y1 : nat => @_dest_rec a0 (@_mk_rec a0 (x2 y1))))).
Definition term82 (a0 : Type') (x0 : type1338 a0) := imp ((forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2)))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))).
Definition term13 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, (forall y2 : nat, @ZRECSPACE a0 (y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 y0 y1)) x1.
Definition term6 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2))))) x1.
Definition term139 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @CONSTR a0 x0 x1 (fun y0 : nat => @_mk_rec a0 (x2 y0)).
Definition term185 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1600 a0) := forall y0 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 x2)).
Definition term177 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : nat, forall y3 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y2 y3 (fun y4 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y4)))))) = y0) -> (y0 -> (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = y1) -> ((forall y2 : nat, forall y3 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y2 y3 (fun y4 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y4)))))) -> x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = (y0 -> y1).
Definition term176 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term7 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1614 a0, (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1)))).
Definition term229 (a0 : Type') := forall y0 : type1338 a0, ((y0 (@BOTTOM a0)) /\ (forall y1 : nat, forall y2 : a0, forall y3 : type1614 a0, (forall y4 : nat, y0 (y3 y4)) -> y0 (@CONSTR a0 y1 y2 y3))) -> forall y1 : recspace a0, y0 y1.
Definition term225 (a0 : Type') (x0 : recspace a0) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 (@_mk_rec a0 (@_dest_rec a0 x0))).
Definition term49 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) := forall y0 : type1600 a0, (forall y1 : nat, (fun y2 : type1597 a0 => (@ZRECSPACE a0 y2) /\ (x0 (@_mk_rec a0 y2))) (y0 y1)) -> (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) (@ZCONSTR a0 x1 x2 y0).
Definition term39 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, (fun y1 : type1597 a0 => (@ZRECSPACE a0 y1) /\ (x0 (@_mk_rec a0 y1))) (x1 y0).
Definition term180 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((forall y1 : nat, forall y2 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y1 y2 (fun y3 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y3)))))) = x4) -> (x4 -> (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = y0) -> ((forall y1 : nat, forall y2 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y1 y2 (fun y3 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y3)))))) -> x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = (x4 -> y0)) x5.
Definition term69 (a0 : Type') (x0 : type1338 a0) := fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0)).
Definition term188 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1338 a0) (x3 : type1600 a0) (x4 : Prop) := ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y2)))))) = (forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3)))) -> ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3))) -> (x2 (@_mk_rec a0 (@ZCONSTR a0 x0 x1 x3))) = x4) -> ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y2)))))) -> x2 (@_mk_rec a0 (@ZCONSTR a0 x0 x1 x3))) = ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3))) -> x4).
Definition term106 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, x0 (@_mk_rec a0 (x1 y0)).
Definition term29 (a0 : Type') (x0 : type1338 a0) := (x0 (@BOTTOM a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, (forall y3 : nat, x0 (y2 y3)) -> x0 (@CONSTR a0 y0 y1 y2)).
Definition term197 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (fun y0 : type1600 a0 => (forall y1 : nat, (@ZRECSPACE a0 (y0 y1)) /\ (x0 (@_mk_rec a0 (y0 y1)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 x2 y0)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 y0)))) x3.
Definition term224 (a0 : Type') (x0 : recspace a0) := @_dest_rec a0 (@_mk_rec a0 (@_dest_rec a0 x0)).
Definition term119 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1614 a0) := (forall y0 : nat, x0 (x3 y0)) -> x0 (@CONSTR a0 x1 x2 x3).
Definition term0 (x0 : Prop) (x1 : Prop) := x0 -> x0 /\ x1.
Definition term152 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (@_mk_rec a0 (x2 y0))).
Definition term160 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => forall y1 : a0, x0 (@CONSTR a0 y0 y1 (fun y2 : nat => @_mk_rec a0 (x1 y2))).
Definition term144 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => (fun y1 : nat => @_mk_rec a0 (x0 y1)) y0.
Definition term193 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1338 a0) (x3 : type1600 a0) := ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3))) -> (x2 (@_mk_rec a0 (@ZCONSTR a0 x0 x1 x3))) = True) -> ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y2)))))) -> x2 (@_mk_rec a0 (@ZCONSTR a0 x0 x1 x3))) = ((forall y0 : nat, forall y1 : a0, x2 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x3))) -> True).
Definition term88 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => @ZRECSPACE a0 (x0 y0).
Definition term200 (a0 : Type') (x0 : Prop) := forall y0 : type1600 a0, x0.
Definition term18 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term40 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, (@ZRECSPACE a0 (x1 y0)) /\ (x0 (@_mk_rec a0 (x1 y0))).
Definition term213 (a0 : Type') (x0 : recspace a0) := imp (@ZRECSPACE a0 (@_dest_rec a0 x0)).
Definition term17 (a0 : Type') (x0 : type1600 a0) := forall y0 : nat, @ZRECSPACE a0 (x0 y0).
Definition term14 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, (forall y1 : nat, @ZRECSPACE a0 (y0 y1)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 y0).
Definition term95 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) (x2 : nat) := x0 (@_mk_rec a0 (x1 x2)).
Definition term203 (a0 : Type') (x0 : type1338 a0) := True -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0)).
Definition term211 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 (@_mk_rec a0 (@_dest_rec a0 x1))).
Definition term169 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => (@_dest_rec a0 (@_mk_rec a0 (x0 y0))) = (x0 y0).
Definition term8 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (fun y0 : type1614 a0 => (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1))))) x2.
Definition term102 (a0 : Type') (x0 : type1600 a0) := and (forall y0 : nat, (fun y1 : nat => @ZRECSPACE a0 (x0 y1)) y0).
Definition term61 (a0 : Type') (x0 : type1338 a0) := imp (((fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZBOT a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (fun y4 : type1597 a0 => (@ZRECSPACE a0 y4) /\ (x0 (@_mk_rec a0 y4))) (y2 y3)) -> (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (@ZCONSTR a0 y0 y1 y2))).
Definition term2 (x0 : Prop) (x1 : Prop) := (x0 -> x1) -> x0 -> x0 /\ x1.
Definition term91 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := @ZRECSPACE a0 (x0 x1).
Definition term113 (x0 : Prop) := forall y0 : nat, x0.
Definition term34 (a0 : Type') (x0 : type1338 a0) := and ((@ZRECSPACE a0 (@ZBOT a0)) /\ (x0 (@_mk_rec a0 (@ZBOT a0)))).
Definition term105 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, (fun y1 : nat => x0 (@_mk_rec a0 (x1 y1))) y0.
Definition term156 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1600 a0) := fun y0 : a0 => x0 (@CONSTR a0 x1 y0 (fun y1 : nat => @_mk_rec a0 (x2 y1))).
Definition term125 (a0 : Type') (x0 : type1338 a0) := forall y0 : type1614 a0, (forall y1 : nat, x0 (y0 y1)) -> forall y1 : nat, forall y2 : a0, x0 (@CONSTR a0 y1 y2 y0).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term130 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := (fun y0 : nat => @_mk_rec a0 (x0 y0)) x1.
Definition term126 (a0 : Type') (x0 : type1338 a0) := (forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, (forall y3 : nat, x0 (y2 y3)) -> x0 (@CONSTR a0 y0 y1 y2)) -> forall y0 : type1614 a0, (forall y1 : nat, x0 (y0 y1)) -> forall y1 : nat, forall y2 : a0, x0 (@CONSTR a0 y1 y2 y0).
Definition term165 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3)).
Definition term19 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term50 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) := forall y0 : type1600 a0, (forall y1 : nat, (@ZRECSPACE a0 (y0 y1)) /\ (x0 (@_mk_rec a0 (y0 y1)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 x2 y0)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 y0))).
Definition term134 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := forall y0 : nat, x0 ((fun y1 : nat => @_mk_rec a0 (x1 y1)) y0).
Definition term158 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1600 a0) := forall y0 : a0, x0 (@CONSTR a0 x1 y0 (fun y1 : nat => @_mk_rec a0 (x2 y1))).
Definition term178 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : nat, forall y3 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y2 y3 (fun y4 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y4)))))) = y0) -> (y0 -> (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = y1) -> ((forall y2 : nat, forall y3 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y2 y3 (fun y4 : nat => @_dest_rec a0 (@_mk_rec a0 (x3 y4)))))) -> x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))) = (y0 -> y1)) x4.
Definition term89 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := fun y0 : nat => x0 (@_mk_rec a0 (x1 y0)).
Definition term164 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := imp (forall y0 : nat, forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y2 : nat => @_dest_rec a0 (@_mk_rec a0 (x1 y2)))))).
Definition term163 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) := imp (forall y0 : nat, forall y1 : a0, x0 (@CONSTR a0 y0 y1 (fun y2 : nat => @_mk_rec a0 (x1 y2)))).
Definition term80 (a0 : Type') (x0 : type1338 a0) := imp (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2)))).
Definition term190 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) (x2 : nat) := (fun y0 : nat => forall y1 : a0, x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 x1))) x2.
Definition term184 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : type1600 a0) := fun y0 : a0 => x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 x2)).
Definition term217 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((@ZRECSPACE a0 (@_dest_rec a0 x1)) -> (@ZRECSPACE a0 (@_dest_rec a0 x1)) /\ (x0 (@_mk_rec a0 (@_dest_rec a0 x1)))) -> x0 x1.
Definition term115 (a0 : Type') (x0 : type1338 a0) (x1 : nat) := forall y0 : a0, forall y1 : type1614 a0, (forall y2 : nat, x0 (y1 y2)) -> x0 (@CONSTR a0 x1 y0 y1).
Definition term54 (a0 : Type') (x0 : type1338 a0) (x1 : nat) := forall y0 : a0, forall y1 : type1600 a0, (forall y2 : nat, (@ZRECSPACE a0 (y1 y2)) /\ (x0 (@_mk_rec a0 (y1 y2)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 x1 y0 y1)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 y0 y1))).
Definition term53 (a0 : Type') (x0 : type1338 a0) (x1 : nat) := forall y0 : a0, forall y1 : type1600 a0, (forall y2 : nat, (fun y3 : type1597 a0 => (@ZRECSPACE a0 y3) /\ (x0 (@_mk_rec a0 y3))) (y1 y2)) -> (fun y2 : type1597 a0 => (@ZRECSPACE a0 y2) /\ (x0 (@_mk_rec a0 y2))) (@ZCONSTR a0 x1 y0 y1).
Definition term12 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, (forall y2 : nat, @ZRECSPACE a0 (y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 y0 y1).
Definition term5 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2)))).
Definition term131 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := @_mk_rec a0 (x0 x1).
Definition term31 (a0 : Type') (x0 : type1338 a0) := (fun y0 : type1597 a0 => (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) (@ZBOT a0).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (x0 y1) /\ (y0 y1)) = ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1))) x1.
Definition term44 (a0 : Type') (x0 : type1338 a0) (x1 : nat) (x2 : a0) (x3 : type1600 a0) := (@ZRECSPACE a0 (@ZCONSTR a0 x1 x2 x3)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 x1 x2 x3))).
Definition term146 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := @eq (recspace a0) ((fun y0 : nat => @_mk_rec a0 (x0 y0)) x1).
Definition term226 (a0 : Type') (x0 : recspace a0) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 x0).
Definition term94 (a0 : Type') (x0 : type1338 a0) (x1 : type1600 a0) (x2 : nat) := (fun y0 : nat => x0 (@_mk_rec a0 (x1 y0))) x2.
Definition term170 (a0 : Type') (x0 : type1600 a0) := forall y0 : nat, (@_dest_rec a0 (@_mk_rec a0 (x0 y0))) = (x0 y0).
Definition term83 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, (@ZRECSPACE a0 (y2 y3)) /\ (x0 (@_mk_rec a0 (y2 y3)))) -> (@ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) /\ (x0 (@_mk_rec a0 (@ZCONSTR a0 y0 y1 y2)))) -> forall y0 : type1597 a0, (@ZRECSPACE a0 y0) -> (@ZRECSPACE a0 y0) /\ (x0 (@_mk_rec a0 y0))) -> x0 x1.
Definition term223 (a0 : Type') (x0 : type1338 a0) (x1 : recspace a0) := ((@ZRECSPACE a0 (@_dest_rec a0 x1)) -> x0 x1) -> (@ZRECSPACE a0 (@_dest_rec a0 x1)) -> x0 x1.
