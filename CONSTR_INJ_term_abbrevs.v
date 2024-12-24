Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term140 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1614 a0, forall y2 : nat, forall y3 : a0, forall y4 : type1614 a0, ((@CONSTR a0 x0 y0 y1) = (@CONSTR a0 y2 y3 y4)) = ((x0 = y2) /\ ((y0 = y3) /\ (y1 = y4))).
Definition term58 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := ((@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) = (@_mk_rec a0 (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))))) -> ((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))))) -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))).
Definition term1 (a0 : Type') (x0 : recspace a0) := forall y0 : recspace a0, ((@_dest_rec a0 x0) = (@_dest_rec a0 y0)) = (x0 = y0).
Definition term103 (x0 : nat) (x1 : nat) := and ((S x0) = (S x1)).
Definition term100 (a0 : Type') (x0 : nat) := @INJN a0 (S x0).
Definition term25 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) (x3 : type1597 a0) := (fun y0 : type1597 a0 => ((@INJP a0 x0 x2) = (@INJP a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term29 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, (@ZCONSTR a0 x0 y0 y1) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1)))) x1.
Definition term76 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_mk_rec a0 (@_dest_rec a0 (x0 x1)).
Definition term94 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x2 y0)))).
Definition term66 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_dest_rec a0 (@_mk_rec a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1)).
Definition term127 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := imp (((S x0) = (S x1)) /\ ((x2 = x3) /\ (forall y0 : nat, (@_dest_rec a0 (x4 y0)) = (@_dest_rec a0 (x5 y0))))).
Definition term116 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := imp (((S x0) = (S x1)) /\ ((x2 = x3) /\ (forall y0 : nat, ((fun y1 : nat => @_dest_rec a0 (x4 y1)) y0) = ((fun y1 : nat => @_dest_rec a0 (x5 y1)) y0)))).
Definition term130 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := imp ((x0 = x1) /\ ((x2 = x3) /\ (forall y0 : nat, (x4 y0) = (x5 y0)))).
Definition term70 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => @_dest_rec a0 (x0 y1)) y0) x1.
Definition term122 (a0 : Type') (x0 : type1614 a0) (x1 : type1614 a0) := fun y0 : nat => ((fun y1 : nat => @_dest_rec a0 (x0 y1)) y0) = ((fun y1 : nat => @_dest_rec a0 (x1 y1)) y0).
Definition term53 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term32 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 x2)).
Definition term43 (a0 : Type') := (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) -> forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2).
Definition term46 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (fun y0 : type1597 a0 => ((@_mk_rec a0 x0) = (@_mk_rec a0 y0)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 y0)) -> x0 = y0) x1.
Definition term84 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term19 (a0 : Type') (x0 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, forall y2 : type1597 a0, forall y3 : type1597 a0, ((@INJP a0 y0 y2) = (@INJP a0 y1 y3)) = ((y0 = y1) /\ (y2 = y3))) x0.
Definition term97 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := imp ((@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x2 y0))))) = (@INJP a0 (@INJN a0 (S x3)) (@INJP a0 (@INJA a0 x4) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x5 y0)))))).
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1614 a0) (x3 : type1614 a0) := (x0 = x1) /\ (x2 = x3).
Definition term17 (a0 : Type') (x0 : nat) := forall y0 : nat, ((@INJN a0 x0) = (@INJN a0 y0)) = (x0 = y0).
Definition term4 (x0 : nat) := forall y0 : nat, ((S x0) = (S y0)) = (x0 = y0).
Definition term124 (a0 : Type') (x0 : type1614 a0) (x1 : type1614 a0) := forall y0 : nat, (@_dest_rec a0 (x0 y0)) = (@_dest_rec a0 (x1 y0)).
Definition term31 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => (@ZCONSTR a0 x0 x1 y0) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0)))) x2.
Definition term119 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term139 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1614 a0, forall y1 : nat, forall y2 : a0, forall y3 : type1614 a0, ((@CONSTR a0 x0 x1 y0) = (@CONSTR a0 y1 y2 y3)) = ((x0 = y1) /\ ((x1 = y2) /\ (y0 = y3))).
Definition term20 (a0 : Type') (x0 : type1597 a0) := forall y0 : type1597 a0, forall y1 : type1597 a0, forall y2 : type1597 a0, ((@INJP a0 x0 y1) = (@INJP a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2)).
Definition term136 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) := forall y0 : type1614 a0, ((@CONSTR a0 x0 x2 x4) = (@CONSTR a0 x1 x3 y0)) = ((x0 = x1) /\ ((x2 = x3) /\ (x4 = y0))).
Definition term61 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0)))).
Definition term48 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1614 a0, (@CONSTR a0 y0 y1 y2) = (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y3 : nat => @_dest_rec a0 (y2 y3))))) x0.
Definition term34 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) x0.
Definition term27 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (@ZCONSTR a0 y0 y1 y2) = (@INJP a0 (@INJN a0 (S y0)) (@INJP a0 (@INJA a0 y1) (@INJF a0 y2)))) x0.
Definition term62 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (forall y0 : nat, @ZRECSPACE a0 ((fun y1 : nat => @_dest_rec a0 (x2 y1)) y0)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term10 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, ((@INJA a0 y0) = (@INJA a0 y1)) = (y0 = y1)) x0.
Definition term86 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term39 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (forall y0 : nat, @ZRECSPACE a0 (x2 y0)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term99 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : type1614 a0) (x4 : a0) (x5 : type1614 a0) := ((@INJN a0 (S x0)) = (@INJN a0 (S x1))) /\ ((@INJP a0 (@INJA a0 x2) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x3 y0)))) = (@INJP a0 (@INJA a0 x4) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x5 y0))))).
Definition term38 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => (forall y1 : nat, @ZRECSPACE a0 (y0 y1)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 y0)) x2.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ((@INJA a0 x0) = (@INJA a0 y0)) = (x0 = y0)) x1.
Definition term77 (a0 : Type') (x0 : recspace a0) := @_mk_rec a0 (@_dest_rec a0 x0).
Definition term57 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @eq (recspace a0) (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))).
Definition term45 (a0 : Type') (x0 : type1597 a0) := forall y0 : type1597 a0, ((@_mk_rec a0 x0) = (@_mk_rec a0 y0)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 y0)) -> x0 = y0.
Definition term128 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := (((S x0) = (S x1)) /\ ((x2 = x3) /\ (forall y0 : nat, (@_dest_rec a0 (x4 y0)) = (@_dest_rec a0 (x5 y0))))) -> (x0 = x1) /\ ((x2 = x3) /\ (forall y0 : nat, (x4 y0) = (x5 y0))).
Definition term121 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := (((S x0) = (S x1)) /\ ((x2 = x3) /\ (forall y0 : nat, ((fun y1 : nat => @_dest_rec a0 (x4 y1)) y0) = ((fun y1 : nat => @_dest_rec a0 (x5 y1)) y0)))) -> (x0 = x1) /\ ((x2 = x3) /\ (forall y0 : nat, (x4 y0) = (x5 y0))).
Definition term54 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := (x0 = x1) /\ ((x2 = x3) /\ (x4 = x5)).
Definition term129 (a0 : Type') (x0 : type1614 a0) (x1 : type1614 a0) := fun y0 : nat => (x0 y0) = (x1 y0).
Definition term47 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := ((@_mk_rec a0 x0) = (@_mk_rec a0 x1)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 x1)) -> x0 = x1.
Definition term24 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) := forall y0 : type1597 a0, ((@INJP a0 x0 x2) = (@INJP a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term56 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @eq (recspace a0) (@CONSTR a0 x0 x1 x2).
Definition term113 (a0 : Type') (x0 : type1614 a0) (x1 : type1614 a0) := forall y0 : nat, ((fun y1 : nat => @_dest_rec a0 (x0 y1)) y0) = ((fun y1 : nat => @_dest_rec a0 (x1 y1)) y0).
Definition term59 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)).
Definition term117 (a0 : Type') (x0 : type1614 a0) (x1 : type1614 a0) := forall y0 : nat, (x0 y0) = (x1 y0).
Definition term112 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := forall y0 : nat, (x0 y0) = (x1 y0).
Definition term120 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := (x0 = x1) /\ ((x2 = x3) /\ (forall y0 : nat, (x4 y0) = (x5 y0))).
Definition term132 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((@_mk_rec a0 (@ZCONSTR a0 x0 x2 (fun y0 : nat => @_dest_rec a0 (x4 y0)))) = (@_mk_rec a0 (@ZCONSTR a0 x1 x3 (fun y0 : nat => @_dest_rec a0 (x5 y0))))) -> (x0 = x1) /\ ((x2 = x3) /\ (x4 = x5)).
Definition term15 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := (fun y0 : type1600 a0 => ((@INJF a0 x0) = (@INJF a0 y0)) = (x0 = y0)) x1.
Definition term131 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((x0 = x1) /\ ((x2 = x3) /\ (forall y0 : nat, (x4 y0) = (x5 y0)))) -> (x0 = x1) /\ ((x2 = x3) /\ (forall y0 : nat, (x4 y0) = (x5 y0))).
Definition term26 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) (x3 : type1597 a0) := (x0 = x1) /\ (x2 = x3).
Definition term95 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @eq (nat -> a0 -> Prop) (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term141 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, forall y3 : nat, forall y4 : a0, forall y5 : type1614 a0, ((@CONSTR a0 y0 y1 y2) = (@CONSTR a0 y3 y4 y5)) = ((y0 = y3) /\ ((y1 = y4) /\ (y2 = y5))).
Definition term138 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, ((@CONSTR a0 x0 x1 x2) = (@CONSTR a0 y0 y1 y2)) = ((x0 = y0) /\ ((x1 = y1) /\ (x2 = y2))).
Definition term33 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2).
Definition term93 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((@ZCONSTR a0 x0 x2 (fun y0 : nat => @_dest_rec a0 (x4 y0))) = (@ZCONSTR a0 x1 x3 (fun y0 : nat => @_dest_rec a0 (x5 y0)))) -> (x0 = x1) /\ ((x2 = x3) /\ (x4 = x5)).
Definition term23 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) (x2 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, ((@INJP a0 x0 y0) = (@INJP a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1))) x2.
Definition term98 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x2) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x4 y0))))) = (@INJP a0 (@INJN a0 (S x1)) (@INJP a0 (@INJA a0 x3) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x5 y0)))))) -> (x0 = x1) /\ ((x2 = x3) /\ (x4 = x5)).
Definition term75 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_mk_rec a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1).
Definition term69 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term83 := forall y0 : nat, True.
Definition term0 (a0 : Type') (x0 : recspace a0) := (fun y0 : recspace a0 => forall y1 : recspace a0, ((@_dest_rec a0 y0) = (@_dest_rec a0 y1)) = (y0 = y1)) x0.
Definition term64 (a0 : Type') (x0 : type1597 a0) := @_dest_rec a0 (@_mk_rec a0 x0).
Definition term81 := fun y0 : nat => True.
Definition term78 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 (@_mk_rec a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1))).
Definition term88 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := imp ((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))))).
Definition term14 (a0 : Type') (x0 : type1600 a0) := forall y0 : type1600 a0, ((@INJF a0 x0) = (@INJF a0 y0)) = (x0 = y0).
Definition term30 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, (@ZCONSTR a0 x0 x1 y0) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 y0))).
Definition term107 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term50 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2))))) x1.
Definition term36 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, (forall y2 : nat, @ZRECSPACE a0 (y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 y0 y1)) x1.
Definition term74 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1614 a0) (x3 : type1614 a0) := ((@INJA a0 x0) = (@INJA a0 x1)) /\ ((@INJF a0 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x3 y0)))).
Definition term109 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((S x0) = (S x1)) /\ ((x2 = x3) /\ ((fun y0 : nat => @_dest_rec a0 (x4 y0)) = (fun y0 : nat => @_dest_rec a0 (x5 y0)))).
Definition term51 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1614 a0, (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1)))).
Definition term79 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 (x0 x1)).
Definition term125 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1614 a0) (x3 : type1614 a0) := (x0 = x1) /\ (forall y0 : nat, (@_dest_rec a0 (x2 y0)) = (@_dest_rec a0 (x3 y0))).
Definition term118 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1614 a0) (x3 : type1614 a0) := (x0 = x1) /\ (forall y0 : nat, (x2 y0) = (x3 y0)).
Definition term114 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1614 a0) (x3 : type1614 a0) := (x0 = x1) /\ (forall y0 : nat, ((fun y1 : nat => @_dest_rec a0 (x2 y1)) y0) = ((fun y1 : nat => @_dest_rec a0 (x3 y1)) y0)).
Definition term101 (a0 : Type') (x0 : a0) (x1 : type1614 a0) := @INJP a0 (@INJA a0 x0) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x1 y0))).
Definition term21 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, forall y2 : type1597 a0, ((@INJP a0 x0 y1) = (@INJP a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2))) x1.
Definition term22 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := forall y0 : type1597 a0, forall y1 : type1597 a0, ((@INJP a0 x0 y0) = (@INJP a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1)).
Definition term105 (a0 : Type') (x0 : type1614 a0) := @INJF a0 (fun y0 : nat => @_dest_rec a0 (x0 y0)).
Definition term65 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @ZRECSPACE a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1).
Definition term16 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((@INJN a0 y0) = (@INJN a0 y1)) = (y0 = y1)) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((S y0) = (S y1)) = (y0 = y1)) x0.
Definition term126 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((S x0) = (S x1)) /\ ((x2 = x3) /\ (forall y0 : nat, (@_dest_rec a0 (x4 y0)) = (@_dest_rec a0 (x5 y0)))).
Definition term115 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((S x0) = (S x1)) /\ ((x2 = x3) /\ (forall y0 : nat, ((fun y1 : nat => @_dest_rec a0 (x4 y1)) y0) = ((fun y1 : nat => @_dest_rec a0 (x5 y1)) y0))).
Definition term123 (a0 : Type') (x0 : type1614 a0) (x1 : type1614 a0) := fun y0 : nat => (@_dest_rec a0 (x0 y0)) = (@_dest_rec a0 (x1 y0)).
Definition term89 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := True -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))).
Definition term41 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term40 (a0 : Type') (x0 : type1600 a0) := forall y0 : nat, @ZRECSPACE a0 (x0 y0).
Definition term37 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, (forall y1 : nat, @ZRECSPACE a0 (y0 y1)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 y0).
Definition term11 (a0 : Type') (x0 : a0) := forall y0 : a0, ((@INJA a0 x0) = (@INJA a0 y0)) = (x0 = y0).
Definition term110 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := imp (((S x0) = (S x1)) /\ ((x2 = x3) /\ ((fun y0 : nat => @_dest_rec a0 (x4 y0)) = (fun y0 : nat => @_dest_rec a0 (x5 y0))))).
Definition term73 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) ((fun y0 : nat => (fun y1 : nat => @_dest_rec a0 (x0 y1)) y0) x1).
Definition term87 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := and (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))).
Definition term52 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (fun y0 : type1614 a0 => (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1))))) x2.
Definition term90 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := imp (((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))))) -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0)))).
Definition term2 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := (fun y0 : recspace a0 => ((@_dest_rec a0 x0) = (@_dest_rec a0 y0)) = (x0 = y0)) x1.
Definition term85 (x0 : Prop) := forall y0 : nat, x0.
Definition term133 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := ((x0 = x3) /\ ((x1 = x4) /\ (x2 = x5))) -> (@CONSTR a0 x0 x1 x2) = (@CONSTR a0 x3 x4 x5).
Definition term134 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := ((@CONSTR a0 x0 x2 x4) = (@CONSTR a0 x1 x3 x5)) -> (x0 = x1) /\ ((x2 = x3) /\ (x4 = x5)).
Definition term44 (a0 : Type') (x0 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, ((@_mk_rec a0 y0) = (@_mk_rec a0 y1)) -> ((@ZRECSPACE a0 y0) /\ (@ZRECSPACE a0 y1)) -> y0 = y1) x0.
Definition term13 (a0 : Type') (x0 : type1600 a0) := (fun y0 : type1600 a0 => forall y1 : type1600 a0, ((@INJF a0 y0) = (@INJF a0 y1)) = (y0 = y1)) x0.
Definition term102 (a0 : Type') (x0 : nat) (x1 : nat) := and ((@INJN a0 (S x0)) = (@INJN a0 (S x1))).
Definition term63 (a0 : Type') (x0 : type1614 a0) := fun y0 : nat => @_dest_rec a0 (x0 y0).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term42 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term92 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := (((@ZRECSPACE a0 (@ZCONSTR a0 x0 x2 (fun y0 : nat => @_dest_rec a0 (x4 y0)))) /\ (@ZRECSPACE a0 (@ZCONSTR a0 x1 x3 (fun y0 : nat => @_dest_rec a0 (x5 y0))))) -> (@ZCONSTR a0 x0 x2 (fun y0 : nat => @_dest_rec a0 (x4 y0))) = (@ZCONSTR a0 x1 x3 (fun y0 : nat => @_dest_rec a0 (x5 y0)))) -> (x0 = x1) /\ ((x2 = x3) /\ (x4 = x5)).
Definition term80 (a0 : Type') (x0 : type1614 a0) := fun y0 : nat => @ZRECSPACE a0 ((fun y1 : nat => @_dest_rec a0 (x0 y1)) y0).
Definition term60 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := ((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))))) -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term96 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @eq (nat -> a0 -> Prop) (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 x1) (@INJF a0 (fun y0 : nat => @_dest_rec a0 (x2 y0))))).
Definition term67 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := (fun y0 : nat => @_dest_rec a0 (x0 y0)) x1.
Definition term135 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := (((@CONSTR a0 x0 x1 x2) = (@CONSTR a0 x3 x4 x5)) -> (x0 = x3) /\ ((x1 = x4) /\ (x2 = x5))) /\ (((x0 = x3) /\ ((x1 = x4) /\ (x2 = x5))) -> (@CONSTR a0 x0 x1 x2) = (@CONSTR a0 x3 x4 x5)).
Definition term18 (a0 : Type') (x0 : nat) (x1 : nat) := (fun y0 : nat => ((@INJN a0 x0) = (@INJN a0 y0)) = (x0 = y0)) x1.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((S x0) = (S y0)) = (x0 = y0)) x1.
Definition term137 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : type1614 a0) := forall y0 : a0, forall y1 : type1614 a0, ((@CONSTR a0 x0 x2 x3) = (@CONSTR a0 x1 y0 y1)) = ((x0 = x1) /\ ((x2 = y0) /\ (x3 = y1))).
Definition term49 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2)))).
Definition term35 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, (forall y2 : nat, @ZRECSPACE a0 (y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 y0 y1).
Definition term28 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, (@ZCONSTR a0 x0 y0 y1) = (@INJP a0 (@INJN a0 (S x0)) (@INJP a0 (@INJA a0 y0) (@INJF a0 y1))).
Definition term111 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) (x3 : a0) (x4 : type1614 a0) (x5 : type1614 a0) := (((S x0) = (S x1)) /\ ((x2 = x3) /\ ((fun y0 : nat => @_dest_rec a0 (x4 y0)) = (fun y0 : nat => @_dest_rec a0 (x5 y0))))) -> (x0 = x1) /\ ((x2 = x3) /\ (x4 = x5)).
Definition term71 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_dest_rec a0 (x0 x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term106 (a0 : Type') (x0 : a0) (x1 : a0) := and ((@INJA a0 x0) = (@INJA a0 x1)).
Definition term91 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) (x3 : nat) (x4 : a0) (x5 : type1614 a0) := imp ((@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZCONSTR a0 x3 x4 (fun y0 : nat => @_dest_rec a0 (x5 y0)))).
Definition term82 (a0 : Type') (x0 : type1614 a0) := forall y0 : nat, @ZRECSPACE a0 ((fun y1 : nat => @_dest_rec a0 (x0 y1)) y0).
Definition term108 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1614 a0) (x3 : type1614 a0) := (x0 = x1) /\ ((fun y0 : nat => @_dest_rec a0 (x2 y0)) = (fun y0 : nat => @_dest_rec a0 (x3 y0))).
Definition term72 (a0 : Type') (x0 : type1614 a0) := fun y0 : nat => (fun y1 : nat => @_dest_rec a0 (x0 y1)) y0.
