Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ True.
Definition term61 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_mk_rec a0 (@_dest_rec a0 (x0 x1)).
Definition term51 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_dest_rec a0 (@_mk_rec a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1)).
Definition term47 (x0 : Prop) := ~ (~ x0).
Definition term55 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => @_dest_rec a0 (x0 y1)) y0) x1.
Definition term27 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term71 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ((@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) = (@_mk_rec a0 (@ZBOT a0))) -> False.
Definition term10 (a0 : Type') := (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) -> forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2).
Definition term20 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (fun y0 : type1597 a0 => ((@_mk_rec a0 x0) = (@_mk_rec a0 y0)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 y0)) -> x0 = y0) x1.
Definition term69 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term44 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) -> False.
Definition term35 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZBOT a0))) -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZBOT a0)) -> False.
Definition term30 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ~ ((@CONSTR a0 x0 x1 x2) = (@BOTTOM a0)).
Definition term32 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ((@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) = (@_mk_rec a0 (@ZBOT a0))) -> ((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZBOT a0))) -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZBOT a0).
Definition term46 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ~ (~ (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))))).
Definition term22 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1614 a0, (@CONSTR a0 y0 y1 y2) = (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y3 : nat => @_dest_rec a0 (y2 y3))))) x0.
Definition term11 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, ~ ((@ZCONSTR a0 y0 y1 y2) = (@ZBOT a0))) x0.
Definition term1 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) x0.
Definition term38 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZBOT a0)).
Definition term48 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (forall y0 : nat, @ZRECSPACE a0 ((fun y1 : nat => @_dest_rec a0 (x2 y1)) y0)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term40 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term6 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (forall y0 : nat, @ZRECSPACE a0 (x2 y0)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term73 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1614 a0, ~ ((@CONSTR a0 x0 y0 y1) = (@BOTTOM a0)).
Definition term12 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, ~ ((@ZCONSTR a0 x0 y0 y1) = (@ZBOT a0)).
Definition term5 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => (forall y1 : nat, @ZRECSPACE a0 (y0 y1)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 y0)) x2.
Definition term62 (a0 : Type') (x0 : recspace a0) := @_mk_rec a0 (@_dest_rec a0 x0).
Definition term29 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @eq (recspace a0) (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))).
Definition term19 (a0 : Type') (x0 : type1597 a0) := forall y0 : type1597 a0, ((@_mk_rec a0 x0) = (@_mk_rec a0 y0)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 y0)) -> x0 = y0.
Definition term21 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := ((@_mk_rec a0 x0) = (@_mk_rec a0 x1)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 x1)) -> x0 = x1.
Definition term28 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @eq (recspace a0) (@CONSTR a0 x0 x1 x2).
Definition term34 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZBOT a0))) -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZBOT a0).
Definition term33 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)).
Definition term15 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (fun y0 : type1600 a0 => ~ ((@ZCONSTR a0 x0 x1 y0) = (@ZBOT a0))) x2.
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term36 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ~ (((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZBOT a0))) -> (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))) = (@ZBOT a0)).
Definition term74 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, ~ ((@CONSTR a0 y0 y1 y2) = (@BOTTOM a0)).
Definition term0 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2).
Definition term60 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_mk_rec a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1).
Definition term54 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term68 := forall y0 : nat, True.
Definition term49 (a0 : Type') (x0 : type1597 a0) := @_dest_rec a0 (@_mk_rec a0 x0).
Definition term72 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1614 a0, ~ ((@CONSTR a0 x0 x1 y0) = (@BOTTOM a0)).
Definition term16 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := ~ ((@ZCONSTR a0 x0 x1 x2) = (@ZBOT a0)).
Definition term66 := fun y0 : nat => True.
Definition term63 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 (@_mk_rec a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1))).
Definition term24 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2))))) x1.
Definition term3 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, (forall y2 : nat, @ZRECSPACE a0 (y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 y0 y1)) x1.
Definition term59 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1).
Definition term25 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1614 a0, (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1)))).
Definition term64 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 (x0 x1)).
Definition term50 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @ZRECSPACE a0 ((fun y0 : nat => @_dest_rec a0 (x0 y0)) x1).
Definition term42 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := imp (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))).
Definition term45 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ~ (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))).
Definition term8 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term7 (a0 : Type') (x0 : type1600 a0) := forall y0 : nat, @ZRECSPACE a0 (x0 y0).
Definition term4 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, (forall y1 : nat, @ZRECSPACE a0 (y0 y1)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 y0).
Definition term58 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @eq (nat -> a0 -> Prop) ((fun y0 : nat => (fun y1 : nat => @_dest_rec a0 (x0 y1)) y0) x1).
Definition term13 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1600 a0, ~ ((@ZCONSTR a0 x0 y0 y1) = (@ZBOT a0))) x1.
Definition term37 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := and (@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))).
Definition term26 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (fun y0 : type1614 a0 => (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1))))) x2.
Definition term70 (x0 : Prop) := forall y0 : nat, x0.
Definition term41 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := imp ((@ZRECSPACE a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) /\ (@ZRECSPACE a0 (@ZBOT a0))).
Definition term18 (a0 : Type') (x0 : type1597 a0) := (fun y0 : type1597 a0 => forall y1 : type1597 a0, ((@_mk_rec a0 y0) = (@_mk_rec a0 y1)) -> ((@ZRECSPACE a0 y0) /\ (@ZRECSPACE a0 y1)) -> y0 = y1) x0.
Definition term43 (a0 : Type') (x0 : type1614 a0) := fun y0 : nat => @_dest_rec a0 (x0 y0).
Definition term9 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 x1 x2).
Definition term17 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1600 a0) := (~ ((@ZCONSTR a0 x0 x1 x2) = (@ZBOT a0))) -> ((@ZCONSTR a0 x0 x1 x2) = (@ZBOT a0)) = False.
Definition term14 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1600 a0, ~ ((@ZCONSTR a0 x0 x1 y0) = (@ZBOT a0)).
Definition term65 (a0 : Type') (x0 : type1614 a0) := fun y0 : nat => @ZRECSPACE a0 ((fun y1 : nat => @_dest_rec a0 (x0 y1)) y0).
Definition term52 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := (fun y0 : nat => @_dest_rec a0 (x0 y0)) x1.
Definition term23 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2)))).
Definition term2 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1600 a0, (forall y2 : nat, @ZRECSPACE a0 (y1 y2)) -> @ZRECSPACE a0 (@ZCONSTR a0 x0 y0 y1).
Definition term56 (a0 : Type') (x0 : type1614 a0) (x1 : nat) := @_dest_rec a0 (x0 x1).
Definition term31 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := ~ ((@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0)))) = (@_mk_rec a0 (@ZBOT a0))).
Definition term67 (a0 : Type') (x0 : type1614 a0) := forall y0 : nat, @ZRECSPACE a0 ((fun y1 : nat => @_dest_rec a0 (x0 y1)) y0).
Definition term57 (a0 : Type') (x0 : type1614 a0) := fun y0 : nat => (fun y1 : nat => @_dest_rec a0 (x0 y1)) y0.
