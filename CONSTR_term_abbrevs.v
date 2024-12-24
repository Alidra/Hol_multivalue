Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y0 : nat => @_dest_rec a0 (x2 y0))).
Definition term0 (a0 : Type') := fun y0 : nat => fun y1 : a0 => fun y2 : type1614 a0 => @_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y3 : nat => @_dest_rec a0 (y2 y3))).
Definition term1 (a0 : Type') (x0 : nat) := (fun y0 : nat => fun y1 : a0 => fun y2 : type1614 a0 => @_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y3 : nat => @_dest_rec a0 (y2 y3)))) x0.
Definition term10 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : type1614 a0, (@CONSTR a0 y0 y1 y2) = (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y3 : nat => @_dest_rec a0 (y2 y3))))) x0.
Definition term3 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => fun y1 : type1614 a0 => @_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2)))) x1.
Definition term4 (a0 : Type') (x0 : nat) (x1 : a0) := fun y0 : type1614 a0 => @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1))).
Definition term9 (a0 : Type') := forall y0 : nat, forall y1 : a0, forall y2 : type1614 a0, (@CONSTR a0 y0 y1 y2) = (@_mk_rec a0 (@ZCONSTR a0 y0 y1 (fun y3 : nat => @_dest_rec a0 (y2 y3)))).
Definition term2 (a0 : Type') (x0 : nat) := fun y0 : a0 => fun y1 : type1614 a0 => @_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2))).
Definition term5 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (fun y0 : type1614 a0 => @_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1)))) x2.
Definition term11 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2))))) x1.
Definition term7 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : type1614 a0, (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1)))).
Definition term12 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : type1614 a0) := (fun y0 : type1614 a0 => (@CONSTR a0 x0 x1 y0) = (@_mk_rec a0 (@ZCONSTR a0 x0 x1 (fun y1 : nat => @_dest_rec a0 (y0 y1))))) x2.
Definition term8 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : type1614 a0, (@CONSTR a0 x0 y0 y1) = (@_mk_rec a0 (@ZCONSTR a0 x0 y0 (fun y2 : nat => @_dest_rec a0 (y1 y2)))).
