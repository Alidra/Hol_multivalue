Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := imp ((@_mk_rec a0 (@_dest_rec a0 x0)) = (@_mk_rec a0 (@_dest_rec a0 x1))).
Definition term10 (a0 : Type') (x0 : recspace a0) := forall y0 : recspace a0, ((@_dest_rec a0 x0) = (@_dest_rec a0 y0)) = (x0 = y0).
Definition term11 (a0 : Type') := forall y0 : recspace a0, forall y1 : recspace a0, ((@_dest_rec a0 y0) = (@_dest_rec a0 y1)) = (y0 = y1).
Definition term1 (a0 : Type') (x0 : recspace a0) := @_mk_rec a0 (@_dest_rec a0 x0).
Definition term8 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := ((@_dest_rec a0 x0) = (@_dest_rec a0 x1)) -> x0 = x1.
Definition term7 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := (x0 = x1) -> (@_dest_rec a0 x0) = (@_dest_rec a0 x1).
Definition term2 (a0 : Type') (x0 : recspace a0) := @eq (recspace a0) (@_mk_rec a0 (@_dest_rec a0 x0)).
Definition term9 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := (((@_dest_rec a0 x0) = (@_dest_rec a0 x1)) -> x0 = x1) /\ ((x0 = x1) -> (@_dest_rec a0 x0) = (@_dest_rec a0 x1)).
Definition term5 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := ((@_mk_rec a0 (@_dest_rec a0 x0)) = (@_mk_rec a0 (@_dest_rec a0 x1))) -> x0 = x1.
Definition term4 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := imp (x0 = x1).
Definition term6 (a0 : Type') (x0 : recspace a0) (x1 : recspace a0) := (x0 = x1) -> x0 = x1.
Definition term0 (a0 : Type') (x0 : recspace a0) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 x0).
