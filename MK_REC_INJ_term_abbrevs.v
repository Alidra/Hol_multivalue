Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 x1).
Definition term5 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := imp ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 x1)).
Definition term9 (a0 : Type') (x0 : type1597 a0) := and (x0 = (@_dest_rec a0 (@_mk_rec a0 x0))).
Definition term13 (a0 : Type') (x0 : type1597 a0) := forall y0 : type1597 a0, ((@_mk_rec a0 x0) = (@_mk_rec a0 y0)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 y0)) -> x0 = y0.
Definition term4 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := ((@_dest_rec a0 (@_mk_rec a0 x0)) = x0) /\ ((@_dest_rec a0 (@_mk_rec a0 x1)) = x1).
Definition term12 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := ((@_mk_rec a0 x0) = (@_mk_rec a0 x1)) -> ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 x1)) -> x0 = x1.
Definition term10 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (x0 = (@_dest_rec a0 (@_mk_rec a0 x0))) /\ (x1 = (@_dest_rec a0 (@_mk_rec a0 x1))).
Definition term0 (a0 : Type') (x0 : type1597 a0) := @_dest_rec a0 (@_mk_rec a0 x0).
Definition term6 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := imp (((@_dest_rec a0 (@_mk_rec a0 x0)) = x0) /\ ((@_dest_rec a0 (@_mk_rec a0 x1)) = x1)).
Definition term7 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := ((@ZRECSPACE a0 x0) /\ (@ZRECSPACE a0 x1)) -> x0 = x1.
Definition term14 (a0 : Type') := forall y0 : type1597 a0, forall y1 : type1597 a0, ((@_mk_rec a0 y0) = (@_mk_rec a0 y1)) -> ((@ZRECSPACE a0 y0) /\ (@ZRECSPACE a0 y1)) -> y0 = y1.
Definition term8 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := (((@_dest_rec a0 (@_mk_rec a0 x0)) = x0) /\ ((@_dest_rec a0 (@_mk_rec a0 x1)) = x1)) -> x0 = x1.
Definition term1 (a0 : Type') (x0 : type1597 a0) := and (@ZRECSPACE a0 x0).
Definition term11 (a0 : Type') (x0 : type1597 a0) := @eq (nat -> a0 -> Prop) (@_dest_rec a0 (@_mk_rec a0 x0)).
Definition term2 (a0 : Type') (x0 : type1597 a0) := and ((@_dest_rec a0 (@_mk_rec a0 x0)) = x0).