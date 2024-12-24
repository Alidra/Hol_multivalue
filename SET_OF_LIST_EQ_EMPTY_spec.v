Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4790578 : forall {_110450 : Type'}, forall l : list _110450, ((@set_of_list _110450 l) = (@EMPTY _110450)) = (l = (@nil _110450)).
