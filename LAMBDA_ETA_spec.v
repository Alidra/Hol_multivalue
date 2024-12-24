Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7624658 : forall {_139958 _139962 : Type'}, forall g : cart _139958 _139962, (@lambda _139958 _139962 (fun i : nat => @dollar _139958 _139962 g i)) = g.
