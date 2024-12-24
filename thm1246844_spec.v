Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1246844 : forall (_22840 : nat) (_22841 : nat) (_22842 : nat -> Prop), (_22842 (dist (@pair nat nat _22841 _22840))) = (forall d : nat, ((_22841 = (Nat.add _22840 d)) -> _22842 d) /\ ((_22840 = (Nat.add _22841 d)) -> _22842 d)).
