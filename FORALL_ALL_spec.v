Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1145518 : forall {_26916 _26917 : Type'}, forall P : _26917 -> _26916 -> Prop, forall l : list _26916, (forall x : _26917, @List.Forall _26916 (P x) l) = (@List.Forall _26916 (fun s : _26916 => forall x : _26917, P x s) l).
