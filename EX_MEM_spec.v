Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1154803 : forall {_27094 : Type'}, forall P : _27094 -> Prop, forall l : list _27094, (exists x : _27094, (P x) /\ (@List.In _27094 x l)) = (@EX _27094 P l).
