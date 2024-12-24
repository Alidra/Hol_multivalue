Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1142383 : forall {_26886 _26887 : Type'}, forall P : _26887 -> _26886 -> Prop, forall l : list _26886, (exists x : _26887, @EX _26886 (P x) l) = (@EX _26886 (fun s : _26886 => exists x : _26887, P x s) l).
