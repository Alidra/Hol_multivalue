Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1128391 : forall {_26528 _26529 : Type'}, forall P : _26528 -> _26529 -> Prop, forall f : _26529 -> _26528, forall l : list _26529, (@ALL2 _26528 _26529 P (@List.map _26529 _26528 f l) l) = (@List.Forall _26529 (fun a : _26529 => P (f a) a) l).
