Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5718049 : forall {_119779 A : Type'}, forall f : A -> _119779, forall s : A -> Prop, forall op : _119779 -> _119779 -> _119779, (@iterate _119779 A op s f) = (@COND _119779 (@FINITE A (@support A _119779 op f s)) (@ITSET _119779 A (fun x : A => fun a : _119779 => op (f x) a) (@support A _119779 op f s) (@neutral _119779 op)) (@neutral _119779 op)).
