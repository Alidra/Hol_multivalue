Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5718586 : forall {_119851 _119862 : Type'}, forall op : _119851 -> _119851 -> _119851, forall f : _119862 -> _119851, forall s : _119862 -> Prop, (@support _119862 _119851 op f (@support _119862 _119851 op f s)) = (@support _119862 _119851 op f s).
