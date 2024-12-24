Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5720601 : forall {_119939 _119945 : Type'}, forall op : _119945 -> _119945 -> _119945, forall f : _119939 -> _119945, forall s : _119939 -> Prop, (@FINITE _119939 s) -> @FINITE _119939 (@support _119939 _119945 op f s).
