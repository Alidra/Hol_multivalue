Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1160191 : forall {_27204 _27220 : Type'}, forall l : list (prod _27220 _27204), forall x : _27220, (@List.In (prod _27220 _27204) (@pair _27220 _27204 x (@ASSOC _27204 _27220 x l)) l) = (@List.In _27220 x (@List.map (prod _27220 _27204) _27220 (@fst _27220 _27204) l)).
