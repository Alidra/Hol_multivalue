Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1139259 : forall {_26848 _26849 : Type'}, forall P : _26849 -> Prop, forall f : _26848 -> _26849, forall l : list _26848, (@EX _26849 P (@List.map _26848 _26849 f l)) = (@EX _26848 (@o _26848 _26849 Prop P f) l).
