Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1156055 : forall {_27145 _27147 : Type'}, forall l1 : list _27145, forall l2 : list _27147, ((@List.length _27145 l1) = (@List.length _27147 l2)) -> (@List.map (prod _27145 _27147) _27147 (@snd _27145 _27147) (@ZIP _27145 _27147 l1 l2)) = l2.
