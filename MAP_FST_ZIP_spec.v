Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1155429 : forall {_27114 _27116 : Type'}, forall l1 : list _27114, forall l2 : list _27116, ((@List.length _27114 l1) = (@List.length _27116 l2)) -> (@List.map (prod _27114 _27116) _27114 (@fst _27114 _27116) (@ZIP _27114 _27116 l1 l2)) = l1.
