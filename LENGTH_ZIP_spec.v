Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1156624 : forall {_27176 _27178 : Type'}, forall l1 : list _27176, forall l2 : list _27178, ((@List.length _27176 l1) = (@List.length _27178 l2)) -> (@List.length (prod _27176 _27178) (@ZIP _27176 _27178 l1 l2)) = (@List.length _27178 l2).
