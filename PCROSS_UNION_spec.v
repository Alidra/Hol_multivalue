Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8038229 : forall {_142544 _142545 _142546 _142580 _142581 _142582 : Type'}, (forall s : (cart _142544 _142545) -> Prop, forall t : (cart _142544 _142546) -> Prop, forall u : (cart _142544 _142546) -> Prop, (@PCROSS _142544 _142545 _142546 s (@UNION (cart _142544 _142546) t u)) = (@UNION (cart _142544 (finite_sum _142545 _142546)) (@PCROSS _142544 _142545 _142546 s t) (@PCROSS _142544 _142545 _142546 s u))) /\ (forall s : (cart _142580 _142581) -> Prop, forall t : (cart _142580 _142581) -> Prop, forall u : (cart _142580 _142582) -> Prop, (@PCROSS _142580 _142581 _142582 (@UNION (cart _142580 _142581) s t) u) = (@UNION (cart _142580 (finite_sum _142581 _142582)) (@PCROSS _142580 _142581 _142582 s u) (@PCROSS _142580 _142581 _142582 t u))).
