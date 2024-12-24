Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8010703 : forall {_142062 _142063 _142064 : Type'}, forall s : (cart _142062 _142063) -> Prop, forall t : (cart _142062 _142064) -> Prop, forall s' : (cart _142062 _142063) -> Prop, forall t' : (cart _142062 _142064) -> Prop, (@SUBSET (cart _142062 (finite_sum _142063 _142064)) (@PCROSS _142062 _142063 _142064 s t) (@PCROSS _142062 _142063 _142064 s' t')) = ((s = (@EMPTY (cart _142062 _142063))) \/ ((t = (@EMPTY (cart _142062 _142064))) \/ ((@SUBSET (cart _142062 _142063) s s') /\ (@SUBSET (cart _142062 _142064) t t')))).
