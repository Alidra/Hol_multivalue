Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1104212 : forall {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : _25471 -> _25470 -> Prop) (t1 : list _25471) (t2 : list _25470), ((@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True) /\ (((@ALL2 _25471 _25470 P (@cons _25471 h1' t1) (@nil _25470)) = False) /\ (((@ALL2 _25471 _25470 P (@nil _25471) (@cons _25470 h2' t2)) = False) /\ ((@ALL2 _25471 _25470 P (@cons _25471 h1' t1) (@cons _25470 h2' t2)) = ((P h1' h2') /\ (@ALL2 _25471 _25470 P t1 t2))))).
