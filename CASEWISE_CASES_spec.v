Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8074572 : forall {_143310 _143311 _143313 _143320 : Type'}, forall clauses : list (prod (_143313 -> _143310) (_143311 -> _143313 -> _143320)), forall c : _143311, forall x : _143310, (exists s : _143313 -> _143310, exists t : _143311 -> _143313 -> _143320, exists a : _143313, (@List.In (prod (_143313 -> _143310) (_143311 -> _143313 -> _143320)) (@pair (_143313 -> _143310) (_143311 -> _143313 -> _143320) s t) clauses) /\ (((s a) = x) /\ ((@CASEWISE _143320 _143313 _143310 _143311 clauses c x) = (t c a)))) \/ ((~ (exists s : _143313 -> _143310, exists t : _143311 -> _143313 -> _143320, exists a : _143313, (@List.In (prod (_143313 -> _143310) (_143311 -> _143313 -> _143320)) (@pair (_143313 -> _143310) (_143311 -> _143313 -> _143320) s t) clauses) /\ ((s a) = x))) /\ ((@CASEWISE _143320 _143313 _143310 _143311 clauses c x) = (@ε _143320 (fun y : _143320 => True)))).
