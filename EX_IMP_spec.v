Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1135797 : forall {_26750 : Type'}, forall P : _26750 -> Prop, forall Q : _26750 -> Prop, forall l : list _26750, ((forall x : _26750, ((@List.In _26750 x l) /\ (P x)) -> Q x) /\ (@EX _26750 P l)) -> @EX _26750 Q l.
