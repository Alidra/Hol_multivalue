Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1189923 : forall {_27796 _27797 _27798 : Type'}, forall f : _27798 -> _27797 -> _27796, forall l : list _27798, forall m : list _27797, forall k : nat, ((Peano.lt k (@List.length _27798 l)) /\ (Peano.lt k (@List.length _27797 m))) -> (@EL _27796 k (@MAP2 _27796 _27798 _27797 f l m)) = (f (@EL _27798 k l) (@EL _27797 k m)).
