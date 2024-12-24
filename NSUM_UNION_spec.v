Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6925097 : forall {_126551 : Type'}, forall f : _126551 -> nat, forall s : _126551 -> Prop, forall t : _126551 -> Prop, ((@FINITE _126551 s) /\ ((@FINITE _126551 t) /\ (@DISJOINT _126551 s t))) -> (@nsum _126551 (@UNION _126551 s t) f) = (Nat.add (@nsum _126551 s f) (@nsum _126551 t f)).
