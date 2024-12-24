Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3303082 : forall {_86426 : Type'} (r : _86426 -> Prop) (p : _86426 -> Prop) (q : _86426 -> Prop), ((@UNION _86426 p q) = (@UNION _86426 q p)) /\ (((@UNION _86426 (@UNION _86426 p q) r) = (@UNION _86426 p (@UNION _86426 q r))) /\ (((@UNION _86426 p (@UNION _86426 q r)) = (@UNION _86426 q (@UNION _86426 p r))) /\ (((@UNION _86426 p p) = p) /\ ((@UNION _86426 p (@UNION _86426 p q)) = (@UNION _86426 p q))))).
