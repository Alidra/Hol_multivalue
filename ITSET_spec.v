Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3815973 : forall {_99240 _99241 : Type'}, forall b : _99240, forall f : _99241 -> _99240 -> _99240, forall s : _99241 -> Prop, (@ITSET _99240 _99241 f s b) = (@ε ((_99241 -> Prop) -> _99240) (fun g : (_99241 -> Prop) -> _99240 => ((g (@EMPTY _99241)) = b) /\ (forall x : _99241, forall s' : _99241 -> Prop, (@FINITE _99241 s') -> (g (@INSERT _99241 x s')) = (@COND _99240 (@IN _99241 x s') (g s') (f x (g s'))))) s).
