Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4323933 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (@FINITE B t)) -> (@CARD (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_128 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_128 ((@IN A x s) /\ (@IN B y t)) (@pair A B x y)))) = (Nat.mul (@CARD A s) (@CARD B t)).
