Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7178267 : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> real, ((@FINITE A s) /\ (forall i : A, (@IN A i s) -> @FINITE B (t i))) -> (@sum A s (fun i : A => @sum B (t i) (x i))) = (@sum (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_327 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_327 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@GABS ((prod A B) -> real) (fun f : (prod A B) -> real => forall i : A, forall j : B, @GEQ real (f (@pair A B i j)) (x i j)))).
