Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7018072 : forall {A B : Type'}, forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> nat, ((@FINITE A s) /\ (forall i : A, (@IN A i s) -> @FINITE B (t i))) -> (@nsum A s (fun i : A => @nsum B (t i) (x i))) = (@nsum (prod A B) (@GSPEC (prod A B) (fun GEN_PVAR_300 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_300 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@GABS ((prod A B) -> nat) (fun f : (prod A B) -> nat => forall i : A, forall j : B, @GEQ nat (f (@pair A B i j)) (x i j)))).
