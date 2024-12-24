Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5970042 : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : A -> B -> Prop, forall x : A -> B -> C, ((@FINITE A s) /\ (forall i : A, (@IN A i s) -> @FINITE B (t i))) -> (@iterate C A op s (fun i : A => @iterate C B op (t i) (x i))) = (@iterate C (prod A B) op (@GSPEC (prod A B) (fun GEN_PVAR_241 : prod A B => exists i : A, exists j : B, @SETSPEC (prod A B) GEN_PVAR_241 ((@IN A i s) /\ (@IN B j (t i))) (@pair A B i j))) (@GABS ((prod A B) -> C) (fun f : (prod A B) -> C => forall i : A, forall j : B, @GEQ C (f (@pair A B i j)) (x i j)))).
