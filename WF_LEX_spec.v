Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem364345 : forall {A B : Type'}, forall R : A -> A -> Prop, forall S' : B -> B -> Prop, ((@WF A R) /\ (@WF B S')) -> @WF (prod A B) (@GABS ((prod A B) -> (prod A B) -> Prop) (fun f : (prod A B) -> (prod A B) -> Prop => forall r1 : A, forall s1 : B, @GEQ ((prod A B) -> Prop) (f (@pair A B r1 s1)) (@GABS ((prod A B) -> Prop) (fun f' : (prod A B) -> Prop => forall r2 : A, forall s2 : B, @GEQ Prop (f' (@pair A B r2 s2)) ((R r1 r2) \/ ((r1 = r2) /\ (S' s1 s2))))))).
