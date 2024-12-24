Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3480368 : forall {A B : Type'}, forall f : A -> (B -> Prop) -> Prop, forall s : A -> Prop, (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_70 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_70 (@IN A x s) (@UNIONS B (f x))))) = (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_74 : B -> Prop => exists g : A -> B -> Prop, @SETSPEC (B -> Prop) GEN_PVAR_74 (forall x : A, (@IN A x s) -> @IN (B -> Prop) (g x) (f x)) (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_73 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_73 (@IN A x s) (g x))))))).
