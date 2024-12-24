Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3486241 : forall {A B : Type'}, forall f : A -> (B -> Prop) -> Prop, forall s : A -> Prop, (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_77 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_77 (@IN A x s) (@INTERS B (f x))))) = (@INTERS B (@GSPEC (B -> Prop) (fun GEN_PVAR_81 : B -> Prop => exists g : A -> B -> Prop, @SETSPEC (B -> Prop) GEN_PVAR_81 (forall x : A, (@IN A x s) -> @IN (B -> Prop) (g x) (f x)) (@UNIONS B (@GSPEC (B -> Prop) (fun GEN_PVAR_80 : B -> Prop => exists x : A, @SETSPEC (B -> Prop) GEN_PVAR_80 (@IN A x s) (g x))))))).
