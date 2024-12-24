Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4612764 : forall {_108216 A : Type'}, ((@GSPEC (_108216 -> Prop) (fun GEN_PVAR_161 : _108216 -> Prop => exists s : _108216 -> Prop, @SETSPEC (_108216 -> Prop) GEN_PVAR_161 (@SUBSET _108216 s (@EMPTY _108216)) s)) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop)))) /\ (forall a : A, forall t : A -> Prop, (@GSPEC (A -> Prop) (fun GEN_PVAR_162 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_162 (@SUBSET A s (@INSERT A a t)) s)) = (@UNION (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_163 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_163 (@SUBSET A s t) s)) (@IMAGE (A -> Prop) (A -> Prop) (fun s : A -> Prop => @INSERT A a s) (@GSPEC (A -> Prop) (fun GEN_PVAR_164 : A -> Prop => exists s : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_164 (@SUBSET A s t) s))))).
