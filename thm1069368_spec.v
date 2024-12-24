Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1069368 : forall {A : Type'} (option' : (recspace A) -> Prop) (NONE' : recspace A) (SOME' : A -> recspace A) (h1 : option' = (fun a : recspace A => forall option'' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = NONE') \/ (exists a'' : A, a' = (SOME' a''))) -> option'' a') -> option'' a)), forall option'' : (recspace A) -> Prop, ((option'' NONE') /\ (forall a : A, option'' (SOME' a))) -> forall a : recspace A, (option' a) -> option'' a.
