Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1069367 : forall {A : Type'} (option' : (recspace A) -> Prop) (NONE' : recspace A) (SOME' : A -> recspace A) (h1 : option' = (fun a : recspace A => forall option'' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = NONE') \/ (exists a'' : A, a' = (SOME' a''))) -> option'' a') -> option'' a)), (option' NONE') /\ (forall a : A, option' (SOME' a)).
