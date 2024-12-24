Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4383326 : forall {A B : Type'}, (@EXTENSIONAL A B (@EMPTY A)) = (@INSERT (A -> B) (fun x : A => @ARB B) (@EMPTY (A -> B))).
