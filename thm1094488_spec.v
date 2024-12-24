Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1094488 : forall {A : Type'}, (fun HD' : (prod nat nat) -> (list A) -> A => forall _17927 : prod nat nat, forall t : list A, forall h : A, (HD' _17927 (@cons A h t)) = h) (@ε ((prod nat nat) -> (list A) -> A) (fun HD' : (prod nat nat) -> (list A) -> A => forall _17927 : prod nat nat, forall t : list A, forall h : A, (HD' _17927 (@cons A h t)) = h)).
