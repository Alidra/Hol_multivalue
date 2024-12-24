Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1097952 : forall {A : Type'}, (fun LAST' : (prod nat (prod nat (prod nat nat))) -> (list A) -> A => forall _17954 : prod nat (prod nat (prod nat nat)), forall h : A, forall t : list A, (LAST' _17954 (@cons A h t)) = (@COND A (t = (@nil A)) h (LAST' _17954 t))) (@ε ((prod nat (prod nat (prod nat nat))) -> (list A) -> A) (fun LAST' : (prod nat (prod nat (prod nat nat))) -> (list A) -> A => forall _17954 : prod nat (prod nat (prod nat nat)), forall h : A, forall t : list A, (LAST' _17954 (@cons A h t)) = (@COND A (t = (@nil A)) h (LAST' _17954 t)))).
