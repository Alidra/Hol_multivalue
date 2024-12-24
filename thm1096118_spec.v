Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1096118 : forall {A : Type'}, (fun REVERSE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A => forall _17939 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), ((REVERSE' _17939 (@nil A)) = (@nil A)) /\ (forall l : list A, forall x : A, (REVERSE' _17939 (@cons A x l)) = (@List.app A (REVERSE' _17939 l) (@cons A x (@nil A))))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A) (fun REVERSE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list A) -> list A => forall _17939 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), ((REVERSE' _17939 (@nil A)) = (@nil A)) /\ (forall l : list A, forall x : A, (REVERSE' _17939 (@cons A x l)) = (@List.app A (REVERSE' _17939 l) (@cons A x (@nil A)))))).
