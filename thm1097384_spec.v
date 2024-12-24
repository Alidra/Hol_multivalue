Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1097384 : forall {A B : Type'}, (fun MAP' : (prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B => forall _17950 : prod nat (prod nat nat), (forall f : A -> B, (MAP' _17950 f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP' _17950 f (@cons A h t)) = (@cons B (f h) (MAP' _17950 f t)))) (@ε ((prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B) (fun MAP' : (prod nat (prod nat nat)) -> (A -> B) -> (list A) -> list B => forall _17950 : prod nat (prod nat nat), (forall f : A -> B, (MAP' _17950 f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : list A, (MAP' _17950 f (@cons A h t)) = (@cons B (f h) (MAP' _17950 f t))))).
