Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1095555 : forall {A : Type'}, (fun APPEND' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A => forall _17935 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall l : list A, (APPEND' _17935 (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND' _17935 (@cons A h t) l) = (@cons A h (APPEND' _17935 t l)))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A) (fun APPEND' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A => forall _17935 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall l : list A, (APPEND' _17935 (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (APPEND' _17935 (@cons A h t) l) = (@cons A h (APPEND' _17935 t l))))).
