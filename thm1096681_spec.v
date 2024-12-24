Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1096681 : forall {A : Type'}, (fun LENGTH' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat => forall _17943 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), ((LENGTH' _17943 (@nil A)) = (NUMERAL 0)) /\ (forall h : A, forall t : list A, (LENGTH' _17943 (@cons A h t)) = (S (LENGTH' _17943 t)))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat) (fun LENGTH' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat => forall _17943 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), ((LENGTH' _17943 (@nil A)) = (NUMERAL 0)) /\ (forall h : A, forall t : list A, (LENGTH' _17943 (@cons A h t)) = (S (LENGTH' _17943 t))))).
