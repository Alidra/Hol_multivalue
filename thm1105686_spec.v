Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1105686 : forall {_25569 : Type'}, (@EL _25569) = (@ε ((prod nat nat) -> nat -> (list _25569) -> _25569) (fun EL' : (prod nat nat) -> nat -> (list _25569) -> _25569 => forall _18015 : prod nat nat, (forall l : list _25569, (EL' _18015 (NUMERAL 0) l) = (@hd _25569 l)) /\ (forall n : nat, forall l : list _25569, (EL' _18015 (S n) l) = (EL' _18015 n (@tl _25569 l)))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))).
