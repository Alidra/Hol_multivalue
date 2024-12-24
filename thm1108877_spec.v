Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108877 : forall {_25719 _25727 : Type'}, (@ZIP _25719 _25727) = (@ε ((prod nat (prod nat nat)) -> (list _25719) -> (list _25727) -> list (prod _25719 _25727)) (fun ZIP' : (prod nat (prod nat nat)) -> (list _25719) -> (list _25727) -> list (prod _25719 _25727) => forall _18042 : prod nat (prod nat nat), (forall l2 : list _25727, (ZIP' _18042 (@nil _25719) l2) = (@nil (prod _25719 _25727))) /\ (forall h1' : _25719, forall t1 : list _25719, forall l2 : list _25727, (ZIP' _18042 (@cons _25719 h1' t1) l2) = (@cons (prod _25719 _25727) (@pair _25719 _25727 h1' (@hd _25727 l2)) (ZIP' _18042 t1 (@tl _25727 l2))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
