Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') := (fun y0 : type1667 => ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y1 : type1238 a0 => forall y2 : type1667, ((y1 y2 (@nil a0)) = (@EMPTY a0)) /\ (forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@INSERT a0 y3 (y1 y2 y4)))) y0 (@nil a0)) = (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : list a0, (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y3 : type1238 a0 => forall y4 : type1667, ((y3 y4 (@nil a0)) = (@EMPTY a0)) /\ (forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@INSERT a0 y5 (y3 y4 y6)))) y0 (@cons a0 y1 y2)) = (@INSERT a0 y1 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y3 : type1238 a0 => forall y4 : type1667, ((y3 y4 (@nil a0)) = (@EMPTY a0)) /\ (forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@INSERT a0 y5 (y3 y4 y6)))) y0 y2)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))).
Definition term4 (a0 : Type') := ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@nil a0)) = (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : list a0, (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y2 : type1238 a0 => forall y3 : type1667, ((y2 y3 (@nil a0)) = (@EMPTY a0)) /\ (forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@INSERT a0 y4 (y2 y3 y5)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@cons a0 y0 y1)) = (@INSERT a0 y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y2 : type1238 a0 => forall y3 : type1667, ((y2 y3 (@nil a0)) = (@EMPTY a0)) /\ (forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@INSERT a0 y4 (y2 y3 y5)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) y1))).
Definition term15 (a0 : Type') (x0 : list a0) := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) x0.
Definition term23 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (@set_of_list a0 (@cons a0 y0 y1)) = (@INSERT a0 y0 (@set_of_list a0 y1)).
Definition term22 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y2 : type1238 a0 => forall y3 : type1667, ((y2 y3 (@nil a0)) = (@EMPTY a0)) /\ (forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@INSERT a0 y4 (y2 y3 y5)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@cons a0 y0 y1)) = (@INSERT a0 y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y2 : type1238 a0 => forall y3 : type1667, ((y2 y3 (@nil a0)) = (@EMPTY a0)) /\ (forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@INSERT a0 y4 (y2 y3 y5)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) y1)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : list a0) := @INSERT a0 x0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) x1).
Definition term0 (a0 : Type') := (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3))))).
Definition term10 (a0 : Type') := and ((@set_of_list a0 (@nil a0)) = (@EMPTY a0)).
Definition term9 (a0 : Type') := and ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@nil a0)) = (@EMPTY a0)).
Definition term8 (a0 : Type') := @eq (a0 -> Prop) (@set_of_list a0 (@nil a0)).
Definition term1 (a0 : Type') := forall y0 : type1667, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y1 : type1238 a0 => forall y2 : type1667, ((y1 y2 (@nil a0)) = (@EMPTY a0)) /\ (forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@INSERT a0 y3 (y1 y2 y4)))) y0 (@nil a0)) = (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : list a0, (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y3 : type1238 a0 => forall y4 : type1667, ((y3 y4 (@nil a0)) = (@EMPTY a0)) /\ (forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@INSERT a0 y5 (y3 y4 y6)))) y0 (@cons a0 y1 y2)) = (@INSERT a0 y1 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y3 : type1238 a0 => forall y4 : type1667, ((y3 y4 (@nil a0)) = (@EMPTY a0)) /\ (forall y5 : a0, forall y6 : list a0, (y3 y4 (@cons a0 y5 y6)) = (@INSERT a0 y5 (y3 y4 y6)))) y0 y2))).
Definition term13 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq (a0 -> Prop) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@cons a0 x0 x1)).
Definition term7 (a0 : Type') := @eq (a0 -> Prop) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@nil a0)).
Definition term11 (a0 : Type') (x0 : a0) (x1 : list a0) := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@cons a0 x0 x1).
Definition term3 := @pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))).
Definition term12 (a0 : Type') (x0 : a0) (x1 : list a0) := @set_of_list a0 (@cons a0 x0 x1).
Definition term17 (a0 : Type') (x0 : a0) (x1 : list a0) := @INSERT a0 x0 (@set_of_list a0 x1).
Definition term21 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@set_of_list a0 (@cons a0 x0 y0)) = (@INSERT a0 x0 (@set_of_list a0 y0)).
Definition term18 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y1 : type1238 a0 => forall y2 : type1667, ((y1 y2 (@nil a0)) = (@EMPTY a0)) /\ (forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@INSERT a0 y3 (y1 y2 y4)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@cons a0 x0 y0)) = (@INSERT a0 x0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y1 : type1238 a0 => forall y2 : type1667, ((y1 y2 (@nil a0)) = (@EMPTY a0)) /\ (forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@INSERT a0 y3 (y1 y2 y4)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) y0)).
Definition term26 (a0 : Type') := ((@set_of_list a0 (@nil a0)) = (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : list a0, (@set_of_list a0 (@cons a0 y0 y1)) = (@INSERT a0 y0 (@set_of_list a0 y1))).
Definition term14 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq (a0 -> Prop) (@set_of_list a0 (@cons a0 x0 x1)).
Definition term19 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (@set_of_list a0 (@cons a0 x0 y0)) = (@INSERT a0 x0 (@set_of_list a0 y0)).
Definition term5 (a0 : Type') := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))).
Definition term6 (a0 : Type') := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y0 : type1238 a0 => forall y1 : type1667, ((y0 y1 (@nil a0)) = (@EMPTY a0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (@INSERT a0 y2 (y0 y1 y3)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@nil a0).
Definition term25 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@set_of_list a0 (@cons a0 y0 y1)) = (@INSERT a0 y0 (@set_of_list a0 y1)).
Definition term24 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y2 : type1238 a0 => forall y3 : type1667, ((y2 y3 (@nil a0)) = (@EMPTY a0)) /\ (forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@INSERT a0 y4 (y2 y3 y5)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@cons a0 y0 y1)) = (@INSERT a0 y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y2 : type1238 a0 => forall y3 : type1667, ((y2 y3 (@nil a0)) = (@EMPTY a0)) /\ (forall y4 : a0, forall y5 : list a0, (y2 y3 (@cons a0 y4 y5)) = (@INSERT a0 y4 (y2 y3 y5)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) y1)).
Definition term20 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y1 : type1238 a0 => forall y2 : type1667, ((y1 y2 (@nil a0)) = (@EMPTY a0)) /\ (forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@INSERT a0 y3 (y1 y2 y4)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) (@cons a0 x0 y0)) = (@INSERT a0 x0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list a0) -> a0 -> Prop) (fun y1 : type1238 a0 => forall y2 : type1667, ((y1 y2 (@nil a0)) = (@EMPTY a0)) /\ (forall y3 : a0, forall y4 : list a0, (y1 y2 (@cons a0 y3 y4)) = (@INSERT a0 y3 (y1 y2 y4)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))))))))))))) y0)).