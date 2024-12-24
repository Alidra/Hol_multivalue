Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term48 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := forall y0 : nat, (x0 (S y0) x1) = (@List.app a0 (x0 y0 x1) (@cons a0 (x1 y0) (@nil a0))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, ((fun y2 : a0 => y0 y2) y1) = (y0 y1)) x0.
Definition term116 (a0 : Type') := fun y0 : type1237 a0 => forall y1 : type1667, (forall y2 : nat -> a0, (y0 y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y0 y1 y2 (S y3)) = (@List.app a0 (y0 y1 y2 y3) (@cons a0 (y2 y3) (@nil a0)))).
Definition term107 (a0 : Type') := @eq Prop (forall y0 : type1667, exists y1 : type971 a0, (forall y2 : nat -> a0, (y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y1 y2 (S y3)) = (@List.app a0 (y1 y2 y3) (@cons a0 (y2 y3) (@nil a0))))).
Definition term106 (a0 : Type') := @eq Prop (forall y0 : type1667, exists y1 : type971 a0, (fun y2 : type1667 => fun y3 : type971 a0 => (forall y4 : nat -> a0, (y3 y4 (NUMERAL 0)) = (@nil a0)) /\ (forall y4 : nat -> a0, forall y5 : nat, (y3 y4 (S y5)) = (@List.app a0 (y3 y4 y5) (@cons a0 (y4 y5) (@nil a0))))) y0 y1).
Definition term43 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) (x2 : nat) := @List.app a0 (x0 x1 x2) (@cons a0 (x1 x2) (@nil a0)).
Definition term115 (a0 : Type') := fun y0 : type1237 a0 => forall y1 : type1667, (fun y2 : type1667 => fun y3 : type971 a0 => (forall y4 : nat -> a0, (y3 y4 (NUMERAL 0)) = (@nil a0)) /\ (forall y4 : nat -> a0, forall y5 : nat, (y3 y4 (S y5)) = (@List.app a0 (y3 y4 y5) (@cons a0 (y4 y5) (@nil a0))))) y1 (y0 y1).
Definition term32 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := @eq (list a0) ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2)).
Definition term71 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := (fun y0 : type974 a0 => fun y1 : nat => fun y2 : nat -> a0 => @List.app a0 (y0 y2) (@cons a0 (y2 y1) (@nil a0))) (x0 x1).
Definition term110 (a0 : Type') (x0 : type1237 a0) (x1 : type1667) := (forall y0 : nat -> a0, (x0 x1 y0 (NUMERAL 0)) = (@nil a0)) /\ (forall y0 : nat -> a0, forall y1 : nat, (x0 x1 y0 (S y1)) = (@List.app a0 (x0 x1 y0 y1) (@cons a0 (y0 y1) (@nil a0)))).
Definition term54 (a0 : Type') (x0 : type1582 a0) := (forall y0 : nat -> a0, (x0 (NUMERAL 0) y0) = (@nil a0)) /\ (forall y0 : nat -> a0, forall y1 : nat, (x0 (S y1) y0) = (@List.app a0 (x0 y1 y0) (@cons a0 (y0 y1) (@nil a0)))).
Definition term53 (a0 : Type') (x0 : type971 a0) := (forall y0 : nat -> a0, (x0 y0 (NUMERAL 0)) = (@nil a0)) /\ (forall y0 : nat -> a0, forall y1 : nat, (x0 y0 (S y1)) = (@List.app a0 (x0 y0 y1) (@cons a0 (y0 y1) (@nil a0)))).
Definition term82 (a0 : Type') := fun y0 : type1582 a0 => ((y0 (NUMERAL 0)) = (fun y1 : nat -> a0 => @nil a0)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat -> a0 => @List.app a0 (y0 y1 y2) (@cons a0 (y2 y1) (@nil a0)))).
Definition term81 (a0 : Type') := fun y0 : type1582 a0 => ((y0 (NUMERAL 0)) = (fun y1 : nat -> a0 => @nil a0)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : type974 a0 => fun y3 : nat => fun y4 : nat -> a0 => @List.app a0 (y2 y4) (@cons a0 (y4 y3) (@nil a0))) (y0 y1) y1)).
Definition term58 (a0 : Type') (x0 : type1582 a0) := forall y0 : nat, (x0 (S y0)) = (fun y1 : nat -> a0 => @List.app a0 (x0 y0 y1) (@cons a0 (y1 y0) (@nil a0))).
Definition term100 (a0 : Type') (x0 : type1667) (x1 : type971 a0) := (fun y0 : type1667 => fun y1 : type971 a0 => (forall y2 : nat -> a0, (y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y1 y2 (S y3)) = (@List.app a0 (y1 y2 y3) (@cons a0 (y2 y3) (@nil a0))))) x0 x1.
Definition term98 (a0 : Type') := fun y0 : type1667 => fun y1 : type971 a0 => (forall y2 : nat -> a0, (y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y1 y2 (S y3)) = (@List.app a0 (y1 y2 y3) (@cons a0 (y2 y3) (@nil a0)))).
Definition term57 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat -> a0 => @nil a0) x0.
Definition term34 (a0 : Type') (x0 : type1582 a0) (x1 : nat) (x2 : nat -> a0) := x0 (S x1) x2.
Definition term17 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, ((fun y1 : a0 => x0 y1) y0) = (x0 y0).
Definition term102 (a0 : Type') (x0 : type1667) := fun y0 : type971 a0 => (fun y1 : type1667 => fun y2 : type971 a0 => (forall y3 : nat -> a0, (y2 y3 (NUMERAL 0)) = (@nil a0)) /\ (forall y3 : nat -> a0, forall y4 : nat, (y2 y3 (S y4)) = (@List.app a0 (y2 y3 y4) (@cons a0 (y3 y4) (@nil a0))))) x0 y0.
Definition term66 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term50 (a0 : Type') (x0 : type1582 a0) := fun y0 : nat -> a0 => forall y1 : nat, (x0 (S y1) y0) = (@List.app a0 (x0 y1 y0) (@cons a0 (y0 y1) (@nil a0))).
Definition term49 (a0 : Type') (x0 : type971 a0) := fun y0 : nat -> a0 => forall y1 : nat, (x0 y0 (S y1)) = (@List.app a0 (x0 y0 y1) (@cons a0 (y0 y1) (@nil a0))).
Definition term73 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := (fun y0 : type974 a0 => fun y1 : nat => fun y2 : nat -> a0 => @List.app a0 (y0 y2) (@cons a0 (y2 y1) (@nil a0))) (x0 x1) x1.
Definition term36 (a0 : Type') (x0 : type1582 a0) (x1 : nat) (x2 : nat -> a0) := @eq (list a0) (x0 (S x1) x2).
Definition term15 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0).
Definition term47 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) := forall y0 : nat, (x0 x1 (S y0)) = (@List.app a0 (x0 x1 y0) (@cons a0 (x1 y0) (@nil a0))).
Definition term6 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => x0 y0) x1.
Definition term62 (a0 : Type') (x0 : type1582 a0) (x1 : nat) (x2 : nat -> a0) := (fun y0 : nat -> a0 => @List.app a0 (x0 x1 y0) (@cons a0 (y0 x1) (@nil a0))) x2.
Definition term121 (a0 : Type') := (fun y0 : type1237 a0 => forall y1 : type1667, (forall y2 : nat -> a0, (y0 y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y0 y1 y2 (S y3)) = (@List.app a0 (y0 y1 y2 y3) (@cons a0 (y2 y3) (@nil a0))))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> a0) -> nat -> list a0) (fun y0 : type1237 a0 => forall y1 : type1667, (forall y2 : nat -> a0, (y0 y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y0 y1 y2 (S y3)) = (@List.app a0 (y0 y1 y2 y3) (@cons a0 (y2 y3) (@nil a0)))))).
Definition term114 (a0 : Type') (x0 : type1237 a0) := forall y0 : type1667, (forall y1 : nat -> a0, (x0 y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (x0 y0 y1 (S y2)) = (@List.app a0 (x0 y0 y1 y2) (@cons a0 (y1 y2) (@nil a0)))).
Definition term86 (a0 : Type') := exists y0 : type971 a0, (forall y1 : nat -> a0, (y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 y1 (S y2)) = (@List.app a0 (y0 y1 y2) (@cons a0 (y1 y2) (@nil a0)))).
Definition term84 (a0 : Type') := exists y0 : type1582 a0, (forall y1 : nat -> a0, (y0 (NUMERAL 0) y1) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 (S y2) y1) = (@List.app a0 (y0 y2 y1) (@cons a0 (y1 y2) (@nil a0)))).
Definition term19 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := @eq (list a0) ((fun y0 : nat => x0 y0 x1) (NUMERAL 0)).
Definition term8 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := fun y0 : nat => x0 y0 x1.
Definition term78 (a0 : Type') (x0 : type1582 a0) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : type974 a0 => fun y2 : nat => fun y3 : nat -> a0 => @List.app a0 (y1 y3) (@cons a0 (y3 y2) (@nil a0))) (x0 y0) y0).
Definition term25 (a0 : Type') (x0 : type971 a0) := forall y0 : nat -> a0, (x0 y0 (NUMERAL 0)) = (@nil a0).
Definition term7 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => (fun y1 : nat -> a0 => fun y2 : nat => x0 y2 y1) y0) x1.
Definition term61 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := fun y0 : nat -> a0 => @List.app a0 (x0 x1 y0) (@cons a0 (y0 x1) (@nil a0)).
Definition term33 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := @eq (list a0) ((fun y0 : nat => x0 y0 x1) (S x2)).
Definition term92 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term24 (a0 : Type') (x0 : type1582 a0) := fun y0 : nat -> a0 => (x0 (NUMERAL 0) y0) = (@nil a0).
Definition term79 (a0 : Type') (x0 : type1582 a0) := and ((x0 (NUMERAL 0)) = (fun y0 : nat -> a0 => @nil a0)).
Definition term117 (a0 : Type') := exists y0 : type1237 a0, forall y1 : type1667, (forall y2 : nat -> a0, (y0 y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y0 y1 y2 (S y3)) = (@List.app a0 (y0 y1 y2 y3) (@cons a0 (y2 y3) (@nil a0)))).
Definition term97 (a0 : Type') := exists y0 : type1237 a0, forall y1 : type1667, (fun y2 : type1667 => fun y3 : type971 a0 => (forall y4 : nat -> a0, (y3 y4 (NUMERAL 0)) = (@nil a0)) /\ (forall y4 : nat -> a0, forall y5 : nat, (y3 y4 (S y5)) = (@List.app a0 (y3 y4 y5) (@cons a0 (y4 y5) (@nil a0))))) y1 (y0 y1).
Definition term95 (a0 : Type') (x0 : type1235 a0) := exists y0 : type1237 a0, forall y1 : type1667, x0 y1 (y0 y1).
Definition term113 (a0 : Type') (x0 : type1237 a0) := forall y0 : type1667, (fun y1 : type1667 => fun y2 : type971 a0 => (forall y3 : nat -> a0, (y2 y3 (NUMERAL 0)) = (@nil a0)) /\ (forall y3 : nat -> a0, forall y4 : nat, (y2 y3 (S y4)) = (@List.app a0 (y2 y3 y4) (@cons a0 (y3 y4) (@nil a0))))) y0 (x0 y0).
Definition term10 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := @eq (nat -> list a0) ((fun y0 : nat -> a0 => (fun y1 : nat -> a0 => fun y2 : nat => x0 y2 y1) y0) x1).
Definition term109 (a0 : Type') (x0 : type1237 a0) (x1 : type1667) := (fun y0 : type971 a0 => (forall y1 : nat -> a0, (y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 y1 (S y2)) = (@List.app a0 (y0 y1 y2) (@cons a0 (y1 y2) (@nil a0))))) (x0 x1).
Definition term119 (a0 : Type') := fun y0 : type335 a0 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> a0) -> nat -> list a0) y0).
Definition term40 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) (x2 : nat) := @List.app a0 (x0 x1 x2).
Definition term76 (a0 : Type') (x0 : type1582 a0) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : type974 a0 => fun y2 : nat => fun y3 : nat -> a0 => @List.app a0 (y1 y3) (@cons a0 (y3 y2) (@nil a0))) (x0 y0) y0).
Definition term22 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := @eq (list a0) (x0 (NUMERAL 0) x1).
Definition term64 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term28 (a0 : Type') (x0 : type1582 a0) := and (forall y0 : nat -> a0, (x0 (NUMERAL 0) y0) = (@nil a0)).
Definition term27 (a0 : Type') (x0 : type971 a0) := and (forall y0 : nat -> a0, (x0 y0 (NUMERAL 0)) = (@nil a0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => ((fun y1 : a0 => x0 y1) y0) = (x0 y0)) x1.
Definition term26 (a0 : Type') (x0 : type1582 a0) := forall y0 : nat -> a0, (x0 (NUMERAL 0) y0) = (@nil a0).
Definition term29 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) (x2 : nat) := x0 x1 (S x2).
Definition term11 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := @eq (nat -> list a0) ((fun y0 : nat -> a0 => fun y1 : nat => x0 y1 y0) x1).
Definition term30 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => x0 y0 x1) (S x2).
Definition term44 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := @List.app a0 (x0 x2 x1) (@cons a0 (x1 x2) (@nil a0)).
Definition term16 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => x0 y0 x1) x2.
Definition term105 (a0 : Type') := fun y0 : type1667 => exists y1 : type971 a0, (forall y2 : nat -> a0, (y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y1 y2 (S y3)) = (@List.app a0 (y1 y2 y3) (@cons a0 (y2 y3) (@nil a0)))).
Definition term83 (a0 : Type') := exists y0 : type1582 a0, ((y0 (NUMERAL 0)) = (fun y1 : nat -> a0 => @nil a0)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat -> a0 => @List.app a0 (y0 y1 y2) (@cons a0 (y2 y1) (@nil a0)))).
Definition term69 (a0 : Type') := exists y0 : type1582 a0, ((y0 (NUMERAL 0)) = (fun y1 : nat -> a0 => @nil a0)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : type974 a0 => fun y3 : nat => fun y4 : nat -> a0 => @List.app a0 (y2 y4) (@cons a0 (y4 y3) (@nil a0))) (y0 y1) y1)).
Definition term118 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term4 (a0 : Type') (x0 : type1582 a0) := fun y0 : nat -> a0 => fun y1 : nat => x0 y1 y0.
Definition term63 (a0 : Type') (x0 : type1582 a0) := ((x0 (NUMERAL 0)) = (fun y0 : nat -> a0 => @nil a0)) /\ (forall y0 : nat, (x0 (S y0)) = (fun y1 : nat -> a0 => @List.app a0 (x0 y0 y1) (@cons a0 (y1 y0) (@nil a0)))).
Definition term108 (a0 : Type') (x0 : type1237 a0) (x1 : type1667) := (fun y0 : type1667 => fun y1 : type971 a0 => (forall y2 : nat -> a0, (y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y1 y2 (S y3)) = (@List.app a0 (y1 y2 y3) (@cons a0 (y2 y3) (@nil a0))))) x1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term120 (a0 : Type') := (fun y0 : type335 a0 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> a0) -> nat -> list a0) y0)) (fun y0 : type1237 a0 => forall y1 : type1667, (forall y2 : nat -> a0, (y0 y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y0 y1 y2 (S y3)) = (@List.app a0 (y0 y1 y2 y3) (@cons a0 (y2 y3) (@nil a0))))).
Definition term112 (a0 : Type') (x0 : type1237 a0) := fun y0 : type1667 => (forall y1 : nat -> a0, (x0 y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (x0 y0 y1 (S y2)) = (@List.app a0 (x0 y0 y1 y2) (@cons a0 (y1 y2) (@nil a0)))).
Definition term39 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := @eq (list a0) ((fun y0 : nat => x0 y0 x1) x2).
Definition term14 (a0 : Type') (x0 : type1609 a0) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term103 (a0 : Type') (x0 : type1667) := exists y0 : type971 a0, (fun y1 : type1667 => fun y2 : type971 a0 => (forall y3 : nat -> a0, (y2 y3 (NUMERAL 0)) = (@nil a0)) /\ (forall y3 : nat -> a0, forall y4 : nat, (y2 y3 (S y4)) = (@List.app a0 (y2 y3 y4) (@cons a0 (y3 y4) (@nil a0))))) x0 y0.
Definition term85 (a0 : Type') := fun y0 : type1582 a0 => (forall y1 : nat -> a0, (y0 (NUMERAL 0) y1) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 (S y2) y1) = (@List.app a0 (y0 y2 y1) (@cons a0 (y1 y2) (@nil a0)))).
Definition term42 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @cons a0 (x0 x1) (@nil a0).
Definition term20 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := x0 (NUMERAL 0) x1.
Definition term18 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := @eq (list a0) ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0)).
Definition term13 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := (fun y0 : nat => x0 y0 x1) (NUMERAL 0).
Definition term77 (a0 : Type') (x0 : type1582 a0) := fun y0 : nat => (x0 (S y0)) = (fun y1 : nat -> a0 => @List.app a0 (x0 y0 y1) (@cons a0 (y1 y0) (@nil a0))).
Definition term80 (a0 : Type') (x0 : type1582 a0) := ((x0 (NUMERAL 0)) = (fun y0 : nat -> a0 => @nil a0)) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : type974 a0 => fun y2 : nat => fun y3 : nat -> a0 => @List.app a0 (y1 y3) (@cons a0 (y3 y2) (@nil a0))) (x0 y0) y0)).
Definition term111 (a0 : Type') (x0 : type1237 a0) := fun y0 : type1667 => (fun y1 : type1667 => fun y2 : type971 a0 => (forall y3 : nat -> a0, (y2 y3 (NUMERAL 0)) = (@nil a0)) /\ (forall y3 : nat -> a0, forall y4 : nat, (y2 y3 (S y4)) = (@List.app a0 (y2 y3 y4) (@cons a0 (y3 y4) (@nil a0))))) y0 (x0 y0).
Definition term9 (a0 : Type') (x0 : type1582 a0) := fun y0 : nat -> a0 => (fun y1 : nat -> a0 => fun y2 : nat => x0 y2 y1) y0.
Definition term52 (a0 : Type') (x0 : type1582 a0) := forall y0 : nat -> a0, forall y1 : nat, (x0 (S y1) y0) = (@List.app a0 (x0 y1 y0) (@cons a0 (y0 y1) (@nil a0))).
Definition term51 (a0 : Type') (x0 : type971 a0) := forall y0 : nat -> a0, forall y1 : nat, (x0 y0 (S y1)) = (@List.app a0 (x0 y0 y1) (@cons a0 (y0 y1) (@nil a0))).
Definition term55 (a0 : Type') (x0 : type1582 a0) := x0 (NUMERAL 0).
Definition term75 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := @eq ((nat -> a0) -> list a0) (x0 (S x1)).
Definition term12 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) := x0 x1 (NUMERAL 0).
Definition term88 (a0 : Type') (x0 : type971 a0) (x1 : type1582 a0) := (x0 = (fun y0 : nat -> a0 => fun y1 : nat => x1 y1 y0)) -> exists y0 : type971 a0, (forall y1 : nat -> a0, (y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 y1 (S y2)) = (@List.app a0 (y0 y1 y2) (@cons a0 (y1 y2) (@nil a0)))).
Definition term41 (a0 : Type') (x0 : type1582 a0) (x1 : nat) (x2 : nat -> a0) := @List.app a0 (x0 x1 x2).
Definition term72 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := fun y0 : nat => fun y1 : nat -> a0 => @List.app a0 (x0 x1 y1) (@cons a0 (y1 y0) (@nil a0)).
Definition term70 (a0 : Type') := fun y0 : type974 a0 => fun y1 : nat => fun y2 : nat -> a0 => @List.app a0 (y0 y2) (@cons a0 (y2 y1) (@nil a0)).
Definition term101 (a0 : Type') (x0 : type971 a0) := (fun y0 : type971 a0 => (forall y1 : nat -> a0, (y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 y1 (S y2)) = (@List.app a0 (y0 y1 y2) (@cons a0 (y1 y2) (@nil a0))))) x0.
Definition term56 (a0 : Type') := fun y0 : nat -> a0 => @nil a0.
Definition term60 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := x0 (S x1).
Definition term65 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term91 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term99 (a0 : Type') (x0 : type1667) := (fun y0 : type1667 => fun y1 : type971 a0 => (forall y2 : nat -> a0, (y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y1 y2 (S y3)) = (@List.app a0 (y1 y2 y3) (@cons a0 (y2 y3) (@nil a0))))) x0.
Definition term38 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := @eq (list a0) ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2).
Definition term35 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) (x2 : nat) := @eq (list a0) (x0 x1 (S x2)).
Definition term5 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => fun y1 : nat => x0 y1 y0) x1.
Definition term31 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2).
Definition term59 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (fun y1 : nat -> a0 => @List.app a0 (x0 y0 y1) (@cons a0 (y1 y0) (@nil a0)))) x1.
Definition term45 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) := fun y0 : nat => (x0 x1 (S y0)) = (@List.app a0 (x0 x1 y0) (@cons a0 (x1 y0) (@nil a0))).
Definition term93 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term68 (a0 : Type') (x0 : type974 a0) (x1 : type245 a0) := exists y0 : type1582 a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term67 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term96 (a0 : Type') := forall y0 : type1667, exists y1 : type971 a0, (fun y2 : type1667 => fun y3 : type971 a0 => (forall y4 : nat -> a0, (y3 y4 (NUMERAL 0)) = (@nil a0)) /\ (forall y4 : nat -> a0, forall y5 : nat, (y3 y4 (S y5)) = (@List.app a0 (y3 y4 y5) (@cons a0 (y4 y5) (@nil a0))))) y0 y1.
Definition term94 (a0 : Type') (x0 : type1235 a0) := forall y0 : type1667, exists y1 : type971 a0, x0 y0 y1.
Definition term23 (a0 : Type') (x0 : type971 a0) := fun y0 : nat -> a0 => (x0 y0 (NUMERAL 0)) = (@nil a0).
Definition term37 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2.
Definition term46 (a0 : Type') (x0 : type1582 a0) (x1 : nat -> a0) := fun y0 : nat => (x0 (S y0) x1) = (@List.app a0 (x0 y0 x1) (@cons a0 (x1 y0) (@nil a0))).
Definition term89 (a0 : Type') (x0 : type1582 a0) := ((fun y0 : nat -> a0 => fun y1 : nat => x0 y1 y0) = (fun y0 : nat -> a0 => fun y1 : nat => x0 y1 y0)) -> exists y0 : type971 a0, (forall y1 : nat -> a0, (y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 y1 (S y2)) = (@List.app a0 (y0 y1 y2) (@cons a0 (y1 y2) (@nil a0)))).
Definition term90 (a0 : Type') := forall y0 : type1667, exists y1 : type971 a0, (forall y2 : nat -> a0, (y1 y2 (NUMERAL 0)) = (@nil a0)) /\ (forall y2 : nat -> a0, forall y3 : nat, (y1 y2 (S y3)) = (@List.app a0 (y1 y2 y3) (@cons a0 (y2 y3) (@nil a0)))).
Definition term87 (a0 : Type') := fun y0 : type971 a0 => (forall y1 : nat -> a0, (y0 y1 (NUMERAL 0)) = (@nil a0)) /\ (forall y1 : nat -> a0, forall y2 : nat, (y0 y1 (S y2)) = (@List.app a0 (y0 y1 y2) (@cons a0 (y1 y2) (@nil a0)))).
Definition term21 (a0 : Type') (x0 : type971 a0) (x1 : nat -> a0) := @eq (list a0) (x0 x1 (NUMERAL 0)).
Definition term74 (a0 : Type') (x0 : type1582 a0) (x1 : nat) := (fun y0 : nat => fun y1 : nat -> a0 => @List.app a0 (x0 x1 y1) (@cons a0 (y1 y0) (@nil a0))) x1.
Definition term104 (a0 : Type') := fun y0 : type1667 => exists y1 : type971 a0, (fun y2 : type1667 => fun y3 : type971 a0 => (forall y4 : nat -> a0, (y3 y4 (NUMERAL 0)) = (@nil a0)) /\ (forall y4 : nat -> a0, forall y5 : nat, (y3 y4 (S y5)) = (@List.app a0 (y3 y4 y5) (@cons a0 (y4 y5) (@nil a0))))) y0 y1.
