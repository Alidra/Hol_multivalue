Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term74 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := @EL a0 x0 (@list_of_seq a0 x1 (NUMERAL 0)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : a1, forall y2 : a0, y0 y2 y1)) x0.
Definition term102 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)).
Definition term137 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := (~ False) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = (x1 x2).
Definition term8 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : list a0) := (fun y0 : list a0 => (@EL a0 x0 (@List.app a0 x1 y0)) = (@COND a0 (Peano.lt x0 (@List.length a0 x1)) (@EL a0 x0 x1) (@EL a0 (Nat.sub x0 (@List.length a0 x1)) y0))) x2.
Definition term77 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (Peano.lt x1 (NUMERAL 0)) -> (@EL a0 x1 (@list_of_seq a0 x0 (NUMERAL 0))) = (x0 x1).
Definition term136 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term31 (a0 : Type') (x0 : nat -> a0) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt x1 y0) -> (@EL a0 x1 (@list_of_seq a0 x0 y0)) = (x0 x1)) x2.
Definition term86 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @list_of_seq a0 x0 (S x1).
Definition term138 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := ((~ False) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = (x1 x2)) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 False (x1 x2) (x1 x2)).
Definition term82 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term140 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @eq a0 (x0 x1).
Definition term89 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @EL a0 x0 (@List.app a0 (@list_of_seq a0 x1 x2) (@cons a0 (x1 x2) (@nil a0))).
Definition term103 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))).
Definition term64 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) -> forall y1 : nat, (Peano.lt y1 (S y0)) -> (@EL a0 y1 (@list_of_seq a0 x0 (S y0))) = (x0 y1).
Definition term125 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : Prop) (x4 : a0) (x5 : a0) := (fun y0 : a0 => ((Peano.lt x0 x2) = x3) -> (x3 -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = x4) -> ((~ x3) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = y0) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 x3 x4 y0)) x5.
Definition term147 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := ((~ True) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 True (x1 x0) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))).
Definition term57 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) (S x1).
Definition term134 (a0 : Type') (x0 : list a0) := @EL a0 (NUMERAL 0) x0.
Definition term5 (a0 : Type') (x0 : nat) := forall y0 : list a0, forall y1 : list a0, (@EL a0 x0 (@List.app a0 y0 y1)) = (@COND a0 (Peano.lt x0 (@List.length a0 y0)) (@EL a0 x0 y0) (@EL a0 (Nat.sub x0 (@List.length a0 y0)) y1)).
Definition term114 (x0 : nat) := (fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) x0.
Definition term71 (a0 : Type') (x0 : nat -> a0) := ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> (@EL a0 y0 (@list_of_seq a0 x0 (NUMERAL 0))) = (x0 y0)) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) -> forall y1 : nat, (Peano.lt y1 (S y0)) -> (@EL a0 y1 (@list_of_seq a0 x0 (S y0))) = (x0 y1))) -> forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1).
Definition term123 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : Prop) (x4 : a0) := (fun y0 : a0 => forall y1 : a0, ((Peano.lt x0 x2) = x3) -> (x3 -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = y0) -> ((~ x3) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = y1) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 x3 y0 y1)) x4.
Definition term30 (a0 : Type') (x0 : nat -> a0) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.lt y0 y1) -> (@EL a0 y0 (@list_of_seq a0 x0 y1)) = (x0 y0)) x1 x2.
Definition term124 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : Prop) (x4 : a0) := forall y0 : a0, ((Peano.lt x0 x2) = x3) -> (x3 -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = x4) -> ((~ x3) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = y0) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 x3 x4 y0).
Definition term117 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term104 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @eq a0 (@EL a0 x0 (@list_of_seq a0 x1 (S x2))).
Definition term43 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) -> (@EL a0 y1 (@list_of_seq a0 x0 y2)) = (x0 y1)) y0 x1.
Definition term149 (a0 : Type') := forall y0 : nat -> a0, forall y1 : nat, forall y2 : nat, (Peano.lt y1 y2) -> (@EL a0 y1 (@list_of_seq a0 y0 y2)) = (y0 y1).
Definition term3 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.length a0 (@list_of_seq a0 x0 x1).
Definition term73 (a0 : Type') (x0 : nat -> a0) := @list_of_seq a0 x0 (NUMERAL 0).
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 y0 y1.
Definition term42 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := fun y0 : nat => (Peano.lt y0 x0) -> (@EL a0 y0 (@list_of_seq a0 x1 x0)) = (x1 y0).
Definition term49 (a0 : Type') (x0 : nat -> a0) := (((fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0.
Definition term17 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term48 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term133 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @EL a0 (NUMERAL 0) (@cons a0 (x0 x1) (@nil a0)).
Definition term67 (a0 : Type') (x0 : nat -> a0) := imp (((fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) (S y0))).
Definition term4 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : list a0, forall y2 : list a0, (@EL a0 y0 (@List.app a0 y1 y2)) = (@COND a0 (Peano.lt y0 (@List.length a0 y1)) (@EL a0 y0 y1) (@EL a0 (Nat.sub y0 (@List.length a0 y1)) y2))) x0.
Definition term72 (x0 : nat) := imp (Peano.lt x0 (NUMERAL 0)).
Definition term100 (a0 : Type') (x0 : nat) (x1 : nat) := @EL a0 (Nat.sub x0 x1).
Definition term54 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) x1.
Definition term63 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) (S y0).
Definition term16 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term145 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) := ((~ True) -> (@EL a0 (Nat.sub x2 x0) (@cons a0 (x1 x0) (@nil a0))) = x3) -> (@COND a0 (Peano.lt x2 x0) (@EL a0 x2 (@list_of_seq a0 x1 x0)) (@EL a0 (Nat.sub x2 x0) (@cons a0 (x1 x0) (@nil a0)))) = (@COND a0 True (x1 x2) x3).
Definition term131 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) := ((~ False) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = x3) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 False (x1 x2) x3).
Definition term97 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)).
Definition term92 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := Peano.lt x0 (@List.length a0 (@list_of_seq a0 x1 x2)).
Definition term98 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := Nat.sub x0 (@List.length a0 (@list_of_seq a0 x1 x2)).
Definition term33 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) -> (@EL a0 y1 (@list_of_seq a0 x0 y2)) = (x0 y1)) x1 y0.
Definition term45 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) -> (@EL a0 y2 (@list_of_seq a0 x0 y3)) = (x0 y2)) y1 y0.
Definition term28 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (Peano.lt y0 y1) -> (@EL a0 y0 (@list_of_seq a0 x0 y1)) = (x0 y0)) x1.
Definition term18 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term52 (a0 : Type') (x0 : nat -> a0) := and ((fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) (NUMERAL 0)).
Definition term40 (a0 : Type') (x0 : nat -> a0) := @eq Prop (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (@EL a0 y0 (@list_of_seq a0 x0 y1)) = (x0 y0)).
Definition term39 (a0 : Type') (x0 : nat -> a0) := @eq Prop (forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) -> (@EL a0 y2 (@list_of_seq a0 x0 y3)) = (x0 y2)) y0 y1).
Definition term127 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) (x4 : a0) := ((Peano.lt x0 x2) = False) -> (False -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = x3) -> ((~ False) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = x4) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 False x3 x4).
Definition term56 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := imp (forall y0 : nat, (Peano.lt y0 x0) -> (@EL a0 y0 (@list_of_seq a0 x1 x0)) = (x1 y0)).
Definition term53 (a0 : Type') (x0 : nat -> a0) := and (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> (@EL a0 y0 (@list_of_seq a0 x0 (NUMERAL 0))) = (x0 y0)).
Definition term50 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) (NUMERAL 0).
Definition term90 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @COND a0 (Peano.lt x0 (@List.length a0 (@list_of_seq a0 x1 x2))) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 (@List.length a0 (@list_of_seq a0 x1 x2))) (@cons a0 (x1 x2) (@nil a0))).
Definition term27 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => fun y1 : nat => (Peano.lt y0 y1) -> (@EL a0 y0 (@list_of_seq a0 x0 y1)) = (x0 y0).
Definition term139 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @COND a0 False (x0 x1) (x0 x1).
Definition term68 (a0 : Type') (x0 : nat -> a0) := imp ((forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> (@EL a0 y0 (@list_of_seq a0 x0 (NUMERAL 0))) = (x0 y0)) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) -> forall y1 : nat, (Peano.lt y1 (S y0)) -> (@EL a0 y1 (@list_of_seq a0 x0 (S y0))) = (x0 y1))).
Definition term113 (x0 : nat) := (~ (Peano.lt x0 x0)) -> (Peano.lt x0 x0) = False.
Definition term130 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) := (False -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = (x1 x2)) -> ((~ False) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = x3) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 False (x1 x2) x3).
Definition term44 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := forall y0 : nat, (Peano.lt y0 x0) -> (@EL a0 y0 (@list_of_seq a0 x1 x0)) = (x1 y0).
Definition term35 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := forall y0 : nat, (Peano.lt x1 y0) -> (@EL a0 x1 (@list_of_seq a0 x0 y0)) = (x0 x1).
Definition term47 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1).
Definition term38 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (@EL a0 y0 (@list_of_seq a0 x0 y1)) = (x0 y0).
Definition term26 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) -> (@EL a0 y2 (@list_of_seq a0 x0 y3)) = (x0 y2)) y1 y0.
Definition term25 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) -> (@EL a0 y2 (@list_of_seq a0 x0 y3)) = (x0 y2)) y0 y1.
Definition term24 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y1 y0.
Definition term23 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term11 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term78 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := False -> (@EL a0 x1 (@nil a0)) = (x0 x1).
Definition term84 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 (S x1)).
Definition term85 (x0 : nat) (x1 : nat) := imp ((x0 = x1) \/ (Peano.lt x0 x1)).
Definition term141 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) (x4 : a0) := ((Peano.lt x0 x2) = True) -> (True -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = x3) -> ((~ True) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = x4) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 True x3 x4).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a1, forall y1 : a0, x0 y1 y0.
Definition term7 (a0 : Type') (x0 : nat) (x1 : list a0) := forall y0 : list a0, (@EL a0 x0 (@List.app a0 x1 y0)) = (@COND a0 (Peano.lt x0 (@List.length a0 x1)) (@EL a0 x0 x1) (@EL a0 (Nat.sub x0 (@List.length a0 x1)) y0)).
Definition term15 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term81 := forall y0 : nat, True.
Definition term9 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : list a0) := @EL a0 x0 (@List.app a0 x1 x2).
Definition term115 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => (Peano.lt y0 x0) -> (@EL a0 y0 (@list_of_seq a0 x1 x0)) = (x1 y0)) x2.
Definition term91 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @cons a0 (x0 x1) (@nil a0).
Definition term129 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := False -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = (x1 x2).
Definition term101 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @EL a0 (Nat.sub x0 (@List.length a0 (@list_of_seq a0 x1 x2))) (@cons a0 (x1 x2) (@nil a0)).
Definition term0 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat -> a0 => forall y1 : nat, (@List.length a0 (@list_of_seq a0 y0 y1)) = y1) x0.
Definition term112 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term80 := fun y0 : nat => True.
Definition term13 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term29 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := fun y0 : nat => (Peano.lt x1 y0) -> (@EL a0 x1 (@list_of_seq a0 x0 y0)) = (x0 x1).
Definition term135 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @hd a0 (@cons a0 (x0 x1) (@nil a0)).
Definition term55 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := imp ((fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) x1).
Definition term6 (a0 : Type') (x0 : nat) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@EL a0 x0 (@List.app a0 y0 y1)) = (@COND a0 (Peano.lt x0 (@List.length a0 y0)) (@EL a0 x0 y0) (@EL a0 (Nat.sub x0 (@List.length a0 y0)) y1))) x1.
Definition term93 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @COND a0 (Peano.lt x0 (@List.length a0 (@list_of_seq a0 x1 x2))).
Definition term34 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) -> (@EL a0 y1 (@list_of_seq a0 x0 y2)) = (x0 y1)) x1 y0.
Definition term36 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (Peano.lt y2 y3) -> (@EL a0 y2 (@list_of_seq a0 x0 y3)) = (x0 y2)) y0 y1.
Definition term62 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => (forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) -> forall y1 : nat, (Peano.lt y1 (S y0)) -> (@EL a0 y1 (@list_of_seq a0 x0 (S y0))) = (x0 y1).
Definition term61 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) (S y0).
Definition term120 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, ((Peano.lt x0 x2) = y0) -> (y0 -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = y1) -> ((~ y0) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = y2) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 y0 y1 y2).
Definition term119 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term59 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) x1) -> (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) (S x1).
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term1 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (@List.length a0 (@list_of_seq a0 x0 y0)) = y0.
Definition term105 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @eq a0 (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))).
Definition term66 (a0 : Type') (x0 : nat -> a0) := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> (@EL a0 y0 (@list_of_seq a0 x0 (NUMERAL 0))) = (x0 y0)) /\ (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) -> forall y1 : nat, (Peano.lt y1 (S y0)) -> (@EL a0 y1 (@list_of_seq a0 x0 (S y0))) = (x0 y1)).
Definition term144 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) := (True -> (@EL a0 x2 (@list_of_seq a0 x1 x0)) = (x1 x2)) -> ((~ True) -> (@EL a0 (Nat.sub x2 x0) (@cons a0 (x1 x0) (@nil a0))) = x3) -> (@COND a0 (Peano.lt x2 x0) (@EL a0 x2 (@list_of_seq a0 x1 x0)) (@EL a0 (Nat.sub x2 x0) (@cons a0 (x1 x0) (@nil a0)))) = (@COND a0 True (x1 x2) x3).
Definition term19 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term121 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, ((Peano.lt x0 x2) = y0) -> (y0 -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = y1) -> ((~ y0) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = y2) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 y0 y1 y2)) x3.
Definition term106 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := (Peano.lt x2 (S x0)) -> (@EL a0 x2 (@list_of_seq a0 x1 (S x0))) = (x1 x2).
Definition term69 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0.
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term10 (a0 : Type') (x0 : nat) (x1 : list a0) (x2 : list a0) := @COND a0 (Peano.lt x0 (@List.length a0 x1)) (@EL a0 x0 x1) (@EL a0 (Nat.sub x0 (@List.length a0 x1)) x2).
Definition term148 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @COND a0 True (x1 x0) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))).
Definition term126 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : Prop) (x4 : a0) (x5 : a0) := ((Peano.lt x0 x2) = x3) -> (x3 -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = x4) -> ((~ x3) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = x5) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 x3 x4 x5).
Definition term65 (a0 : Type') (x0 : nat -> a0) := ((fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0) -> (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) (S y0)).
Definition term122 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : Prop) := forall y0 : a0, forall y1 : a0, ((Peano.lt x0 x2) = x3) -> (x3 -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = y0) -> ((~ x3) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = y1) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 x3 y0 y1).
Definition term118 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term111 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term142 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) (x4 : a0) := (True -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = x3) -> ((~ True) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = x4) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 True x3 x4).
Definition term99 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @EL a0 (Nat.sub x0 (@List.length a0 (@list_of_seq a0 x1 x2))).
Definition term108 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := fun y0 : nat => (Peano.lt y0 (S x0)) -> (@EL a0 y0 (@list_of_seq a0 x1 (S x0))) = (x1 y0).
Definition term143 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := True -> (@EL a0 x2 (@list_of_seq a0 x1 x0)) = (x1 x2).
Definition term88 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @EL a0 x0 (@list_of_seq a0 x1 (S x2)).
Definition term75 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := @eq a0 (@EL a0 x0 (@list_of_seq a0 x1 (NUMERAL 0))).
Definition term132 (a0 : Type') := @EL a0 (NUMERAL 0).
Definition term110 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := forall y0 : nat, ((y0 = x0) \/ (Peano.lt y0 x0)) -> (@COND a0 (Peano.lt y0 x0) (@EL a0 y0 (@list_of_seq a0 x1 x0)) (@EL a0 (Nat.sub y0 x0) (@cons a0 (x1 x0) (@nil a0)))) = (x1 y0).
Definition term58 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := forall y0 : nat, (Peano.lt y0 (S x0)) -> (@EL a0 y0 (@list_of_seq a0 x1 (S x0))) = (x1 y0).
Definition term51 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) -> (@EL a0 y0 (@list_of_seq a0 x0 (NUMERAL 0))) = (x0 y0).
Definition term109 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := fun y0 : nat => ((y0 = x0) \/ (Peano.lt y0 x0)) -> (@COND a0 (Peano.lt y0 x0) (@EL a0 y0 (@list_of_seq a0 x1 x0)) (@EL a0 (Nat.sub y0 x0) (@cons a0 (x1 x0) (@nil a0)))) = (x1 y0).
Definition term107 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := ((x2 = x0) \/ (Peano.lt x2 x0)) -> (@COND a0 (Peano.lt x2 x0) (@EL a0 x2 (@list_of_seq a0 x1 x0)) (@EL a0 (Nat.sub x2 x0) (@cons a0 (x1 x0) (@nil a0)))) = (x1 x2).
Definition term2 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) x1.
Definition term83 (x0 : Prop) := forall y0 : nat, x0.
Definition term76 (a0 : Type') (x0 : nat) := @eq a0 (@EL a0 x0 (@nil a0)).
Definition term79 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) -> (@EL a0 y0 (@list_of_seq a0 x0 (NUMERAL 0))) = (x0 y0).
Definition term95 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @EL a0 x0 (@list_of_seq a0 x1 x2).
Definition term41 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (Peano.lt y1 y2) -> (@EL a0 y1 (@list_of_seq a0 x0 y2)) = (x0 y1)) y0 x1.
Definition term128 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) (x3 : a0) (x4 : a0) := (False -> (@EL a0 x0 (@list_of_seq a0 x1 x2)) = x3) -> ((~ False) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = x4) -> (@COND a0 (Peano.lt x0 x2) (@EL a0 x0 (@list_of_seq a0 x1 x2)) (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0)))) = (@COND a0 False x3 x4).
Definition term87 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.app a0 (@list_of_seq a0 x0 x1) (@cons a0 (x0 x1) (@nil a0)).
Definition term94 (a0 : Type') (x0 : nat) (x1 : nat) := @COND a0 (Peano.lt x0 x1).
Definition term146 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := (~ True) -> (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))) = (@EL a0 (Nat.sub x0 x2) (@cons a0 (x1 x2) (@nil a0))).
Definition term70 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y2 y1) -> (@EL a0 y2 (@list_of_seq a0 x0 y1)) = (x0 y2)) y0.
Definition term116 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term32 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := (Peano.lt x2 x0) -> (@EL a0 x2 (@list_of_seq a0 x1 x0)) = (x1 x2).
Definition term46 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (@EL a0 y1 (@list_of_seq a0 x0 y0)) = (x0 y1).
Definition term37 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> (@EL a0 y0 (@list_of_seq a0 x0 y1)) = (x0 y0).
Definition term96 (a0 : Type') (x0 : nat) (x1 : nat -> a0) (x2 : nat) := @COND a0 (Peano.lt x0 (@List.length a0 (@list_of_seq a0 x1 x2))) (@EL a0 x0 (@list_of_seq a0 x1 x2)).
Definition term60 (a0 : Type') (x0 : nat) (x1 : nat -> a0) := (forall y0 : nat, (Peano.lt y0 x0) -> (@EL a0 y0 (@list_of_seq a0 x1 x0)) = (x1 y0)) -> forall y0 : nat, (Peano.lt y0 (S x0)) -> (@EL a0 y0 (@list_of_seq a0 x1 (S x0))) = (x1 y0).
