Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (a0 : Type') (x0 : a0) (x1 : list a0) := ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) x1) -> (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) (@cons a0 x0 x1).
Definition term65 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.length a0 (@tl a0 (@cons a0 x0 x1)).
Definition term52 (a0 : Type') := ~ ((@nil a0) = (@nil a0)).
Definition term25 (a0 : Type') := (~ ((@nil a0) = (@nil a0))) -> (@List.length a0 (@tl a0 (@nil a0))) = (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))).
Definition term41 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 y0 y1))) = (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))).
Definition term71 (a0 : Type') (x0 : list a0) := Nat.sub (S (@List.length a0 x0)) (NUMERAL (BIT1 0)).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.sub x0 y0))) x1.
Definition term19 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.length a0 (@cons a0 x0 x1).
Definition term46 (a0 : Type') := imp (((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) (@cons a0 y0 y1))).
Definition term3 := ((Nat.sub 0 0) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)))))))))).
Definition term66 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq nat (@List.length a0 (@tl a0 (@cons a0 x0 x1))).
Definition term22 (a0 : Type') := (((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) y0.
Definition term21 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term17 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0)).
Definition term36 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) y0) -> (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) (@cons a0 x0 y0).
Definition term20 (a0 : Type') (x0 : list a0) := S (@List.length a0 x0).
Definition term29 (a0 : Type') (x0 : list a0) := (~ (x0 = (@nil a0))) -> (@List.length a0 (@tl a0 x0)) = (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))).
Definition term0 (x0 : nat) := (fun y0 : nat => (Nat.sub (S y0) (NUMERAL (BIT1 0))) = y0) x0.
Definition term48 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) y0.
Definition term31 (a0 : Type') (x0 : list a0) := imp ((~ (x0 = (@nil a0))) -> (@List.length a0 (@tl a0 x0)) = (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0)))).
Definition term54 (a0 : Type') := Nat.sub (@List.length a0 (@nil a0)).
Definition term40 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) (@cons a0 y0 y1).
Definition term1 (x0 : nat) := Nat.sub (S x0) (NUMERAL (BIT1 0)).
Definition term33 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 x0 x1))) = (Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0))).
Definition term28 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) x0.
Definition term70 (a0 : Type') (x0 : a0) (x1 : list a0) := Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0)).
Definition term59 := NUMERAL (Nat.sub 0 (BIT1 0)).
Definition term73 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> True.
Definition term64 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term58 := Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.sub (NUMERAL x0) (NUMERAL y0)) = (NUMERAL (Nat.sub x0 y0)).
Definition term37 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 x0 y0) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 x0 y0))) = (Nat.sub (@List.length a0 (@cons a0 x0 y0)) (NUMERAL (BIT1 0))).
Definition term35 (a0 : Type') (x0 : a0) (x1 : list a0) := ((~ (x1 = (@nil a0))) -> (@List.length a0 (@tl a0 x1)) = (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 x0 x1) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 x0 x1))) = (Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0))).
Definition term62 (a0 : Type') := @List.length a0 (@tl a0 (@nil a0)).
Definition term14 (x0 : nat) (x1 : nat) := NUMERAL (Nat.sub x0 x1).
Definition term6 := forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0.
Definition term38 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) y0) -> (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) (@cons a0 x0 y0).
Definition term16 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1))) x0.
Definition term9 := forall y0 : nat, forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1)).
Definition term23 (a0 : Type') := fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))).
Definition term60 := Nat.sub 0 (BIT1 0).
Definition term26 (a0 : Type') := and ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) (@nil a0)).
Definition term39 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 x0 y0) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 x0 y0))) = (Nat.sub (@List.length a0 (@cons a0 x0 y0)) (NUMERAL (BIT1 0))).
Definition term18 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0))) x1.
Definition term27 (a0 : Type') := and ((~ ((@nil a0) = (@nil a0))) -> (@List.length a0 (@tl a0 (@nil a0))) = (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0)))).
Definition term61 (a0 : Type') := @eq nat (@List.length a0 (@tl a0 (@nil a0))).
Definition term53 (a0 : Type') := imp (~ ((@nil a0) = (@nil a0))).
Definition term69 (a0 : Type') (x0 : list a0) := Nat.sub (S (@List.length a0 x0)).
Definition term51 (a0 : Type') := (((~ ((@nil a0) = (@nil a0))) -> (@List.length a0 (@tl a0 (@nil a0))) = (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0)))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 y0 y1))) = (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))))) -> forall y0 : list a0, (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))).
Definition term7 (x0 : nat) := (fun y0 : nat => (Nat.sub 0 (BIT1 y0)) = 0) x0.
Definition term74 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@cons a0 x0 x1) = (@nil a0)).
Definition term55 := Nat.sub (NUMERAL 0).
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1))) x0.
Definition term57 (a0 : Type') := Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0)).
Definition term68 (a0 : Type') (x0 : a0) (x1 : list a0) := Nat.sub (@List.length a0 (@cons a0 x0 x1)).
Definition term67 (a0 : Type') (x0 : list a0) := @eq nat (@List.length a0 x0).
Definition term63 (a0 : Type') := False -> (@List.length a0 (@tl a0 (@nil a0))) = (NUMERAL 0).
Definition term24 (a0 : Type') := (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) (@nil a0).
Definition term47 (a0 : Type') := imp (((~ ((@nil a0) = (@nil a0))) -> (@List.length a0 (@tl a0 (@nil a0))) = (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0)))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 y0 y1))) = (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))))).
Definition term72 (a0 : Type') (x0 : a0) (x1 : list a0) := imp (~ ((@cons a0 x0 x1) = (@nil a0))).
Definition term30 (a0 : Type') (x0 : list a0) := imp ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) x0).
Definition term5 := (forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)))))))).
Definition term4 := (forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))))))).
Definition term13 (x0 : nat) (x1 : nat) := Nat.sub (NUMERAL x0) (NUMERAL x1).
Definition term8 (x0 : nat) := Nat.sub 0 (BIT1 x0).
Definition term2 := (forall y0 : nat, forall y1 : nat, (Nat.sub (NUMERAL y0) (NUMERAL y1)) = (NUMERAL (Nat.sub y0 y1))) /\ (((Nat.sub 0 0) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT0 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub 0 (BIT1 y0)) = 0) /\ ((forall y0 : nat, (Nat.sub (BIT0 y0) 0) = (BIT0 y0)) /\ ((forall y0 : nat, (Nat.sub (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))))))))).
Definition term49 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) y0.
Definition term43 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 y0 y1))) = (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))).
Definition term42 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) (@cons a0 y0 y1).
Definition term15 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1)).
Definition term32 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) (@cons a0 x0 x1).
Definition term56 := NUMERAL (BIT1 0).
Definition term44 (a0 : Type') := ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0)))) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@List.length a0 (@tl a0 y2)) = (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0)))) (@cons a0 y0 y1)).
Definition term45 (a0 : Type') := ((~ ((@nil a0) = (@nil a0))) -> (@List.length a0 (@tl a0 (@nil a0))) = (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0)))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@List.length a0 (@tl a0 y1)) = (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0)))) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@List.length a0 (@tl a0 (@cons a0 y0 y1))) = (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0)))).
Definition term50 (a0 : Type') := forall y0 : list a0, (~ (y0 = (@nil a0))) -> (@List.length a0 (@tl a0 y0)) = (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))).
