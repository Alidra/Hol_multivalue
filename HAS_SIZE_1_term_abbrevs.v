Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term70 := (~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False.
Definition term112 := (~ False) -> (S (@CARD unit (@EMPTY unit))) = (NUMERAL (BIT1 0)).
Definition term102 (x0 : Prop) (x1 : nat) := forall y0 : nat, ((@IN unit tt (@EMPTY unit)) = x0) -> (x0 -> (@CARD unit (@EMPTY unit)) = x1) -> ((~ x0) -> (S (@CARD unit (@EMPTY unit))) = y0) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat x0 x1 y0).
Definition term105 (x0 : nat) (x1 : nat) := ((@IN unit tt (@EMPTY unit)) = False) -> (False -> (@CARD unit (@EMPTY unit)) = x0) -> ((~ False) -> (S (@CARD unit (@EMPTY unit))) = x1) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat False x0 x1).
Definition term1 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term0 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term4 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term2 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term57 := @HAS_SIZE unit (@UNIV unit) (NUMERAL (BIT1 0)).
Definition term22 (x0 : nat) := NUMERAL (S x0).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @CARD a0 (@INSERT a0 x0 x1).
Definition term110 := S (NUMERAL 0).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term67 (x0 : Prop) := (~ x0) -> False.
Definition term8 := (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)).
Definition term81 := (@FINITE unit (@INSERT unit tt (@EMPTY unit))) /\ ((@CARD unit (@INSERT unit tt (@EMPTY unit))) = (NUMERAL (BIT1 0))).
Definition term15 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term11 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0)))) x1.
Definition term78 := @eq Prop ((fun y0 : Prop => y0 = True) ((~ (forall y0 : unit, y0 = tt)) -> ~ (forall y0 : unit, y0 = tt))).
Definition term93 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term106 (x0 : nat) (x1 : nat) := (False -> (@CARD unit (@EMPTY unit)) = x0) -> ((~ False) -> (S (@CARD unit (@EMPTY unit))) = x1) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat False x0 x1).
Definition term88 (x0 : unit) (x1 : unit -> Prop) := (@FINITE unit x1) -> (@CARD unit (@INSERT unit x0 x1)) = (@COND nat (@IN unit x0 x1) (@CARD unit x1) (S (@CARD unit x1))).
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@CARD a0 (@INSERT a0 x0 x1)) = (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))).
Definition term61 (x0 : unit) := @eq Prop (@IN unit x0 (@UNIV unit)).
Definition term99 (x0 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN unit tt (@EMPTY unit)) = y0) -> (y0 -> (@CARD unit (@EMPTY unit)) = y1) -> ((~ y0) -> (S (@CARD unit (@EMPTY unit))) = y2) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat y0 y1 y2)) x0.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term59 (x0 : unit -> Prop) (x1 : unit -> Prop) := forall y0 : unit, (@IN unit y0 x0) = (@IN unit y0 x1).
Definition term98 := S (@CARD unit (@EMPTY unit)).
Definition term53 := (fun y0 : unit -> Prop => @HAS_SIZE unit y0 (NUMERAL (BIT1 0))) (@UNIV unit).
Definition term18 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term24 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))) x0.
Definition term91 := @COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit))).
Definition term43 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term21 (x0 : nat) := S (NUMERAL x0).
Definition term32 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0).
Definition term20 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term54 := (fun y0 : unit -> Prop => @HAS_SIZE unit y0 (NUMERAL (BIT1 0))) (@INSERT unit tt (@EMPTY unit)).
Definition term69 := ~ (forall y0 : unit, y0 = tt).
Definition term101 (x0 : Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN unit tt (@EMPTY unit)) = x0) -> (x0 -> (@CARD unit (@EMPTY unit)) = y0) -> ((~ x0) -> (S (@CARD unit (@EMPTY unit))) = y1) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat x0 y0 y1)) x1.
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a0 (@INSERT a0 x0 x1).
Definition term87 := and (@FINITE unit (@INSERT unit tt (@EMPTY unit))).
Definition term6 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))).
Definition term79 := @eq Prop (((~ (forall y0 : unit, y0 = tt)) -> ~ (forall y0 : unit, y0 = tt)) = True).
Definition term74 := (forall y0 : unit, y0 = tt) -> False.
Definition term66 := forall y0 : unit, y0 = tt.
Definition term85 := (@FINITE unit (@EMPTY unit)) -> (@FINITE unit (@INSERT unit tt (@EMPTY unit))) = True.
Definition term107 := False -> (@CARD unit (@EMPTY unit)) = (NUMERAL 0).
Definition term90 := @CARD unit (@INSERT unit tt (@EMPTY unit)).
Definition term7 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))).
Definition term111 := NUMERAL (S 0).
Definition term72 := (((~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False) -> (~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False) -> (~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False.
Definition term47 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term104 (x0 : Prop) (x1 : nat) (x2 : nat) := ((@IN unit tt (@EMPTY unit)) = x0) -> (x0 -> (@CARD unit (@EMPTY unit)) = x1) -> ((~ x0) -> (S (@CARD unit (@EMPTY unit))) = x2) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat x0 x1 x2).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term62 (x0 : unit) (x1 : unit) := @IN unit x0 (@INSERT unit x1 (@EMPTY unit)).
Definition term25 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term64 := fun y0 : unit => (@IN unit y0 (@UNIV unit)) = (@IN unit y0 (@INSERT unit tt (@EMPTY unit))).
Definition term100 (x0 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN unit tt (@EMPTY unit)) = x0) -> (x0 -> (@CARD unit (@EMPTY unit)) = y0) -> ((~ x0) -> (S (@CARD unit (@EMPTY unit))) = y1) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat x0 y0 y1).
Definition term13 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term9 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1)).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term68 := (~ (forall y0 : unit, y0 = tt)) -> False.
Definition term86 := @FINITE unit (@INSERT unit tt (@EMPTY unit)).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0)) x1.
Definition term80 (x0 : unit -> Prop) (x1 : nat) := (@FINITE unit x0) /\ ((@CARD unit x0) = x1).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term97 := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN unit tt (@EMPTY unit)) = y0) -> (y0 -> (@CARD unit (@EMPTY unit)) = y1) -> ((~ y0) -> (S (@CARD unit (@EMPTY unit))) = y2) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat y0 y1 y2).
Definition term96 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term95 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term56 := @eq Prop ((fun y0 : unit -> Prop => @HAS_SIZE unit y0 (NUMERAL (BIT1 0))) (@UNIV unit)).
Definition term103 (x0 : Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((@IN unit tt (@EMPTY unit)) = x0) -> (x0 -> (@CARD unit (@EMPTY unit)) = x1) -> ((~ x0) -> (S (@CARD unit (@EMPTY unit))) = y0) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat x0 x1 y0)) x2.
Definition term89 := (@FINITE unit (@EMPTY unit)) -> (@CARD unit (@INSERT unit tt (@EMPTY unit))) = (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))).
Definition term84 (x0 : unit) (x1 : unit -> Prop) := (@FINITE unit x1) -> (@FINITE unit (@INSERT unit x0 x1)) = True.
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE a0 (@INSERT a0 x0 x1)) = True.
Definition term109 (x0 : nat) := ((~ False) -> (S (@CARD unit (@EMPTY unit))) = x0) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat False (NUMERAL 0) x0).
Definition term77 := (fun y0 : Prop => y0 = True) ((~ (forall y0 : unit, y0 = tt)) -> ~ (forall y0 : unit, y0 = tt)).
Definition term116 := @eq nat (NUMERAL (BIT1 0)).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)) x0.
Definition term19 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term31 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)) x0.
Definition term94 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term58 := @eq Prop (@HAS_SIZE unit (@UNIV unit) (NUMERAL (BIT1 0))).
Definition term65 := fun y0 : unit => y0 = tt.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term44 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term55 := @HAS_SIZE unit (@INSERT unit tt (@EMPTY unit)) (NUMERAL (BIT1 0)).
Definition term76 := (~ (forall y0 : unit, y0 = tt)) -> ~ (forall y0 : unit, y0 = tt).
Definition term113 := ((~ False) -> (S (@CARD unit (@EMPTY unit))) = (NUMERAL (BIT1 0))) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat False (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term115 := @eq nat (@CARD unit (@INSERT unit tt (@EMPTY unit))).
Definition term42 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term108 (x0 : nat) := (False -> (@CARD unit (@EMPTY unit)) = (NUMERAL 0)) -> ((~ False) -> (S (@CARD unit (@EMPTY unit))) = x0) -> (@COND nat (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) (S (@CARD unit (@EMPTY unit)))) = (@COND nat False (NUMERAL 0) x0).
Definition term3 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term17 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term63 (x0 : unit) := @IN unit x0 (@INSERT unit tt (@EMPTY unit)).
Definition term60 := forall y0 : unit, (@IN unit y0 (@UNIV unit)) = (@IN unit y0 (@INSERT unit tt (@EMPTY unit))).
Definition term71 := ((~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False) -> (~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term114 := @COND nat False (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term73 := (((~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False) -> (~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False) -> ((~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False) -> (~ (forall y0 : unit, y0 = tt)) -> (forall y0 : unit, y0 = tt) -> False.
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((BIT1 x0) = (BIT1 y0)) = (x0 = y0)) x1.
Definition term30 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1).
Definition term23 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term92 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term52 := fun y0 : unit -> Prop => @HAS_SIZE unit y0 (NUMERAL (BIT1 0)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term5 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term82 := NUMERAL (BIT1 0).
Definition term75 := imp (~ (forall y0 : unit, y0 = tt)).
Definition term40 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
