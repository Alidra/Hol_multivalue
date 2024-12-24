Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term152 := (~ True) -> (S (@CARD Prop (@EMPTY Prop))) = (NUMERAL (BIT1 0)).
Definition term1 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term172 := ((~ False) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = (NUMERAL (BIT0 (BIT1 0)))) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat False (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term97 (x0 : Prop) := @eq Prop ((~ x0) \/ (x0 \/ (@IN Prop x0 (@EMPTY Prop)))).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 (@INSERT a0 y1 y0)) = (@FINITE a0 y0)) x0.
Definition term100 := or (~ True).
Definition term56 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term163 := (~ False) -> (S (@CARD Prop (@EMPTY Prop))) = (NUMERAL (BIT1 0)).
Definition term98 := (fun y0 : Prop => (~ y0) \/ (y0 \/ (@IN Prop y0 (@EMPTY Prop)))) False.
Definition term141 (x0 : Prop) (x1 : nat) := forall y0 : nat, ((@IN Prop True (@EMPTY Prop)) = x0) -> (x0 -> (@CARD Prop (@EMPTY Prop)) = x1) -> ((~ x0) -> (S (@CARD Prop (@EMPTY Prop))) = y0) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat x0 x1 y0).
Definition term128 (x0 : Prop) (x1 : nat) := forall y0 : nat, ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = x0) -> (x0 -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = x1) -> ((~ x0) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = y0) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat x0 x1 y0).
Definition term124 := S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))).
Definition term158 (x0 : nat) (x1 : nat) := ((@IN Prop True (@EMPTY Prop)) = False) -> (False -> (@CARD Prop (@EMPTY Prop)) = x0) -> ((~ False) -> (S (@CARD Prop (@EMPTY Prop))) = x1) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat False x0 x1).
Definition term8 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term7 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term11 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term9 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term70 := @HAS_SIZE Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop))) (NUMERAL (BIT0 (BIT1 0))).
Definition term96 (x0 : Prop) := @eq Prop ((fun y0 : Prop => (~ y0) \/ (y0 \/ (@IN Prop y0 (@EMPTY Prop)))) x0).
Definition term34 (x0 : nat) := BIT0 (S x0).
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term38 (x0 : nat) := NUMERAL (S x0).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @CARD a0 (@INSERT a0 x0 x1).
Definition term149 := S (NUMERAL 0).
Definition term67 := fun y0 : Prop -> Prop => @HAS_SIZE Prop y0 (NUMERAL (BIT0 (BIT1 0))).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term15 := (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)).
Definition term88 := fun y0 : Prop => (@IN Prop y0 (@UNIV Prop)) = (@IN Prop y0 (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop)))).
Definition term145 (x0 : nat) (x1 : nat) := (True -> (@CARD Prop (@EMPTY Prop)) = x0) -> ((~ True) -> (S (@CARD Prop (@EMPTY Prop))) = x1) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat True x0 x1).
Definition term146 := True -> (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0).
Definition term26 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term22 (x0 : nat) := forall y0 : nat, ((BIT0 x0) = (BIT0 y0)) = (x0 = y0).
Definition term18 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0)))) x1.
Definition term117 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term175 := @eq nat (NUMERAL (BIT0 (BIT1 0))).
Definition term159 (x0 : nat) (x1 : nat) := (False -> (@CARD Prop (@EMPTY Prop)) = x0) -> ((~ False) -> (S (@CARD Prop (@EMPTY Prop))) = x1) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat False x0 x1).
Definition term133 (x0 : nat) (x1 : nat) := (False -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = x0) -> ((~ False) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = x1) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat False x0 x1).
Definition term112 (x0 : Prop) (x1 : Prop -> Prop) := (@FINITE Prop x1) -> (@CARD Prop (@INSERT Prop x0 x1)) = (@COND nat (@IN Prop x0 x1) (@CARD Prop x1) (S (@CARD Prop x1))).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@CARD a0 (@INSERT a0 x0 x1)) = (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))).
Definition term76 (x0 : Prop) := @eq Prop (@IN Prop x0 (@UNIV Prop)).
Definition term138 (x0 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN Prop True (@EMPTY Prop)) = y0) -> (y0 -> (@CARD Prop (@EMPTY Prop)) = y1) -> ((~ y0) -> (S (@CARD Prop (@EMPTY Prop))) = y2) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat y0 y1 y2)) x0.
Definition term125 (x0 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = y0) -> (y0 -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = y1) -> ((~ y0) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = y2) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat y0 y1 y2)) x0.
Definition term54 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@FINITE a0 (@INSERT a0 y0 x0)) = (@FINITE a0 x0)) x1.
Definition term85 (x0 : Prop) := or (x0 = True).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term137 := S (@CARD Prop (@EMPTY Prop)).
Definition term29 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term110 := @FINITE Prop (@INSERT Prop True (@EMPTY Prop)).
Definition term44 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))) x0.
Definition term83 (x0 : Prop) := @IN Prop x0 (@INSERT Prop True (@EMPTY Prop)).
Definition term73 := @eq Prop (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term135 := @COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop))).
Definition term3 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term37 (x0 : nat) := S (NUMERAL x0).
Definition term36 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term94 := (fun y0 : Prop => (~ y0) \/ (y0 \/ (@IN Prop y0 (@EMPTY Prop)))) True.
Definition term102 := or (~ False).
Definition term140 (x0 : Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN Prop True (@EMPTY Prop)) = x0) -> (x0 -> (@CARD Prop (@EMPTY Prop)) = y0) -> ((~ x0) -> (S (@CARD Prop (@EMPTY Prop))) = y1) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat x0 y0 y1)) x1.
Definition term127 (x0 : Prop) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = x0) -> (x0 -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = y0) -> ((~ x0) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = y1) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat x0 y0 y1)) x1.
Definition term32 (x0 : nat) := (fun y0 : nat => (S (BIT1 y0)) = (BIT0 (S y0))) x0.
Definition term13 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))).
Definition term72 := @HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))).
Definition term75 := forall y0 : Prop, (@IN Prop y0 (@UNIV Prop)) = (@IN Prop y0 (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop)))).
Definition term160 := False -> (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0).
Definition term14 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))).
Definition term33 (x0 : nat) := S (BIT1 x0).
Definition term150 := NUMERAL (S 0).
Definition term174 := @eq nat (@CARD Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop)))).
Definition term155 := False -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = (NUMERAL 0).
Definition term169 := BIT0 (S 0).
Definition term131 (x0 : Prop) (x1 : Prop) := @IN Prop x0 (@INSERT Prop x1 (@EMPTY Prop)).
Definition term84 (x0 : Prop) := (x0 = True) \/ (@IN Prop x0 (@EMPTY Prop)).
Definition term61 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term143 (x0 : Prop) (x1 : nat) (x2 : nat) := ((@IN Prop True (@EMPTY Prop)) = x0) -> (x0 -> (@CARD Prop (@EMPTY Prop)) = x1) -> ((~ x0) -> (S (@CARD Prop (@EMPTY Prop))) = x2) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat x0 x1 x2).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term69 := (fun y0 : Prop -> Prop => @HAS_SIZE Prop y0 (NUMERAL (BIT0 (BIT1 0)))) (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop))).
Definition term45 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term139 (x0 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN Prop True (@EMPTY Prop)) = x0) -> (x0 -> (@CARD Prop (@EMPTY Prop)) = y0) -> ((~ x0) -> (S (@CARD Prop (@EMPTY Prop))) = y1) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat x0 y0 y1).
Definition term126 (x0 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = x0) -> (x0 -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = y0) -> ((~ x0) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = y1) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat x0 y0 y1).
Definition term24 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term20 := forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1).
Definition term16 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term79 (x0 : Prop) := @IN Prop x0 (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop))).
Definition term122 := @IN Prop False (@INSERT Prop True (@EMPTY Prop)).
Definition term166 := S (NUMERAL (BIT1 0)).
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term74 (x0 : Prop -> Prop) (x1 : Prop -> Prop) := forall y0 : Prop, (@IN Prop y0 x0) = (@IN Prop y0 x1).
Definition term109 := @FINITE Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop))).
Definition term66 := @INSERT Prop False (@INSERT Prop True (@EMPTY Prop)).
Definition term78 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (x1 = x0) \/ (@IN Prop x1 x2).
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term108 (x0 : Prop) (x1 : Prop -> Prop) := @FINITE Prop (@INSERT Prop x0 x1).
Definition term89 := fun y0 : Prop => (~ y0) \/ (y0 \/ (@IN Prop y0 (@EMPTY Prop))).
Definition term130 (x0 : Prop) (x1 : nat) (x2 : nat) := ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = x0) -> (x0 -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = x1) -> ((~ x0) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = x2) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat x0 x1 x2).
Definition term92 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term31 := forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)).
Definition term105 (x0 : Prop -> Prop) (x1 : nat) := (@FINITE Prop x0) /\ ((@CARD Prop x0) = x1).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term136 := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN Prop True (@EMPTY Prop)) = y0) -> (y0 -> (@CARD Prop (@EMPTY Prop)) = y1) -> ((~ y0) -> (S (@CARD Prop (@EMPTY Prop))) = y2) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat y0 y1 y2).
Definition term121 := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = y0) -> (y0 -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = y1) -> ((~ y0) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = y2) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat y0 y1 y2).
Definition term120 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term119 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term104 := True \/ (@IN Prop False (@EMPTY Prop)).
Definition term68 := (fun y0 : Prop -> Prop => @HAS_SIZE Prop y0 (NUMERAL (BIT0 (BIT1 0)))) (@UNIV Prop).
Definition term107 := NUMERAL (BIT0 (BIT1 0)).
Definition term71 := @eq Prop ((fun y0 : Prop -> Prop => @HAS_SIZE Prop y0 (NUMERAL (BIT0 (BIT1 0)))) (@UNIV Prop)).
Definition term123 := @CARD Prop (@INSERT Prop True (@EMPTY Prop)).
Definition term111 := and (@FINITE Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop)))).
Definition term106 := (@FINITE Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop)))) /\ ((@CARD Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop)))) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term30 := (forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))).
Definition term114 := @CARD Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop))).
Definition term154 := @COND nat True (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term77 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := @IN Prop x0 (@INSERT Prop x1 x2).
Definition term142 (x0 : Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((@IN Prop True (@EMPTY Prop)) = x0) -> (x0 -> (@CARD Prop (@EMPTY Prop)) = x1) -> ((~ x0) -> (S (@CARD Prop (@EMPTY Prop))) = y0) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat x0 x1 y0)) x2.
Definition term129 (x0 : Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = x0) -> (x0 -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = x1) -> ((~ x0) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = y0) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat x0 x1 y0)) x2.
Definition term134 := (@FINITE Prop (@EMPTY Prop)) -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))).
Definition term80 (x0 : Prop) := (x0 = False) \/ (@IN Prop x0 (@INSERT Prop True (@EMPTY Prop))).
Definition term144 (x0 : nat) (x1 : nat) := ((@IN Prop True (@EMPTY Prop)) = True) -> (True -> (@CARD Prop (@EMPTY Prop)) = x0) -> ((~ True) -> (S (@CARD Prop (@EMPTY Prop))) = x1) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat True x0 x1).
Definition term81 (x0 : Prop) := or (x0 = False).
Definition term162 (x0 : nat) := ((~ False) -> (S (@CARD Prop (@EMPTY Prop))) = x0) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat False (NUMERAL 0) x0).
Definition term157 (x0 : nat) := ((~ False) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = x0) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat False (NUMERAL 0) x0).
Definition term148 (x0 : nat) := ((~ True) -> (S (@CARD Prop (@EMPTY Prop))) = x0) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat True (NUMERAL 0) x0).
Definition term115 := @COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))).
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)) x0.
Definition term35 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term101 := True \/ (@IN Prop True (@EMPTY Prop)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term118 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term87 (x0 : Prop) := (~ x0) \/ (x0 \/ (@IN Prop x0 (@EMPTY Prop))).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term4 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term170 := BIT0 (BIT1 0).
Definition term90 := forall y0 : Prop, (~ y0) \/ (y0 \/ (@IN Prop y0 (@EMPTY Prop))).
Definition term99 := (~ False) \/ (False \/ (@IN Prop False (@EMPTY Prop))).
Definition term164 := ((~ False) -> (S (@CARD Prop (@EMPTY Prop))) = (NUMERAL (BIT1 0))) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat False (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term153 := ((~ True) -> (S (@CARD Prop (@EMPTY Prop))) = (NUMERAL (BIT1 0))) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat True (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term168 := S (BIT1 0).
Definition term132 (x0 : nat) (x1 : nat) := ((@IN Prop False (@INSERT Prop True (@EMPTY Prop))) = False) -> (False -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = x0) -> ((~ False) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = x1) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat False x0 x1).
Definition term2 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term171 := (~ False) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = (NUMERAL (BIT0 (BIT1 0))).
Definition term82 (x0 : Prop) := or (~ x0).
Definition term167 := NUMERAL (S (BIT1 0)).
Definition term103 := False \/ (@IN Prop False (@EMPTY Prop)).
Definition term95 := (~ True) \/ (True \/ (@IN Prop True (@EMPTY Prop))).
Definition term161 (x0 : nat) := (False -> (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0)) -> ((~ False) -> (S (@CARD Prop (@EMPTY Prop))) = x0) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat False (NUMERAL 0) x0).
Definition term156 (x0 : nat) := (False -> (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) = (NUMERAL 0)) -> ((~ False) -> (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop)))) = x0) -> (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))) = (@COND nat False (NUMERAL 0) x0).
Definition term10 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term173 := @COND nat False (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term28 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term86 (x0 : Prop) := x0 \/ (@IN Prop x0 (@EMPTY Prop)).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term165 := @COND nat False (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@FINITE a0 (@INSERT a0 y0 x0)) = (@FINITE a0 x0).
Definition term91 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((BIT0 x0) = (BIT0 y0)) = (x0 = y0)) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((BIT1 x0) = (BIT1 y0)) = (x0 = y0)) x1.
Definition term55 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term43 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term116 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term12 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term151 := NUMERAL (BIT1 0).
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term113 := (@FINITE Prop (@INSERT Prop True (@EMPTY Prop))) -> (@CARD Prop (@INSERT Prop False (@INSERT Prop True (@EMPTY Prop)))) = (@COND nat (@IN Prop False (@INSERT Prop True (@EMPTY Prop))) (@CARD Prop (@INSERT Prop True (@EMPTY Prop))) (S (@CARD Prop (@INSERT Prop True (@EMPTY Prop))))).
Definition term93 (x0 : Prop) := (fun y0 : Prop => (~ y0) \/ (y0 \/ (@IN Prop y0 (@EMPTY Prop)))) x0.
Definition term147 (x0 : nat) := (True -> (@CARD Prop (@EMPTY Prop)) = (NUMERAL 0)) -> ((~ True) -> (S (@CARD Prop (@EMPTY Prop))) = x0) -> (@COND nat (@IN Prop True (@EMPTY Prop)) (@CARD Prop (@EMPTY Prop)) (S (@CARD Prop (@EMPTY Prop)))) = (@COND nat True (NUMERAL 0) x0).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
