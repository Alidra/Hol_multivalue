Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term118 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term49 := forall y0 : nat, (@IN nat y0 (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii)))) = (@IN nat y0 (@UNIV nat)).
Definition term99 (x0 : nat -> Prop) := ~ (all x0).
Definition term146 := (~ False) -> False.
Definition term58 (x0 : nat) := fun y0 : list Ascii.ascii => x0 = (@List.length Ascii.ascii y0).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term106 := exists y0 : nat, forall y1 : list Ascii.ascii, ~ (y0 = (@List.length Ascii.ascii y1)).
Definition term132 (x0 : Prop) := ~ (~ x0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := forall y0 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1)).
Definition term64 := forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1).
Definition term85 (a0 : Type') (x0 : nat) := fun y0 : a0 => (@List.length a0 (@repeat_with_perm_args a0 x0 y0)) = x0.
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term27 (x0 : Prop) := forall y0 : Prop, ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term65 (x0 : Prop) := (~ x0) -> False.
Definition term35 := imp (~ (@FINITE nat (@UNIV nat))).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term97 (x0 : nat) := fun y0 : list Ascii.ascii => ~ (x0 = (@List.length Ascii.ascii y0)).
Definition term141 (x0 : nat) (x1 : Ascii.ascii) := (((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)) = x0) /\ ((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)) = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)))) -> x0 = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)).
Definition term23 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> a1, @FINITE a1 (@IMAGE a0 a1 y1 y0).
Definition term47 := ((@FINITE nat (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii)))) = (@FINITE nat (@UNIV nat))) -> (@FINITE nat (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii)))) -> @FINITE nat (@UNIV nat).
Definition term125 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term135 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : a0 -> Prop, forall y2 : a0 -> a1, (@IN a1 y0 (@IMAGE a0 a1 y2 y1)) = (exists y3 : a0, (y0 = (y2 y3)) /\ (@IN a0 y3 y1))) x0.
Definition term57 (x0 : nat) := fun y0 : list Ascii.ascii => (x0 = (@List.length Ascii.ascii y0)) /\ (@IN (list Ascii.ascii) y0 (@UNIV (list Ascii.ascii))).
Definition term74 := ~ (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0).
Definition term67 := ~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term48 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) = (@IN nat y0 x1).
Definition term113 (x0 : Prop) := (~ x0) -> x0.
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term70 (a0 : Type') := ((~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False) -> (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False.
Definition term38 := (@INFINITE nat (@UNIV nat)) -> @INFINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii)).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term129 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term41 (a0 : Type') (x0 : type1156) := (@FINITE (list Ascii.ascii) x0) -> forall y0 : type1155 a0, @FINITE a0 (@IMAGE (list Ascii.ascii) a0 y0 x0).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> forall y0 : a0 -> a1, @FINITE a1 (@IMAGE a0 a1 y0 x0).
Definition term144 (x0 : nat) (x1 : list Ascii.ascii) := (x0 = (@List.length Ascii.ascii x1)) -> False.
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a1 (@IMAGE a0 a1 x0 y0).
Definition term26 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0)) x0.
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term76 (a0 : Type') := (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False.
Definition term102 (x0 : nat) := (fun y0 : nat => exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1)) x0.
Definition term92 (x0 : nat) := forall y0 : list Ascii.ascii, ~ ((fun y1 : list Ascii.ascii => x0 = (@List.length Ascii.ascii y1)) y0).
Definition term121 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term79 (a0 : Type') := (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> ~ (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0))) x1.
Definition term60 (x0 : nat) := @eq Prop (@IN nat x0 (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii)))).
Definition term29 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term55 (x0 : nat) (x1 : list Ascii.ascii) := (x0 = (@List.length Ascii.ascii x1)) /\ (@IN (list Ascii.ascii) x1 (@UNIV (list Ascii.ascii))).
Definition term63 := fun y0 : nat => exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1).
Definition term36 (x0 : type1156) := ~ (@FINITE (list Ascii.ascii) x0).
Definition term32 (x0 : nat -> Prop) := ~ (@FINITE nat x0).
Definition term87 (a0 : Type') := fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0.
Definition term111 (x0 : Ascii.ascii) (x1 : nat) := (~ ((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x1 x0)) = x1)) -> (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x1 x0)) = x1.
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := @IN a1 x0 (@IMAGE a0 a1 x1 x2).
Definition term14 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> (x0 = x1) -> x0 -> x1.
Definition term105 := fun y0 : nat => forall y1 : list Ascii.ascii, ~ (y0 = (@List.length Ascii.ascii y1)).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term73 := (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False.
Definition term44 := forall y0 : type1157, @FINITE nat (@IMAGE (list Ascii.ascii) nat y0 (@UNIV (list Ascii.ascii))).
Definition term43 (a0 : Type') := forall y0 : type1155 a0, @FINITE a0 (@IMAGE (list Ascii.ascii) a0 y0 (@UNIV (list Ascii.ascii))).
Definition term82 (x0 : nat) := forall y0 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 y0)) = x0.
Definition term83 := fun y0 : nat => forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0.
Definition term145 (x0 : nat) (x1 : Ascii.ascii) := (x0 = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1))) -> False.
Definition term7 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term95 (x0 : nat) (x1 : list Ascii.ascii) := ~ (x0 = (@List.length Ascii.ascii x1)).
Definition term80 (x0 : nat) (x1 : Ascii.ascii) := @List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> forall y1 : a0 -> a1, @FINITE a1 (@IMAGE a0 a1 y1 y0)) x0.
Definition term128 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term88 (a0 : Type') := forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0.
Definition term68 := forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0.
Definition term12 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 -> x1.
Definition term143 (x0 : nat) (x1 : Ascii.ascii) := ~ (x0 = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1))).
Definition term89 (x0 : type1156) := ~ (ex x0).
Definition term40 := (@FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) -> @FINITE nat (@UNIV nat).
Definition term71 (a0 : Type') := (((~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False) -> (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False) -> (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False.
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, @FINITE a1 (@IMAGE a0 a1 y0 x0).
Definition term54 (x0 : nat) (x1 : list Ascii.ascii) := and (x0 = (@List.length Ascii.ascii x1)).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term53 (x0 : nat) := exists y0 : list Ascii.ascii, (x0 = (@List.length Ascii.ascii y0)) /\ (@IN (list Ascii.ascii) y0 (@UNIV (list Ascii.ascii))).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term66 := (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> False.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term104 := fun y0 : nat => ~ ((fun y1 : nat => exists y2 : list Ascii.ascii, y1 = (@List.length Ascii.ascii y2)) y0).
Definition term59 (x0 : nat) := exists y0 : list Ascii.ascii, x0 = (@List.length Ascii.ascii y0).
Definition term109 (x0 : nat) (x1 : list Ascii.ascii) := (fun y0 : list Ascii.ascii => ~ (x0 = (@List.length Ascii.ascii y0))) x1.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a1 (@IMAGE a0 a1 x0 y0)) x1.
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term72 (a0 : Type') := (((~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False) -> (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False) -> ((~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False) -> (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False.
Definition term107 (x0 : nat) := (fun y0 : nat => forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) x0.
Definition term134 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term61 (x0 : nat) := @eq Prop (exists y0 : list Ascii.ascii, x0 = (@List.length Ascii.ascii y0)).
Definition term15 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a1 (@IMAGE a0 a1 y0 y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@IN a1 x0 (@IMAGE a0 a1 y1 y0)) = (exists y2 : a0, (x0 = (y1 y2)) /\ (@IN a0 y2 y0)).
Definition term84 (a0 : Type') (x0 : nat) (x1 : a0) := @List.length a0 (@repeat_with_perm_args a0 x0 x1).
Definition term34 := imp (@INFINITE nat (@UNIV nat)).
Definition term50 (x0 : nat) (x1 : type1157) (x2 : type1156) := @IN nat x0 (@IMAGE (list Ascii.ascii) nat x1 x2).
Definition term108 (x0 : nat) (x1 : Ascii.ascii) := (fun y0 : Ascii.ascii => (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 y0)) = x0) x1.
Definition term98 (x0 : nat) := forall y0 : list Ascii.ascii, ~ (x0 = (@List.length Ascii.ascii y0)).
Definition term103 (x0 : nat) := ~ ((fun y0 : nat => exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1)) x0).
Definition term56 (x0 : nat) (x1 : list Ascii.ascii) := (x0 = (@List.length Ascii.ascii x1)) /\ True.
Definition term52 (x0 : nat) := @IN nat x0 (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))).
Definition term51 (x0 : nat) (x1 : type1157) (x2 : type1156) := exists y0 : list Ascii.ascii, (x0 = (x1 y0)) /\ (@IN (list Ascii.ascii) y0 x2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> Prop) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => (@IN a1 x0 (@IMAGE a0 a1 y0 x1)) = (exists y1 : a0, (x0 = (y0 y1)) /\ (@IN a0 y1 x1))) x2.
Definition term93 (x0 : nat) (x1 : list Ascii.ascii) := (fun y0 : list Ascii.ascii => x0 = (@List.length Ascii.ascii y0)) x1.
Definition term90 (x0 : type1156) := forall y0 : list Ascii.ascii, ~ (x0 y0).
Definition term81 (x0 : nat) := fun y0 : Ascii.ascii => (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 y0)) = x0.
Definition term142 (x0 : nat) (x1 : Ascii.ascii) := (~ (x0 = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)))) -> x0 = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)).
Definition term112 (x0 : Ascii.ascii) (x1 : nat) := ~ ((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x1 x0)) = x1).
Definition term86 (a0 : Type') (x0 : nat) := forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 x0 y0)) = x0.
Definition term46 := @FINITE nat (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))).
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term62 := fun y0 : nat => (@IN nat y0 (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii)))) = (@IN nat y0 (@UNIV nat)).
Definition term101 := exists y0 : nat, ~ ((fun y1 : nat => exists y2 : list Ascii.ascii, y1 = (@List.length Ascii.ascii y2)) y0).
Definition term37 := ~ (@FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))).
Definition term33 := ~ (@FINITE nat (@UNIV nat)).
Definition term28 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ x0) -> ~ y0) = (y0 -> x0)) x1.
Definition term42 (a0 : Type') := (@FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) -> forall y0 : type1155 a0, @FINITE a0 (@IMAGE (list Ascii.ascii) a0 y0 (@UNIV (list Ascii.ascii))).
Definition term77 (a0 : Type') := (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> ~ (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0).
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term94 (x0 : nat) (x1 : list Ascii.ascii) := ~ ((fun y0 : list Ascii.ascii => x0 = (@List.length Ascii.ascii y0)) x1).
Definition term24 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a1 (@IMAGE a0 a1 y0 y1)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> a1, @FINITE a1 (@IMAGE a0 a1 y1 y0).
Definition term114 (x0 : nat) (x1 : Ascii.ascii) := (~ ((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)) = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)))) -> (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)) = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)).
Definition term140 (x0 : nat) (x1 : Ascii.ascii) := ((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)) = x0) /\ ((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)) = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) (x2 : a0 -> Prop) := exists y0 : a0, (x0 = (x1 y0)) /\ (@IN a0 y0 x2).
Definition term13 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> x0 -> x1.
Definition term115 (x0 : nat) (x1 : Ascii.ascii) := ~ ((@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1)) = (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii x0 x1))).
Definition term39 := (~ (@FINITE nat (@UNIV nat))) -> ~ (@FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term133 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a1 (@IMAGE a0 a1 y0 y1)) x0.
Definition term147 := (@FINITE nat (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii)))) -> @FINITE nat (@UNIV nat).
Definition term119 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term91 (x0 : nat) := ~ (exists y0 : list Ascii.ascii, x0 = (@List.length Ascii.ascii y0)).
Definition term96 (x0 : nat) := fun y0 : list Ascii.ascii => ~ ((fun y1 : list Ascii.ascii => x0 = (@List.length Ascii.ascii y1)) y0).
Definition term75 (a0 : Type') := imp (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INFINITE a0 y0) = (~ (@FINITE a0 y0))) x0.
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term69 (a0 : Type') := (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))) -> (forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> (forall y0 : nat, forall y1 : Ascii.ascii, (@List.length Ascii.ascii (@repeat_with_perm_args Ascii.ascii y0 y1)) = y0) -> False.
Definition term100 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term45 := (fun y0 : type1157 => @FINITE nat (@IMAGE (list Ascii.ascii) nat y0 (@UNIV (list Ascii.ascii)))) (@List.length Ascii.ascii).
Definition term78 := imp (~ (forall y0 : nat, exists y1 : list Ascii.ascii, y0 = (@List.length Ascii.ascii y1))).
