Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term163 (a0 : Type') (x0 : nat) (x1 : type686 a0) := exists y0 : a0 -> Prop, (@HAS_SIZE a0 y0 (S x0)) /\ (x1 y0).
Definition term1 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> x1 y0.
Definition term53 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@HAS_SIZE a0 x0 x1) /\ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) = (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((forall y3 : a0, (@IN a0 y3 x0) -> @IN Prop (y2 y3) (@UNIV Prop)) /\ (forall y3 : a0, (~ (@IN a0 y3 x0)) -> (y2 y3) = False)) y2))).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((forall y0 : a0, (@IN a0 y0 x1) -> @IN Prop (x2 y0) (@UNIV Prop)) /\ (forall y0 : a0, (~ (@IN a0 y0 x1)) -> (x2 y0) = False)) x2.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 y0) = (y0 y1)) x0.
Definition term245 := True \/ (~ True).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1))) x1.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a1 -> Prop) (x3 : nat) := (@HAS_SIZE a0 x0 x1) /\ (@HAS_SIZE a1 x2 x3).
Definition term152 (x0 : Prop -> Prop) := @HAS_SIZE Prop x0 (NUMERAL (BIT1 0)).
Definition term249 := False \/ (~ False).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @SUBSET a0 y0 x0) x1.
Definition term235 (x0 : Prop) := x0 \/ (~ x0).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x2).
Definition term60 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : type686 a0 => @HAS_SIZE (a0 -> Prop) y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x1) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = False)) y1)).
Definition term59 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : type686 a0 => @HAS_SIZE (a0 -> Prop) y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((forall y1 : a0, (@IN a0 y1 x1) -> @IN Prop (y0 y1) (@UNIV Prop)) /\ (forall y1 : a0, (~ (@IN a0 y1 x1)) -> (y0 y1) = False)) y0.
Definition term246 (x0 : Prop) := @eq Prop ((fun y0 : Prop => y0 \/ (~ y0)) x0).
Definition term203 := fun y0 : Prop => exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 (NUMERAL (BIT1 0))) /\ ((~ (@IN Prop y0 y1)) /\ ((@UNIV Prop) = (@INSERT Prop y0 y1))).
Definition term188 (x0 : Prop) := fun y0 : Prop => exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 (NUMERAL 0)) /\ ((~ (@IN Prop y0 y1)) /\ ((~ (@IN Prop x0 (@INSERT Prop y0 y1))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop y0 y1))))).
Definition term187 (x0 : Prop) := fun y0 : Prop => exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 (NUMERAL 0)) /\ ((~ (@IN Prop y0 y1)) /\ ((fun y2 : Prop -> Prop => (~ (@IN Prop x0 y2)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y2))) (@INSERT Prop y0 y1))).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term194 (x0 : Prop) (x1 : Prop) := fun y0 : Prop -> Prop => (~ (@IN Prop x1 y0)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y0))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y0)))).
Definition term118 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term211 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (~ (@IN Prop x0 (@INSERT Prop x1 (@EMPTY Prop)))) /\ x2.
Definition term209 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) /\ x2.
Definition term217 := fun y0 : Prop => exists y1 : Prop, (~ (y0 = y1)) /\ ((@UNIV Prop) = (@INSERT Prop y0 (@INSERT Prop y1 (@EMPTY Prop)))).
Definition term204 := fun y0 : Prop => exists y1 : Prop, (~ (@IN Prop y1 (@EMPTY Prop))) /\ ((~ (@IN Prop y0 (@INSERT Prop y1 (@EMPTY Prop)))) /\ ((@UNIV Prop) = (@INSERT Prop y0 (@INSERT Prop y1 (@EMPTY Prop))))).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, ((@HAS_SIZE a0 y1 y0) /\ (@HAS_SIZE a1 x0 x2)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y2 : a0 -> a1 => exists y3 : a0 -> a1, @SETSPEC (a0 -> a1) y2 ((forall y4 : a0, (@IN a0 y4 y1) -> @IN a1 (y3 y4) x0) /\ (forall y4 : a0, (~ (@IN a0 y4 y1)) -> (y3 y4) = x1)) y3)) (Nat.pow x2 y0)) x3.
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (@IN a0 x0 x1)).
Definition term197 (x0 : Prop) (x1 : Prop) := fun y0 : Prop -> Prop => (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x1 y1)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y1))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y1))))) y0).
Definition term33 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, forall y1 : a0 -> Prop, forall y2 : a1, forall y3 : nat, forall y4 : nat, ((@HAS_SIZE a0 y1 y4) /\ (@HAS_SIZE a1 y0 y3)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y5 : a0 -> a1 => exists y6 : a0 -> a1, @SETSPEC (a0 -> a1) y5 ((forall y7 : a0, (@IN a0 y7 y1) -> @IN a1 (y6 y7) y0) /\ (forall y7 : a0, (~ (@IN a0 y7 y1)) -> (y6 y7) = y2)) y6)) (Nat.pow y3 y4).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : nat) := forall y0 : a1 -> Prop, forall y1 : nat, forall y2 : a0 -> Prop, ((@HAS_SIZE a0 y2 y1) /\ (@HAS_SIZE a1 y0 x1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y3 : a0 -> a1 => exists y4 : a0 -> a1, @SETSPEC (a0 -> a1) y3 ((forall y5 : a0, (@IN a0 y5 y2) -> @IN a1 (y4 y5) y0) /\ (forall y5 : a0, (~ (@IN a0 y5 y2)) -> (y4 y5) = x0)) y4)) (Nat.pow x1 y1).
Definition term151 := S (NUMERAL 0).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term41 (x0 : Prop) := forall y0 : Prop, ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @HAS_SIZE a0 x0 (S x1).
Definition term236 := fun y0 : Prop => (@IN Prop y0 (@UNIV Prop)) = (@IN Prop y0 (@INSERT Prop True (@INSERT Prop False (@EMPTY Prop)))).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x0) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x0)) -> (y1 y2) = False)) y1.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (forall y3 : a0, (@IN a0 y3 x0) -> @IN Prop (y2 y3) (@UNIV Prop)) /\ (forall y3 : a0, (~ (@IN a0 y3 x0)) -> (y2 y3) = False)) y1) y1.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) y1.
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y3) /\ (@HAS_SIZE a1 x0 y2)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y4 : a0 -> a1 => exists y5 : a0 -> a1, @SETSPEC (a0 -> a1) y4 ((forall y6 : a0, (@IN a0 y6 y0) -> @IN a1 (y5 y6) x0) /\ (forall y6 : a0, (~ (@IN a0 y6 y0)) -> (y5 y6) = y1)) y5)) (Nat.pow y2 y3)) x1.
Definition term207 (x0 : Prop) (x1 : Prop) := (~ (@IN Prop x0 (@EMPTY Prop))) /\ x1.
Definition term206 (a0 : Type') (x0 : a0) (x1 : Prop) := (~ (@IN a0 x0 (@EMPTY a0))) /\ x1.
Definition term117 (a0 : Type') := forall y0 : a0, True.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : nat, forall y2 : a1 -> Prop, forall y3 : nat, forall y4 : a0 -> Prop, ((@HAS_SIZE a0 y4 y3) /\ (@HAS_SIZE a1 y2 y1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y5 : a0 -> a1 => exists y6 : a0 -> a1, @SETSPEC (a0 -> a1) y5 ((forall y7 : a0, (@IN a0 y7 y4) -> @IN a1 (y6 y7) y2) /\ (forall y7 : a0, (~ (@IN a0 y7 y4)) -> (y6 y7) = y0)) y6)) (Nat.pow y1 y3)) x0.
Definition term132 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term224 (x0 : Prop) := @eq Prop (@IN Prop x0 (@UNIV Prop)).
Definition term3 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2))) x0.
Definition term229 (x0 : Prop) := or (x0 = True).
Definition term219 := ~ (True = False).
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 x1) y0.
Definition term160 (x0 : Prop) := fun y0 : Prop -> Prop => (@HAS_SIZE Prop y0 (S (NUMERAL 0))) /\ ((~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))).
Definition term159 (x0 : Prop) := fun y0 : Prop -> Prop => (@HAS_SIZE Prop y0 (NUMERAL (BIT1 0))) /\ ((~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))).
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@HAS_SIZE a0 x0 x1) -> @HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term165 (x0 : nat) (x1 : type920) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (S x0)) /\ (x1 y0).
Definition term184 (x0 : Prop) (x1 : Prop) := fun y0 : Prop -> Prop => (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((~ (@IN Prop x1 y0)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y0))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y0))))).
Definition term190 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, (@HAS_SIZE a0 y0 (NUMERAL 0)) /\ (x0 y0).
Definition term40 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0)) x0.
Definition term200 (x0 : Prop) (x1 : Prop) := (~ (@IN Prop x1 (@EMPTY Prop))) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 (@EMPTY Prop)))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 (@EMPTY Prop))))).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and (@HAS_SIZE a0 x0 x1).
Definition term170 (x0 : Prop) (x1 : Prop -> Prop) := (fun y0 : Prop -> Prop => (~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))) x1.
Definition term231 (x0 : Prop) := (x0 = False) \/ (@IN Prop x0 (@EMPTY Prop)).
Definition term186 (x0 : Prop) (x1 : Prop) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((~ (@IN Prop x1 y0)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y0))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y0))))).
Definition term162 (x0 : Prop) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (S (NUMERAL 0))) /\ ((~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))).
Definition term161 (x0 : Prop) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (NUMERAL (BIT1 0))) /\ ((~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))).
Definition term153 (x0 : Prop -> Prop) := @HAS_SIZE Prop x0 (S (NUMERAL 0)).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (@HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term183 (x0 : Prop) (x1 : Prop) := fun y0 : Prop -> Prop => (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((~ (@IN Prop x1 y0)) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x0 y1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y1))) (@INSERT Prop x1 y0))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => (forall y2 : a0, (@IN a0 y2 x1) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = False)) y0) y0.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) y0.
Definition term129 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) = (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 ((forall y3 : a0, (@IN a0 y3 x0) -> @IN Prop (y2 y3) (@UNIV Prop)) /\ (forall y3 : a0, (~ (@IN a0 y3 x0)) -> (y2 y3) = False)) y2))).
Definition term180 (x0 : Prop -> Prop) := and (@HAS_SIZE Prop x0 (NUMERAL 0)).
Definition term43 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) -> ~ (x1 x2).
Definition term208 (x0 : Prop) (x1 : Prop) := (~ (@IN Prop x0 (@INSERT Prop x1 (@EMPTY Prop)))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 (@EMPTY Prop)))).
Definition term193 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop -> Prop => (~ (@IN Prop x1 y0)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y0))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y0))))) (@EMPTY Prop).
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) = (@IN (a0 -> Prop) y0 x1).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) := (fun y0 : a1 => forall y1 : nat, forall y2 : nat, ((@HAS_SIZE a0 x1 y2) /\ (@HAS_SIZE a1 x0 y1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y3 : a0 -> a1 => exists y4 : a0 -> a1, @SETSPEC (a0 -> a1) y3 ((forall y5 : a0, (@IN a0 y5 x1) -> @IN a1 (y4 y5) x0) /\ (forall y5 : a0, (~ (@IN a0 y5 x1)) -> (y4 y5) = y0)) y4)) (Nat.pow y1 y2)) x2.
Definition term137 := @HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))).
Definition term210 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ (x0 = x1)) /\ x2.
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (@IN a0 y0 x0)) -> (x1 y0) = False.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : nat) (x2 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : nat, forall y2 : a0 -> Prop, ((@HAS_SIZE a0 y2 y1) /\ (@HAS_SIZE a1 y0 x1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y3 : a0 -> a1 => exists y4 : a0 -> a1, @SETSPEC (a0 -> a1) y3 ((forall y5 : a0, (@IN a0 y5 y2) -> @IN a1 (y4 y5) y0) /\ (forall y5 : a0, (~ (@IN a0 y5 y2)) -> (y4 y5) = x0)) y4)) (Nat.pow x1 y1)) x2.
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) = (x0 y0)) x1.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => (forall y2 : a0, (@IN a0 y2 x1) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = False)) y0) y0.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) y0.
Definition term223 := forall y0 : Prop, (@IN Prop y0 (@UNIV Prop)) = (@IN Prop y0 (@INSERT Prop True (@INSERT Prop False (@EMPTY Prop)))).
Definition term195 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (fun y0 : Prop -> Prop => (~ (@IN Prop x1 y0)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y0))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y0))))) x2.
Definition term243 (x0 : Prop) := (fun y0 : Prop => y0 \/ (~ y0)) x0.
Definition term253 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) -> @HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term214 (x0 : Prop) (x1 : Prop) := @INSERT Prop x0 (@INSERT Prop x1 (@EMPTY Prop)).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x0) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x0)) -> (y1 y2) = False)) y1)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term158 (x0 : Prop) (x1 : Prop -> Prop) := (@HAS_SIZE Prop x1 (S (NUMERAL 0))) /\ ((~ (@IN Prop x0 x1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 x1))).
Definition term10 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term240 := True /\ (forall y0 : Prop, y0 \/ (~ y0)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) (x3 : nat) := (fun y0 : nat => forall y1 : nat, ((@HAS_SIZE a0 x1 y1) /\ (@HAS_SIZE a1 x0 y0)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y2 : a0 -> a1 => exists y3 : a0 -> a1, @SETSPEC (a0 -> a1) y2 ((forall y4 : a0, (@IN a0 y4 x1) -> @IN a1 (y3 y4) x0) /\ (forall y4 : a0, (~ (@IN a0 y4 x1)) -> (y3 y4) = x2)) y3)) (Nat.pow y0 y1)) x3.
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x0) -> @IN Prop (x1 y0) (@UNIV Prop)) /\ (forall y0 : a0, (~ (@IN a0 y0 x0)) -> (x1 y0) = False).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) (x3 : nat) (x4 : nat) := @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y0 : a0 -> a1 => exists y1 : a0 -> a1, @SETSPEC (a0 -> a1) y0 ((forall y2 : a0, (@IN a0 y2 x1) -> @IN a1 (y1 y2) x0) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = x2)) y1)) (Nat.pow x3 x4).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) := forall y0 : nat, forall y1 : nat, ((@HAS_SIZE a0 x1 y1) /\ (@HAS_SIZE a1 x0 y0)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y2 : a0 -> a1 => exists y3 : a0 -> a1, @SETSPEC (a0 -> a1) y2 ((forall y4 : a0, (@IN a0 y4 x1) -> @IN a1 (y3 y4) x0) /\ (forall y4 : a0, (~ (@IN a0 y4 x1)) -> (y3 y4) = x2)) y3)) (Nat.pow y0 y1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : nat) := forall y0 : nat, forall y1 : a0 -> Prop, ((@HAS_SIZE a0 y1 y0) /\ (@HAS_SIZE a1 x0 x2)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y2 : a0 -> a1 => exists y3 : a0 -> a1, @SETSPEC (a0 -> a1) y2 ((forall y4 : a0, (@IN a0 y4 y1) -> @IN a1 (y3 y4) x0) /\ (forall y4 : a0, (~ (@IN a0 y4 y1)) -> (y3 y4) = x1)) y3)) (Nat.pow x2 y0).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : nat, forall y1 : a1 -> Prop, forall y2 : nat, forall y3 : a0 -> Prop, ((@HAS_SIZE a0 y3 y2) /\ (@HAS_SIZE a1 y1 y0)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y4 : a0 -> a1 => exists y5 : a0 -> a1, @SETSPEC (a0 -> a1) y4 ((forall y6 : a0, (@IN a0 y6 y3) -> @IN a1 (y5 y6) y1) /\ (forall y6 : a0, (~ (@IN a0 y6 y3)) -> (y5 y6) = x0)) y5)) (Nat.pow y0 y2).
Definition term213 (x0 : Prop) (x1 : Prop) := (~ (x0 = x1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 (@EMPTY Prop)))).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term115 (a0 : Type') := fun y0 : a0 => True.
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x2) x2.
Definition term237 := fun y0 : Prop => y0 \/ (~ y0).
Definition term250 := exists y0 : Prop, (~ (True = y0)) /\ ((@UNIV Prop) = (@INSERT Prop True (@INSERT Prop y0 (@EMPTY Prop)))).
Definition term216 (x0 : Prop) := exists y0 : Prop, (~ (x0 = y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop y0 (@EMPTY Prop)))).
Definition term215 (x0 : Prop) := fun y0 : Prop => (~ (x0 = y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop y0 (@EMPTY Prop)))).
Definition term142 := S (NUMERAL (BIT1 0)).
Definition term139 := True /\ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0)))).
Definition term218 := exists y0 : Prop, exists y1 : Prop, (~ (y0 = y1)) /\ ((@UNIV Prop) = (@INSERT Prop y0 (@INSERT Prop y1 (@EMPTY Prop)))).
Definition term205 := exists y0 : Prop, exists y1 : Prop, (~ (@IN Prop y1 (@EMPTY Prop))) /\ ((~ (@IN Prop y0 (@INSERT Prop y1 (@EMPTY Prop)))) /\ ((@UNIV Prop) = (@INSERT Prop y0 (@INSERT Prop y1 (@EMPTY Prop))))).
Definition term189 (x0 : Prop) := exists y0 : Prop, exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 (NUMERAL 0)) /\ ((~ (@IN Prop y0 y1)) /\ ((~ (@IN Prop x0 (@INSERT Prop y0 y1))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop y0 y1))))).
Definition term168 (x0 : Prop) := exists y0 : Prop, exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 (NUMERAL 0)) /\ ((~ (@IN Prop y0 y1)) /\ ((fun y2 : Prop -> Prop => (~ (@IN Prop x0 y2)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y2))) (@INSERT Prop y0 y1))).
Definition term166 (x0 : nat) (x1 : type920) := exists y0 : Prop, exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 x0) /\ ((~ (@IN Prop y0 y1)) /\ (x1 (@INSERT Prop y0 y1))).
Definition term148 := exists y0 : Prop, exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 (NUMERAL (BIT1 0))) /\ ((~ (@IN Prop y0 y1)) /\ ((@UNIV Prop) = (@INSERT Prop y0 y1))).
Definition term147 (x0 : nat) (x1 : Prop -> Prop) := exists y0 : Prop, exists y1 : Prop -> Prop, (@HAS_SIZE Prop y1 x0) /\ ((~ (@IN Prop y0 y1)) /\ (x1 = (@INSERT Prop y0 y1))).
Definition term157 (x0 : Prop) (x1 : Prop -> Prop) := (@HAS_SIZE Prop x1 (NUMERAL (BIT1 0))) /\ ((~ (@IN Prop x0 x1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 x1))).
Definition term181 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (@HAS_SIZE Prop x2 (NUMERAL 0)) /\ ((~ (@IN Prop x1 x2)) /\ ((fun y0 : Prop -> Prop => (~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))) (@INSERT Prop x1 x2))).
Definition term155 (x0 : Prop -> Prop) := and (@HAS_SIZE Prop x0 (S (NUMERAL 0))).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := True /\ (forall y0 : a0, (x0 y0) -> x1 y0).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term182 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (@HAS_SIZE Prop x2 (NUMERAL 0)) /\ ((~ (@IN Prop x1 x2)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 x2))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 x2))))).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (@IN a0 x2 x0)) -> (x1 x2) = False.
Definition term150 := S (Nat.add 0 0).
Definition term58 (a0 : Type') (x0 : nat) := fun y0 : type686 a0 => @HAS_SIZE (a0 -> Prop) y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term34 (a0 : Type') (a1 : Type') := (forall y0 : a1, forall y1 : nat, forall y2 : a1 -> Prop, forall y3 : nat, forall y4 : a0 -> Prop, ((@HAS_SIZE a0 y4 y3) /\ (@HAS_SIZE a1 y2 y1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y5 : a0 -> a1 => exists y6 : a0 -> a1, @SETSPEC (a0 -> a1) y5 ((forall y7 : a0, (@IN a0 y7 y4) -> @IN a1 (y6 y7) y2) /\ (forall y7 : a0, (~ (@IN a0 y7 y4)) -> (y6 y7) = y0)) y6)) (Nat.pow y1 y3)) -> forall y0 : a1 -> Prop, forall y1 : a0 -> Prop, forall y2 : a1, forall y3 : nat, forall y4 : nat, ((@HAS_SIZE a0 y1 y4) /\ (@HAS_SIZE a1 y0 y3)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y5 : a0 -> a1 => exists y6 : a0 -> a1, @SETSPEC (a0 -> a1) y5 ((forall y7 : a0, (@IN a0 y7 y1) -> @IN a1 (y6 y7) y0) /\ (forall y7 : a0, (~ (@IN a0 y7 y1)) -> (y6 y7) = y2)) y6)) (Nat.pow y3 y4).
Definition term221 (x0 : Prop -> Prop) (x1 : Prop -> Prop) := forall y0 : Prop, (@IN Prop y0 x0) = (@IN Prop y0 x1).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (forall y0 : a0, (@IN a0 y0 x0) -> @IN Prop (x1 y0) (@UNIV Prop)).
Definition term227 (x0 : Prop) := @IN Prop x0 (@INSERT Prop True (@INSERT Prop False (@EMPTY Prop))).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@HAS_SIZE a0 x0 x1) /\ (@HAS_SIZE Prop (@UNIV Prop) (NUMERAL (BIT0 (BIT1 0))))) -> @HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x0) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x0)) -> (y1 y2) = False)) y1)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term130 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((forall y0 : a0, (@IN a0 y0 x1) -> @IN Prop (x2 y0) (@UNIV Prop)) /\ (forall y0 : a0, (~ (@IN a0 y0 x1)) -> (x2 y0) = False)).
Definition term244 := (fun y0 : Prop => y0 \/ (~ y0)) True.
Definition term226 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (x1 = x0) \/ (@IN Prop x1 x2).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0))) x2.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN Prop (x1 y0) (@UNIV Prop).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> True.
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 x0) -> @IN Prop (y0 y1) (@UNIV Prop)) /\ (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = False)) x1.
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) (x3 : nat) (x4 : nat) := (forall y0 : a1, forall y1 : nat, forall y2 : a1 -> Prop, forall y3 : nat, forall y4 : a0 -> Prop, ((@HAS_SIZE a0 y4 y3) /\ (@HAS_SIZE a1 y2 y1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y5 : a0 -> a1 => exists y6 : a0 -> a1, @SETSPEC (a0 -> a1) y5 ((forall y7 : a0, (@IN a0 y7 y4) -> @IN a1 (y6 y7) y2) /\ (forall y7 : a0, (~ (@IN a0 y7 y4)) -> (y6 y7) = y0)) y6)) (Nat.pow y1 y3)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y0 : a0 -> a1 => exists y1 : a0 -> a1, @SETSPEC (a0 -> a1) y0 ((forall y2 : a0, (@IN a0 y2 x1) -> @IN a1 (y1 y2) x0) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = x2)) y1)) (Nat.pow x3 x4).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x1) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = False)) y1))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (forall y3 : a0, (@IN a0 y3 x1) -> @IN Prop (y2 y3) (@UNIV Prop)) /\ (forall y3 : a0, (~ (@IN a0 y3 x1)) -> (y2 y3) = False)) y1) y1))).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1))).
Definition term242 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term143 := @HAS_SIZE Prop (@UNIV Prop) (S (NUMERAL (BIT1 0))).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (forall y3 : a0, (@IN a0 y3 x0) -> @IN Prop (y2 y3) (@UNIV Prop)) /\ (forall y3 : a0, (~ (@IN a0 y3 x0)) -> (y2 y3) = False)) y1) y1).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) y1).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x0) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x0)) -> (y1 y2) = False)) y1).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1).
Definition term135 := NUMERAL (BIT0 (BIT1 0)).
Definition term254 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) -> @HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 y0) y3)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := forall y0 : a1, forall y1 : nat, forall y2 : nat, ((@HAS_SIZE a0 x1 y2) /\ (@HAS_SIZE a1 x0 y1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y3 : a0 -> a1 => exists y4 : a0 -> a1, @SETSPEC (a0 -> a1) y3 ((forall y5 : a0, (@IN a0 y5 x1) -> @IN a1 (y4 y5) x0) /\ (forall y5 : a0, (~ (@IN a0 y5 x1)) -> (y4 y5) = y0)) y4)) (Nat.pow y1 y2).
Definition term15 (a0 : Type') (a1 : Type') := forall y0 : a1, forall y1 : nat, forall y2 : a1 -> Prop, forall y3 : nat, forall y4 : a0 -> Prop, ((@HAS_SIZE a0 y4 y3) /\ (@HAS_SIZE a1 y2 y1)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y5 : a0 -> a1 => exists y6 : a0 -> a1, @SETSPEC (a0 -> a1) y5 ((forall y7 : a0, (@IN a0 y7 y4) -> @IN a1 (y6 y7) y2) /\ (forall y7 : a0, (~ (@IN a0 y7 y4)) -> (y6 y7) = y0)) y6)) (Nat.pow y1 y3).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term225 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := @IN Prop x0 (@INSERT Prop x1 x2).
Definition term198 (x0 : Prop) (x1 : Prop) := @eq Prop (exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x1 y1)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y1))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y1))))) y0)).
Definition term173 (x0 : Prop) := @eq Prop (exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (S (NUMERAL 0))) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x0 y1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y1))) y0)).
Definition term234 (x0 : Prop) := (~ x0) \/ False.
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 x1) -> @IN Prop (y0 y1) (@UNIV Prop)) /\ (forall y1 : a0, (~ (@IN a0 y1 x1)) -> (y0 y1) = False)) x2).
Definition term156 (x0 : Prop) (x1 : Prop -> Prop) := (~ (@IN Prop x0 x1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 x1)).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term232 (x0 : Prop) := or (x0 = False).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : nat) (x3 : nat) (x4 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@HAS_SIZE a0 y0 x3) /\ (@HAS_SIZE a1 x0 x2)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 ((forall y3 : a0, (@IN a0 y3 y0) -> @IN a1 (y2 y3) x0) /\ (forall y3 : a0, (~ (@IN a0 y3 y0)) -> (y2 y3) = x1)) y2)) (Nat.pow x2 x3)) x4.
Definition term178 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (~ (@IN Prop x1 x2)) /\ ((fun y0 : Prop -> Prop => (~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))) (@INSERT Prop x1 x2)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 x0) -> @IN Prop (y0 y1) (@UNIV Prop)) /\ (forall y1 : a0, (~ (@IN a0 y1 x0)) -> (y0 y1) = False).
Definition term171 (x0 : Prop) (x1 : Prop -> Prop) := (@HAS_SIZE Prop x1 (S (NUMERAL 0))) /\ ((fun y0 : Prop -> Prop => (~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))) x1).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 x1) -> @IN Prop (y0 y1) (@UNIV Prop)) /\ (forall y1 : a0, (~ (@IN a0 y1 x1)) -> (y0 y1) = False)) x2) x2.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) (x3 : nat) := forall y0 : nat, ((@HAS_SIZE a0 x1 y0) /\ (@HAS_SIZE a1 x0 x3)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 ((forall y3 : a0, (@IN a0 y3 x1) -> @IN a1 (y2 y3) x0) /\ (forall y3 : a0, (~ (@IN a0 y3 x1)) -> (y2 y3) = x2)) y2)) (Nat.pow x3 y0).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (x0 x1)).
Definition term133 (a0 : Type') (x0 : Prop -> Prop) (x1 : a0 -> Prop) (x2 : Prop) (x3 : nat) (x4 : nat) := ((@HAS_SIZE a0 x1 x4) /\ (@HAS_SIZE Prop x0 x3)) -> @HAS_SIZE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x1) -> @IN Prop (y1 y2) x0) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = x2)) y1)) (Nat.pow x3 x4).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) (x3 : nat) (x4 : nat) := ((@HAS_SIZE a0 x1 x4) /\ (@HAS_SIZE a1 x0 x3)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y0 : a0 -> a1 => exists y1 : a0 -> a1, @SETSPEC (a0 -> a1) y0 ((forall y2 : a0, (@IN a0 y2 x1) -> @IN a1 (y1 y2) x0) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = x2)) y1)) (Nat.pow x3 x4).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) -> x1 x2.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (x0 y0).
Definition term248 := (fun y0 : Prop => y0 \/ (~ y0)) False.
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (@IN a0 y0 x0)) -> (x1 y0) = False.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => @SUBSET a0 y0 x0.
Definition term146 (x0 : Prop -> Prop) (x1 : nat) := @HAS_SIZE Prop x0 (S x1).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (@IN a0 x2 x0) -> @IN Prop (x1 x2) (@UNIV Prop).
Definition term141 := BIT0 (BIT1 0).
Definition term196 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (@HAS_SIZE Prop x2 (NUMERAL 0)) /\ ((fun y0 : Prop -> Prop => (~ (@IN Prop x1 y0)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y0))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y0))))) x2).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((forall y2 : a0, (@IN a0 y2 x1) -> @IN Prop (y1 y2) (@UNIV Prop)) /\ (forall y2 : a0, (~ (@IN a0 y2 x1)) -> (y1 y2) = False)) y1)).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => (forall y3 : a0, (@IN a0 y3 x1) -> @IN Prop (y2 y3) (@UNIV Prop)) /\ (forall y3 : a0, (~ (@IN a0 y3 x1)) -> (y2 y3) = False)) y1) y1)).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (x1 y1) y1)).
Definition term228 (x0 : Prop) := (x0 = True) \/ (@IN Prop x0 (@INSERT Prop False (@EMPTY Prop))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, forall y2 : a1, forall y3 : nat, forall y4 : nat, ((@HAS_SIZE a0 y1 y4) /\ (@HAS_SIZE a1 y0 y3)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y5 : a0 -> a1 => exists y6 : a0 -> a1, @SETSPEC (a0 -> a1) y5 ((forall y7 : a0, (@IN a0 y7 y1) -> @IN a1 (y6 y7) y0) /\ (forall y7 : a0, (~ (@IN a0 y7 y1)) -> (y6 y7) = y2)) y6)) (Nat.pow y3 y4)) x0.
Definition term42 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ x0) -> ~ y0) = (y0 -> x0)) x1.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : nat) := (fun y0 : nat => forall y1 : a1 -> Prop, forall y2 : nat, forall y3 : a0 -> Prop, ((@HAS_SIZE a0 y3 y2) /\ (@HAS_SIZE a1 y1 y0)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y4 : a0 -> a1 => exists y5 : a0 -> a1, @SETSPEC (a0 -> a1) y4 ((forall y6 : a0, (@IN a0 y6 y3) -> @IN a1 (y5 y6) y1) /\ (forall y6 : a0, (~ (@IN a0 y6 y3)) -> (y5 y6) = x0)) y5)) (Nat.pow y0 y2)) x1.
Definition term169 (x0 : Prop) := fun y0 : Prop -> Prop => (~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0)).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x2 x1) x2.
Definition term199 (x0 : Prop) (x1 : Prop) := @eq Prop (exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((~ (@IN Prop x1 y0)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y0))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y0)))))).
Definition term174 (x0 : Prop) := @eq Prop (exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (S (NUMERAL 0))) /\ ((~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0)))).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 x1) y0.
Definition term185 (x0 : Prop) (x1 : Prop) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((~ (@IN Prop x1 y0)) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x0 y1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y1))) (@INSERT Prop x1 y0))).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term191 (x0 : type920) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ (x0 y0).
Definition term176 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (~ (@IN Prop x0 (@INSERT Prop x1 x2))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 x2))).
Definition term2 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((@HAS_SIZE a0 x1 y0) /\ (@HAS_SIZE a1 x0 x3)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 ((forall y3 : a0, (@IN a0 y3 x1) -> @IN a1 (y2 y3) x0) /\ (forall y3 : a0, (~ (@IN a0 y3 x1)) -> (y2 y3) = x2)) y2)) (Nat.pow x3 y0)) x4.
Definition term164 (a0 : Type') (x0 : nat) (x1 : type686 a0) := exists y0 : a0, exists y1 : a0 -> Prop, (@HAS_SIZE a0 y1 x0) /\ ((~ (@IN a0 y0 y1)) /\ (x1 (@INSERT a0 y0 y1))).
Definition term145 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := exists y0 : a0, exists y1 : a0 -> Prop, (@HAS_SIZE a0 y1 x0) /\ ((~ (@IN a0 y0 y1)) /\ (x1 = (@INSERT a0 y0 y1))).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a1, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y3) /\ (@HAS_SIZE a1 x0 y2)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y4 : a0 -> a1 => exists y5 : a0 -> a1, @SETSPEC (a0 -> a1) y4 ((forall y6 : a0, (@IN a0 y6 y0) -> @IN a1 (y5 y6) x0) /\ (forall y6 : a0, (~ (@IN a0 y6 y0)) -> (y5 y6) = y1)) y5)) (Nat.pow y2 y3).
Definition term233 (x0 : Prop) := or (~ x0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN Prop (x1 y0) (@UNIV Prop).
Definition term201 (x0 : Prop) := fun y0 : Prop => (~ (@IN Prop y0 (@EMPTY Prop))) /\ ((~ (@IN Prop x0 (@INSERT Prop y0 (@EMPTY Prop)))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop y0 (@EMPTY Prop))))).
Definition term177 (x0 : Prop) (x1 : Prop -> Prop) := and (~ (@IN Prop x0 x1)).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x1 x2).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @IN Prop (x0 x1) (@UNIV Prop).
Definition term192 (x0 : Prop) (x1 : Prop) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (NUMERAL 0)) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x1 y1)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 y1))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 y1))))) y0).
Definition term167 (x0 : Prop) := exists y0 : Prop -> Prop, (@HAS_SIZE Prop y0 (S (NUMERAL 0))) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x0 y1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y1))) y0).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) -> @IN a0 x1 x2.
Definition term239 := (~ (True = False)) /\ ((@UNIV Prop) = (@INSERT Prop True (@INSERT Prop False (@EMPTY Prop)))).
Definition term179 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (~ (@IN Prop x1 x2)) /\ ((~ (@IN Prop x0 (@INSERT Prop x1 x2))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop x1 x2)))).
Definition term220 := and (~ (True = False)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term23 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : nat) (x3 : nat) := forall y0 : a0 -> Prop, ((@HAS_SIZE a0 y0 x3) /\ (@HAS_SIZE a1 x0 x2)) -> @HAS_SIZE (a0 -> a1) (@GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 ((forall y3 : a0, (@IN a0 y3 y0) -> @IN a1 (y2 y3) x0) /\ (forall y3 : a0, (~ (@IN a0 y3 y0)) -> (y2 y3) = x1)) y2)) (Nat.pow x2 x3).
Definition term238 := forall y0 : Prop, y0 \/ (~ y0).
Definition term241 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term172 (x0 : Prop) := fun y0 : Prop -> Prop => (@HAS_SIZE Prop y0 (S (NUMERAL 0))) /\ ((fun y1 : Prop -> Prop => (~ (@IN Prop x0 y1)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y1))) y0).
Definition term140 := S (Nat.add 0 (BIT1 0)).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (forall y0 : a0, (x0 y0) -> x1 y0).
Definition term251 := fun y0 : Prop => (~ (True = y0)) /\ ((@UNIV Prop) = (@INSERT Prop True (@INSERT Prop y0 (@EMPTY Prop)))).
Definition term175 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) := (fun y0 : Prop -> Prop => (~ (@IN Prop x0 y0)) /\ ((@UNIV Prop) = (@INSERT Prop x0 y0))) (@INSERT Prop x1 x2).
Definition term4 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((forall y1 : a0, (@IN a0 y1 x1) -> @IN Prop (y0 y1) (@UNIV Prop)) /\ (forall y1 : a0, (~ (@IN a0 y1 x1)) -> (y0 y1) = False)) y0.
Definition term154 (x0 : Prop -> Prop) := and (@HAS_SIZE Prop x0 (NUMERAL (BIT1 0))).
Definition term222 := @INSERT Prop True (@INSERT Prop False (@EMPTY Prop)).
Definition term247 (x0 : Prop) := @eq Prop (x0 \/ (~ x0)).
Definition term51 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term230 (x0 : Prop) := @IN Prop x0 (@INSERT Prop False (@EMPTY Prop)).
Definition term212 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (~ (x0 = x1)) /\ x2.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term149 := NUMERAL (BIT1 0).
Definition term202 (x0 : Prop) := exists y0 : Prop, (~ (@IN Prop y0 (@EMPTY Prop))) /\ ((~ (@IN Prop x0 (@INSERT Prop y0 (@EMPTY Prop)))) /\ ((@UNIV Prop) = (@INSERT Prop x0 (@INSERT Prop y0 (@EMPTY Prop))))).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term62 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : type686 a0 => @HAS_SIZE (a0 -> Prop) y0 (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0)) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term131 (a0 : Type') := forall y0 : a0 -> Prop, True.
