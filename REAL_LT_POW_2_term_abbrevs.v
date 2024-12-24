Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term115 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term155 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term32 (x0 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) = ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0)))))).
Definition term147 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term128 (x0 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term96 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term103 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term142 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term34 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term15 := real_of_num (NUMERAL 0).
Definition term30 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))))) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0)))))).
Definition term27 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term1 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term0 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term56 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term2 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term26 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0)))))).
Definition term173 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term124 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) := and (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term71 (x0 : real) := or (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term122 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term129 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term171 := fun y0 : real => True.
Definition term151 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term148 (x0 : real) := (~ ((real_lt (real_of_num (NUMERAL 0)) x0) = ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))))) -> False.
Definition term144 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term61 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term163 := forall y0 : real, (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_of_num (NUMERAL 0)))) = (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term10 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term21 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term45 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term52 (x0 : real) := @eq real (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term125 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term42 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term172 := forall y0 : real, True.
Definition term137 (x0 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term174 (x0 : Prop) := forall y0 : real, x0.
Definition term5 (x0 : nat) := (fun y0 : nat => ((BIT1 y0) = 0) = False) x0.
Definition term74 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term7 (x0 : nat) := (fun y0 : nat => ((BIT0 y0) = 0) = (y0 = 0)) x0.
Definition term41 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term35 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term83 (x0 : real) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term44 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term92 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term49 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term156 (x0 : real) := ~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_of_num (NUMERAL 0))).
Definition term88 (x0 : real) := (((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term38 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term36 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term77 (x0 : real) := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term69 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term130 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term57 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term133 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term104 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term23 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term157 (x0 : real) := True /\ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_of_num (NUMERAL 0)))).
Definition term37 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term73 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term18 (x0 : real) := or (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term70 (x0 : real) := or (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term158 (x0 : real) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term12 (x0 : real) := (fun y0 : real => forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term82 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term87 (x0 : real) := or (((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term4 := forall y0 : nat, ((BIT1 y0) = 0) = False.
Definition term113 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term154 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term135 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term65 (x0 : real) := (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term85 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term121 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term39 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term67 (x0 : real) := @eq real (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term58 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) := or (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term164 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))).
Definition term43 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term120 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term6 := forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0).
Definition term8 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term143 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term99 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term110 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term131 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term14 (x0 : real) (x1 : nat) := (fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term55 (x0 : real) := and (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term105 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term68 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term162 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term134 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term170 (x0 : real) := @eq Prop (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term90 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term93 := S (Nat.add 0 0).
Definition term111 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term54 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term22 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term112 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term28 (x0 : real) := or ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))))).
Definition term80 (x0 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term116 := real_mul (real_of_num (NUMERAL 0)).
Definition term78 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term100 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term50 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term48 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term165 := NUMERAL (BIT0 (BIT1 0)).
Definition term46 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term89 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term149 (x0 : real) := ((~ ((real_lt (real_of_num (NUMERAL 0)) x0) = ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))))) -> False) -> (real_lt (real_of_num (NUMERAL 0)) x0) = ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term81 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term19 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term141 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term33 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term31 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (x0 = (real_of_num (NUMERAL 0))))) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0)))))).
Definition term16 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))).
Definition term150 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term126 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term140 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term47 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term145 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term60 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term167 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term169 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ True.
Definition term86 (x0 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term97 := real_of_num (NUMERAL (BIT1 0)).
Definition term166 := BIT0 (BIT1 0).
Definition term138 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) := real_neg (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term117 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term160 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term153 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_of_num (NUMERAL 0)))).
Definition term118 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term109 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term84 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term75 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term132 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term168 (x0 : real) := and (x0 = (real_of_num (NUMERAL 0))).
Definition term3 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term106 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term123 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term146 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term161 := fun y0 : real => (~ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_of_num (NUMERAL 0)))) = (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term79 (x0 : real) := or ((real_gt x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))))).
Definition term24 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term98 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term51 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term29 (x0 : real) := or ((real_lt (real_of_num (NUMERAL 0)) x0) /\ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (x0 = (real_of_num (NUMERAL 0))))).
Definition term114 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term101 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term63 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term62 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term102 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term152 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term17 (x0 : real) := ~ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term94 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term40 := NUMERAL (BIT1 0).
Definition term159 (x0 : real) := @eq Prop (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_of_num (NUMERAL 0)))).
Definition term136 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term127 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term95 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term139 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term91 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term13 (x0 : real) := forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
Definition term119 := real_gt (real_of_num (NUMERAL 0)).
