Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term129 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term120 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0.
Definition term137 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term131 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) -> (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)))).
Definition term113 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub x0 x1).
Definition term48 (x0 : nat) := fun y0 : nat => (Nat.sub (BIT1 x0) (BIT0 y0)) = (@COND nat (Peano.le y0 x0) (BIT1 (Nat.sub x0 y0)) 0).
Definition term26 (x0 : nat) := fun y0 : nat => (Nat.sub (Nat.add x0 x0) (S (Nat.add y0 y0))) = (Nat.pred (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0))).
Definition term58 (x0 : nat) (x1 : nat) := Nat.sub (BIT1 x0) (BIT1 x1).
Definition term172 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)))).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.sub x1 x2).
Definition term175 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1)) (NUMERAL (BIT1 0)).
Definition term45 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (S (Nat.add (Nat.sub x0 x1) (Nat.sub x0 x1))).
Definition term149 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt y1 y2))) x0.
Definition term2 (x0 : nat) (x1 : nat) := Nat.sub (BIT0 x0) (BIT0 x1).
Definition term138 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term139 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term102 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) 0.
Definition term47 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (S (Nat.add (Nat.sub x0 x1) (Nat.sub x0 x1))) 0.
Definition term167 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)))) x1.
Definition term134 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) (@COND nat (Peano.le x1 x0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) 0)).
Definition term112 (x0 : nat) (x1 : nat) := Nat.sub x0 (S x1).
Definition term206 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term86 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term93 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term28 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 x0) (S (Nat.add y0 y0))) = (Nat.pred (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0))).
Definition term121 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) (@COND nat (Peano.le x1 x0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) 0).
Definition term4 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (BIT0 x0) (BIT0 x1)).
Definition term132 (x0 : nat) (x1 : nat) := and ((Peano.le x1 x0) -> (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)))).
Definition term110 := (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) 0)).
Definition term71 := (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))).
Definition term70 := (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))).
Definition term176 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1).
Definition term180 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1)).
Definition term1 (x0 : nat) := Nat.sub (Nat.add x0 x0).
Definition term147 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term64 (x0 : nat) := forall y0 : nat, (Nat.sub (BIT1 x0) (BIT1 y0)) = (BIT0 (Nat.sub x0 y0)).
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.sub (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.sub x0 y0)).
Definition term101 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term89 (x0 : nat) (x1 : nat) := Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term171 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)))) x1).
Definition term160 (x0 : nat) (x1 : nat) := Peano.lt (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term200 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (NUMERAL (BIT1 0)))).
Definition term116 (x0 : nat -> Prop) (x1 : Prop) (x2 : nat) (x3 : nat) := x0 (@COND nat x1 x2 x3).
Definition term170 (x0 : nat) (x1 : nat) := S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x1 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term123 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) 0.
Definition term128 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term142 (x0 : nat) := (fun y0 : nat => ((BIT1 y0) = 0) = False) x0.
Definition term144 (x0 : nat) := (fun y0 : nat => ((BIT0 y0) = 0) = (y0 = 0)) x0.
Definition term24 (x0 : nat) (x1 : nat) := Nat.pred (Nat.add (Nat.sub x0 x1) (Nat.sub x0 x1)).
Definition term63 (x0 : nat) := fun y0 : nat => (Nat.sub (S (Nat.add x0 x0)) (S (Nat.add y0 y0))) = (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0)).
Definition term122 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) -> (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)))) /\ ((~ (Peano.le x1 x0)) -> (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) 0).
Definition term118 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : nat) (x4 : nat) := (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) (@COND nat x2 x3 x4).
Definition term183 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) (NUMERAL (BIT1 0)).
Definition term104 (x0 : nat) := forall y0 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (@COND nat (Peano.le y0 x0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) 0).
Definition term51 (x0 : nat) := forall y0 : nat, (Nat.sub (S (Nat.add x0 x0)) (Nat.add y0 y0)) = (@COND nat (Peano.le y0 x0) (S (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0))) 0).
Definition term50 (x0 : nat) := forall y0 : nat, (Nat.sub (BIT1 x0) (BIT0 y0)) = (@COND nat (Peano.le y0 x0) (BIT1 (Nat.sub x0 y0)) 0).
Definition term179 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term41 (x0 : nat) (x1 : nat) := BIT1 (Nat.sub x0 x1).
Definition term100 (x0 : nat) (x1 : nat) := S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term37 (x0 : nat) (x1 : nat) := Nat.sub (BIT1 x0) (BIT0 x1).
Definition term205 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term186 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (NUMERAL (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term184 (x0 : nat) (x1 : nat) := Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1))).
Definition term20 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 x0) (S (Nat.add x1 x1)).
Definition term151 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt y0 y1))) x1.
Definition term195 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term194 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x1 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term196 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) (NUMERAL (BIT1 0)).
Definition term189 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x1 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) (NUMERAL (BIT1 0)).
Definition term75 := (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Nat.pred (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))))).
Definition term74 := (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1))))).
Definition term103 (x0 : nat) := fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) = (@COND nat (Peano.le y0 x0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) 0).
Definition term78 (x0 : nat) (x1 : nat) := Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term204 (x0 : nat) := @eq nat (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT1 0))).
Definition term18 (x0 : nat) := S (Nat.add x0 x0).
Definition term117 (x0 : nat) (x1 : Prop) (x2 : nat -> Prop) (x3 : nat) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term133 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) -> (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)))) /\ ((~ (Peano.le x1 x0)) -> (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = 0).
Definition term114 (x0 : nat) (x1 : nat) := @eq nat (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term191 (x0 : nat) (x1 : nat) := Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1)).
Definition term88 (x0 : nat) := S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term111 := True /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) 0))).
Definition term190 (x0 : nat) (x1 : nat) := Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x1 x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term98 (x0 : nat) (x1 : nat) := Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term0 (x0 : nat) := Nat.sub (BIT0 x0).
Definition term136 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term73 := (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Nat.pred (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)))).
Definition term72 := (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)))).
Definition term76 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term19 (x0 : nat) (x1 : nat) := Nat.sub (BIT0 x0) (BIT1 x1).
Definition term141 := forall y0 : nat, ((BIT1 y0) = 0) = False.
Definition term9 (x0 : nat) := fun y0 : nat => (Nat.sub (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0)).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 y0))) x2.
Definition term59 (x0 : nat) (x1 : nat) := Nat.sub (S (Nat.add x0 x0)) (S (Nat.add x1 x1)).
Definition term157 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term115 := True /\ (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) 0)).
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term165 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term25 (x0 : nat) := fun y0 : nat => (Nat.sub (BIT0 x0) (BIT1 y0)) = (Nat.pred (BIT0 (Nat.sub x0 y0))).
Definition term158 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1.
Definition term92 (x0 : nat) := fun y0 : nat => (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))) = (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term202 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term143 := forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0).
Definition term135 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = (@COND nat (Peano.le x1 x0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))) 0)).
Definition term150 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt y0 y1)).
Definition term145 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term106 := forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) 0).
Definition term95 := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term69 := forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)).
Definition term68 := forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)).
Definition term55 := forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))) 0).
Definition term54 := forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0).
Definition term32 := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Nat.pred (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))).
Definition term31 := forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1))).
Definition term15 := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)).
Definition term14 := forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1)).
Definition term21 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (BIT0 x0) (BIT1 x1)).
Definition term36 (x0 : nat) := Nat.sub (S (Nat.add x0 x0)).
Definition term185 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) (NUMERAL (BIT1 0))).
Definition term46 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (BIT1 (Nat.sub x0 x1)) 0.
Definition term85 := forall y0 : nat, True.
Definition term27 (x0 : nat) := forall y0 : nat, (Nat.sub (BIT0 x0) (BIT1 y0)) = (Nat.pred (BIT0 (Nat.sub x0 y0))).
Definition term90 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term79 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term173 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term60 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (BIT1 x0) (BIT1 x1)).
Definition term119 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) (x4 : nat) := (x1 -> (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x3)) = y0) x0) /\ ((~ x1) -> (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x3)) = y0) x4).
Definition term84 := fun y0 : nat => True.
Definition term152 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 y0)).
Definition term65 (x0 : nat) := forall y0 : nat, (Nat.sub (S (Nat.add x0 x0)) (S (Nat.add y0 y0))) = (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0)).
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 x0) (Nat.add y0 y0)) = (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0)).
Definition term125 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) 0.
Definition term193 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term6 (x0 : nat) (x1 : nat) := BIT0 (Nat.sub x0 x1).
Definition term49 (x0 : nat) := fun y0 : nat => (Nat.sub (S (Nat.add x0 x0)) (Nat.add y0 y0)) = (@COND nat (Peano.le y0 x0) (S (Nat.add (Nat.sub x0 y0) (Nat.sub x0 y0))) 0).
Definition term38 (x0 : nat) (x1 : nat) := Nat.sub (S (Nat.add x0 x0)) (Nat.add x1 x1).
Definition term40 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (S (Nat.add x0 x0)) (Nat.add x1 x1)).
Definition term127 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term169 (x0 : nat) (x1 : nat) := Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x1 x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term164 := and (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))).
Definition term39 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (BIT1 x0) (BIT0 x1)).
Definition term83 := NUMERAL (BIT0 (BIT1 0)).
Definition term126 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = 0.
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term80 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.sub x0 x1).
Definition term107 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) 0)).
Definition term96 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))).
Definition term57 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))) 0)).
Definition term56 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0)).
Definition term34 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Nat.pred (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)))).
Definition term33 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1)))).
Definition term17 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))).
Definition term16 := and (forall y0 : nat, forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1))).
Definition term42 (x0 : nat) (x1 : nat) := S (Nat.add (Nat.sub x0 x1) (Nat.sub x0 x1)).
Definition term108 (x0 : nat) (x1 : nat) := Nat.sub (S x0) (S x1).
Definition term7 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1) (Nat.sub x0 x1).
Definition term174 (x0 : nat) (x1 : nat) := S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x1)).
Definition term156 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) x0.
Definition term146 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term22 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.add x0 x0) (S (Nat.add x1 x1))).
Definition term97 (x0 : nat) := Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term109 := (forall y0 : nat, forall y1 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) 0)) /\ True.
Definition term91 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term62 (x0 : nat) := fun y0 : nat => (Nat.sub (BIT1 x0) (BIT1 y0)) = (BIT0 (Nat.sub x0 y0)).
Definition term163 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term166 (x0 : nat) := fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0))).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term124 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term5 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.add x0 x0) (Nat.add x1 x1)).
Definition term162 := BIT0 (BIT1 0).
Definition term99 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term159 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term44 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x1 x0) (BIT1 (Nat.sub x0 x1)).
Definition term3 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 x0) (Nat.add x1 x1).
Definition term35 (x0 : nat) := Nat.sub (BIT1 x0).
Definition term43 (x0 : nat) (x1 : nat) := @COND nat (Peano.le x0 x1).
Definition term87 (x0 : Prop) := forall y0 : nat, x0.
Definition term23 (x0 : nat) (x1 : nat) := Nat.pred (BIT0 (Nat.sub x0 x1)).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term203 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT1 0)).
Definition term94 := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) = (Nat.pred (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))).
Definition term66 := fun y0 : nat => forall y1 : nat, (Nat.sub (BIT1 y0) (BIT1 y1)) = (BIT0 (Nat.sub y0 y1)).
Definition term30 := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y0) (S (Nat.add y1 y1))) = (Nat.pred (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))).
Definition term29 := fun y0 : nat => forall y1 : nat, (Nat.sub (BIT0 y0) (BIT1 y1)) = (Nat.pred (BIT0 (Nat.sub y0 y1))).
Definition term12 := fun y0 : nat => forall y1 : nat, (Nat.sub (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.sub y0 y1)).
Definition term188 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (NUMERAL (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term201 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT1 0)))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term61 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (S (Nat.add x0 x0)) (S (Nat.add x1 x1))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term140 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term199 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (NUMERAL (BIT1 0))).
Definition term8 (x0 : nat) := fun y0 : nat => (Nat.sub (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.sub x0 y0)).
Definition term192 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term168 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)))) (Nat.add x0 x1).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 x2).
Definition term130 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)) = (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1))).
Definition term148 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term105 := fun y0 : nat => forall y1 : nat, (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1))) 0).
Definition term53 := fun y0 : nat => forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (Nat.add y1 y1)) = (@COND nat (Peano.le y1 y0) (S (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1))) 0).
Definition term52 := fun y0 : nat => forall y1 : nat, (Nat.sub (BIT1 y0) (BIT0 y1)) = (@COND nat (Peano.le y1 y0) (BIT1 (Nat.sub y0 y1)) 0).
Definition term77 (x0 : nat) := Nat.sub (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term161 (x0 : nat) (x1 : nat) := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0))) /\ (Peano.lt x0 x1).
Definition term67 := fun y0 : nat => forall y1 : nat, (Nat.sub (S (Nat.add y0 y0)) (S (Nat.add y1 y1))) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)).
Definition term13 := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y0) (Nat.add y1 y1)) = (Nat.add (Nat.sub y0 y1) (Nat.sub y0 y1)).
Definition term182 := NUMERAL (BIT1 0).
Definition term187 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x1 x0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term181 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
