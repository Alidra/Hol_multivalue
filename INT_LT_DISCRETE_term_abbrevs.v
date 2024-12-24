Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term139 (x0 : int) (x1 : int) := real_le (real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term105 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt (real_neg x0) (real_neg y0)) = (real_lt y0 x0)) x1.
Definition term240 (x0 : nat) (x1 : nat) := real_le (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1).
Definition term54 (x0 : real) := forall y0 : real, (real_add x0 (real_neg y0)) = (real_sub x0 y0).
Definition term201 (x0 : nat) := real_le (real_add (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term50 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term265 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (NUMERAL 0) (Nat.add x0 x1)).
Definition term162 (x0 : nat) (x1 : int) := (fun y0 : int => (real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int y0)) = (real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) x1.
Definition term152 (x0 : nat) (x1 : int) := (fun y0 : int => (real_lt (real_of_int (int_of_num x0)) (real_of_int y0)) = (real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) x1.
Definition term141 (x0 : int) (x1 : int) := (fun y0 : int => (real_lt (real_of_int y0) (real_of_int x0)) = (real_le (real_add (real_of_int y0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0))) x1.
Definition term252 (x0 : nat) (x1 : nat) := real_lt (real_of_num (Nat.add x0 x1)) (real_of_num (NUMERAL 0)).
Definition term223 (x0 : nat) (x1 : nat) := real_le (real_add (real_neg (real_of_num x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term45 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term164 (x0 : nat) (x1 : nat) := real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num x1)).
Definition term219 (x0 : nat) (x1 : nat) := real_add (real_add (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1).
Definition term227 (x0 : nat) (x1 : nat) := real_lt (real_add (real_of_num x0) (real_of_num x1)).
Definition term149 (x0 : nat) (x1 : int) := real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int x1).
Definition term272 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (NUMERAL (BIT1 0)) x0) (Nat.add (NUMERAL 0) x1).
Definition term186 (x0 : nat) := real_neg (real_of_num x0).
Definition term217 := real_of_num (NUMERAL 0).
Definition term254 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (Nat.add x0 x1) (NUMERAL 0)).
Definition term188 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_int (int_of_num x0)) (real_of_int (int_neg (int_of_num x1)))).
Definition term222 (x0 : nat) (x1 : nat) := real_le (real_add (real_neg (real_of_num x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x1))).
Definition term195 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term264 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.add x0 x1).
Definition term285 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x1)) (NUMERAL 0).
Definition term113 (x0 : int) := (exists y0 : nat, x0 = (int_of_num y0)) \/ (exists y0 : nat, x0 = (int_neg (int_of_num y0))).
Definition term19 (x0 : nat) := NUMERAL (S x0).
Definition term125 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) = (real_le (real_of_int y0) (real_of_int y1))) x0.
Definition term121 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) = (real_lt (real_of_int y0) (real_of_int y1))) x0.
Definition term116 (x0 : int) := (fun y0 : int => forall y1 : int, (real_of_int (int_add y0 y1)) = (real_add (real_of_int y0) (real_of_int y1))) x0.
Definition term241 (x0 : nat) (x1 : nat) := real_le (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_num x0) (real_of_num x1)).
Definition term20 := S (NUMERAL 0).
Definition term260 (x0 : nat) (x1 : nat) := real_le (real_of_num (Nat.add (Nat.add (NUMERAL (BIT1 0)) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term25 := fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term224 (x0 : nat) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0).
Definition term5 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term268 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 x1).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le (real_sub x0 x1) y0) = (real_le x0 (real_add y0 x1))) x2.
Definition term40 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term134 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term90 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 (real_neg y0)) = (real_lt (real_add x0 y0) (real_of_num (NUMERAL 0)))) x1.
Definition term196 (x0 : nat) := real_add (real_of_int (int_neg (int_of_num x0))).
Definition term26 := forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term47 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term43 (x0 : nat) := forall y0 : nat, (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0).
Definition term259 (x0 : nat) (x1 : nat) := real_le (real_of_num (Nat.add (Nat.add (NUMERAL (BIT1 0)) x0) x1)).
Definition term69 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term109 (x0 : int) := (fun y0 : int => (real_of_int (int_neg y0)) = (real_neg (real_of_int y0))) x0.
Definition term258 (x0 : nat) (x1 : nat) := real_of_num (Nat.add (Nat.add (NUMERAL (BIT1 0)) x0) x1).
Definition term70 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term284 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x1)).
Definition term118 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0))) x1.
Definition term216 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x1))).
Definition term154 (x0 : nat) (x1 : nat) := real_lt (real_of_int (int_of_num x0)) (real_of_int (int_of_num x1)).
Definition term36 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL (BIT1 0)) y0) = (S y0)) x0.
Definition term129 (x0 : int) (x1 : int) := @eq Prop (int_lt x0 x1).
Definition term172 (x0 : nat) := real_lt (real_of_num x0).
Definition term132 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term242 (x0 : nat) (x1 : nat) := real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1).
Definition term270 (x0 : nat) := real_of_num (Nat.add (NUMERAL 0) x0).
Definition term15 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := real_le x0 (real_add x1 x2).
Definition term52 (x0 : real) := fun y0 : real => (real_add x0 (real_neg y0)) = (real_sub x0 y0).
Definition term280 (x0 : nat) (x1 : nat) := Peano.le (S x0) (Nat.add (NUMERAL 0) x1).
Definition term249 (x0 : nat) (x1 : nat) := real_le (real_of_num (Nat.add (NUMERAL (BIT1 0)) x0)) (real_of_num x1).
Definition term271 (x0 : nat) (x1 : nat) := real_le (real_of_num (Nat.add (NUMERAL (BIT1 0)) x0)) (real_of_num (Nat.add (NUMERAL 0) x1)).
Definition term18 (x0 : nat) := S (NUMERAL x0).
Definition term35 := forall y0 : nat, (Nat.add (NUMERAL (BIT1 0)) y0) = (S y0).
Definition term8 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term135 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term84 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2)).
Definition term83 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term80 (x0 : real) := forall y0 : real, forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1)).
Definition term79 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term60 (x0 : real) := forall y0 : real, forall y1 : real, (real_le (real_sub x0 y0) y1) = (real_le x0 (real_add y1 y0)).
Definition term58 := forall y0 : real, forall y1 : real, (real_add y0 (real_neg y1)) = (real_sub y0 y1).
Definition term57 := forall y0 : real, forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1)).
Definition term17 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term192 (x0 : nat) := real_lt (real_neg (real_of_num x0)).
Definition term287 (x0 : int) := fun y0 : nat => x0 = (int_neg (int_of_num y0)).
Definition term126 (x0 : int) := forall y0 : int, (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0)).
Definition term122 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (real_lt (real_of_int x0) (real_of_int y0)).
Definition term117 (x0 : int) := forall y0 : int, (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0)).
Definition term174 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_num x0) (real_of_num x1)).
Definition term193 (x0 : nat) (x1 : nat) := real_lt (real_neg (real_of_num x0)) (real_of_num x1).
Definition term239 (x0 : nat) := real_le (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)).
Definition term119 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term96 (x0 : real) (x1 : real) := real_le x0 (real_neg x1).
Definition term163 (x0 : nat) (x1 : nat) := (fun y0 : int => (real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int y0)) = (real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) (int_of_num x1).
Definition term153 (x0 : nat) (x1 : nat) := (fun y0 : int => (real_lt (real_of_int (int_of_num x0)) (real_of_int y0)) = (real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) (int_of_num x1).
Definition term142 (x0 : int) (x1 : nat) := (fun y0 : int => (real_lt (real_of_int y0) (real_of_int x0)) = (real_le (real_add (real_of_int y0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0))) (int_of_num x1).
Definition term76 (x0 : real) (x1 : real) := forall y0 : real, (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0)).
Definition term62 (x0 : real) (x1 : real) := forall y0 : real, (real_le (real_sub x0 x1) y0) = (real_le x0 (real_add y0 x1)).
Definition term198 (x0 : nat) := real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term180 (x0 : nat) := real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term183 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1).
Definition term276 (x0 : nat) := Nat.add (S x0).
Definition term221 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term215 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term231 := real_lt (real_of_num (NUMERAL 0)).
Definition term184 (x0 : nat) := real_of_int (int_neg (int_of_num x0)).
Definition term171 (x0 : nat) := real_lt (real_of_int (int_of_num x0)).
Definition term33 (x0 : nat) := @eq nat (Nat.add (NUMERAL (BIT1 0)) x0).
Definition term112 (x0 : int) := (fun y0 : int => (exists y1 : nat, y0 = (int_of_num y1)) \/ (exists y1 : nat, y0 = (int_neg (int_of_num y1)))) x0.
Definition term199 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term108 (x0 : nat) := real_of_int (int_of_num x0).
Definition term102 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term78 (x0 : real) := fun y0 : real => forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1)).
Definition term55 := fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1)).
Definition term73 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term131 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term166 (x0 : nat) (x1 : int) := @eq Prop ((fun y0 : int => (real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int y0)) = (real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) x1).
Definition term156 (x0 : nat) (x1 : int) := @eq Prop ((fun y0 : int => (real_lt (real_of_int (int_of_num x0)) (real_of_int y0)) = (real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) x1).
Definition term145 (x0 : int) (x1 : int) := @eq Prop ((fun y0 : int => (real_lt (real_of_int y0) (real_of_int x0)) = (real_le (real_add (real_of_int y0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0))) x1).
Definition term182 (x0 : nat) := real_le (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term256 (x0 : nat) := real_add (real_of_num (Nat.add (NUMERAL (BIT1 0)) x0)).
Definition term120 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term278 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (S x0) x1).
Definition term21 := NUMERAL (S 0).
Definition term210 (x0 : nat) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_add (real_of_num x0) (real_of_num x1)).
Definition term246 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term261 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (Nat.add (NUMERAL (BIT1 0)) x0) x1) (NUMERAL 0).
Definition term1 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term165 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num x1)).
Definition term155 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num x1)).
Definition term75 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term124 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term100 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt (real_neg x0) y0) = (real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0))) x1.
Definition term237 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term48 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term247 (x0 : nat) := real_of_num (Nat.add (NUMERAL (BIT1 0)) x0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1.
Definition term14 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term214 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x1)).
Definition term11 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term289 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term6 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term263 (x0 : nat) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_of_num (Nat.add x0 x1)).
Definition term107 (x0 : nat) := (fun y0 : nat => (real_of_int (int_of_num y0)) = (real_of_num y0)) x0.
Definition term233 (x0 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num x0))).
Definition term191 (x0 : nat) := real_lt (real_of_int (int_neg (int_of_num x0))).
Definition term130 (x0 : int) (x1 : int) := @eq Prop (real_lt (real_of_int x0) (real_of_int x1)).
Definition term208 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (NUMERAL 0))).
Definition term34 := fun y0 : nat => (Nat.add (NUMERAL (BIT1 0)) y0) = (S y0).
Definition term225 (x0 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)).
Definition term226 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1).
Definition term77 (x0 : real) := fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term56 := fun y0 : real => forall y1 : real, (real_add y0 (real_neg y1)) = (real_sub y0 y1).
Definition term87 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0))) x2.
Definition term277 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (Nat.add (NUMERAL (BIT1 0)) x0) x1).
Definition term104 (x0 : real) := forall y0 : real, (real_lt (real_neg x0) (real_neg y0)) = (real_lt y0 x0).
Definition term12 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term150 (x0 : nat) (x1 : int) := real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term144 (x0 : nat) (x1 : int) := real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term290 := forall y0 : int, forall y1 : int, (int_lt y0 y1) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1).
Definition term103 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_neg y0) (real_neg y1)) = (real_lt y1 y0)) x0.
Definition term98 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_neg y0) y1) = (real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) x0.
Definition term93 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 (real_neg y1)) = (real_le (real_add y0 y1) (real_of_num (NUMERAL 0)))) x0.
Definition term88 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 (real_neg y1)) = (real_lt (real_add y0 y1) (real_of_num (NUMERAL 0)))) x0.
Definition term68 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term66 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 (real_neg y1)) = (real_sub y0 y1)) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term23 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term275 (x0 : nat) := Nat.add (Nat.add (NUMERAL (BIT1 0)) x0).
Definition term94 (x0 : real) := forall y0 : real, (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0))).
Definition term89 (x0 : real) := forall y0 : real, (real_lt x0 (real_neg y0)) = (real_lt (real_add x0 y0) (real_of_num (NUMERAL 0))).
Definition term133 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term253 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add x0 x1) (NUMERAL 0).
Definition term230 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term212 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term209 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term143 (x0 : nat) (x1 : int) := real_lt (real_of_int (int_of_num x0)) (real_of_int x1).
Definition term251 (x0 : nat) (x1 : nat) := real_lt (real_of_num (Nat.add x0 x1)).
Definition term243 (x0 : nat) (x1 : nat) := real_le (real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1)).
Definition term167 (x0 : nat) (x1 : int) := @eq Prop ((real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int x1)) = (real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1))).
Definition term157 (x0 : nat) (x1 : int) := @eq Prop ((real_lt (real_of_int (int_of_num x0)) (real_of_int x1)) = (real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1))).
Definition term146 (x0 : int) (x1 : int) := @eq Prop ((real_lt (real_of_int x0) (real_of_int x1)) = (real_le (real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1))).
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0)) x1.
Definition term204 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_neg (int_of_num x1)))).
Definition term29 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term106 (x0 : real) (x1 : real) := real_lt (real_neg x0) (real_neg x1).
Definition term207 (x0 : nat) (x1 : nat) := real_lt (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term228 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1).
Definition term53 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term86 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1))) x1.
Definition term61 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le (real_sub x0 y0) y1) = (real_le x0 (real_add y1 y0))) x1.
Definition term234 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num x0))) (real_of_num x1).
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term4 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term235 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term248 (x0 : nat) := real_le (real_of_num (Nat.add (NUMERAL (BIT1 0)) x0)).
Definition term200 (x0 : nat) := real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))).
Definition term173 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_int (int_of_num x0)) (real_of_int (int_of_num x1))).
Definition term137 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term175 (x0 : nat) := real_add (real_of_int (int_of_num x0)).
Definition term114 (x0 : int) := exists y0 : nat, x0 = (int_of_num y0).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := real_le (real_sub x0 x1) x2.
Definition term262 (x0 : nat) (x1 : nat) := Nat.add (Nat.add (NUMERAL (BIT1 0)) x0) x1.
Definition term91 (x0 : real) (x1 : real) := real_lt x0 (real_neg x1).
Definition term111 (x0 : int) := real_neg (real_of_int x0).
Definition term288 (x0 : int) := fun y0 : nat => x0 = (int_of_num y0).
Definition term194 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num x1))).
Definition term203 (x0 : nat) (x1 : nat) := real_lt (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term71 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term101 (x0 : real) (x1 : real) := real_lt (real_neg x0) x1.
Definition term267 (x0 : nat) (x1 : nat) := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (Nat.add x0 x1)).
Definition term138 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))).
Definition term147 (x0 : nat) := int_neg (int_of_num x0).
Definition term128 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) x0.
Definition term279 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (S x0) x1) (NUMERAL 0).
Definition term16 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term229 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1)).
Definition term82 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2)).
Definition term81 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term286 (x0 : nat) (x1 : nat) := Peano.lt x0 (Nat.add (NUMERAL 0) x1).
Definition term176 (x0 : nat) := real_add (real_of_num x0).
Definition term32 (x0 : nat) := @eq nat (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term197 (x0 : nat) := real_add (real_neg (real_of_num x0)).
Definition term282 := Peano.le (S (NUMERAL 0)).
Definition term236 (x0 : nat) (x1 : nat) := real_le (real_add (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term211 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (real_add (real_of_num x0) (real_of_num x1))).
Definition term213 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1).
Definition term74 (x0 : real) (x1 : real) := fun y0 : real => (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0)).
Definition term218 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term169 (x0 : nat) (x1 : nat) := real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_neg (int_of_num x1))).
Definition term38 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term178 := real_of_num (NUMERAL (BIT1 0)).
Definition term238 (x0 : nat) := real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term179 (x0 : nat) := real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term273 (x0 : nat) := Peano.le (Nat.add (NUMERAL (BIT1 0)) x0).
Definition term95 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0)))) x1.
Definition term123 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) = (real_lt (real_of_int x0) (real_of_int y0))) x1.
Definition term140 (x0 : int) := fun y0 : int => (real_lt (real_of_int y0) (real_of_int x0)) = (real_le (real_add (real_of_int y0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)).
Definition term97 (x0 : real) (x1 : real) := real_le (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term283 (x0 : nat) (x1 : nat) := Peano.le (S (NUMERAL 0)) (Nat.add x0 x1).
Definition term244 (x0 : nat) (x1 : nat) := real_le (real_sub (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term67 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 (real_neg y0)) = (real_sub x0 y0)) x1.
Definition term92 (x0 : real) (x1 : real) := real_lt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term190 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num x1)).
Definition term110 (x0 : int) := real_of_int (int_neg x0).
Definition term177 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term170 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_neg (int_of_num x1))).
Definition term160 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_neg (int_of_num x1))).
Definition term49 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term274 (x0 : nat) := Peano.le (S x0).
Definition term115 (x0 : int) := exists y0 : nat, x0 = (int_neg (int_of_num y0)).
Definition term189 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_of_num x0) (real_neg (real_of_num x1))).
Definition term168 (x0 : nat) (x1 : nat) := (fun y0 : int => (real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int y0)) = (real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) (int_neg (int_of_num x1)).
Definition term158 (x0 : nat) (x1 : nat) := (fun y0 : int => (real_lt (real_of_int (int_of_num x0)) (real_of_int y0)) = (real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0))) (int_neg (int_of_num x1)).
Definition term148 (x0 : int) (x1 : nat) := (fun y0 : int => (real_lt (real_of_int y0) (real_of_int x0)) = (real_le (real_add (real_of_int y0) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0))) (int_neg (int_of_num x1)).
Definition term257 (x0 : nat) (x1 : nat) := real_add (real_of_num (Nat.add (NUMERAL (BIT1 0)) x0)) (real_of_num x1).
Definition term99 (x0 : real) := forall y0 : real, (real_lt (real_neg x0) y0) = (real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term127 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0))) x1.
Definition term51 (x0 : real) := fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term185 (x0 : nat) := real_neg (real_of_int (int_of_num x0)).
Definition term31 (x0 : nat) := Nat.add (NUMERAL (BIT1 0)) x0.
Definition term27 := forall y0 : nat, (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term206 (x0 : nat) (x1 : nat) := real_le (real_add (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num x1)).
Definition term220 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x1)).
Definition term161 (x0 : nat) := fun y0 : int => (real_lt (real_of_int (int_neg (int_of_num x0))) (real_of_int y0)) = (real_le (real_add (real_of_int (int_neg (int_of_num x0))) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0)).
Definition term151 (x0 : nat) := fun y0 : int => (real_lt (real_of_int (int_of_num x0)) (real_of_int y0)) = (real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))) (real_of_int y0)).
Definition term269 (x0 : nat) := real_add (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term24 := fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term266 := real_le (real_of_num (NUMERAL (BIT1 0))).
Definition term202 (x0 : nat) (x1 : nat) := real_le (real_add (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1).
Definition term232 (x0 : nat) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num x0)).
Definition term181 (x0 : nat) := real_le (real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0))))).
Definition term245 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num x1)).
Definition term72 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term41 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term85 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2))) x0.
Definition term59 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le (real_sub y0 y1) y2) = (real_le y0 (real_add y2 y1))) x0.
Definition term136 := int_of_num (NUMERAL (BIT1 0)).
Definition term205 (x0 : nat) (x1 : nat) := @eq Prop (real_lt (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term10 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term22 := NUMERAL (BIT1 0).
Definition term281 := Peano.le (NUMERAL (BIT1 0)).
Definition term250 (x0 : nat) (x1 : nat) := Peano.le (Nat.add (NUMERAL (BIT1 0)) x0) x1.
Definition term159 (x0 : nat) (x1 : nat) := real_lt (real_of_int (int_of_num x0)) (real_of_int (int_neg (int_of_num x1))).
Definition term255 (x0 : nat) := real_add (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0)).
Definition term187 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_neg (real_of_num x1)).
