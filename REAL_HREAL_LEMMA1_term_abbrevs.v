Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term111 := hreal_of_num (NUMERAL 0).
Definition term194 (x0 : hreal) (x1 : prod hreal hreal) := treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))) x1.
Definition term217 (x0 : real) := @eq Prop ((fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) x0).
Definition term185 (x0 : hreal) := treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))).
Definition term7 := forall y0 : hreal, (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term28 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term166 (x0 : prod hreal hreal) := (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (@snd hreal hreal x0)) (hreal_add (@fst hreal hreal x0) (hreal_of_num (NUMERAL 0)))) -> exists y0 : hreal, (mk_real (treal_eq (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term188 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x0)) y0) = (treal_eq (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))) y0)) x2.
Definition term209 (x0 : hreal) (x1 : prod hreal hreal) := fun y0 : hreal => (mk_real (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x1)))) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term126 (x0 : real) := (exists y0 : prod hreal hreal, (dest_real x0) = (treal_eq y0)) -> (real_le (real_of_num (NUMERAL 0)) x0) -> exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term205 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := @eq hreal (hreal_add (@snd hreal hreal x0) (hreal_add x1 (@snd hreal hreal x2))).
Definition term160 (x0 : prod hreal hreal) := treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)).
Definition term44 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => ((hreal_add x0 x1) = (hreal_add x0 y0)) = (x1 = y0)) x2.
Definition term32 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term139 := real_of_num (NUMERAL 0).
Definition term8 := forall y0 : hreal, y0 = (hreal_add (hreal_of_num (NUMERAL 0)) y0).
Definition term57 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0))) x3.
Definition term135 (x0 : prod hreal hreal) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) (mk_real (treal_eq x0)).
Definition term133 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))).
Definition term12 (x0 : hreal) := (fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term176 (x0 : prod hreal hreal) (x1 : hreal) := hreal_add (@snd hreal hreal x0) x1.
Definition term189 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x0)) y0) = (treal_eq (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))) y0)) (@pair hreal hreal (@fst hreal hreal x2) (@snd hreal hreal x2)).
Definition term195 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := @eq Prop ((treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x0)) x2) = (treal_eq (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))) x2)).
Definition term92 := and (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))))).
Definition term91 := and (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y1))).
Definition term19 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0))) x3.
Definition term208 (x0 : hreal) (x1 : prod hreal hreal) := mk_real (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x1))).
Definition term55 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1))) x2.
Definition term17 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1))) x2.
Definition term115 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term163 (x0 : prod hreal hreal) := imp (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0))).
Definition term182 (x0 : prod hreal hreal) := @eq Prop (exists y0 : hreal, (mk_real (treal_eq (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))))).
Definition term212 (x0 : real) := fun y0 : prod hreal hreal => (dest_real x0) = (treal_eq y0).
Definition term215 (x0 : hreal) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) (mk_real (treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))))).
Definition term136 (x0 : prod hreal hreal) := (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) -> exists y0 : hreal, (mk_real (treal_eq x0)) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term85 (x0 : real) := @eq Prop (real_le (real_of_num (NUMERAL 0)) x0).
Definition term198 (x0 : hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := @eq Prop (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x1)) (@pair hreal hreal (@fst hreal hreal x2) (@snd hreal hreal x2))).
Definition term68 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_le x0 y0) -> exists y1 : hreal, y0 = (hreal_add x0 y1)) x1.
Definition term27 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_add x0 x1) x2.
Definition term170 (x0 : prod hreal hreal) := hreal_add (@fst hreal hreal x0) (hreal_of_num (NUMERAL 0)).
Definition term206 (x0 : hreal) (x1 : prod hreal hreal) := @eq Prop ((hreal_add x0 (@snd hreal hreal x1)) = (@fst hreal hreal x1)).
Definition term224 := hreal_le (hreal_of_num (NUMERAL 0)).
Definition term101 (x0 : hreal) := fun y0 : hreal => (hreal_le x0 y0) = (treal_le (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))) (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))).
Definition term157 := @pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0)).
Definition term137 (x0 : real) := @eq Prop ((fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) x0).
Definition term229 := exists y0 : hreal -> real, (forall y1 : real, (real_le (real_of_num (NUMERAL 0)) y1) = (exists y2 : hreal, y1 = (y0 y2))) /\ (forall y1 : hreal, forall y2 : hreal, (hreal_le y1 y2) = (real_le (y0 y1) (y0 y2))).
Definition term142 := real_le (mk_real (treal_eq (treal_of_num (NUMERAL 0)))).
Definition term171 (x0 : prod hreal hreal) := hreal_le (@snd hreal hreal x0) (@fst hreal hreal x0).
Definition term158 := treal_le (treal_of_num (NUMERAL 0)).
Definition term114 := forall y0 : hreal, True.
Definition term168 (x0 : prod hreal hreal) := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (@snd hreal hreal x0)).
Definition term226 (x0 : hreal) := hreal_le (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_of_num (NUMERAL 0)) x0).
Definition term177 (x0 : prod hreal hreal) := fun y0 : hreal => exists y1 : hreal, (mk_real (treal_eq (@pair hreal hreal y0 (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))).
Definition term21 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add x0 x1) (hreal_add x2 x3).
Definition term186 (x0 : prod hreal hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x0)) y0) = (treal_eq (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))) y0).
Definition term210 (x0 : prod hreal hreal) := fun y0 : hreal => (@fst hreal hreal x0) = (hreal_add (@snd hreal hreal x0) y0).
Definition term152 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_le (treal_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, (mk_real (treal_eq y0)) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) x0.
Definition term53 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2))) x1.
Definition term15 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2))) x1.
Definition term100 (x0 : hreal) := fun y0 : hreal => (hreal_le x0 y0) = (real_le ((fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) x0) ((fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) y0)).
Definition term150 (x0 : prod hreal hreal) := (treal_le (treal_of_num (NUMERAL 0)) x0) -> exists y0 : hreal, (mk_real (treal_eq x0)) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term128 (x0 : real) := @eq real (mk_real (dest_real x0)).
Definition term120 (x0 : real) := @eq ((prod hreal hreal) -> Prop) (dest_real x0).
Definition term118 (x0 : real) := mk_real (dest_real x0).
Definition term230 := fun y0 : hreal -> real => (forall y1 : real, (real_le (real_of_num (NUMERAL 0)) y1) = (exists y2 : hreal, y1 = (y0 y2))) /\ (forall y1 : hreal, forall y2 : hreal, (hreal_le y1 y2) = (real_le (y0 y1) (y0 y2))).
Definition term123 (x0 : real) := imp (exists y0 : prod hreal hreal, (dest_real x0) = (treal_eq y0)).
Definition term175 (x0 : prod hreal hreal) := exists y0 : hreal, (@fst hreal hreal x0) = (hreal_add (@snd hreal hreal x0) y0).
Definition term4 (x0 : hreal) := hreal_add (hreal_of_num (NUMERAL 0)) x0.
Definition term153 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_le (treal_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, (mk_real (treal_eq y0)) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)).
Definition term90 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))).
Definition term89 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y1)).
Definition term144 (x0 : prod hreal hreal) := real_le (mk_real (treal_eq (treal_of_num (NUMERAL 0)))) (mk_real (treal_eq x0)).
Definition term141 := real_le (real_of_num (NUMERAL 0)).
Definition term1 (x0 : hreal) := forall y0 : hreal, hreal_le x0 (hreal_add x0 y0).
Definition term169 (x0 : prod hreal hreal) := hreal_le (@snd hreal hreal x0).
Definition term59 := forall y0 : prod hreal hreal, (@pair hreal hreal (@fst hreal hreal y0) (@snd hreal hreal y0)) = y0.
Definition term102 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) = (real_le ((fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) x0) ((fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) y0)).
Definition term200 (x0 : hreal) (x1 : prod hreal hreal) := hreal_add x0 (@snd hreal hreal x1).
Definition term82 (x0 : real) := fun y0 : hreal => x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term148 (x0 : prod hreal hreal) := imp (treal_le (treal_of_num (NUMERAL 0)) x0).
Definition term47 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0))) x2.
Definition term60 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => (@pair hreal hreal (@fst hreal hreal y0) (@snd hreal hreal y0)) = y0) x0.
Definition term146 := treal_of_num (NUMERAL 0).
Definition term202 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := @eq hreal (hreal_add (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x2)).
Definition term117 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))))) /\ True.
Definition term199 (x0 : hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := @eq Prop ((hreal_add (hreal_add (@snd hreal hreal x2) x0) (@snd hreal hreal x1)) = (hreal_add (@fst hreal hreal x1) (@snd hreal hreal x2))).
Definition term81 (x0 : real) := fun y0 : hreal => x0 = ((fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) y0).
Definition term222 := hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0)).
Definition term227 (x0 : real) := (exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))))) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term112 (x0 : hreal) := hreal_le (hreal_add x0 (hreal_of_num (NUMERAL 0))).
Definition term218 (x0 : hreal) := real_le (mk_real (treal_eq (treal_of_num (NUMERAL 0)))) (mk_real (treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))))).
Definition term11 (x0 : hreal) := hreal_add x0 (hreal_of_num (NUMERAL 0)).
Definition term3 (x0 : hreal) (x1 : hreal) := hreal_le x0 (hreal_add x0 x1).
Definition term220 (x0 : hreal) := treal_le (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))).
Definition term107 := forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (treal_le (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))) (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))).
Definition term106 := forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y0) ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y1)).
Definition term54 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_eq (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = ((hreal_add x0 x1) = (hreal_add y0 y1)).
Definition term52 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_eq (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = ((hreal_add x0 y0) = (hreal_add y1 y2)).
Definition term41 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, ((hreal_add x0 y0) = (hreal_add x0 y1)) = (y0 = y1).
Definition term39 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term38 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term35 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term34 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term16 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1)).
Definition term14 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2)).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term95 (x0 : hreal) (x1 : hreal) := real_le ((fun y0 : hreal => mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))) x0) ((fun y0 : hreal => mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))) x1).
Definition term23 (x0 : nat) := @pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0)).
Definition term179 (x0 : prod hreal hreal) (x1 : hreal) := (fun y0 : hreal => exists y1 : hreal, (mk_real (treal_eq (@pair hreal hreal y0 (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) (hreal_add (@snd hreal hreal x0) x1).
Definition term193 (x0 : hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x1)) x2.
Definition term98 (x0 : hreal) := @pair hreal hreal x0 (hreal_of_num (NUMERAL 0)).
Definition term178 (x0 : prod hreal hreal) := (fun y0 : hreal => exists y1 : hreal, (mk_real (treal_eq (@pair hreal hreal y0 (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) (@fst hreal hreal x0).
Definition term122 (x0 : real) := imp ((exists y0 : prod hreal hreal, (dest_real x0) = (treal_eq y0)) = ((dest_real (mk_real (dest_real x0))) = (dest_real x0))).
Definition term109 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))))) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (treal_le (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))) (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))).
Definition term108 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y1))) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y0) ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y1))).
Definition term162 (x0 : prod hreal hreal) := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (@snd hreal hreal x0)) (hreal_add (@fst hreal hreal x0) (hreal_of_num (NUMERAL 0))).
Definition term225 (x0 : hreal) := hreal_le (hreal_of_num (NUMERAL 0)) x0.
Definition term192 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := @eq Prop ((fun y0 : prod hreal hreal => (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x0)) y0) = (treal_eq (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))) y0)) x2).
Definition term197 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := hreal_add (@fst hreal hreal x0) (@snd hreal hreal x1).
Definition term228 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) -> exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))))) /\ ((exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))))) -> real_le (real_of_num (NUMERAL 0)) x0).
Definition term130 (x0 : real) (x1 : prod hreal hreal) := imp (x0 = (mk_real (treal_eq x1))).
Definition term145 (x0 : prod hreal hreal) := treal_le (treal_of_num (NUMERAL 0)) x0.
Definition term129 (x0 : real) (x1 : prod hreal hreal) := imp ((mk_real (dest_real x0)) = (mk_real (treal_eq x1))).
Definition term74 (x0 : hreal) := (fun y0 : hreal => (fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) y0) x0.
Definition term174 (x0 : prod hreal hreal) := (hreal_le (@snd hreal hreal x0) (@fst hreal hreal x0)) -> exists y0 : hreal, (@fst hreal hreal x0) = (hreal_add (@snd hreal hreal x0) y0).
Definition term173 (x0 : prod hreal hreal) := (hreal_le (@snd hreal hreal x0) (@fst hreal hreal x0)) -> exists y0 : hreal, (mk_real (treal_eq (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term30 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term132 (x0 : prod hreal hreal) (x1 : real) := (x1 = (mk_real (treal_eq x0))) -> (real_le (real_of_num (NUMERAL 0)) x1) -> exists y0 : hreal, x1 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term159 := treal_le (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))).
Definition term219 (x0 : hreal) := treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))).
Definition term172 (x0 : prod hreal hreal) := imp (hreal_le (@snd hreal hreal x0) (@fst hreal hreal x0)).
Definition term86 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term211 (x0 : prod hreal hreal) (x1 : real) := ((dest_real x1) = (treal_eq x0)) -> (real_le (real_of_num (NUMERAL 0)) x1) -> exists y0 : hreal, x1 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term203 (x0 : hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := @eq Prop ((hreal_add (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x2)) = (hreal_add (@snd hreal hreal x1) (@fst hreal hreal x2))).
Definition term96 (x0 : hreal) (x1 : hreal) := real_le (mk_real (treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))))) (mk_real (treal_eq (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))))).
Definition term24 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term180 (x0 : hreal) (x1 : prod hreal hreal) := exists y0 : hreal, (mk_real (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x1)))) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term165 (x0 : prod hreal hreal) := exists y0 : hreal, (mk_real (treal_eq (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term149 (x0 : prod hreal hreal) := exists y0 : hreal, (mk_real (treal_eq x0)) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term221 (x0 : hreal) := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (hreal_add x0 (hreal_of_num (NUMERAL 0))).
Definition term10 (x0 : hreal) := (fun y0 : hreal => (hreal_add y0 (hreal_of_num (NUMERAL 0))) = y0) x0.
Definition term201 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := hreal_add (@snd hreal hreal x0) (@fst hreal hreal x1).
Definition term37 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term36 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term80 (x0 : hreal) := @eq real ((fun y0 : hreal => mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))) x0).
Definition term25 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term116 (x0 : Prop) := forall y0 : hreal, x0.
Definition term97 (x0 : hreal) (x1 : hreal) := treal_le (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))) (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))).
Definition term105 := fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) = (treal_le (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))) (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))).
Definition term104 := fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) = (real_le ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y0) ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y1)).
Definition term33 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term88 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))).
Definition term87 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = ((fun y2 : hreal => mk_real (treal_eq (@pair hreal hreal y2 (hreal_of_num (NUMERAL 0))))) y1)).
Definition term76 := fun y0 : hreal => mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))).
Definition term79 (x0 : hreal) := @eq real ((fun y0 : hreal => (fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) y0) x0).
Definition term156 (x0 : prod hreal hreal) := @eq Prop ((treal_le (treal_of_num (NUMERAL 0)) x0) -> exists y0 : hreal, (mk_real (treal_eq x0)) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))))).
Definition term138 (x0 : real) := @eq Prop ((real_le (real_of_num (NUMERAL 0)) x0) -> exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))))).
Definition term147 (x0 : prod hreal hreal) := imp (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))).
Definition term43 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, ((hreal_add x0 x1) = (hreal_add x0 y0)) = (x1 = y0).
Definition term83 (x0 : real) := exists y0 : hreal, x0 = ((fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) y0).
Definition term29 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term6 := fun y0 : hreal => y0 = (hreal_add (hreal_of_num (NUMERAL 0)) y0).
Definition term191 (x0 : hreal) (x1 : prod hreal hreal) := treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (@fst hreal hreal x1) (@snd hreal hreal x1)).
Definition term119 (x0 : real) := @eq ((prod hreal hreal) -> Prop) (dest_real (mk_real (dest_real x0))).
Definition term216 (x0 : hreal) := real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))))).
Definition term50 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_add x0 y0) = (hreal_add y0 x0)) x1.
Definition term66 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) -> exists y2 : hreal, y1 = (hreal_add y0 y2)) x0.
Definition term48 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add y0 y1) = (hreal_add y1 y0)) x0.
Definition term0 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, hreal_le y0 (hreal_add y0 y1)) x0.
Definition term183 (x0 : type1233) (x1 : type1233) := forall y0 : prod hreal hreal, (x0 y0) = (x1 y0).
Definition term9 (x0 : hreal) := (fun y0 : hreal => y0 = (hreal_add (hreal_of_num (NUMERAL 0)) y0)) x0.
Definition term127 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term84 (x0 : real) := exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term77 (x0 : hreal) := mk_real (treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0)))).
Definition term46 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1))) x1.
Definition term42 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, ((hreal_add x0 y0) = (hreal_add x0 y1)) = (y0 = y1)) x1.
Definition term103 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) = (treal_le (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))) (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0)))).
Definition term164 (x0 : prod hreal hreal) := imp (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (@snd hreal hreal x0)) (hreal_add (@fst hreal hreal x0) (hreal_of_num (NUMERAL 0)))).
Definition term61 (x0 : prod hreal hreal) := @pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0).
Definition term75 (x0 : hreal) := (fun y0 : hreal => mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))) x0.
Definition term110 (x0 : hreal) (x1 : hreal) := hreal_le (hreal_add x0 (hreal_of_num (NUMERAL 0))) (hreal_add x1 (hreal_of_num (NUMERAL 0))).
Definition term167 (x0 : prod hreal hreal) := hreal_add (hreal_of_num (NUMERAL 0)) (@snd hreal hreal x0).
Definition term204 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := hreal_add (@snd hreal hreal x0) (hreal_add x1 (@snd hreal hreal x2)).
Definition term2 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => hreal_le x0 (hreal_add x0 y0)) x1.
Definition term94 (x0 : hreal) := real_le (mk_real (treal_eq (@pair hreal hreal x0 (hreal_of_num (NUMERAL 0))))).
Definition term99 (x0 : hreal) (x1 : hreal) := @eq Prop (hreal_le x0 x1).
Definition term20 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term22 (x0 : nat) := (fun y0 : nat => (treal_of_num y0) = (@pair hreal hreal (hreal_of_num y0) (hreal_of_num (NUMERAL 0)))) x0.
Definition term214 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0) x0.
Definition term124 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term31 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term56 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_eq (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = ((hreal_add x0 x1) = (hreal_add x2 y0)).
Definition term18 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0)).
Definition term187 (x0 : prod hreal hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x0)) y0) = (treal_eq (@pair hreal hreal x1 (hreal_of_num (NUMERAL 0))) y0).
Definition term121 (x0 : real) := @eq Prop (exists y0 : prod hreal hreal, (dest_real x0) = (treal_eq y0)).
Definition term69 (x0 : hreal) (x1 : hreal) := (hreal_le x1 x0) -> exists y0 : hreal, x0 = (hreal_add x1 y0).
Definition term134 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, y0 = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) x0.
Definition term113 := fun y0 : hreal => True.
Definition term93 (x0 : hreal) := real_le ((fun y0 : hreal => mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))) x0).
Definition term181 (x0 : prod hreal hreal) := @eq Prop ((fun y0 : hreal => exists y1 : hreal, (mk_real (treal_eq (@pair hreal hreal y0 (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) (@fst hreal hreal x0)).
Definition term78 := fun y0 : hreal => (fun y1 : hreal => mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))) y0.
Definition term49 (x0 : hreal) := forall y0 : hreal, (hreal_add x0 y0) = (hreal_add y0 x0).
Definition term125 (x0 : real) := ((exists y0 : prod hreal hreal, (dest_real x0) = (treal_eq y0)) = ((dest_real (mk_real (dest_real x0))) = (dest_real x0))) -> (real_le (real_of_num (NUMERAL 0)) x0) -> exists y0 : hreal, x0 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term151 := fun y0 : prod hreal hreal => (treal_le (treal_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, (mk_real (treal_eq y0)) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0))))).
Definition term26 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add x0 (hreal_add x1 x2).
Definition term143 (x0 : prod hreal hreal) := real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0)).
Definition term5 := fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term207 (x0 : hreal) (x1 : prod hreal hreal) := @eq hreal (hreal_add x0 (@snd hreal hreal x1)).
Definition term67 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) -> exists y1 : hreal, y0 = (hreal_add x0 y1).
Definition term196 (x0 : prod hreal hreal) (x1 : hreal) (x2 : prod hreal hreal) := hreal_add (hreal_add (@snd hreal hreal x0) x1) (@snd hreal hreal x2).
Definition term71 (x0 : real) := dest_real (mk_real (dest_real x0)).
Definition term155 (x0 : prod hreal hreal) := @eq Prop ((fun y0 : prod hreal hreal => (treal_le (treal_of_num (NUMERAL 0)) y0) -> exists y1 : hreal, (mk_real (treal_eq y0)) = (mk_real (treal_eq (@pair hreal hreal y1 (hreal_of_num (NUMERAL 0)))))) x0).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term190 (x0 : hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x1)) (@pair hreal hreal (@fst hreal hreal x2) (@snd hreal hreal x2)).
Definition term161 (x0 : prod hreal hreal) := treal_le (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)).
Definition term213 := fun y0 : real => real_le (real_of_num (NUMERAL 0)) y0.
Definition term58 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_eq (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term131 (x0 : prod hreal hreal) (x1 : real) := ((mk_real (dest_real x1)) = (mk_real (treal_eq x0))) -> (real_le (real_of_num (NUMERAL 0)) x1) -> exists y0 : hreal, x1 = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term140 := mk_real (treal_eq (treal_of_num (NUMERAL 0))).
Definition term154 (x0 : prod hreal hreal) := (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0))) -> exists y0 : hreal, (mk_real (treal_eq (@pair hreal hreal (@fst hreal hreal x0) (@snd hreal hreal x0)))) = (mk_real (treal_eq (@pair hreal hreal y0 (hreal_of_num (NUMERAL 0))))).
Definition term64 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term184 (x0 : hreal) (x1 : prod hreal hreal) := treal_eq (@pair hreal hreal (hreal_add (@snd hreal hreal x1) x0) (@snd hreal hreal x1)).
Definition term223 := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term51 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_eq (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = ((hreal_add y0 y1) = (hreal_add y2 y3))) x0.
Definition term45 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2))) x0.
Definition term40 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y1) = (hreal_add y0 y2)) = (y1 = y2)) x0.
Definition term13 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_le (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = (hreal_le (hreal_add y0 y1) (hreal_add y2 y3))) x0.
Definition term70 (x0 : real) := exists y0 : prod hreal hreal, (dest_real x0) = (treal_eq y0).
Definition term73 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : hreal => x0 y0) x1.
