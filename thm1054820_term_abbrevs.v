Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 := @eq Prop (forall y0 : type1669, exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3)).
Definition term42 := @eq Prop (forall y0 : type1669, exists y1 : nat -> nat, (fun y2 : type1669 => fun y3 : nat -> nat => forall y4 : Prop, forall y5 : nat, ((NUMLEFT (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) y0 y1).
Definition term45 (x0 : type1249) (x1 : type1669) := (fun y0 : nat -> nat => forall y1 : Prop, forall y2 : nat, ((NUMLEFT (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2)) (x0 x1).
Definition term51 := fun y0 : type1249 => forall y1 : type1669, (fun y2 : type1669 => fun y3 : nat -> nat => forall y4 : Prop, forall y5 : nat, ((NUMLEFT (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) y1 (y0 y1).
Definition term38 (x0 : type1669) := fun y0 : nat -> nat => (fun y1 : type1669 => fun y2 : nat -> nat => forall y3 : Prop, forall y4 : nat, ((NUMLEFT (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) x0 y0.
Definition term37 (x0 : nat -> nat) := (fun y0 : nat -> nat => forall y1 : Prop, forall y2 : nat, ((NUMLEFT (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2)) x0.
Definition term18 (x0 : nat -> nat) (x1 : Prop) := forall y0 : nat, ((NUMLEFT (NUMSUM x1 y0)) = x1) /\ ((x0 (NUMSUM x1 y0)) = y0).
Definition term17 (x0 : nat -> nat) (x1 : Prop) := forall y0 : nat, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y1 : type1260 => forall y2 : type1670, exists y3 : nat -> nat, forall y4 : Prop, forall y5 : nat, ((y1 y2 (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM x1 y0)) = x1) /\ ((x0 (NUMSUM x1 y0)) = y0).
Definition term14 (x0 : nat -> nat) (x1 : Prop) (x2 : nat) := ((NUMLEFT (NUMSUM x1 x2)) = x1) /\ ((x0 (NUMSUM x1 x2)) = x2).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term33 := exists y0 : type1249, forall y1 : type1669, (fun y2 : type1669 => fun y3 : nat -> nat => forall y4 : Prop, forall y5 : nat, ((NUMLEFT (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) y1 (y0 y1).
Definition term31 (x0 : type1246) := exists y0 : type1249, forall y1 : type1669, x0 y1 (y0 y1).
Definition term49 (x0 : type1249) := forall y0 : type1669, (fun y1 : type1669 => fun y2 : nat -> nat => forall y3 : Prop, forall y4 : nat, ((NUMLEFT (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) y0 (x0 y0).
Definition term6 (x0 : Prop) (x1 : nat) := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM x0 x1).
Definition term11 (x0 : nat) (x1 : Prop) := and ((NUMLEFT (NUMSUM x1 x0)) = x1).
Definition term55 := fun y0 : type341 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat) y0).
Definition term9 (x0 : Prop) (x1 : nat) := @eq Prop (NUMLEFT (NUMSUM x0 x1)).
Definition term34 := fun y0 : type1669 => fun y1 : nat -> nat => forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term7 (x0 : Prop) (x1 : nat) := NUMLEFT (NUMSUM x0 x1).
Definition term54 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term50 (x0 : type1249) := forall y0 : type1669, forall y1 : Prop, forall y2 : nat, ((NUMLEFT (NUMSUM y1 y2)) = y1) /\ ((x0 y0 (NUMSUM y1 y2)) = y2).
Definition term57 := (fun y0 : type1249 => forall y1 : type1669, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y0 y1 (NUMSUM y2 y3)) = y3)) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat) (fun y0 : type1249 => forall y1 : type1669, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y0 y1 (NUMSUM y2 y3)) = y3))).
Definition term0 := (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4))).
Definition term56 := (fun y0 : type341 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat) y0)) (fun y0 : type1249 => forall y1 : type1669, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y0 y1 (NUMSUM y2 y3)) = y3)).
Definition term13 (x0 : nat -> nat) (x1 : Prop) (x2 : nat) := ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM x1 x2)) = x1) /\ ((x0 (NUMSUM x1 x2)) = x2).
Definition term39 (x0 : type1669) := exists y0 : nat -> nat, (fun y1 : type1669 => fun y2 : nat -> nat => forall y3 : Prop, forall y4 : nat, ((NUMLEFT (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) x0 y0.
Definition term52 := fun y0 : type1249 => forall y1 : type1669, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y0 y1 (NUMSUM y2 y3)) = y3).
Definition term2 := (fun y0 : type1670 => exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y4 : type1260 => forall y5 : type1670, exists y6 : nat -> nat, forall y7 : Prop, forall y8 : nat, ((y4 y5 (NUMSUM y7 y8)) = y7) /\ ((y6 (NUMSUM y7 y8)) = y8)) y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Definition term46 (x0 : type1249) (x1 : type1669) := forall y0 : Prop, forall y1 : nat, ((NUMLEFT (NUMSUM y0 y1)) = y0) /\ ((x0 x1 (NUMSUM y0 y1)) = y1).
Definition term22 (x0 : nat -> nat) := forall y0 : Prop, forall y1 : nat, ((NUMLEFT (NUMSUM y0 y1)) = y0) /\ ((x0 (NUMSUM y0 y1)) = y1).
Definition term21 (x0 : nat -> nat) := forall y0 : Prop, forall y1 : nat, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y2 : type1260 => forall y3 : type1670, exists y4 : nat -> nat, forall y5 : Prop, forall y6 : nat, ((y2 y3 (NUMSUM y5 y6)) = y5) /\ ((y4 (NUMSUM y5 y6)) = y6)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM y0 y1)) = y0) /\ ((x0 (NUMSUM y0 y1)) = y1).
Definition term35 (x0 : type1669) := (fun y0 : type1669 => fun y1 : nat -> nat => forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3)) x0.
Definition term3 := @pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))).
Definition term47 (x0 : type1249) := fun y0 : type1669 => (fun y1 : type1669 => fun y2 : nat -> nat => forall y3 : Prop, forall y4 : nat, ((NUMLEFT (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) y0 (x0 y0).
Definition term24 := fun y0 : nat -> nat => forall y1 : Prop, forall y2 : nat, ((NUMLEFT (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2).
Definition term23 := fun y0 : nat -> nat => forall y1 : Prop, forall y2 : nat, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y3 : type1260 => forall y4 : type1670, exists y5 : nat -> nat, forall y6 : Prop, forall y7 : nat, ((y3 y4 (NUMSUM y6 y7)) = y6) /\ ((y5 (NUMSUM y6 y7)) = y7)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2).
Definition term48 (x0 : type1249) := fun y0 : type1669 => forall y1 : Prop, forall y2 : nat, ((NUMLEFT (NUMSUM y1 y2)) = y1) /\ ((x0 y0 (NUMSUM y1 y2)) = y2).
Definition term20 (x0 : nat -> nat) := fun y0 : Prop => forall y1 : nat, ((NUMLEFT (NUMSUM y0 y1)) = y0) /\ ((x0 (NUMSUM y0 y1)) = y1).
Definition term19 (x0 : nat -> nat) := fun y0 : Prop => forall y1 : nat, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y2 : type1260 => forall y3 : type1670, exists y4 : nat -> nat, forall y5 : Prop, forall y6 : nat, ((y2 y3 (NUMSUM y5 y6)) = y5) /\ ((y4 (NUMSUM y5 y6)) = y6)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM y0 y1)) = y0) /\ ((x0 (NUMSUM y0 y1)) = y1).
Definition term8 (x0 : Prop) (x1 : nat) := @eq Prop (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM x0 x1)).
Definition term53 := exists y0 : type1249, forall y1 : type1669, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y0 y1 (NUMSUM y2 y3)) = y3).
Definition term25 := exists y0 : nat -> nat, forall y1 : Prop, forall y2 : nat, ((NUMLEFT (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2).
Definition term4 := exists y0 : nat -> nat, forall y1 : Prop, forall y2 : nat, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y3 : type1260 => forall y4 : type1670, exists y5 : nat -> nat, forall y6 : Prop, forall y7 : nat, ((y3 y4 (NUMSUM y6 y7)) = y6) /\ ((y5 (NUMSUM y6 y7)) = y7)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM y1 y2)) = y1) /\ ((y0 (NUMSUM y1 y2)) = y2).
Definition term16 (x0 : nat -> nat) (x1 : Prop) := fun y0 : nat => ((NUMLEFT (NUMSUM x1 y0)) = x1) /\ ((x0 (NUMSUM x1 y0)) = y0).
Definition term15 (x0 : nat -> nat) (x1 : Prop) := fun y0 : nat => ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y1 : type1260 => forall y2 : type1670, exists y3 : nat -> nat, forall y4 : Prop, forall y5 : nat, ((y1 y2 (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM x1 y0)) = x1) /\ ((x0 (NUMSUM x1 y0)) = y0).
Definition term36 (x0 : type1669) (x1 : nat -> nat) := (fun y0 : type1669 => fun y1 : nat -> nat => forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3)) x0 x1.
Definition term26 := forall y0 : type1669, exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term1 := forall y0 : type1670, exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y4 : type1260 => forall y5 : type1670, exists y6 : nat -> nat, forall y7 : Prop, forall y8 : nat, ((y4 y5 (NUMSUM y7 y8)) = y7) /\ ((y6 (NUMSUM y7 y8)) = y8)) y0 (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term5 := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Definition term10 (x0 : nat) (x1 : Prop) := and ((@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun y0 : type1260 => forall y1 : type1670, exists y2 : nat -> nat, forall y3 : Prop, forall y4 : nat, ((y0 y1 (NUMSUM y3 y4)) = y3) /\ ((y2 (NUMSUM y3 y4)) = y4)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))) (NUMSUM x1 x0)) = x1).
Definition term41 := fun y0 : type1669 => exists y1 : nat -> nat, forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3).
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term32 := forall y0 : type1669, exists y1 : nat -> nat, (fun y2 : type1669 => fun y3 : nat -> nat => forall y4 : Prop, forall y5 : nat, ((NUMLEFT (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) y0 y1.
Definition term30 (x0 : type1246) := forall y0 : type1669, exists y1 : nat -> nat, x0 y0 y1.
Definition term44 (x0 : type1249) (x1 : type1669) := (fun y0 : type1669 => fun y1 : nat -> nat => forall y2 : Prop, forall y3 : nat, ((NUMLEFT (NUMSUM y2 y3)) = y2) /\ ((y1 (NUMSUM y2 y3)) = y3)) x1 (x0 x1).
Definition term12 (x0 : nat -> nat) (x1 : Prop) (x2 : nat) := x0 (NUMSUM x1 x2).
Definition term40 := fun y0 : type1669 => exists y1 : nat -> nat, (fun y2 : type1669 => fun y3 : nat -> nat => forall y4 : Prop, forall y5 : nat, ((NUMLEFT (NUMSUM y4 y5)) = y4) /\ ((y3 (NUMSUM y4 y5)) = y5)) y0 y1.