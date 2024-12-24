Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term66 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 (x0 : int) := (fun y0 : int => forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1)) x0.
Definition term2 (x0 : int) := (fun y0 : int => forall y1 : int, (rem y0 (int_neg y1)) = (rem y0 y1)) x0.
Definition term34 := (forall y0 : nat, forall y1 : int, (rem (int_of_num y0) (int_abs y1)) = (rem (int_of_num y0) y1)) /\ (forall y0 : nat, forall y1 : int, (rem (int_neg (int_of_num y0)) (int_abs y1)) = (rem (int_neg (int_of_num y0)) y1)).
Definition term61 (x0 : nat) := rem (int_of_num x0).
Definition term48 (x0 : nat) := fun y0 : nat => (rem (int_of_num x0) (int_abs (int_of_num y0))) = (rem (int_of_num x0) (int_of_num y0)).
Definition term72 (x0 : nat) := fun y0 : int => (rem (int_neg (int_of_num x0)) (int_abs y0)) = (rem (int_neg (int_of_num x0)) y0).
Definition term8 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term83 (x0 : nat) := fun y0 : nat => (rem (int_neg (int_of_num x0)) (int_abs (int_of_num y0))) = (rem (int_neg (int_of_num x0)) (int_of_num y0)).
Definition term73 (x0 : nat) (x1 : int) := (fun y0 : int => (rem (int_neg (int_of_num x0)) (int_abs y0)) = (rem (int_neg (int_of_num x0)) y0)) x1.
Definition term38 (x0 : nat) (x1 : int) := (fun y0 : int => (rem (int_of_num x0) (int_abs y0)) = (rem (int_of_num x0) y0)) x1.
Definition term20 (x0 : nat) := (fun y0 : int => forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1)) (int_of_num x0).
Definition term4 (x0 : int) (x1 : int) := (fun y0 : int => (rem x0 (int_neg y0)) = (rem x0 y0)) x1.
Definition term15 (x0 : int) := forall y0 : int, (rem x0 (int_abs y0)) = (rem x0 y0).
Definition term3 (x0 : int) := forall y0 : int, (rem x0 (int_neg y0)) = (rem x0 y0).
Definition term88 (x0 : nat) (x1 : nat) := (fun y0 : int => (rem (int_neg (int_of_num x0)) (int_abs y0)) = (rem (int_neg (int_of_num x0)) y0)) (int_neg (int_of_num x1)).
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : int => (rem (int_of_num x0) (int_abs y0)) = (rem (int_of_num x0) y0)) (int_neg (int_of_num x1)).
Definition term75 (x0 : nat) (x1 : int) := rem (int_neg (int_of_num x0)) x1.
Definition term5 (x0 : int) (x1 : int) := rem x0 (int_neg x1).
Definition term81 (x0 : nat) (x1 : nat) := rem (int_neg (int_of_num x0)) (int_of_num x1).
Definition term37 (x0 : nat) := fun y0 : int => (rem (int_of_num x0) (int_abs y0)) = (rem (int_of_num x0) y0).
Definition term7 (x0 : int) := int_abs (int_neg x0).
Definition term82 (x0 : nat) := fun y0 : nat => (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) (int_of_num y0).
Definition term47 (x0 : nat) := fun y0 : nat => (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) (int_of_num y0).
Definition term28 (x0 : nat) := (fun y0 : int => forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1)) (int_neg (int_of_num x0)).
Definition term78 (x0 : nat) := @eq Prop (forall y0 : int, (rem (int_neg (int_of_num x0)) (int_abs y0)) = (rem (int_neg (int_of_num x0)) y0)).
Definition term43 (x0 : nat) := @eq Prop (forall y0 : int, (rem (int_of_num x0) (int_abs y0)) = (rem (int_of_num x0) y0)).
Definition term71 (x0 : nat) := (forall y0 : nat, (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) (int_neg (int_of_num y0))).
Definition term36 (x0 : nat) := (forall y0 : nat, (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) (int_neg (int_of_num y0))).
Definition term12 := (forall y0 : nat, (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) (int_neg (int_of_num y0))).
Definition term46 (x0 : nat) (x1 : nat) := rem (int_of_num x0) (int_of_num x1).
Definition term6 (x0 : int) := (fun y0 : int => (int_abs (int_neg y0)) = (int_abs y0)) x0.
Definition term87 (x0 : nat) := and (forall y0 : nat, (rem (int_neg (int_of_num x0)) (int_abs (int_of_num y0))) = (rem (int_neg (int_of_num x0)) (int_of_num y0))).
Definition term52 (x0 : nat) := and (forall y0 : nat, (rem (int_of_num x0) (int_abs (int_of_num y0))) = (rem (int_of_num x0) (int_of_num y0))).
Definition term91 (x0 : nat) := fun y0 : nat => (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) (int_neg (int_of_num y0)).
Definition term56 (x0 : nat) := fun y0 : nat => (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) (int_neg (int_of_num y0)).
Definition term9 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term29 (x0 : nat) := forall y0 : int, (rem (int_neg (int_of_num x0)) (int_abs y0)) = (rem (int_neg (int_of_num x0)) y0).
Definition term21 (x0 : nat) := forall y0 : int, (rem (int_of_num x0) (int_abs y0)) = (rem (int_of_num x0) y0).
Definition term79 (x0 : nat) (x1 : nat) := (fun y0 : int => (rem (int_neg (int_of_num x0)) (int_abs y0)) = (rem (int_neg (int_of_num x0)) y0)) (int_of_num x1).
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : int => (rem (int_of_num x0) (int_abs y0)) = (rem (int_of_num x0) y0)) (int_of_num x1).
Definition term45 (x0 : nat) (x1 : nat) := rem (int_of_num x0) (int_abs (int_of_num x1)).
Definition term74 (x0 : nat) (x1 : int) := rem (int_neg (int_of_num x0)) (int_abs x1).
Definition term33 := forall y0 : nat, forall y1 : int, (rem (int_neg (int_of_num y0)) (int_abs y1)) = (rem (int_neg (int_of_num y0)) y1).
Definition term25 := forall y0 : nat, forall y1 : int, (rem (int_of_num y0) (int_abs y1)) = (rem (int_of_num y0) y1).
Definition term19 := @eq Prop (forall y0 : int, forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1)).
Definition term65 := forall y0 : nat, True.
Definition term57 (x0 : nat) := fun y0 : nat => (rem (int_of_num x0) (int_abs (int_neg (int_of_num y0)))) = (rem (int_of_num x0) (int_neg (int_of_num y0))).
Definition term86 (x0 : nat) := and (forall y0 : nat, (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) (int_of_num y0)).
Definition term51 (x0 : nat) := and (forall y0 : nat, (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) (int_of_num y0)).
Definition term26 := and (forall y0 : nat, (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) (int_of_num y0)).
Definition term17 := forall y0 : int, forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1).
Definition term31 := fun y0 : nat => forall y1 : int, (rem (int_neg (int_of_num y0)) (int_abs y1)) = (rem (int_neg (int_of_num y0)) y1).
Definition term23 := fun y0 : nat => forall y1 : int, (rem (int_of_num y0) (int_abs y1)) = (rem (int_of_num y0) y1).
Definition term1 (x0 : nat) := int_abs (int_of_num x0).
Definition term64 := fun y0 : nat => True.
Definition term13 := fun y0 : int => forall y1 : int, (rem y0 (int_abs y1)) = (rem y0 y1).
Definition term99 (x0 : nat) (x1 : nat) := @eq int (rem (int_neg (int_of_num x0)) (int_abs (int_neg (int_of_num x1)))).
Definition term22 := fun y0 : nat => (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) (int_of_num y0).
Definition term98 (x0 : nat) (x1 : nat) := @eq int (rem (int_neg (int_of_num x0)) (int_of_num x1)).
Definition term11 := forall y0 : int, (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) y0.
Definition term90 (x0 : nat) (x1 : nat) := rem (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term39 (x0 : nat) (x1 : int) := rem (int_of_num x0) (int_abs x1).
Definition term77 (x0 : nat) := @eq Prop (forall y0 : int, (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) y0).
Definition term42 (x0 : nat) := @eq Prop (forall y0 : int, (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) y0).
Definition term18 := @eq Prop (forall y0 : int, (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) y0).
Definition term95 (x0 : nat) := (forall y0 : nat, (rem (int_neg (int_of_num x0)) (int_abs (int_of_num y0))) = (rem (int_neg (int_of_num x0)) (int_of_num y0))) /\ (forall y0 : nat, (rem (int_neg (int_of_num x0)) (int_abs (int_neg (int_of_num y0)))) = (rem (int_neg (int_of_num x0)) (int_neg (int_of_num y0)))).
Definition term60 (x0 : nat) := (forall y0 : nat, (rem (int_of_num x0) (int_abs (int_of_num y0))) = (rem (int_of_num x0) (int_of_num y0))) /\ (forall y0 : nat, (rem (int_of_num x0) (int_abs (int_neg (int_of_num y0)))) = (rem (int_of_num x0) (int_neg (int_of_num y0)))).
Definition term27 := and (forall y0 : nat, forall y1 : int, (rem (int_of_num y0) (int_abs y1)) = (rem (int_of_num y0) y1)).
Definition term97 (x0 : nat) (x1 : nat) := @eq int (rem (int_neg (int_of_num x0)) (int_abs (int_of_num x1))).
Definition term100 (x0 : nat) := int_neg (int_of_num x0).
Definition term0 (x0 : nat) := (fun y0 : nat => (int_abs (int_of_num y0)) = (int_of_num y0)) x0.
Definition term96 (x0 : nat) := rem (int_neg (int_of_num x0)).
Definition term55 (x0 : nat) (x1 : nat) := rem (int_of_num x0) (int_neg (int_of_num x1)).
Definition term84 (x0 : nat) := forall y0 : nat, (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) (int_of_num y0).
Definition term49 (x0 : nat) := forall y0 : nat, (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) (int_of_num y0).
Definition term32 := forall y0 : nat, (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) (int_neg (int_of_num y0)).
Definition term69 (x0 : nat) (x1 : nat) := @eq int (rem (int_of_num x0) (int_abs (int_neg (int_of_num x1)))).
Definition term63 (x0 : nat) (x1 : nat) := @eq int (rem (int_of_num x0) (int_of_num x1)).
Definition term92 (x0 : nat) := fun y0 : nat => (rem (int_neg (int_of_num x0)) (int_abs (int_neg (int_of_num y0)))) = (rem (int_neg (int_of_num x0)) (int_neg (int_of_num y0))).
Definition term89 (x0 : nat) (x1 : nat) := rem (int_neg (int_of_num x0)) (int_abs (int_neg (int_of_num x1))).
Definition term67 (x0 : Prop) := forall y0 : nat, x0.
Definition term40 (x0 : nat) (x1 : int) := rem (int_of_num x0) x1.
Definition term93 (x0 : nat) := forall y0 : nat, (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) (int_neg (int_of_num y0)).
Definition term58 (x0 : nat) := forall y0 : nat, (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) (int_neg (int_of_num y0)).
Definition term80 (x0 : nat) (x1 : nat) := rem (int_neg (int_of_num x0)) (int_abs (int_of_num x1)).
Definition term24 := forall y0 : nat, (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) (int_of_num y0).
Definition term30 := fun y0 : nat => (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) (int_neg (int_of_num y0)).
Definition term76 (x0 : nat) := fun y0 : int => (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) y0.
Definition term41 (x0 : nat) := fun y0 : int => (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) y0.
Definition term68 (x0 : nat) := int_abs (int_neg (int_of_num x0)).
Definition term54 (x0 : nat) (x1 : nat) := rem (int_of_num x0) (int_abs (int_neg (int_of_num x1))).
Definition term85 (x0 : nat) := forall y0 : nat, (rem (int_neg (int_of_num x0)) (int_abs (int_of_num y0))) = (rem (int_neg (int_of_num x0)) (int_of_num y0)).
Definition term50 (x0 : nat) := forall y0 : nat, (rem (int_of_num x0) (int_abs (int_of_num y0))) = (rem (int_of_num x0) (int_of_num y0)).
Definition term70 (x0 : nat) := forall y0 : int, (fun y1 : int => (rem (int_neg (int_of_num x0)) (int_abs y1)) = (rem (int_neg (int_of_num x0)) y1)) y0.
Definition term35 (x0 : nat) := forall y0 : int, (fun y1 : int => (rem (int_of_num x0) (int_abs y1)) = (rem (int_of_num x0) y1)) y0.
Definition term16 := fun y0 : int => (fun y1 : int => forall y2 : int, (rem y1 (int_abs y2)) = (rem y1 y2)) y0.
Definition term62 (x0 : nat) (x1 : nat) := @eq int (rem (int_of_num x0) (int_abs (int_of_num x1))).
Definition term94 (x0 : nat) := forall y0 : nat, (rem (int_neg (int_of_num x0)) (int_abs (int_neg (int_of_num y0)))) = (rem (int_neg (int_of_num x0)) (int_neg (int_of_num y0))).
Definition term59 (x0 : nat) := forall y0 : nat, (rem (int_of_num x0) (int_abs (int_neg (int_of_num y0)))) = (rem (int_of_num x0) (int_neg (int_of_num y0))).
