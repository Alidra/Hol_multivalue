Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_MONO_LE_IMP_term_abbrevs.
Require Import LE_MULT2_spec.
Require Import LE_REFL_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm86199_spec.
Lemma lem150396 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem150397 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem150398 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem150397 A P) (@lem150396 A P)). Qed.
Lemma lem150399 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem150398 A P Q). Qed.
Lemma lem150400 {A : Type'} (P : Prop) (Q : A -> Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem150411 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem150400 A P Q) (@lem150399 A P Q)). Qed.
Lemma lem150412 (P : Prop) (Q : nat -> Prop) : (term5 P Q) = (term6 P Q).
Proof. exact (@lem150411 nat P Q). Qed.
Lemma lem150413 (x : nat) (y : nat) : (term7 x y) = (term8 x y).
Proof. exact (@lem150412 (Peano.le x y) (term9 x y)). Qed.
Lemma lem150414 (x : nat) (y : nat) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (eq_refl (term10 x y n)). Qed.
Lemma lem150415 (x : nat) (y : nat) : (term12 x y) = (term12 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem150416 (x : nat) (y : nat) (n : nat) : (term13 x y n) = (term14 x y n).
Proof. exact (MK_COMB (@lem150415 x y) (@lem150414 x y n)). Qed.
Lemma lem150417 (x : nat) (y : nat) : (term15 x y) = (term16 x y).
Proof. exact (fun_ext (fun n : nat => @lem150416 x y n)). Qed.
Lemma lem150418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150419 (x : nat) (y : nat) : (term7 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem150418) (@lem150417 x y)). Qed.
Lemma lem150420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem150421 (x : nat) (y : nat) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem150420) (@lem150419 x y)). Qed.
Lemma lem150422 (x : nat) (y : nat) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (eq_refl (term10 x y n)). Qed.
Lemma lem150423 (x : nat) (y : nat) : (term20 x y) = (term9 x y).
Proof. exact (fun_ext (fun n : nat => @lem150422 x y n)). Qed.
Lemma lem150424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150425 (x : nat) (y : nat) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem150424) (@lem150423 x y)). Qed.
Lemma lem150426 (x : nat) (y : nat) : (term12 x y) = (term12 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem150427 (x : nat) (y : nat) : (term8 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem150426 x y) (@lem150425 x y)). Qed.
Lemma lem150428 (x : nat) (y : nat) : ((term7 x y) = (term8 x y)) = ((term17 x y) = (term23 x y)).
Proof. exact (MK_COMB (@lem150421 x y) (@lem150427 x y)). Qed.
Lemma lem150429 (x : nat) (y : nat) : (term17 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem150428 x y) (@lem150413 x y)). Qed.
Lemma lem150436 (x : nat) : (term24 x) = (term25 x).
Proof. exact (fun_ext (fun y : nat => @lem150429 x y)). Qed.
Lemma lem150437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150438 (x : nat) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem150437) (@lem150436 x)). Qed.
Lemma lem150463 : term28 = term29.
Proof. exact (fun_ext (fun x : nat => @lem150438 x)). Qed.
Lemma lem150464 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150465 : term30 = term31.
Proof. exact (MK_COMB (@lem150464) (@lem150463)). Qed.
Lemma lem150470 : term31 = term30.
Proof. exact (SYM (@lem150465)). Qed.
Lemma lem150471 (x : nat) (y : nat) (h1 : Peano.le x y) : Peano.le x y.
Proof. exact (h1). Qed.
Lemma lem150473 (P : nat -> Prop) : term32 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem150474 (x : nat) (y : nat) : term33 x y.
Proof. exact (@lem150473 (term9 x y)). Qed.
Lemma lem150475 (x : nat) (y : nat) : (term34 x y) = (term35 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem150476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150477 (x : nat) (y : nat) : (term36 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem150476) (@lem150475 x y)). Qed.
Lemma lem150478 (x : nat) (y : nat) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (eq_refl (term10 x y n)). Qed.
Lemma lem150479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem150480 (x : nat) (y : nat) (n : nat) : (term38 x y n) = (term39 x y n).
Proof. exact (MK_COMB (@lem150479) (@lem150478 x y n)). Qed.
Lemma lem150481 (x : nat) (y : nat) (n : nat) : (term40 x y n) = (term41 x y n).
Proof. exact (eq_refl (term40 x y n)). Qed.
Lemma lem150482 (x : nat) (y : nat) (n : nat) : (term42 x y n) = (term43 x y n).
Proof. exact (MK_COMB (@lem150480 x y n) (@lem150481 x y n)). Qed.
Lemma lem150483 (x : nat) (y : nat) : (term44 x y) = (term45 x y).
Proof. exact (fun_ext (fun n : nat => @lem150482 x y n)). Qed.
Lemma lem150484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150485 (x : nat) (y : nat) : (term46 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem150484) (@lem150483 x y)). Qed.
Lemma lem150486 (x : nat) (y : nat) : (term48 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem150477 x y) (@lem150485 x y)). Qed.
Lemma lem150487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem150488 (x : nat) (y : nat) : (term50 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem150487) (@lem150486 x y)). Qed.
Lemma lem150489 (x : nat) (y : nat) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (eq_refl (term10 x y n)). Qed.
Lemma lem150490 (x : nat) (y : nat) : (term20 x y) = (term9 x y).
Proof. exact (fun_ext (fun n : nat => @lem150489 x y n)). Qed.
Lemma lem150491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150492 (x : nat) (y : nat) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem150491) (@lem150490 x y)). Qed.
Lemma lem150493 (x : nat) (y : nat) : (term33 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem150488 x y) (@lem150492 x y)). Qed.
Lemma lem150494 (x : nat) (y : nat) : term52 x y.
Proof. exact (EQ_MP (@lem150493 x y) (@lem150474 x y)). Qed.
Lemma lem150495 (x : nat) (y : nat) (n : nat) (h1 : term11 x y n) : term11 x y n.
Proof. exact (h1). Qed.
Lemma lem150496 (n : nat) : term53 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem150497 (n : nat) : (term53 n) = (Peano.le n n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem150498 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem150497 n) (@lem150496 n)). Qed.
Lemma lem150499 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem150508 : term54.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem150509 (m : nat) : term55 m.
Proof. exact (@lem150508 m). Qed.
Lemma lem150510 (m : nat) : (term55 m) = ((term56 m) = term57).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem150538 (m : nat) : (term56 m) = term57.
Proof. exact (EQ_MP (@lem150510 m) (@lem150509 m)). Qed.
Lemma lem150539 (x : nat) : (term56 x) = term57.
Proof. exact (@lem150538 x). Qed.
Lemma lem150540 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem150541 (x : nat) : (term58 x) = term59.
Proof. exact (MK_COMB (@lem150540) (@lem150539 x)). Qed.
Lemma lem150543 (m : nat) : (term56 m) = term57.
Proof. exact (EQ_MP (@lem150510 m) (@lem150509 m)). Qed.
Lemma lem150544 (y : nat) : (term56 y) = term57.
Proof. exact (@lem150543 y). Qed.
Lemma lem150545 (x : nat) (y : nat) : (term35 x y) = term60.
Proof. exact (MK_COMB (@lem150541 x) (@lem150544 y)). Qed.
Lemma lem150547 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem150499 n) (@lem150498 n)). Qed.
Lemma lem150548 : term60 = True.
Proof. exact (@lem150547 term57). Qed.
Lemma lem150549 (x : nat) (y : nat) : (term35 x y) = True.
Proof. exact (TRANS (@lem150545 x y) (@lem150548)). Qed.
Lemma lem150550 (x : nat) (y : nat) : True = (term35 x y).
Proof. exact (SYM (@lem150549 x y)). Qed.
Lemma lem150551 (x : nat) (y : nat) : term35 x y.
Proof. exact (EQ_MP (@lem150550 x y) (@lem0)). Qed.
Lemma lem150557 : term61.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem150558 (m : nat) : term62 m.
Proof. exact (@lem150557 m). Qed.
Lemma lem150559 (m : nat) : (term62 m) = (term63 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem150560 (m : nat) : term63 m.
Proof. exact (EQ_MP (@lem150559 m) (@lem150558 m)). Qed.
Lemma lem150561 (m : nat) (n : nat) : term64 m n.
Proof. exact (@lem150560 m n). Qed.
Lemma lem150562 (m : nat) (n : nat) : (term64 m n) = ((term65 m n) = (term66 m n)).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem150568 (m : nat) : term67 m.
Proof. exact (@lem102387 m). Qed.
Lemma lem150569 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem150570 (m : nat) : term68 m.
Proof. exact (EQ_MP (@lem150569 m) (@lem150568 m)). Qed.
Lemma lem150571 (m : nat) (n : nat) : term69 m n.
Proof. exact (@lem150570 m n). Qed.
Lemma lem150572 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem150573 (m : nat) (n : nat) : term70 m n.
Proof. exact (EQ_MP (@lem150572 m n) (@lem150571 m n)). Qed.
Lemma lem150574 (m : nat) (n : nat) (p : nat) : term71 m n p.
Proof. exact (@lem150573 m n p). Qed.
Lemma lem150575 (m : nat) (p : nat) (n : nat) : (term71 m n p) = (term72 m p n).
Proof. exact (eq_refl (term71 m n p)). Qed.
Lemma lem150576 (m : nat) (p : nat) (n : nat) : term72 m p n.
Proof. exact (EQ_MP (@lem150575 m p n) (@lem150574 m n p)). Qed.
Lemma lem150577 (m : nat) (p : nat) (n : nat) (q : nat) : term73 m p n q.
Proof. exact (@lem150576 m p n q). Qed.
Lemma lem150578 (m : nat) (p : nat) (n : nat) (q : nat) : (term73 m p n q) = (term74 m p n q).
Proof. exact (eq_refl (term73 m p n q)). Qed.
Lemma lem150579 (m : nat) (p : nat) (n : nat) (q : nat) : term74 m p n q.
Proof. exact (EQ_MP (@lem150578 m p n q) (@lem150577 m p n q)). Qed.
Lemma lem150580 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term75 m n p q) : term75 m n p q.
Proof. exact (h1). Qed.
Lemma lem150581 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term75 m n p q) : term76 m p n q.
Proof. exact (@lem150579 m p n q (@lem150580 m n p q h1)). Qed.
Lemma lem150582 (m : nat) (p : nat) (n : nat) (q : nat) : (term76 m p n q) = ((term76 m p n q) = True).
Proof. exact (@lem7 (term76 m p n q)). Qed.
Lemma lem150583 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term75 m n p q) : (term76 m p n q) = True.
Proof. exact (EQ_MP (@lem150582 m p n q) (@lem150581 m n p q h1)). Qed.
Lemma lem150589 (x : nat) (y : nat) : (Peano.le x y) = ((Peano.le x y) = True).
Proof. exact (@lem7 (Peano.le x y)). Qed.
Lemma lem150591 (x : nat) (y : nat) (n : nat) : (term11 x y n) = ((term11 x y n) = True).
Proof. exact (@lem7 (term11 x y n)). Qed.
Lemma lem150596 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem150562 m n) (@lem150561 m n)). Qed.
Lemma lem150597 (x : nat) (n : nat) : (term65 x n) = (term66 x n).
Proof. exact (@lem150596 x n). Qed.
Lemma lem150598 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem150599 (x : nat) (n : nat) : (term77 x n) = (term78 x n).
Proof. exact (MK_COMB (@lem150598) (@lem150597 x n)). Qed.
Lemma lem150601 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem150562 m n) (@lem150561 m n)). Qed.
Lemma lem150602 (y : nat) (n : nat) : (term65 y n) = (term66 y n).
Proof. exact (@lem150601 y n). Qed.
Lemma lem150603 (x : nat) (y : nat) (n : nat) : (term41 x y n) = (term79 x y n).
Proof. exact (MK_COMB (@lem150599 x n) (@lem150602 y n)). Qed.
Lemma lem150605 (m : nat) (p : nat) (n : nat) (q : nat) : term80 m p n q.
Proof. exact (fun h0 : term75 m n p q => @lem150583 m n p q h0). Qed.
Lemma lem150606 (x : nat) (y : nat) (n : nat) : term81 x y n.
Proof. exact (@lem150605 x (Nat.pow x n) y (Nat.pow y n)). Qed.
Lemma lem150610 (x : nat) (y : nat) (h1 : Peano.le x y) : (Peano.le x y) = True.
Proof. exact (EQ_MP (@lem150589 x y) (@lem150471 x y h1)). Qed.
Lemma lem150611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150612 (x : nat) (y : nat) (h1 : Peano.le x y) : (term82 x y) = (and True).
Proof. exact (MK_COMB (@lem150611) (@lem150610 x y h1)). Qed.
Lemma lem150614 (x : nat) (y : nat) (n : nat) (h1 : term11 x y n) : (term11 x y n) = True.
Proof. exact (EQ_MP (@lem150591 x y n) (@lem150495 x y n h1)). Qed.
Lemma lem150615 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : (term83 x y n) = (True /\ True).
Proof. exact (MK_COMB (@lem150612 x y h1) (@lem150614 x y n h2)). Qed.
Lemma lem150617 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150618 : (True /\ True) = True.
Proof. exact (@lem150617 True). Qed.
Lemma lem150619 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : (term83 x y n) = True.
Proof. exact (TRANS (@lem150615 x y n h1 h2) (@lem150618)). Qed.
Lemma lem150620 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : True = (term83 x y n).
Proof. exact (SYM (@lem150619 x y n h1 h2)). Qed.
Lemma lem150621 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : term83 x y n.
Proof. exact (EQ_MP (@lem150620 x y n h1 h2) (@lem0)). Qed.
Lemma lem150622 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : (term79 x y n) = True.
Proof. exact (@lem150606 x y n (@lem150621 x y n h1 h2)). Qed.
Lemma lem150623 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : (term41 x y n) = True.
Proof. exact (TRANS (@lem150603 x y n) (@lem150622 x y n h1 h2)). Qed.
Lemma lem150624 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : True = (term41 x y n).
Proof. exact (SYM (@lem150623 x y n h1 h2)). Qed.
Lemma lem150625 (x : nat) (y : nat) (n : nat) (h1 : Peano.le x y) (h2 : term11 x y n) : term41 x y n.
Proof. exact (EQ_MP (@lem150624 x y n h1 h2) (@lem0)). Qed.
Lemma lem150626 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : term43 x y n.
Proof. exact (fun h0 : term11 x y n => @lem150625 x y n h1 h0). Qed.
Lemma lem150631 (x : nat) (y : nat) (h1 : Peano.le x y) : term47 x y.
Proof. exact (fun n : nat => @lem150626 n x y h1). Qed.
Lemma lem150632 (x : nat) (y : nat) (h1 : Peano.le x y) : term49 x y.
Proof. exact (conj (@lem150551 x y) (@lem150631 x y h1)). Qed.
Lemma lem150633 (x : nat) (y : nat) (h1 : Peano.le x y) : term22 x y.
Proof. exact (@lem150494 x y (@lem150632 x y h1)). Qed.
Lemma lem150634 (x : nat) (y : nat) : term23 x y.
Proof. exact (fun h0 : Peano.le x y => @lem150633 x y h0). Qed.
Lemma lem150639 (x : nat) : term27 x.
Proof. exact (fun y : nat => @lem150634 x y). Qed.
Lemma lem150644 : term31.
Proof. exact (fun x : nat => @lem150639 x). Qed.
Lemma lem150645 : term30.
Proof. exact (EQ_MP (@lem150470) (@lem150644)). Qed.
