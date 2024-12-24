Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_TOTAL_LEMMA_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_ADD_spec.
Require Import LE_ADDR_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm10568_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1271367 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1271368 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1271369 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1271368 m) (@lem1271367 m)). Qed.
Lemma lem1271370 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1271369 m n). Qed.
Lemma lem1271371 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1271372 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1271371 m n) (@lem1271370 m n)). Qed.
Lemma lem1271373 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1271384 (m : nat) : term4 m.
Proof. exact (@lem98377 m). Qed.
Lemma lem1271385 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1271386 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1271385 m) (@lem1271384 m)). Qed.
Lemma lem1271387 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1271386 m n). Qed.
Lemma lem1271388 (n : nat) (m : nat) : (term6 m n) = ((term7 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1271390 (n : nat) : term8 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem1271391 (n : nat) : (term8 n) = (term9 n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem1271392 (n : nat) : term9 n.
Proof. exact (EQ_MP (@lem1271391 n) (@lem1271390 n)). Qed.
Lemma lem1271394 (n : nat) (h1 : term10 n) : term10 n.
Proof. exact (h1). Qed.
Lemma lem1271395 (m : nat) : term11 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1271396 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem1271397 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1271396 m) (@lem1271395 m)). Qed.
Lemma lem1271398 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem1271397 m n). Qed.
Lemma lem1271399 (n : nat) (m : nat) : (term13 m n) = ((term14 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem1271401 {A : Type'} (P : A -> Prop) : term15 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem1271402 {A : Type'} (P : A -> Prop) : (term15 A P) = ((term16 A P) = (term17 A P)).
Proof. exact (eq_refl (term15 A P)). Qed.
Lemma lem1271404 {A : Type'} (P : A -> Prop) : term18 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem1271405 {A : Type'} (P : A -> Prop) : (term18 A P) = ((term19 A P) = (term20 A P)).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem1271407 (x : nadd) : term21 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1271408 (x : nadd) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1271409 (x : nadd) : term22 x.
Proof. exact (EQ_MP (@lem1271408 x) (@lem1271407 x)). Qed.
Lemma lem1271410 (x : nadd) (y : nadd) : term23 x y.
Proof. exact (@lem1271409 x y). Qed.
Lemma lem1271411 (x : nadd) (y : nadd) : (term23 x y) = ((nadd_le x y) = (term24 x y)).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1271416 (x : nadd) (y : nadd) : (nadd_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem1271411 x y) (@lem1271410 x y)). Qed.
Lemma lem1271425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1271426 (x : nadd) (y : nadd) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1271425) (@lem1271416 x y)). Qed.
Lemma lem1271428 {A : Type'} (P : A -> Prop) : (term16 A P) = (term17 A P).
Proof. exact (EQ_MP (@lem1271402 A P) (@lem1271401 A P)). Qed.
Lemma lem1271429 (P : nat -> Prop) : (term27 P) = (term28 P).
Proof. exact (@lem1271428 nat P). Qed.
Lemma lem1271430 (x : nadd) (y : nadd) : (term29 x y) = (term30 x y).
Proof. exact (@lem1271429 (term31 x y)). Qed.
Lemma lem1271431 (x : nadd) (y : nadd) (B : nat) : (term32 x y B) = (term33 x y B).
Proof. exact (eq_refl (term32 x y B)). Qed.
Lemma lem1271432 (x : nadd) (y : nadd) : (term34 x y) = (term31 x y).
Proof. exact (fun_ext (fun B : nat => @lem1271431 x y B)). Qed.
Lemma lem1271433 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1271434 (x : nadd) (y : nadd) : (term35 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1271433) (@lem1271432 x y)). Qed.
Lemma lem1271435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1271436 (x : nadd) (y : nadd) : (term29 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1271435) (@lem1271434 x y)). Qed.
Lemma lem1271437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1271438 (x : nadd) (y : nadd) : (term36 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem1271437) (@lem1271436 x y)). Qed.
Lemma lem1271439 (x : nadd) (y : nadd) (B : nat) : (term32 x y B) = (term33 x y B).
Proof. exact (eq_refl (term32 x y B)). Qed.
Lemma lem1271440 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1271441 (x : nadd) (y : nadd) (B : nat) : (term38 x y B) = (term39 x y B).
Proof. exact (MK_COMB (@lem1271440) (@lem1271439 x y B)). Qed.
Lemma lem1271442 (x : nadd) (y : nadd) : (term40 x y) = (term41 x y).
Proof. exact (fun_ext (fun B : nat => @lem1271441 x y B)). Qed.
Lemma lem1271443 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271444 (x : nadd) (y : nadd) : (term30 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1271443) (@lem1271442 x y)). Qed.
Lemma lem1271445 (x : nadd) (y : nadd) : ((term29 x y) = (term30 x y)) = ((term26 x y) = (term42 x y)).
Proof. exact (MK_COMB (@lem1271438 x y) (@lem1271444 x y)). Qed.
Lemma lem1271446 (x : nadd) (y : nadd) : (term26 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem1271445 x y) (@lem1271430 x y)). Qed.
Lemma lem1271452 {A : Type'} (P : A -> Prop) : (term19 A P) = (term20 A P).
Proof. exact (EQ_MP (@lem1271405 A P) (@lem1271404 A P)). Qed.
Lemma lem1271453 (P : nat -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem1271452 nat P). Qed.
Lemma lem1271454 (x : nadd) (y : nadd) (B : nat) : (term45 x y B) = (term46 x y B).
Proof. exact (@lem1271453 (term47 x y B)). Qed.
Lemma lem1271455 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term48 x y B n) = (term49 x y n B).
Proof. exact (eq_refl (term48 x y B n)). Qed.
Lemma lem1271456 (x : nadd) (y : nadd) (B : nat) : (term50 x y B) = (term47 x y B).
Proof. exact (fun_ext (fun n : nat => @lem1271455 x y n B)). Qed.
Lemma lem1271457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271458 (x : nadd) (y : nadd) (B : nat) : (term51 x y B) = (term33 x y B).
Proof. exact (MK_COMB (@lem1271457) (@lem1271456 x y B)). Qed.
Lemma lem1271459 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1271460 (x : nadd) (y : nadd) (B : nat) : (term45 x y B) = (term39 x y B).
Proof. exact (MK_COMB (@lem1271459) (@lem1271458 x y B)). Qed.
Lemma lem1271461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1271462 (x : nadd) (y : nadd) (B : nat) : (term52 x y B) = (term53 x y B).
Proof. exact (MK_COMB (@lem1271461) (@lem1271460 x y B)). Qed.
Lemma lem1271463 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term48 x y B n) = (term49 x y n B).
Proof. exact (eq_refl (term48 x y B n)). Qed.
Lemma lem1271464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1271465 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term54 x y B n) = (term55 x y n B).
Proof. exact (MK_COMB (@lem1271464) (@lem1271463 x y n B)). Qed.
Lemma lem1271466 (x : nadd) (y : nadd) (B : nat) : (term56 x y B) = (term57 x y B).
Proof. exact (fun_ext (fun n : nat => @lem1271465 x y n B)). Qed.
Lemma lem1271467 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1271468 (x : nadd) (y : nadd) (B : nat) : (term46 x y B) = (term58 x y B).
Proof. exact (MK_COMB (@lem1271467) (@lem1271466 x y B)). Qed.
Lemma lem1271469 (x : nadd) (y : nadd) (B : nat) : ((term45 x y B) = (term46 x y B)) = ((term39 x y B) = (term58 x y B)).
Proof. exact (MK_COMB (@lem1271462 x y B) (@lem1271468 x y B)). Qed.
Lemma lem1271470 (x : nadd) (y : nadd) (B : nat) : (term39 x y B) = (term58 x y B).
Proof. exact (EQ_MP (@lem1271469 x y B) (@lem1271454 x y B)). Qed.
Lemma lem1271475 (x : nadd) (y : nadd) : (term41 x y) = (term59 x y).
Proof. exact (fun_ext (fun B : nat => @lem1271470 x y B)). Qed.
Lemma lem1271476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271477 (x : nadd) (y : nadd) : (term42 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1271476) (@lem1271475 x y)). Qed.
Lemma lem1271482 (x : nadd) (y : nadd) : (term26 x y) = (term60 x y).
Proof. exact (TRANS (@lem1271446 x y) (@lem1271477 x y)). Qed.
Lemma lem1271483 (x : nadd) (y : nadd) : (term25 x y) = (term60 x y).
Proof. exact (TRANS (@lem1271426 x y) (@lem1271482 x y)). Qed.
Lemma lem1271484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1271485 (x : nadd) (y : nadd) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1271484) (@lem1271483 x y)). Qed.
Lemma lem1271498 (y : nadd) (x : nadd) : (term63 y x) = (term63 y x).
Proof. exact (eq_refl (term63 y x)). Qed.
Lemma lem1271499 (y : nadd) (x : nadd) : (term64 y x) = (term65 y x).
Proof. exact (MK_COMB (@lem1271485 x y) (@lem1271498 y x)). Qed.
Lemma lem1271502 (y : nadd) (x : nadd) : (term65 y x) = (term64 y x).
Proof. exact (SYM (@lem1271499 y x)). Qed.
Lemma lem1271514 (n : nat) (m : nat) : (term14 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1271399 n m) (@lem1271398 m n)). Qed.
Lemma lem1271515 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term55 x y n B) = (term66 y B x n).
Proof. exact (@lem1271514 (term67 y n B) (dest_nadd x n)). Qed.
Lemma lem1271516 (y : nadd) (B : nat) (x : nadd) : (term57 x y B) = (term68 y B x).
Proof. exact (fun_ext (fun n : nat => @lem1271515 y B x n)). Qed.
Lemma lem1271517 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1271518 (y : nadd) (B : nat) (x : nadd) : (term58 x y B) = (term69 y B x).
Proof. exact (MK_COMB (@lem1271517) (@lem1271516 y B x)). Qed.
Lemma lem1271523 (y : nadd) (x : nadd) : (term59 x y) = (term70 y x).
Proof. exact (fun_ext (fun B : nat => @lem1271518 y B x)). Qed.
Lemma lem1271524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1271525 (y : nadd) (x : nadd) : (term60 x y) = (term71 y x).
Proof. exact (MK_COMB (@lem1271524) (@lem1271523 y x)). Qed.
Lemma lem1271530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1271531 (y : nadd) (x : nadd) : (term62 x y) = (term72 y x).
Proof. exact (MK_COMB (@lem1271530) (@lem1271525 y x)). Qed.
Lemma lem1271544 (y : nadd) (x : nadd) : (term63 y x) = (term63 y x).
Proof. exact (eq_refl (term63 y x)). Qed.
Lemma lem1271545 (y : nadd) (x : nadd) : (term65 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1271531 y x) (@lem1271544 y x)). Qed.
Lemma lem1271548 (y : nadd) (x : nadd) : (term73 y x) = (term65 y x).
Proof. exact (SYM (@lem1271545 y x)). Qed.
Lemma lem1271549 (y : nadd) (x : nadd) (h1 : term71 y x) : term71 y x.
Proof. exact (h1). Qed.
Lemma lem1271550 (B : nat) (y : nadd) (x : nadd) (h1 : term71 y x) : term74 y B x.
Proof. exact (@lem1271549 y x h1 (term75 B x)). Qed.
Lemma lem1271551 (y : nadd) (B : nat) (x : nadd) : (term74 y B x) = (term76 y B x).
Proof. exact (eq_refl (term74 y B x)). Qed.
Lemma lem1271552 (B : nat) (y : nadd) (x : nadd) (h1 : term71 y x) : term76 y B x.
Proof. exact (EQ_MP (@lem1271551 y B x) (@lem1271550 B y x h1)). Qed.
Lemma lem1271553 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term77 y B x n) : term77 y B x n.
Proof. exact (h1). Qed.
Lemma lem1271554 (m : nat) : term78 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1271555 (m : nat) : (term78 m) = (term79 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem1271556 (m : nat) : term79 m.
Proof. exact (EQ_MP (@lem1271555 m) (@lem1271554 m)). Qed.
Lemma lem1271557 (m : nat) (n : nat) : term80 m n.
Proof. exact (@lem1271556 m n). Qed.
Lemma lem1271558 (m : nat) (n : nat) : (term80 m n) = (term81 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem1271559 (m : nat) (n : nat) : term81 m n.
Proof. exact (EQ_MP (@lem1271558 m n) (@lem1271557 m n)). Qed.
Lemma lem1271560 (m : nat) (n : nat) : (term81 m n) = ((term81 m n) = True).
Proof. exact (@lem7 (term81 m n)). Qed.
Lemma lem1271562 (m : nat) : term82 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1271563 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1271564 (m : nat) : term83 m.
Proof. exact (EQ_MP (@lem1271563 m) (@lem1271562 m)). Qed.
Lemma lem1271565 (m : nat) (n : nat) : term84 m n.
Proof. exact (@lem1271564 m n). Qed.
Lemma lem1271566 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1271567 (m : nat) (n : nat) : term85 m n.
Proof. exact (EQ_MP (@lem1271566 m n) (@lem1271565 m n)). Qed.
Lemma lem1271568 (m : nat) (n : nat) (p : nat) : term86 m n p.
Proof. exact (@lem1271567 m n p). Qed.
Lemma lem1271569 (m : nat) (n : nat) (p : nat) : (term86 m n p) = ((term87 m n p) = (term88 m n p)).
Proof. exact (eq_refl (term86 m n p)). Qed.
Lemma lem1271571 (m : nat) : term4 m.
Proof. exact (@lem98377 m). Qed.
Lemma lem1271572 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1271573 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1271572 m) (@lem1271571 m)). Qed.
Lemma lem1271574 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1271573 m n). Qed.
Lemma lem1271575 (n : nat) (m : nat) : (term6 m n) = ((term7 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1271580 (m : nat) (n : nat) (p : nat) : (term87 m n p) = (term88 m n p).
Proof. exact (EQ_MP (@lem1271569 m n p) (@lem1271568 m n p)). Qed.
Lemma lem1271581 (y : nadd) (n : nat) (B : nat) (x : nadd) : (term89 y n B x) = (term90 y n B x).
Proof. exact (@lem1271580 (dest_nadd y n) B (term91 x)). Qed.
Lemma lem1271583 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1271584 (y : nadd) : (dest_nadd y) = (dest_nadd y).
Proof. exact (eq_refl (dest_nadd y)). Qed.
Lemma lem1271585 (y : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (dest_nadd y n) = (term91 y).
Proof. exact (MK_COMB (@lem1271584 y) (@lem1271583 n h1)). Qed.
Lemma lem1271586 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1271587 (y : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term92 y n) = (term93 y).
Proof. exact (MK_COMB (@lem1271586) (@lem1271585 y n h1)). Qed.
Lemma lem1271588 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1271589 (y : nadd) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term67 y n B) = (term94 y B).
Proof. exact (MK_COMB (@lem1271587 y n h1) (@lem1271588 B)). Qed.
Lemma lem1271590 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1271591 (y : nadd) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term95 y n B) = (term96 y B).
Proof. exact (MK_COMB (@lem1271590) (@lem1271589 y B n h1)). Qed.
Lemma lem1271592 (x : nadd) : (term91 x) = (term91 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1271593 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term90 y n B x) = (term97 y B x).
Proof. exact (MK_COMB (@lem1271591 y B n h1) (@lem1271592 x)). Qed.
Lemma lem1271594 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term89 y n B x) = (term97 y B x).
Proof. exact (TRANS (@lem1271581 y n B x) (@lem1271593 y B x n h1)). Qed.
Lemma lem1271595 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem1271596 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term98 y n B x) = (term99 y B x).
Proof. exact (MK_COMB (@lem1271595) (@lem1271594 y B x n h1)). Qed.
Lemma lem1271598 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1271599 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1271600 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (dest_nadd x n) = (term91 x).
Proof. exact (MK_COMB (@lem1271599 x) (@lem1271598 n h1)). Qed.
Lemma lem1271601 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term77 y B x n) = (term100 y B x).
Proof. exact (MK_COMB (@lem1271596 y B x n h1) (@lem1271600 x n h1)). Qed.
Lemma lem1271602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1271603 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term101 y B x n) = (term102 y B x).
Proof. exact (MK_COMB (@lem1271602) (@lem1271601 y B x n h1)). Qed.
Lemma lem1271609 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1271610 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1271611 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term103.
Proof. exact (MK_COMB (@lem1271610) (@lem1271609 n h1)). Qed.
Lemma lem1271612 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1271613 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1271611 n h1) (@lem1271612)). Qed.
Lemma lem1271615 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1271616 (x : nat) : (x = x) = True.
Proof. exact (@lem1271615 nat x). Qed.
Lemma lem1271617 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1271616 (NUMERAL 0)). Qed.
Lemma lem1271618 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1271613 n h1) (@lem1271617)). Qed.
Lemma lem1271619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1271620 (n : nat) (h1 : n = (NUMERAL 0)) : (term10 n) = (~ True).
Proof. exact (MK_COMB (@lem1271619) (@lem1271618 n h1)). Qed.
Lemma lem1271622 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1271623 (n : nat) (h1 : n = (NUMERAL 0)) : (term10 n) = False.
Proof. exact (TRANS (@lem1271620 n h1) (@lem1271622)). Qed.
Lemma lem1271624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1271625 (n : nat) (h1 : n = (NUMERAL 0)) : (term104 n) = (and False).
Proof. exact (MK_COMB (@lem1271624) (@lem1271623 n h1)). Qed.
Lemma lem1271627 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1271628 (y : nadd) : (dest_nadd y) = (dest_nadd y).
Proof. exact (eq_refl (dest_nadd y)). Qed.
Lemma lem1271629 (y : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (dest_nadd y n) = (term91 y).
Proof. exact (MK_COMB (@lem1271628 y) (@lem1271627 n h1)). Qed.
Lemma lem1271630 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1271631 (y : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term92 y n) = (term93 y).
Proof. exact (MK_COMB (@lem1271630) (@lem1271629 y n h1)). Qed.
Lemma lem1271632 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1271633 (y : nadd) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term67 y n B) = (term94 y B).
Proof. exact (MK_COMB (@lem1271631 y n h1) (@lem1271632 B)). Qed.
Lemma lem1271634 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem1271635 (y : nadd) (B : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term105 y n B) = (term106 y B).
Proof. exact (MK_COMB (@lem1271634) (@lem1271633 y B n h1)). Qed.
Lemma lem1271637 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1271638 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1271639 (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (dest_nadd x n) = (term91 x).
Proof. exact (MK_COMB (@lem1271638 x) (@lem1271637 n h1)). Qed.
Lemma lem1271640 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term66 y B x n) = (term107 y B x).
Proof. exact (MK_COMB (@lem1271635 y B n h1) (@lem1271639 x n h1)). Qed.
Lemma lem1271641 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term108 y B x n) = (term109 y B x).
Proof. exact (MK_COMB (@lem1271625 n h1) (@lem1271640 y B x n h1)). Qed.
Lemma lem1271643 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1271644 (y : nadd) (B : nat) (x : nadd) : (term109 y B x) = False.
Proof. exact (@lem1271643 (term107 y B x)). Qed.
Lemma lem1271645 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term108 y B x n) = False.
Proof. exact (TRANS (@lem1271641 y B x n h1) (@lem1271644 y B x)). Qed.
Lemma lem1271646 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term110 y B x n) = (term111 y B x).
Proof. exact (MK_COMB (@lem1271603 y B x n h1) (@lem1271645 y B x n h1)). Qed.
Lemma lem1271648 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1271649 (y : nadd) (B : nat) (x : nadd) : (term111 y B x) = (term112 y B x).
Proof. exact (@lem1271648 (term100 y B x)). Qed.
Lemma lem1271651 (n : nat) (m : nat) : (term7 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem1271575 n m) (@lem1271574 m n)). Qed.
Lemma lem1271652 (y : nadd) (B : nat) (x : nadd) : (term112 y B x) = (term113 y B x).
Proof. exact (@lem1271651 (term91 x) (term97 y B x)). Qed.
Lemma lem1271654 (m : nat) (n : nat) : (term81 m n) = True.
Proof. exact (EQ_MP (@lem1271560 m n) (@lem1271559 m n)). Qed.
Lemma lem1271655 (y : nadd) (B : nat) (x : nadd) : (term113 y B x) = True.
Proof. exact (@lem1271654 (term94 y B) (term91 x)). Qed.
Lemma lem1271656 (y : nadd) (B : nat) (x : nadd) : (term112 y B x) = True.
Proof. exact (TRANS (@lem1271652 y B x) (@lem1271655 y B x)). Qed.
Lemma lem1271657 (y : nadd) (B : nat) (x : nadd) : (term111 y B x) = True.
Proof. exact (TRANS (@lem1271649 y B x) (@lem1271656 y B x)). Qed.
Lemma lem1271658 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : (term110 y B x n) = True.
Proof. exact (TRANS (@lem1271646 y B x n h1) (@lem1271657 y B x)). Qed.
Lemma lem1271659 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term110 y B x n).
Proof. exact (SYM (@lem1271658 y B x n h1)). Qed.
Lemma lem1271660 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : n = (NUMERAL 0)) : term110 y B x n.
Proof. exact (EQ_MP (@lem1271659 y B x n h1) (@lem0)). Qed.
Lemma lem1271669 (m : nat) : term82 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1271670 (m : nat) : (term82 m) = (term83 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1271671 (m : nat) : term83 m.
Proof. exact (EQ_MP (@lem1271670 m) (@lem1271669 m)). Qed.
Lemma lem1271672 (m : nat) (n : nat) : term84 m n.
Proof. exact (@lem1271671 m n). Qed.
Lemma lem1271673 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem1271674 (m : nat) (n : nat) : term85 m n.
Proof. exact (EQ_MP (@lem1271673 m n) (@lem1271672 m n)). Qed.
Lemma lem1271675 (m : nat) (n : nat) (p : nat) : term86 m n p.
Proof. exact (@lem1271674 m n p). Qed.
Lemma lem1271676 (m : nat) (n : nat) (p : nat) : (term86 m n p) = ((term87 m n p) = (term88 m n p)).
Proof. exact (eq_refl (term86 m n p)). Qed.
Lemma lem1271684 (n : nat) : term114 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1271700 (m : nat) (n : nat) (p : nat) : (term87 m n p) = (term88 m n p).
Proof. exact (EQ_MP (@lem1271676 m n p) (@lem1271675 m n p)). Qed.
Lemma lem1271701 (y : nadd) (n : nat) (B : nat) (x : nadd) : (term89 y n B x) = (term90 y n B x).
Proof. exact (@lem1271700 (dest_nadd y n) B (term91 x)). Qed.
Lemma lem1271702 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem1271703 (y : nadd) (n : nat) (B : nat) (x : nadd) : (term98 y n B x) = (term115 y n B x).
Proof. exact (MK_COMB (@lem1271702) (@lem1271701 y n B x)). Qed.
Lemma lem1271704 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1271705 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term77 y B x n) = (term116 y B x n).
Proof. exact (MK_COMB (@lem1271703 y n B x) (@lem1271704 x n)). Qed.
Lemma lem1271706 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1271707 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term101 y B x n) = (term117 y B x n).
Proof. exact (MK_COMB (@lem1271706) (@lem1271705 y B x n)). Qed.
Lemma lem1271711 (n : nat) (h1 : term10 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1271684 n (@lem1271394 n h1)). Qed.
Lemma lem1271712 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1271713 (n : nat) (h1 : term10 n) : (term10 n) = (~ False).
Proof. exact (MK_COMB (@lem1271712) (@lem1271711 n h1)). Qed.
Lemma lem1271715 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1271716 (n : nat) (h1 : term10 n) : (term10 n) = True.
Proof. exact (TRANS (@lem1271713 n h1) (@lem1271715)). Qed.
Lemma lem1271717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1271718 (n : nat) (h1 : term10 n) : (term104 n) = (and True).
Proof. exact (MK_COMB (@lem1271717) (@lem1271716 n h1)). Qed.
Lemma lem1271719 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term66 y B x n) = (term66 y B x n).
Proof. exact (eq_refl (term66 y B x n)). Qed.
Lemma lem1271720 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term10 n) : (term108 y B x n) = (term118 y B x n).
Proof. exact (MK_COMB (@lem1271718 n h1) (@lem1271719 y B x n)). Qed.
Lemma lem1271722 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1271723 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term118 y B x n) = (term66 y B x n).
Proof. exact (@lem1271722 (term66 y B x n)). Qed.
Lemma lem1271724 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term10 n) : (term108 y B x n) = (term66 y B x n).
Proof. exact (TRANS (@lem1271720 y B x n h1) (@lem1271723 y B x n)). Qed.
Lemma lem1271725 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term10 n) : (term110 y B x n) = (term119 y B x n).
Proof. exact (MK_COMB (@lem1271707 y B x n) (@lem1271724 y B x n h1)). Qed.
Lemma lem1271728 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term10 n) : (term119 y B x n) = (term110 y B x n).
Proof. exact (SYM (@lem1271725 y B x n h1)). Qed.
Lemma lem1271729 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term119 y B x n) = (term120 y B x n).
Proof. exact (@lem10568 (term66 y B x n) (term116 y B x n)). Qed.
Lemma lem1271730 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term120 y B x n) = (term119 y B x n).
Proof. exact (SYM (@lem1271729 y B x n)). Qed.
Lemma lem1271734 (n : nat) (m : nat) : (term7 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem1271388 n m) (@lem1271387 m n)). Qed.
Lemma lem1271735 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term121 y B x n) = (term49 x y n B).
Proof. exact (@lem1271734 (dest_nadd x n) (term67 y n B)). Qed.
Lemma lem1271736 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1271737 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term122 y B x n) = (term123 x y n B).
Proof. exact (MK_COMB (@lem1271736) (@lem1271735 x y n B)). Qed.
Lemma lem1271739 (n : nat) (m : nat) : (term7 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem1271388 n m) (@lem1271387 m n)). Qed.
Lemma lem1271740 (y : nadd) (n : nat) (B : nat) (x : nadd) : (term124 y B x n) = (term125 y n B x).
Proof. exact (@lem1271739 (dest_nadd x n) (term90 y n B x)). Qed.
Lemma lem1271741 (y : nadd) (n : nat) (B : nat) (x : nadd) : (term120 y B x n) = (term126 y n B x).
Proof. exact (MK_COMB (@lem1271737 x y n B) (@lem1271740 y n B x)). Qed.
Lemma lem1271744 (y : nadd) (B : nat) (x : nadd) (n : nat) : (term126 y n B x) = (term120 y B x n).
Proof. exact (SYM (@lem1271741 y n B x)). Qed.
Lemma lem1271745 (x : nadd) (y : nadd) (n : nat) (B : nat) (h1 : term49 x y n B) : term49 x y n B.
Proof. exact (h1). Qed.
Lemma lem1271746 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1271747 (m : nat) (h1 : term127) : term128 m.
Proof. exact (@lem1271746 h1 m). Qed.
Lemma lem1271748 (m : nat) : (term128 m) = (term129 m).
Proof. exact (eq_refl (term128 m)). Qed.
Lemma lem1271749 (m : nat) (h1 : term127) : term129 m.
Proof. exact (EQ_MP (@lem1271748 m) (@lem1271747 m h1)). Qed.
Lemma lem1271750 (m : nat) (n : nat) (h1 : term127) : term130 m n.
Proof. exact (@lem1271749 m h1 n). Qed.
Lemma lem1271751 (n : nat) (m : nat) : (term130 m n) = (term131 n m).
Proof. exact (eq_refl (term130 m n)). Qed.
Lemma lem1271752 (n : nat) (m : nat) (h1 : term127) : term131 n m.
Proof. exact (EQ_MP (@lem1271751 n m) (@lem1271750 m n h1)). Qed.
Lemma lem1271753 (n : nat) (m : nat) (p : nat) (h1 : term127) : term132 n m p.
Proof. exact (@lem1271752 n m h1 p). Qed.
Lemma lem1271754 (n : nat) (m : nat) (p : nat) : (term132 n m p) = (term133 n m p).
Proof. exact (eq_refl (term132 n m p)). Qed.
Lemma lem1271755 (n : nat) (m : nat) (p : nat) (h1 : term127) : term133 n m p.
Proof. exact (EQ_MP (@lem1271754 n m p) (@lem1271753 n m p h1)). Qed.
Lemma lem1271756 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1271757 (p : nat) (m : nat) (n : nat) (h1 : term127) (h2 : Peano.le m n) : term134 n m p.
Proof. exact (@lem1271755 n m p h1 (@lem1271756 m n h2)). Qed.
Lemma lem1271758 (m : nat) (n : nat) (h1 : term127) (h2 : Peano.le m n) : term135 n m.
Proof. exact (fun p : nat => @lem1271757 p m n h1 h2). Qed.
Lemma lem1271759 (n : nat) (m : nat) (h1 : term127) : term136 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1271758 m n h1 h0). Qed.
Lemma lem1271760 (m : nat) (h1 : term127) : term137 m.
Proof. exact (fun n : nat => @lem1271759 n m h1). Qed.
Lemma lem1271761 (h1 : term127) : term138.
Proof. exact (fun m : nat => @lem1271760 m h1). Qed.
Lemma lem1271762 : term139.
Proof. exact (fun h0 : term127 => @lem1271761 h0). Qed.
Lemma lem1271763 : term138.
Proof. exact (@lem1271762 (@lem272809)). Qed.
Lemma lem1271764 (m : nat) : term140 m.
Proof. exact (@lem1271763 m). Qed.
Lemma lem1271765 (m : nat) : (term140 m) = (term137 m).
Proof. exact (eq_refl (term140 m)). Qed.
Lemma lem1271766 (m : nat) : term137 m.
Proof. exact (EQ_MP (@lem1271765 m) (@lem1271764 m)). Qed.
Lemma lem1271767 (m : nat) (n : nat) : term141 m n.
Proof. exact (@lem1271766 m n). Qed.
Lemma lem1271768 (n : nat) (m : nat) : (term141 m n) = (term136 n m).
Proof. exact (eq_refl (term141 m n)). Qed.
Lemma lem1271771 (n : nat) (m : nat) : term136 n m.
Proof. exact (EQ_MP (@lem1271768 n m) (@lem1271767 m n)). Qed.
Lemma lem1271772 (y : nadd) (B : nat) (x : nadd) (n : nat) : term142 y B x n.
Proof. exact (@lem1271771 (term67 y n B) (dest_nadd x n)). Qed.
Lemma lem1271773 (x : nadd) (y : nadd) (n : nat) (B : nat) (h1 : term49 x y n B) : term143 y B x n.
Proof. exact (@lem1271772 y B x n (@lem1271745 x y n B h1)). Qed.
Lemma lem1271774 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term143 y B x n) : term143 y B x n.
Proof. exact (h1). Qed.
Lemma lem1271775 (p : nat) (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term143 y B x n) : term144 y B x n p.
Proof. exact (@lem1271774 y B x n h1 p). Qed.
Lemma lem1271776 (y : nadd) (B : nat) (x : nadd) (n : nat) (p : nat) : (term144 y B x n p) = (term145 y B x n p).
Proof. exact (eq_refl (term144 y B x n p)). Qed.
Lemma lem1271777 (p : nat) (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term143 y B x n) : term145 y B x n p.
Proof. exact (EQ_MP (@lem1271776 y B x n p) (@lem1271775 p y B x n h1)). Qed.
Lemma lem1271778 (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term146 y n B p) : term146 y n B p.
Proof. exact (h1). Qed.
Lemma lem1271779 (x : nadd) (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term143 y B x n) (h2 : term146 y n B p) : term147 x n p.
Proof. exact (@lem1271777 p y B x n h1 (@lem1271778 y n B p h2)). Qed.
Lemma lem1271780 (x : nadd) (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term146 y n B p) : term148 y B x n p.
Proof. exact (fun h0 : term143 y B x n => @lem1271779 x y n B p h0 h1). Qed.
Lemma lem1271781 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term143 y B x n) : term143 y B x n.
Proof. exact (h1). Qed.
Lemma lem1271782 (x : nadd) (y : nadd) (n : nat) (B : nat) (p : nat) (h1 : term143 y B x n) (h2 : term146 y n B p) : term147 x n p.
Proof. exact (@lem1271780 x y n B p h2 (@lem1271781 y B x n h1)). Qed.
Lemma lem1271783 (p : nat) (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term143 y B x n) : term145 y B x n p.
Proof. exact (fun h0 : term146 y n B p => @lem1271782 x y n B p h1 h0). Qed.
Lemma lem1271784 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term143 y B x n) : term143 y B x n.
Proof. exact (fun p : nat => @lem1271783 p y B x n h1). Qed.
Lemma lem1271785 (y : nadd) (B : nat) (x : nadd) (n : nat) : term149 y B x n.
Proof. exact (fun h0 : term143 y B x n => @lem1271784 y B x n h0). Qed.
Lemma lem1271786 (x : nadd) (y : nadd) (n : nat) (B : nat) (h1 : term49 x y n B) : term143 y B x n.
Proof. exact (@lem1271785 y B x n (@lem1271773 x y n B h1)). Qed.
Lemma lem1271787 (p : nat) (x : nadd) (y : nadd) (n : nat) (B : nat) (h1 : term49 x y n B) : term144 y B x n p.
Proof. exact (@lem1271786 x y n B h1 p). Qed.
Lemma lem1271788 (y : nadd) (B : nat) (x : nadd) (n : nat) (p : nat) : (term144 y B x n p) = (term145 y B x n p).
Proof. exact (eq_refl (term144 y B x n p)). Qed.
Lemma lem1271791 (p : nat) (x : nadd) (y : nadd) (n : nat) (B : nat) (h1 : term49 x y n B) : term145 y B x n p.
Proof. exact (EQ_MP (@lem1271788 y B x n p) (@lem1271787 p x y n B h1)). Qed.
Lemma lem1271792 (x : nadd) (y : nadd) (n : nat) (B : nat) (h1 : term49 x y n B) : term150 y n B x.
Proof. exact (@lem1271791 (term90 y n B x) x y n B h1). Qed.
Lemma lem1271794 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1271373 m n) (@lem1271372 m n)). Qed.
Lemma lem1271795 (y : nadd) (n : nat) (B : nat) (x : nadd) : (term151 y n B x) = True.
Proof. exact (@lem1271794 (term67 y n B) (term91 x)). Qed.
Lemma lem1271796 (y : nadd) (n : nat) (B : nat) (x : nadd) : True = (term151 y n B x).
Proof. exact (SYM (@lem1271795 y n B x)). Qed.
Lemma lem1271797 (y : nadd) (n : nat) (B : nat) (x : nadd) : term151 y n B x.
Proof. exact (EQ_MP (@lem1271796 y n B x) (@lem0)). Qed.
Lemma lem1271798 (x : nadd) (y : nadd) (n : nat) (B : nat) (h1 : term49 x y n B) : term125 y n B x.
Proof. exact (@lem1271792 x y n B h1 (@lem1271797 y n B x)). Qed.
Lemma lem1271799 (y : nadd) (n : nat) (B : nat) (x : nadd) : term126 y n B x.
Proof. exact (fun h0 : term49 x y n B => @lem1271798 x y n B h0). Qed.
Lemma lem1271800 (y : nadd) (B : nat) (x : nadd) (n : nat) : term120 y B x n.
Proof. exact (EQ_MP (@lem1271744 y B x n) (@lem1271799 y n B x)). Qed.
Lemma lem1271801 (y : nadd) (B : nat) (x : nadd) (n : nat) : term119 y B x n.
Proof. exact (EQ_MP (@lem1271730 y B x n) (@lem1271800 y B x n)). Qed.
Lemma lem1271802 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term10 n) : term110 y B x n.
Proof. exact (EQ_MP (@lem1271728 y B x n h1) (@lem1271801 y B x n)). Qed.
Lemma lem1271803 (y : nadd) (B : nat) (x : nadd) (n : nat) : term110 y B x n.
Proof. exact (or_elim (@lem1271392 n) (fun h0 : n = (NUMERAL 0) => @lem1271660 y B x n h0) (fun h0 : term10 n => @lem1271802 y B x n h0)). Qed.
Lemma lem1271804 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term77 y B x n) : term108 y B x n.
Proof. exact (@lem1271803 y B x n (@lem1271553 y B x n h1)). Qed.
Lemma lem1271805 (y : nadd) (B : nat) (x : nadd) (n : nat) (h1 : term77 y B x n) : term152 y B x.
Proof. exact (ex_intro (term153 y B x) n (@lem1271804 y B x n h1)). Qed.
Lemma lem1271806 (B : nat) (y : nadd) (x : nadd) (h1 : term71 y x) : term152 y B x.
Proof. exact (ex_elim (@lem1271552 B y x h1) (fun n : nat => fun h0 : term154 y B x n => @lem1271805 y B x n h0)). Qed.
Lemma lem1271811 (y : nadd) (x : nadd) (h1 : term71 y x) : term63 y x.
Proof. exact (fun B : nat => @lem1271806 B y x h1). Qed.
Lemma lem1271812 (y : nadd) (x : nadd) : term73 y x.
Proof. exact (fun h0 : term71 y x => @lem1271811 y x h0). Qed.
Lemma lem1271813 (y : nadd) (x : nadd) : term65 y x.
Proof. exact (EQ_MP (@lem1271548 y x) (@lem1271812 y x)). Qed.
Lemma lem1271814 (y : nadd) (x : nadd) : term64 y x.
Proof. exact (EQ_MP (@lem1271502 y x) (@lem1271813 y x)). Qed.
Lemma lem1271819 (x : nadd) : term155 x.
Proof. exact (fun y : nadd => @lem1271814 y x). Qed.
Lemma lem1271824 : term156.
Proof. exact (fun x : nadd => @lem1271819 x). Qed.
