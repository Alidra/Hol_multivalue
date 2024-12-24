Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6921992_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm69_spec.
Require Import thm6920403_spec.
Require Import thm6920404_spec.
Lemma lem6920433 {A : Type'} (P : A -> Prop) (x : A) : term0 A P x.
Proof. exact (EQ_MP (@lem6920404 A P x) (@lem6920403 A P x)). Qed.
Lemma lem6920434 (P : nat -> Prop) (x : nat) : term1 P x.
Proof. exact (@lem6920433 nat P x). Qed.
Lemma lem6920435 : term2.
Proof. exact (@lem6920434 term3 (NUMERAL 0)). Qed.
Lemma lem6920437 (p : Prop) : p = (term4 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6920438 : term5 = term6.
Proof. exact (@lem6920437 term5). Qed.
Lemma lem6920439 : term6 = term5.
Proof. exact (SYM (@lem6920438)). Qed.
Lemma lem6920440 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem6920443 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem6920444 : term9.
Proof. exact (fun h0 : term8 => @lem6920443 h0). Qed.
Lemma lem6920445 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6920446 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem6920447 (h1 : term8) (h2 : term9) : term8.
Proof. exact (@lem6920445 h2 (@lem6920446 h1)). Qed.
Lemma lem6920448 (h1 : term8) : term10.
Proof. exact (fun h0 : term9 => @lem6920447 h1 h0). Qed.
Lemma lem6920449 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6920450 (h1 : term8) (h2 : term9) : term8.
Proof. exact (@lem6920448 h1 (@lem6920449 h2)). Qed.
Lemma lem6920451 (h1 : term9) : term9.
Proof. exact (fun h0 : term8 => @lem6920450 h0 h1). Qed.
Lemma lem6920452 : term11.
Proof. exact (fun h0 : term9 => @lem6920451 h0). Qed.
Lemma lem6920455 : term9.
Proof. exact (@lem6920452 (@lem6920444)). Qed.
Lemma lem6920463 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term12 A P Q) = (term13 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem6920464 (P : nat -> Prop) (Q : nat -> Prop) : (term14 P Q) = (term15 P Q).
Proof. exact (@lem6920463 nat P Q). Qed.
Lemma lem6920465 (x : nat) : (term16 x) = (term17 x).
Proof. exact (@lem6920464 (term18 x) (term19 x)). Qed.
Lemma lem6920466 (x : nat) (y : nat) : (term20 x y) = ((Nat.add x y) = y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem6920467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920468 (x : nat) (y : nat) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem6920467) (@lem6920466 x y)). Qed.
Lemma lem6920469 (x : nat) (y : nat) : (term23 x y) = ((Nat.add y x) = y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem6920470 (x : nat) (y : nat) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem6920468 x y) (@lem6920469 x y)). Qed.
Lemma lem6920471 (x : nat) : (term26 x) = (term27 x).
Proof. exact (fun_ext (fun y : nat => @lem6920470 x y)). Qed.
Lemma lem6920472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920473 (x : nat) : (term16 x) = (term28 x).
Proof. exact (MK_COMB (@lem6920472) (@lem6920471 x)). Qed.
Lemma lem6920474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920475 (x : nat) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem6920474) (@lem6920473 x)). Qed.
Lemma lem6920476 (x : nat) (y : nat) : (term20 x y) = ((Nat.add x y) = y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem6920477 (x : nat) : (term31 x) = (term18 x).
Proof. exact (fun_ext (fun y : nat => @lem6920476 x y)). Qed.
Lemma lem6920478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920479 (x : nat) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem6920478) (@lem6920477 x)). Qed.
Lemma lem6920480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920481 (x : nat) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem6920480) (@lem6920479 x)). Qed.
Lemma lem6920482 (x : nat) (y : nat) : (term23 x y) = ((Nat.add y x) = y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem6920483 (x : nat) : (term36 x) = (term19 x).
Proof. exact (fun_ext (fun y : nat => @lem6920482 x y)). Qed.
Lemma lem6920484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920485 (x : nat) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem6920484) (@lem6920483 x)). Qed.
Lemma lem6920486 (x : nat) : (term17 x) = (term39 x).
Proof. exact (MK_COMB (@lem6920481 x) (@lem6920485 x)). Qed.
Lemma lem6920487 (x : nat) : ((term16 x) = (term17 x)) = ((term28 x) = (term39 x)).
Proof. exact (MK_COMB (@lem6920475 x) (@lem6920486 x)). Qed.
Lemma lem6920488 (x : nat) : (term28 x) = (term39 x).
Proof. exact (EQ_MP (@lem6920487 x) (@lem6920465 x)). Qed.
Lemma lem6920499 : term3 = term40.
Proof. exact (fun_ext (fun x : nat => @lem6920488 x)). Qed.
Lemma lem6920500 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6920501 (y : nat) : (term41 y) = (term42 y).
Proof. exact (MK_COMB (@lem6920499) (@lem6920500 y)). Qed.
Lemma lem6920502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920503 (y : nat) : (term43 y) = (term44 y).
Proof. exact (MK_COMB (@lem6920502) (@lem6920501 y)). Qed.
Lemma lem6920504 (y : nat) : (y = (NUMERAL 0)) = (y = (NUMERAL 0)).
Proof. exact (eq_refl (y = (NUMERAL 0))). Qed.
Lemma lem6920505 (y : nat) : ((term41 y) = (y = (NUMERAL 0))) = ((term42 y) = (y = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem6920503 y) (@lem6920504 y)). Qed.
Lemma lem6920506 : term45 = term46.
Proof. exact (fun_ext (fun y : nat => @lem6920505 y)). Qed.
Lemma lem6920507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920508 : term5 = term47.
Proof. exact (MK_COMB (@lem6920507) (@lem6920506)). Qed.
Lemma lem6920513 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6920514 : term7 = term48.
Proof. exact (MK_COMB (@lem6920513) (@lem6920508)). Qed.
Lemma lem6920515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6920516 : term49 = term50.
Proof. exact (MK_COMB (@lem6920515) (@lem6920514)). Qed.
Lemma lem6920518 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6920519 : term51 = term52.
Proof. exact (@lem6920518 term53). Qed.
Lemma lem6920550 : term8 = term54.
Proof. exact (MK_COMB (@lem6920516) (@lem6920519)). Qed.
Lemma lem6920553 (y : nat) : (term42 y) = (term39 y).
Proof. exact (eq_refl (term42 y)). Qed.
Lemma lem6920554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920555 (y : nat) : (term44 y) = (term55 y).
Proof. exact (MK_COMB (@lem6920554) (@lem6920553 y)). Qed.
Lemma lem6920556 (y : nat) : (y = (NUMERAL 0)) = (y = (NUMERAL 0)).
Proof. exact (eq_refl (y = (NUMERAL 0))). Qed.
Lemma lem6920557 (y : nat) : ((term42 y) = (y = (NUMERAL 0))) = ((term39 y) = (y = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem6920555 y) (@lem6920556 y)). Qed.
Lemma lem6920558 : term46 = term56.
Proof. exact (fun_ext (fun y : nat => @lem6920557 y)). Qed.
Lemma lem6920559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920560 : term47 = term57.
Proof. exact (MK_COMB (@lem6920559) (@lem6920558)). Qed.
Lemma lem6920561 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6920562 : term48 = term58.
Proof. exact (MK_COMB (@lem6920561) (@lem6920560)). Qed.
Lemma lem6920563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6920564 : term50 = term59.
Proof. exact (MK_COMB (@lem6920563) (@lem6920562)). Qed.
Lemma lem6920565 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem6920566 : term54 = term60.
Proof. exact (MK_COMB (@lem6920564) (@lem6920565)). Qed.
Lemma lem6920569 : term8 = term60.
Proof. exact (TRANS (@lem6920550) (@lem6920566)). Qed.
Lemma lem6920570 (m : nat) (n : nat) : ((term61 m n) = (term62 m n)) = ((term61 m n) = (term62 m n)).
Proof. exact (eq_refl ((term61 m n) = (term62 m n))). Qed.
Lemma lem6920571 (m : nat) : (term63 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem6920570 m n)). Qed.
Lemma lem6920572 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920573 (m : nat) : (term64 m) = (term64 m).
Proof. exact (MK_COMB (@lem6920572) (@lem6920571 m)). Qed.
Lemma lem6920574 : term65 = term65.
Proof. exact (fun_ext (fun m : nat => @lem6920573 m)). Qed.
Lemma lem6920575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920576 : term66 = term66.
Proof. exact (MK_COMB (@lem6920575) (@lem6920574)). Qed.
Lemma lem6920577 (m : nat) (n : nat) : ((term67 m n) = (term62 m n)) = ((term67 m n) = (term62 m n)).
Proof. exact (eq_refl ((term67 m n) = (term62 m n))). Qed.
Lemma lem6920578 (m : nat) : (term68 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem6920577 m n)). Qed.
Lemma lem6920579 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920580 (m : nat) : (term69 m) = (term69 m).
Proof. exact (MK_COMB (@lem6920579) (@lem6920578 m)). Qed.
Lemma lem6920581 : term70 = term70.
Proof. exact (fun_ext (fun m : nat => @lem6920580 m)). Qed.
Lemma lem6920582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920583 : term71 = term71.
Proof. exact (MK_COMB (@lem6920582) (@lem6920581)). Qed.
Lemma lem6920584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920585 : term72 = term72.
Proof. exact (MK_COMB (@lem6920584) (@lem6920583)). Qed.
Lemma lem6920586 : term73 = term73.
Proof. exact (MK_COMB (@lem6920585) (@lem6920576)). Qed.
Lemma lem6920587 (m : nat) : ((term74 m) = m) = ((term74 m) = m).
Proof. exact (eq_refl ((term74 m) = m)). Qed.
Lemma lem6920588 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6920587 m)). Qed.
Lemma lem6920589 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920590 : term76 = term76.
Proof. exact (MK_COMB (@lem6920589) (@lem6920588)). Qed.
Lemma lem6920591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920592 : term77 = term77.
Proof. exact (MK_COMB (@lem6920591) (@lem6920590)). Qed.
Lemma lem6920593 : term78 = term78.
Proof. exact (MK_COMB (@lem6920592) (@lem6920586)). Qed.
Lemma lem6920594 (n : nat) : ((term79 n) = n) = ((term79 n) = n).
Proof. exact (eq_refl ((term79 n) = n)). Qed.
Lemma lem6920595 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem6920594 n)). Qed.
Lemma lem6920596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920597 : term81 = term81.
Proof. exact (MK_COMB (@lem6920596) (@lem6920595)). Qed.
Lemma lem6920598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920599 : term82 = term82.
Proof. exact (MK_COMB (@lem6920598) (@lem6920597)). Qed.
Lemma lem6920600 : term53 = term53.
Proof. exact (MK_COMB (@lem6920599) (@lem6920593)). Qed.
Lemma lem6920601 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6920602 : term52 = term52.
Proof. exact (MK_COMB (@lem6920601) (@lem6920600)). Qed.
Lemma lem6920603 (y : nat) : (y = (NUMERAL 0)) = (y = (NUMERAL 0)).
Proof. exact (eq_refl (y = (NUMERAL 0))). Qed.
Lemma lem6920604 (y : nat) (y' : nat) : ((Nat.add y' y) = y') = ((Nat.add y' y) = y').
Proof. exact (eq_refl ((Nat.add y' y) = y')). Qed.
Lemma lem6920605 (y : nat) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920604 y y')). Qed.
Lemma lem6920606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920607 (y : nat) : (term38 y) = (term38 y).
Proof. exact (MK_COMB (@lem6920606) (@lem6920605 y)). Qed.
Lemma lem6920608 (y : nat) (y' : nat) : ((Nat.add y y') = y') = ((Nat.add y y') = y').
Proof. exact (eq_refl ((Nat.add y y') = y')). Qed.
Lemma lem6920609 (y : nat) : (term18 y) = (term18 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920608 y y')). Qed.
Lemma lem6920610 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920611 (y : nat) : (term33 y) = (term33 y).
Proof. exact (MK_COMB (@lem6920610) (@lem6920609 y)). Qed.
Lemma lem6920612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920613 (y : nat) : (term35 y) = (term35 y).
Proof. exact (MK_COMB (@lem6920612) (@lem6920611 y)). Qed.
Lemma lem6920614 (y : nat) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6920613 y) (@lem6920607 y)). Qed.
Lemma lem6920615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920616 (y : nat) : (term55 y) = (term55 y).
Proof. exact (MK_COMB (@lem6920615) (@lem6920614 y)). Qed.
Lemma lem6920617 (y : nat) : ((term39 y) = (y = (NUMERAL 0))) = ((term39 y) = (y = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem6920616 y) (@lem6920603 y)). Qed.
Lemma lem6920618 : term56 = term56.
Proof. exact (fun_ext (fun y : nat => @lem6920617 y)). Qed.
Lemma lem6920619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920620 : term57 = term57.
Proof. exact (MK_COMB (@lem6920619) (@lem6920618)). Qed.
Lemma lem6920621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6920622 : term58 = term58.
Proof. exact (MK_COMB (@lem6920621) (@lem6920620)). Qed.
Lemma lem6920623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6920624 : term59 = term59.
Proof. exact (MK_COMB (@lem6920623) (@lem6920622)). Qed.
Lemma lem6920625 : term60 = term60.
Proof. exact (MK_COMB (@lem6920624) (@lem6920602)). Qed.
Lemma lem6920692 : term8 = term60.
Proof. exact (TRANS (@lem6920569) (@lem6920625)). Qed.
Lemma lem6920693 : term60 = term8.
Proof. exact (SYM (@lem6920692)). Qed.
Lemma lem6920694 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem6920695 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem6920697 (y : nat) (y' : nat) : ((Nat.add y y') = y') = ((Nat.add y y') = y').
Proof. exact (eq_refl ((Nat.add y y') = y')). Qed.
Lemma lem6920698 (P : nat -> Prop) : (term83 P) = (term84 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6920699 (y : nat) : (term85 y) = (term86 y).
Proof. exact (@lem6920698 (term18 y)). Qed.
Lemma lem6920700 (y : nat) (y' : nat) : (term20 y y') = ((Nat.add y y') = y').
Proof. exact (eq_refl (term20 y y')). Qed.
Lemma lem6920701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6920703 (y : nat) (y' : nat) : (term87 y y') = (term88 y y').
Proof. exact (MK_COMB (@lem6920701) (@lem6920700 y y')). Qed.
Lemma lem6920704 (y : nat) : (term89 y) = (term90 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920703 y y')). Qed.
Lemma lem6920705 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920706 (y : nat) : (term86 y) = (term91 y).
Proof. exact (MK_COMB (@lem6920705) (@lem6920704 y)). Qed.
Lemma lem6920707 (y : nat) : (term85 y) = (term91 y).
Proof. exact (TRANS (@lem6920699 y) (@lem6920706 y)). Qed.
Lemma lem6920708 (y : nat) : (term18 y) = (term18 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920697 y y')). Qed.
Lemma lem6920709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920710 (y : nat) : (term33 y) = (term33 y).
Proof. exact (MK_COMB (@lem6920709) (@lem6920708 y)). Qed.
Lemma lem6920712 (y : nat) (y' : nat) : ((Nat.add y' y) = y') = ((Nat.add y' y) = y').
Proof. exact (eq_refl ((Nat.add y' y) = y')). Qed.
Lemma lem6920713 (P : nat -> Prop) : (term83 P) = (term84 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6920714 (y : nat) : (term92 y) = (term93 y).
Proof. exact (@lem6920713 (term19 y)). Qed.
Lemma lem6920715 (y : nat) (y' : nat) : (term23 y y') = ((Nat.add y' y) = y').
Proof. exact (eq_refl (term23 y y')). Qed.
Lemma lem6920716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6920718 (y : nat) (y' : nat) : (term94 y y') = (term95 y y').
Proof. exact (MK_COMB (@lem6920716) (@lem6920715 y y')). Qed.
Lemma lem6920719 (y : nat) : (term96 y) = (term97 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920718 y y')). Qed.
Lemma lem6920720 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920721 (y : nat) : (term93 y) = (term98 y).
Proof. exact (MK_COMB (@lem6920720) (@lem6920719 y)). Qed.
Lemma lem6920722 (y : nat) : (term92 y) = (term98 y).
Proof. exact (TRANS (@lem6920714 y) (@lem6920721 y)). Qed.
Lemma lem6920723 (y : nat) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920712 y y')). Qed.
Lemma lem6920724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6920725 (y : nat) : (term38 y) = (term38 y).
Proof. exact (MK_COMB (@lem6920724) (@lem6920723 y)). Qed.
Lemma lem6920726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920727 (y : nat) : (term99 y) = (term100 y).
Proof. exact (MK_COMB (@lem6920726) (@lem6920707 y)). Qed.
Lemma lem6920728 (y : nat) : (term101 y) = (term102 y).
Proof. exact (MK_COMB (@lem6920727 y) (@lem6920722 y)). Qed.
Lemma lem6920729 (y : nat) : (term103 y) = (term101 y).
Proof. exact (@lem17045 (term33 y) (term38 y)). Qed.
Lemma lem6920730 (y : nat) : (term103 y) = (term102 y).
Proof. exact (TRANS (@lem6920729 y) (@lem6920728 y)). Qed.
Lemma lem6920731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920732 (y : nat) : (term35 y) = (term35 y).
Proof. exact (MK_COMB (@lem6920731) (@lem6920710 y)). Qed.
Lemma lem6920733 (y : nat) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6920732 y) (@lem6920725 y)). Qed.
Lemma lem6920734 (y : nat) : (term104 y) = (term104 y).
Proof. exact (eq_refl (term104 y)). Qed.
Lemma lem6920735 (y : nat) : (y = (NUMERAL 0)) = (y = (NUMERAL 0)).
Proof. exact (eq_refl (y = (NUMERAL 0))). Qed.
Lemma lem6920736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920737 (y : nat) : (term105 y) = (term106 y).
Proof. exact (MK_COMB (@lem6920736) (@lem6920730 y)). Qed.
Lemma lem6920738 (y : nat) : (term107 y) = (term108 y).
Proof. exact (MK_COMB (@lem6920737 y) (@lem6920735 y)). Qed.
Lemma lem6920739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920740 (y : nat) : (term109 y) = (term109 y).
Proof. exact (MK_COMB (@lem6920739) (@lem6920733 y)). Qed.
Lemma lem6920741 (y : nat) : (term110 y) = (term110 y).
Proof. exact (MK_COMB (@lem6920740 y) (@lem6920734 y)). Qed.
Lemma lem6920742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920743 (y : nat) : (term111 y) = (term111 y).
Proof. exact (MK_COMB (@lem6920742) (@lem6920741 y)). Qed.
Lemma lem6920744 (y : nat) : (term112 y) = (term113 y).
Proof. exact (MK_COMB (@lem6920743 y) (@lem6920738 y)). Qed.
Lemma lem6920745 (y : nat) : (term114 y) = (term112 y).
Proof. exact (@lem17646 (term39 y) (y = (NUMERAL 0))). Qed.
Lemma lem6920746 (y : nat) : (term114 y) = (term113 y).
Proof. exact (TRANS (@lem6920745 y) (@lem6920744 y)). Qed.
Lemma lem6920747 (P : nat -> Prop) : (term83 P) = (term84 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6920748 : term58 = term115.
Proof. exact (@lem6920747 term56). Qed.
Lemma lem6920749 (y : nat) : (term116 y) = ((term39 y) = (y = (NUMERAL 0))).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6920750 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6920751 (y : nat) : (term117 y) = (term114 y).
Proof. exact (MK_COMB (@lem6920750) (@lem6920749 y)). Qed.
Lemma lem6920752 (y : nat) : (term117 y) = (term113 y).
Proof. exact (TRANS (@lem6920751 y) (@lem6920746 y)). Qed.
Lemma lem6920753 : term118 = term119.
Proof. exact (fun_ext (fun y : nat => @lem6920752 y)). Qed.
Lemma lem6920754 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920755 : term115 = term120.
Proof. exact (MK_COMB (@lem6920754) (@lem6920753)). Qed.
Lemma lem6920756 : term58 = term120.
Proof. exact (TRANS (@lem6920748) (@lem6920755)). Qed.
Lemma lem6920758 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6920759 (P : nat -> Prop) (Q : nat -> Prop) : (term123 P Q) = (term124 P Q).
Proof. exact (@lem6920758 nat P Q). Qed.
Lemma lem6920760 : term125 = term126.
Proof. exact (@lem6920759 term127 term128). Qed.
Lemma lem6920761 (y : nat) : (term129 y) = (term110 y).
Proof. exact (eq_refl (term129 y)). Qed.
Lemma lem6920762 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920763 (y : nat) : (term130 y) = (term111 y).
Proof. exact (MK_COMB (@lem6920762) (@lem6920761 y)). Qed.
Lemma lem6920764 (y : nat) : (term131 y) = (term108 y).
Proof. exact (eq_refl (term131 y)). Qed.
Lemma lem6920765 (y : nat) : (term132 y) = (term113 y).
Proof. exact (MK_COMB (@lem6920763 y) (@lem6920764 y)). Qed.
Lemma lem6920766 : term133 = term119.
Proof. exact (fun_ext (fun y : nat => @lem6920765 y)). Qed.
Lemma lem6920767 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920768 : term125 = term120.
Proof. exact (MK_COMB (@lem6920767) (@lem6920766)). Qed.
Lemma lem6920769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920770 : term134 = term135.
Proof. exact (MK_COMB (@lem6920769) (@lem6920768)). Qed.
Lemma lem6920771 (y : nat) : (term129 y) = (term110 y).
Proof. exact (eq_refl (term129 y)). Qed.
Lemma lem6920772 : term136 = term127.
Proof. exact (fun_ext (fun y : nat => @lem6920771 y)). Qed.
Lemma lem6920773 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920774 : term137 = term138.
Proof. exact (MK_COMB (@lem6920773) (@lem6920772)). Qed.
Lemma lem6920775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920776 : term139 = term140.
Proof. exact (MK_COMB (@lem6920775) (@lem6920774)). Qed.
Lemma lem6920777 (y : nat) : (term131 y) = (term108 y).
Proof. exact (eq_refl (term131 y)). Qed.
Lemma lem6920778 : term141 = term128.
Proof. exact (fun_ext (fun y : nat => @lem6920777 y)). Qed.
Lemma lem6920779 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920780 : term142 = term143.
Proof. exact (MK_COMB (@lem6920779) (@lem6920778)). Qed.
Lemma lem6920781 : term126 = term144.
Proof. exact (MK_COMB (@lem6920776) (@lem6920780)). Qed.
Lemma lem6920782 : (term125 = term126) = (term120 = term144).
Proof. exact (MK_COMB (@lem6920770) (@lem6920781)). Qed.
Lemma lem6920783 : term120 = term144.
Proof. exact (EQ_MP (@lem6920782) (@lem6920760)). Qed.
Lemma lem6920897 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term122 A P Q) = (term121 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6920898 (P : nat -> Prop) (Q : nat -> Prop) : (term124 P Q) = (term123 P Q).
Proof. exact (@lem6920897 nat P Q). Qed.
Lemma lem6920899 (y : nat) : (term145 y) = (term146 y).
Proof. exact (@lem6920898 (term90 y) (term97 y)). Qed.
Lemma lem6920900 (y : nat) (y' : nat) : (term147 y y') = (term88 y y').
Proof. exact (eq_refl (term147 y y')). Qed.
Lemma lem6920901 (y : nat) : (term148 y) = (term90 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920900 y y')). Qed.
Lemma lem6920902 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920903 (y : nat) : (term149 y) = (term91 y).
Proof. exact (MK_COMB (@lem6920902) (@lem6920901 y)). Qed.
Lemma lem6920904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920905 (y : nat) : (term150 y) = (term100 y).
Proof. exact (MK_COMB (@lem6920904) (@lem6920903 y)). Qed.
Lemma lem6920906 (y : nat) (y' : nat) : (term151 y y') = (term95 y y').
Proof. exact (eq_refl (term151 y y')). Qed.
Lemma lem6920907 (y : nat) : (term152 y) = (term97 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920906 y y')). Qed.
Lemma lem6920908 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920909 (y : nat) : (term153 y) = (term98 y).
Proof. exact (MK_COMB (@lem6920908) (@lem6920907 y)). Qed.
Lemma lem6920910 (y : nat) : (term145 y) = (term102 y).
Proof. exact (MK_COMB (@lem6920905 y) (@lem6920909 y)). Qed.
Lemma lem6920911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920912 (y : nat) : (term154 y) = (term155 y).
Proof. exact (MK_COMB (@lem6920911) (@lem6920910 y)). Qed.
Lemma lem6920913 (y : nat) (y' : nat) : (term147 y y') = (term88 y y').
Proof. exact (eq_refl (term147 y y')). Qed.
Lemma lem6920914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920915 (y : nat) (y' : nat) : (term156 y y') = (term157 y y').
Proof. exact (MK_COMB (@lem6920914) (@lem6920913 y y')). Qed.
Lemma lem6920916 (y : nat) (y' : nat) : (term151 y y') = (term95 y y').
Proof. exact (eq_refl (term151 y y')). Qed.
Lemma lem6920917 (y : nat) (y' : nat) : (term158 y y') = (term159 y y').
Proof. exact (MK_COMB (@lem6920915 y y') (@lem6920916 y y')). Qed.
Lemma lem6920918 (y : nat) : (term160 y) = (term161 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920917 y y')). Qed.
Lemma lem6920919 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920920 (y : nat) : (term146 y) = (term162 y).
Proof. exact (MK_COMB (@lem6920919) (@lem6920918 y)). Qed.
Lemma lem6920921 (y : nat) : ((term145 y) = (term146 y)) = ((term102 y) = (term162 y)).
Proof. exact (MK_COMB (@lem6920912 y) (@lem6920920 y)). Qed.
Lemma lem6920922 (y : nat) : (term102 y) = (term162 y).
Proof. exact (EQ_MP (@lem6920921 y) (@lem6920899 y)). Qed.
Lemma lem6920923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920924 (y : nat) : (term106 y) = (term163 y).
Proof. exact (MK_COMB (@lem6920923) (@lem6920922 y)). Qed.
Lemma lem6920925 (y : nat) : (y = (NUMERAL 0)) = (y = (NUMERAL 0)).
Proof. exact (eq_refl (y = (NUMERAL 0))). Qed.
Lemma lem6920926 (y : nat) : (term108 y) = (term164 y).
Proof. exact (MK_COMB (@lem6920924 y) (@lem6920925 y)). Qed.
Lemma lem6920928 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6920929 (P : nat -> Prop) (Q : Prop) : (term167 P Q) = (term168 P Q).
Proof. exact (@lem6920928 nat P Q). Qed.
Lemma lem6920930 (y : nat) : (term169 y) = (term170 y).
Proof. exact (@lem6920929 (term161 y) (y = (NUMERAL 0))). Qed.
Lemma lem6920931 (y : nat) (y' : nat) : (term171 y y') = (term159 y y').
Proof. exact (eq_refl (term171 y y')). Qed.
Lemma lem6920932 (y : nat) : (term172 y) = (term161 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920931 y y')). Qed.
Lemma lem6920933 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920934 (y : nat) : (term173 y) = (term162 y).
Proof. exact (MK_COMB (@lem6920933) (@lem6920932 y)). Qed.
Lemma lem6920935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920936 (y : nat) : (term174 y) = (term163 y).
Proof. exact (MK_COMB (@lem6920935) (@lem6920934 y)). Qed.
Lemma lem6920937 (y : nat) : (y = (NUMERAL 0)) = (y = (NUMERAL 0)).
Proof. exact (eq_refl (y = (NUMERAL 0))). Qed.
Lemma lem6920938 (y : nat) : (term169 y) = (term164 y).
Proof. exact (MK_COMB (@lem6920936 y) (@lem6920937 y)). Qed.
Lemma lem6920939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920940 (y : nat) : (term175 y) = (term176 y).
Proof. exact (MK_COMB (@lem6920939) (@lem6920938 y)). Qed.
Lemma lem6920941 (y : nat) (y' : nat) : (term171 y y') = (term159 y y').
Proof. exact (eq_refl (term171 y y')). Qed.
Lemma lem6920942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6920943 (y : nat) (y' : nat) : (term177 y y') = (term178 y y').
Proof. exact (MK_COMB (@lem6920942) (@lem6920941 y y')). Qed.
Lemma lem6920944 (y : nat) : (y = (NUMERAL 0)) = (y = (NUMERAL 0)).
Proof. exact (eq_refl (y = (NUMERAL 0))). Qed.
Lemma lem6920945 (y' : nat) (y : nat) : (term179 y' y) = (term180 y' y).
Proof. exact (MK_COMB (@lem6920943 y y') (@lem6920944 y)). Qed.
Lemma lem6920946 (y : nat) : (term181 y) = (term182 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920945 y' y)). Qed.
Lemma lem6920947 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920948 (y : nat) : (term170 y) = (term183 y).
Proof. exact (MK_COMB (@lem6920947) (@lem6920946 y)). Qed.
Lemma lem6920949 (y : nat) : ((term169 y) = (term170 y)) = ((term164 y) = (term183 y)).
Proof. exact (MK_COMB (@lem6920940 y) (@lem6920948 y)). Qed.
Lemma lem6920950 (y : nat) : (term164 y) = (term183 y).
Proof. exact (EQ_MP (@lem6920949 y) (@lem6920930 y)). Qed.
Lemma lem6920951 (y : nat) : (term108 y) = (term183 y).
Proof. exact (TRANS (@lem6920926 y) (@lem6920950 y)). Qed.
Lemma lem6920952 : term128 = term184.
Proof. exact (fun_ext (fun y : nat => @lem6920951 y)). Qed.
Lemma lem6920953 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920954 : term143 = term185.
Proof. exact (MK_COMB (@lem6920953) (@lem6920952)). Qed.
Lemma lem6920955 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem6920956 : term144 = term186.
Proof. exact (MK_COMB (@lem6920955) (@lem6920954)). Qed.
Lemma lem6920958 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term122 A P Q) = (term121 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6920959 (P : nat -> Prop) (Q : nat -> Prop) : (term124 P Q) = (term123 P Q).
Proof. exact (@lem6920958 nat P Q). Qed.
Lemma lem6920960 : term187 = term188.
Proof. exact (@lem6920959 term127 term184). Qed.
Lemma lem6920961 (y : nat) : (term129 y) = (term110 y).
Proof. exact (eq_refl (term129 y)). Qed.
Lemma lem6920962 : term136 = term127.
Proof. exact (fun_ext (fun y : nat => @lem6920961 y)). Qed.
Lemma lem6920963 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920964 : term137 = term138.
Proof. exact (MK_COMB (@lem6920963) (@lem6920962)). Qed.
Lemma lem6920965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920966 : term139 = term140.
Proof. exact (MK_COMB (@lem6920965) (@lem6920964)). Qed.
Lemma lem6920967 (y : nat) : (term189 y) = (term183 y).
Proof. exact (eq_refl (term189 y)). Qed.
Lemma lem6920968 : term190 = term184.
Proof. exact (fun_ext (fun y : nat => @lem6920967 y)). Qed.
Lemma lem6920969 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920970 : term191 = term185.
Proof. exact (MK_COMB (@lem6920969) (@lem6920968)). Qed.
Lemma lem6920971 : term187 = term186.
Proof. exact (MK_COMB (@lem6920966) (@lem6920970)). Qed.
Lemma lem6920972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920973 : term192 = term193.
Proof. exact (MK_COMB (@lem6920972) (@lem6920971)). Qed.
Lemma lem6920974 (y : nat) : (term129 y) = (term110 y).
Proof. exact (eq_refl (term129 y)). Qed.
Lemma lem6920975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6920976 (y : nat) : (term130 y) = (term111 y).
Proof. exact (MK_COMB (@lem6920975) (@lem6920974 y)). Qed.
Lemma lem6920977 (y : nat) : (term189 y) = (term183 y).
Proof. exact (eq_refl (term189 y)). Qed.
Lemma lem6920978 (y : nat) : (term194 y) = (term195 y).
Proof. exact (MK_COMB (@lem6920976 y) (@lem6920977 y)). Qed.
Lemma lem6920979 : term196 = term197.
Proof. exact (fun_ext (fun y : nat => @lem6920978 y)). Qed.
Lemma lem6920980 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920981 : term188 = term198.
Proof. exact (MK_COMB (@lem6920980) (@lem6920979)). Qed.
Lemma lem6920982 : (term187 = term188) = (term186 = term198).
Proof. exact (MK_COMB (@lem6920973) (@lem6920981)). Qed.
Lemma lem6920983 : term186 = term198.
Proof. exact (EQ_MP (@lem6920982) (@lem6920960)). Qed.
Lemma lem6920985 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6920986 (P : Prop) (Q : nat -> Prop) : (term201 P Q) = (term202 P Q).
Proof. exact (@lem6920985 nat P Q). Qed.
Lemma lem6920987 (y : nat) : (term203 y) = (term204 y).
Proof. exact (@lem6920986 (term110 y) (term182 y)). Qed.
Lemma lem6920988 (y' : nat) (y : nat) : (term205 y y') = (term180 y' y).
Proof. exact (eq_refl (term205 y y')). Qed.
Lemma lem6920989 (y : nat) : (term206 y) = (term182 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920988 y' y)). Qed.
Lemma lem6920990 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6920991 (y : nat) : (term207 y) = (term183 y).
Proof. exact (MK_COMB (@lem6920990) (@lem6920989 y)). Qed.
Lemma lem6920992 (y : nat) : (term111 y) = (term111 y).
Proof. exact (eq_refl (term111 y)). Qed.
Lemma lem6920993 (y : nat) : (term203 y) = (term195 y).
Proof. exact (MK_COMB (@lem6920992 y) (@lem6920991 y)). Qed.
Lemma lem6920994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6920995 (y : nat) : (term208 y) = (term209 y).
Proof. exact (MK_COMB (@lem6920994) (@lem6920993 y)). Qed.
Lemma lem6920996 (y' : nat) (y : nat) : (term205 y y') = (term180 y' y).
Proof. exact (eq_refl (term205 y y')). Qed.
Lemma lem6920997 (y : nat) : (term111 y) = (term111 y).
Proof. exact (eq_refl (term111 y)). Qed.
Lemma lem6920998 (y' : nat) (y : nat) : (term210 y y') = (term211 y' y).
Proof. exact (MK_COMB (@lem6920997 y) (@lem6920996 y' y)). Qed.
Lemma lem6920999 (y : nat) : (term212 y) = (term213 y).
Proof. exact (fun_ext (fun y' : nat => @lem6920998 y' y)). Qed.
Lemma lem6921000 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6921001 (y : nat) : (term204 y) = (term214 y).
Proof. exact (MK_COMB (@lem6921000) (@lem6920999 y)). Qed.
Lemma lem6921002 (y : nat) : ((term203 y) = (term204 y)) = ((term195 y) = (term214 y)).
Proof. exact (MK_COMB (@lem6920995 y) (@lem6921001 y)). Qed.
Lemma lem6921003 (y : nat) : (term195 y) = (term214 y).
Proof. exact (EQ_MP (@lem6921002 y) (@lem6920987 y)). Qed.
Lemma lem6921004 : term197 = term215.
Proof. exact (fun_ext (fun y : nat => @lem6921003 y)). Qed.
Lemma lem6921005 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6921006 : term198 = term216.
Proof. exact (MK_COMB (@lem6921005) (@lem6921004)). Qed.
Lemma lem6921007 : term186 = term216.
Proof. exact (TRANS (@lem6920983) (@lem6921006)). Qed.
Lemma lem6921008 : term144 = term216.
Proof. exact (TRANS (@lem6920956) (@lem6921007)). Qed.
Lemma lem6921009 : term120 = term216.
Proof. exact (TRANS (@lem6920783) (@lem6921008)). Qed.
Lemma lem6921010 : term58 = term216.
Proof. exact (TRANS (@lem6920756) (@lem6921009)). Qed.
Lemma lem6921011 (h1 : term58) : term216.
Proof. exact (EQ_MP (@lem6921010) (@lem6920694 h1)). Qed.
Lemma lem6921012 (n : nat) : ((term79 n) = n) = ((term79 n) = n).
Proof. exact (eq_refl ((term79 n) = n)). Qed.
Lemma lem6921013 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem6921012 n)). Qed.
Lemma lem6921014 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921015 : term81 = term81.
Proof. exact (MK_COMB (@lem6921014) (@lem6921013)). Qed.
Lemma lem6921016 (m : nat) : ((term74 m) = m) = ((term74 m) = m).
Proof. exact (eq_refl ((term74 m) = m)). Qed.
Lemma lem6921017 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6921016 m)). Qed.
Lemma lem6921018 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921019 : term76 = term76.
Proof. exact (MK_COMB (@lem6921018) (@lem6921017)). Qed.
Lemma lem6921020 (m : nat) (n : nat) : ((term67 m n) = (term62 m n)) = ((term67 m n) = (term62 m n)).
Proof. exact (eq_refl ((term67 m n) = (term62 m n))). Qed.
Lemma lem6921021 (m : nat) : (term68 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem6921020 m n)). Qed.
Lemma lem6921022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921023 (m : nat) : (term69 m) = (term69 m).
Proof. exact (MK_COMB (@lem6921022) (@lem6921021 m)). Qed.
Lemma lem6921024 : term70 = term70.
Proof. exact (fun_ext (fun m : nat => @lem6921023 m)). Qed.
Lemma lem6921025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921026 : term71 = term71.
Proof. exact (MK_COMB (@lem6921025) (@lem6921024)). Qed.
Lemma lem6921027 (m : nat) (n : nat) : ((term61 m n) = (term62 m n)) = ((term61 m n) = (term62 m n)).
Proof. exact (eq_refl ((term61 m n) = (term62 m n))). Qed.
Lemma lem6921028 (m : nat) : (term63 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem6921027 m n)). Qed.
Lemma lem6921029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921030 (m : nat) : (term64 m) = (term64 m).
Proof. exact (MK_COMB (@lem6921029) (@lem6921028 m)). Qed.
Lemma lem6921031 : term65 = term65.
Proof. exact (fun_ext (fun m : nat => @lem6921030 m)). Qed.
Lemma lem6921032 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921033 : term66 = term66.
Proof. exact (MK_COMB (@lem6921032) (@lem6921031)). Qed.
Lemma lem6921034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921035 : term72 = term72.
Proof. exact (MK_COMB (@lem6921034) (@lem6921026)). Qed.
Lemma lem6921036 : term73 = term73.
Proof. exact (MK_COMB (@lem6921035) (@lem6921033)). Qed.
Lemma lem6921037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921038 : term77 = term77.
Proof. exact (MK_COMB (@lem6921037) (@lem6921019)). Qed.
Lemma lem6921039 : term78 = term78.
Proof. exact (MK_COMB (@lem6921038) (@lem6921036)). Qed.
Lemma lem6921040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921041 : term82 = term82.
Proof. exact (MK_COMB (@lem6921040) (@lem6921015)). Qed.
Lemma lem6921070 : term53 = term53.
Proof. exact (MK_COMB (@lem6921041) (@lem6921039)). Qed.
Lemma lem6921071 (h1 : term53) : term53.
Proof. exact (EQ_MP (@lem6921070) (@lem6920695 h1)). Qed.
Lemma lem6921072 (y : nat) (h1 : term214 y) : term214 y.
Proof. exact (h1). Qed.
Lemma lem6921073 (y' : nat) (y : nat) (h1 : term211 y' y) : term211 y' y.
Proof. exact (h1). Qed.
Lemma lem6921090 (m : nat) (n : nat) : ((term61 m n) = (term62 m n)) = ((term61 m n) = (term62 m n)).
Proof. exact (eq_refl ((term61 m n) = (term62 m n))). Qed.
Lemma lem6921091 (m : nat) : (term63 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem6921090 m n)). Qed.
Lemma lem6921092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921093 (m : nat) : (term64 m) = (term64 m).
Proof. exact (MK_COMB (@lem6921092) (@lem6921091 m)). Qed.
Lemma lem6921094 : term65 = term65.
Proof. exact (fun_ext (fun m : nat => @lem6921093 m)). Qed.
Lemma lem6921095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921096 : term66 = term66.
Proof. exact (MK_COMB (@lem6921095) (@lem6921094)). Qed.
Lemma lem6921113 (m : nat) (n : nat) : ((term67 m n) = (term62 m n)) = ((term67 m n) = (term62 m n)).
Proof. exact (eq_refl ((term67 m n) = (term62 m n))). Qed.
Lemma lem6921114 (m : nat) : (term68 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem6921113 m n)). Qed.
Lemma lem6921115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921116 (m : nat) : (term69 m) = (term69 m).
Proof. exact (MK_COMB (@lem6921115) (@lem6921114 m)). Qed.
Lemma lem6921117 : term70 = term70.
Proof. exact (fun_ext (fun m : nat => @lem6921116 m)). Qed.
Lemma lem6921118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921119 : term71 = term71.
Proof. exact (MK_COMB (@lem6921118) (@lem6921117)). Qed.
Lemma lem6921120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921121 : term72 = term72.
Proof. exact (MK_COMB (@lem6921120) (@lem6921119)). Qed.
Lemma lem6921122 : term73 = term73.
Proof. exact (MK_COMB (@lem6921121) (@lem6921096)). Qed.
Lemma lem6921133 (m : nat) : ((term74 m) = m) = ((term74 m) = m).
Proof. exact (eq_refl ((term74 m) = m)). Qed.
Lemma lem6921134 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6921133 m)). Qed.
Lemma lem6921135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921136 : term76 = term76.
Proof. exact (MK_COMB (@lem6921135) (@lem6921134)). Qed.
Lemma lem6921137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921138 : term77 = term77.
Proof. exact (MK_COMB (@lem6921137) (@lem6921136)). Qed.
Lemma lem6921139 : term78 = term78.
Proof. exact (MK_COMB (@lem6921138) (@lem6921122)). Qed.
Lemma lem6921150 (n : nat) : ((term79 n) = n) = ((term79 n) = n).
Proof. exact (eq_refl ((term79 n) = n)). Qed.
Lemma lem6921151 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem6921150 n)). Qed.
Lemma lem6921152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921153 : term81 = term81.
Proof. exact (MK_COMB (@lem6921152) (@lem6921151)). Qed.
Lemma lem6921154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921155 : term82 = term82.
Proof. exact (MK_COMB (@lem6921154) (@lem6921153)). Qed.
Lemma lem6921156 : term53 = term53.
Proof. exact (MK_COMB (@lem6921155) (@lem6921139)). Qed.
Lemma lem6921157 (h1 : term53) : term53.
Proof. exact (EQ_MP (@lem6921156) (@lem6921071 h1)). Qed.
Lemma lem6921192 (y' : nat) (y : nat) : (term180 y' y) = (term180 y' y).
Proof. exact (eq_refl (term180 y' y)). Qed.
Lemma lem6921201 (y : nat) : (term104 y) = (term104 y).
Proof. exact (eq_refl (term104 y)). Qed.
Lemma lem6921210 (y : nat) (y' : nat) : ((Nat.add y' y) = y') = ((Nat.add y' y) = y').
Proof. exact (eq_refl ((Nat.add y' y) = y')). Qed.
Lemma lem6921211 (y : nat) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : nat => @lem6921210 y y')). Qed.
Lemma lem6921212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921213 (y : nat) : (term38 y) = (term38 y).
Proof. exact (MK_COMB (@lem6921212) (@lem6921211 y)). Qed.
Lemma lem6921222 (y : nat) (y' : nat) : ((Nat.add y y') = y') = ((Nat.add y y') = y').
Proof. exact (eq_refl ((Nat.add y y') = y')). Qed.
Lemma lem6921223 (y : nat) : (term18 y) = (term18 y).
Proof. exact (fun_ext (fun y' : nat => @lem6921222 y y')). Qed.
Lemma lem6921224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921225 (y : nat) : (term33 y) = (term33 y).
Proof. exact (MK_COMB (@lem6921224) (@lem6921223 y)). Qed.
Lemma lem6921226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921227 (y : nat) : (term35 y) = (term35 y).
Proof. exact (MK_COMB (@lem6921226) (@lem6921225 y)). Qed.
Lemma lem6921228 (y : nat) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6921227 y) (@lem6921213 y)). Qed.
Lemma lem6921229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921230 (y : nat) : (term109 y) = (term109 y).
Proof. exact (MK_COMB (@lem6921229) (@lem6921228 y)). Qed.
Lemma lem6921231 (y : nat) : (term110 y) = (term110 y).
Proof. exact (MK_COMB (@lem6921230 y) (@lem6921201 y)). Qed.
Lemma lem6921232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6921233 (y : nat) : (term111 y) = (term111 y).
Proof. exact (MK_COMB (@lem6921232) (@lem6921231 y)). Qed.
Lemma lem6921234 (y' : nat) (y : nat) : (term211 y' y) = (term211 y' y).
Proof. exact (MK_COMB (@lem6921233 y) (@lem6921192 y' y)). Qed.
Lemma lem6921235 (y' : nat) (y : nat) (h1 : term211 y' y) : term211 y' y.
Proof. exact (EQ_MP (@lem6921234 y' y) (@lem6921073 y' y h1)). Qed.
Lemma lem6921236 (h1 : term53) : term78.
Proof. exact (proj2 (@lem6921157 h1)). Qed.
Lemma lem6921237 (h1 : term53) : term81.
Proof. exact (proj1 (@lem6921157 h1)). Qed.
Lemma lem6921239 (h1 : term53) : term76.
Proof. exact (proj1 (@lem6921236 h1)). Qed.
Lemma lem6921242 (y : nat) (h1 : term110 y) : term110 y.
Proof. exact (h1). Qed.
Lemma lem6921243 (y' : nat) (y : nat) (h1 : term180 y' y) : term180 y' y.
Proof. exact (h1). Qed.
Lemma lem6921245 (y : nat) (h1 : term110 y) : term39 y.
Proof. exact (proj1 (@lem6921242 y h1)). Qed.
Lemma lem6921247 (y : nat) (h1 : term110 y) : term33 y.
Proof. exact (proj1 (@lem6921245 y h1)). Qed.
Lemma lem6921249 (y' : nat) (y : nat) (h1 : term180 y' y) : term159 y y'.
Proof. exact (proj1 (@lem6921243 y' y h1)). Qed.
Lemma lem6921260 (m : nat) : ((term74 m) = m) = ((term74 m) = m).
Proof. exact (eq_refl ((term74 m) = m)). Qed.
Lemma lem6921261 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6921260 m)). Qed.
Lemma lem6921262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921264 : term76 = term76.
Proof. exact (MK_COMB (@lem6921262) (@lem6921261)). Qed.
Lemma lem6921265 (h1 : term53) : term76.
Proof. exact (EQ_MP (@lem6921264) (@lem6921239 h1)). Qed.
Lemma lem6921291 (y : nat) (y' : nat) : ((Nat.add y y') = y') = ((Nat.add y y') = y').
Proof. exact (eq_refl ((Nat.add y y') = y')). Qed.
Lemma lem6921292 (y : nat) : (term18 y) = (term18 y).
Proof. exact (fun_ext (fun y' : nat => @lem6921291 y y')). Qed.
Lemma lem6921293 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921295 (y : nat) : (term33 y) = (term33 y).
Proof. exact (MK_COMB (@lem6921293) (@lem6921292 y)). Qed.
Lemma lem6921296 (y : nat) (h1 : term110 y) : term33 y.
Proof. exact (EQ_MP (@lem6921295 y) (@lem6921247 y h1)). Qed.
Lemma lem6921305 (n : nat) : ((term79 n) = n) = ((term79 n) = n).
Proof. exact (eq_refl ((term79 n) = n)). Qed.
Lemma lem6921306 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem6921305 n)). Qed.
Lemma lem6921307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921309 : term81 = term81.
Proof. exact (MK_COMB (@lem6921307) (@lem6921306)). Qed.
Lemma lem6921310 (h1 : term53) : term81.
Proof. exact (EQ_MP (@lem6921309) (@lem6921237 h1)). Qed.
Lemma lem6921345 (y : nat) (y' : nat) (h1 : term88 y y') : term88 y y'.
Proof. exact (h1). Qed.
Lemma lem6921354 (m : nat) : ((term74 m) = m) = ((term74 m) = m).
Proof. exact (eq_refl ((term74 m) = m)). Qed.
Lemma lem6921355 : term75 = term75.
Proof. exact (fun_ext (fun m : nat => @lem6921354 m)). Qed.
Lemma lem6921356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6921358 : term76 = term76.
Proof. exact (MK_COMB (@lem6921356) (@lem6921355)). Qed.
Lemma lem6921359 (h1 : term53) : term76.
Proof. exact (EQ_MP (@lem6921358) (@lem6921239 h1)). Qed.
Lemma lem6921387 (y : nat) (y' : nat) (h1 : term95 y y') : term95 y y'.
Proof. exact (h1). Qed.
Lemma lem6921391 (_92325 : nat) (h1 : term53) : term217 _92325.
Proof. exact (@lem6921265 h1 _92325). Qed.
Lemma lem6921392 (_92325 : nat) : (term217 _92325) = ((term74 _92325) = _92325).
Proof. exact (eq_refl (term217 _92325)). Qed.
Lemma lem6921406 (_92330 : nat) (y : nat) (h1 : term110 y) : term20 y _92330.
Proof. exact (@lem6921296 y h1 _92330). Qed.
Lemma lem6921407 (y : nat) (_92330 : nat) : (term20 y _92330) = ((Nat.add y _92330) = _92330).
Proof. exact (eq_refl (term20 y _92330)). Qed.
Lemma lem6921412 (_92332 : nat) (h1 : term53) : term218 _92332.
Proof. exact (@lem6921310 h1 _92332). Qed.
Lemma lem6921413 (_92332 : nat) : (term218 _92332) = ((term79 _92332) = _92332).
Proof. exact (eq_refl (term218 _92332)). Qed.
Lemma lem6921433 (_92339 : nat) (h1 : term53) : term217 _92339.
Proof. exact (@lem6921359 h1 _92339). Qed.
Lemma lem6921434 (_92339 : nat) : (term217 _92339) = ((term74 _92339) = _92339).
Proof. exact (eq_refl (term217 _92339)). Qed.
Lemma lem6921457 (y : nat) (h1 : term110 y) : term104 y.
Proof. exact (proj2 (@lem6921242 y h1)). Qed.
Lemma lem6921471 (y' : nat) (y : nat) (h1 : term180 y' y) : y = (NUMERAL 0).
Proof. exact (proj2 (@lem6921243 y' y h1)). Qed.
Lemma lem6921473 (y : nat) (y' : nat) (h1 : term88 y y') : term88 y y'.
Proof. exact (h1). Qed.
Lemma lem6921483 (y' : nat) (y : nat) (h1 : term180 y' y) : y = (NUMERAL 0).
Proof. exact (proj2 (@lem6921243 y' y h1)). Qed.
Lemma lem6921485 (y : nat) (y' : nat) (h1 : term95 y y') : term95 y y'.
Proof. exact (h1). Qed.
Lemma lem6921556 (y' : nat) : (term219 y') = (term219 y').
Proof. exact (eq_refl (term219 y')). Qed.
Lemma lem6921557 (y' : nat) (y : nat) (h1 : term180 y' y) : (term220 y' y) = (term221 y').
Proof. exact (MK_COMB (@lem6921556 y') (@lem6921471 y' y h1)). Qed.
Lemma lem6921558 (y' : nat) : (term221 y') = (term222 y').
Proof. exact (eq_refl (term221 y')). Qed.
Lemma lem6921559 (y' : nat) (y : nat) : (term223 y' y) = (term223 y' y).
Proof. exact (eq_refl (term223 y' y)). Qed.
Lemma lem6921560 (y : nat) (y' : nat) : ((term220 y' y) = (term221 y')) = ((term220 y' y) = (term222 y')).
Proof. exact (MK_COMB (@lem6921559 y' y) (@lem6921558 y')). Qed.
Lemma lem6921561 (y : nat) (y' : nat) : (term220 y' y) = (term88 y y').
Proof. exact (eq_refl (term220 y' y)). Qed.
Lemma lem6921562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6921563 (y : nat) (y' : nat) : (term223 y' y) = (term224 y y').
Proof. exact (MK_COMB (@lem6921562) (@lem6921561 y y')). Qed.
Lemma lem6921564 (y' : nat) : (term222 y') = (term222 y').
Proof. exact (eq_refl (term222 y')). Qed.
Lemma lem6921565 (y : nat) (y' : nat) : ((term220 y' y) = (term222 y')) = ((term88 y y') = (term222 y')).
Proof. exact (MK_COMB (@lem6921563 y y') (@lem6921564 y')). Qed.
Lemma lem6921566 (y : nat) (y' : nat) : ((term220 y' y) = (term221 y')) = ((term88 y y') = (term222 y')).
Proof. exact (TRANS (@lem6921560 y y') (@lem6921565 y y')). Qed.
Lemma lem6921567 (y' : nat) (y : nat) (h1 : term180 y' y) : (term88 y y') = (term222 y').
Proof. exact (EQ_MP (@lem6921566 y y') (@lem6921557 y' y h1)). Qed.
Lemma lem6921568 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term180 y' y) : term222 y'.
Proof. exact (EQ_MP (@lem6921567 y' y h2) (@lem6921473 y y' h1)). Qed.
Lemma lem6921639 (y' : nat) : (term225 y') = (term225 y').
Proof. exact (eq_refl (term225 y')). Qed.
Lemma lem6921640 (y' : nat) (y : nat) (h1 : term180 y' y) : (term226 y' y) = (term227 y').
Proof. exact (MK_COMB (@lem6921639 y') (@lem6921483 y' y h1)). Qed.
Lemma lem6921641 (y' : nat) : (term227 y') = (term228 y').
Proof. exact (eq_refl (term227 y')). Qed.
Lemma lem6921642 (y' : nat) (y : nat) : (term229 y' y) = (term229 y' y).
Proof. exact (eq_refl (term229 y' y)). Qed.
Lemma lem6921643 (y : nat) (y' : nat) : ((term226 y' y) = (term227 y')) = ((term226 y' y) = (term228 y')).
Proof. exact (MK_COMB (@lem6921642 y' y) (@lem6921641 y')). Qed.
Lemma lem6921644 (y : nat) (y' : nat) : (term226 y' y) = (term95 y y').
Proof. exact (eq_refl (term226 y' y)). Qed.
Lemma lem6921645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6921646 (y : nat) (y' : nat) : (term229 y' y) = (term230 y y').
Proof. exact (MK_COMB (@lem6921645) (@lem6921644 y y')). Qed.
Lemma lem6921647 (y' : nat) : (term228 y') = (term228 y').
Proof. exact (eq_refl (term228 y')). Qed.
Lemma lem6921648 (y : nat) (y' : nat) : ((term226 y' y) = (term228 y')) = ((term95 y y') = (term228 y')).
Proof. exact (MK_COMB (@lem6921646 y y') (@lem6921647 y')). Qed.
Lemma lem6921649 (y : nat) (y' : nat) : ((term226 y' y) = (term227 y')) = ((term95 y y') = (term228 y')).
Proof. exact (TRANS (@lem6921643 y y') (@lem6921648 y y')). Qed.
Lemma lem6921650 (y' : nat) (y : nat) (h1 : term180 y' y) : (term95 y y') = (term228 y').
Proof. exact (EQ_MP (@lem6921649 y y') (@lem6921640 y' y h1)). Qed.
Lemma lem6921651 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term180 y' y) : term228 y'.
Proof. exact (EQ_MP (@lem6921650 y' y h2) (@lem6921485 y y' h1)). Qed.
Lemma lem6921684 (x : nat) (y : nat) (z : nat) : term231 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem6921686 (_92325 : nat) (h1 : term53) : (term74 _92325) = _92325.
Proof. exact (EQ_MP (@lem6921392 _92325) (@lem6921391 _92325 h1)). Qed.
Lemma lem6921687 (y : nat) (h1 : term53) : (term74 y) = y.
Proof. exact (@lem6921686 y h1). Qed.
Lemma lem6921688 (y : nat) (h1 : term53) : term232 y.
Proof. exact (fun h0 : term228 y => @lem6921687 y h1). Qed.
Lemma lem6921690 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921691 (y : nat) : (term232 y) = ((term74 y) = y).
Proof. exact (@lem6921690 ((term74 y) = y)). Qed.
Lemma lem6921692 (y : nat) (h1 : term53) : (term74 y) = y.
Proof. exact (EQ_MP (@lem6921691 y) (@lem6921688 y h1)). Qed.
Lemma lem6921694 (_92330 : nat) (y : nat) (h1 : term110 y) : (Nat.add y _92330) = _92330.
Proof. exact (EQ_MP (@lem6921407 y _92330) (@lem6921406 _92330 y h1)). Qed.
Lemma lem6921695 (y : nat) (h1 : term110 y) : (term74 y) = (NUMERAL 0).
Proof. exact (@lem6921694 (NUMERAL 0) y h1). Qed.
Lemma lem6921696 (y : nat) (h1 : term110 y) : term234 y.
Proof. exact (fun h0 : term235 y => @lem6921695 y h1). Qed.
Lemma lem6921698 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921699 (y : nat) : (term234 y) = ((term74 y) = (NUMERAL 0)).
Proof. exact (@lem6921698 ((term74 y) = (NUMERAL 0))). Qed.
Lemma lem6921700 (y : nat) (h1 : term110 y) : (term74 y) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6921699 y) (@lem6921696 y h1)). Qed.
Lemma lem6921718 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6921719 (y : nat) (x : nat) (z : nat) : (term236 x y z) = (term237 y x z).
Proof. exact (@lem6921718 (y = z) (term238 x z)). Qed.
Lemma lem6921729 (x : nat) (y : nat) : (term239 x y) = (term239 x y).
Proof. exact (eq_refl (term239 x y)). Qed.
Lemma lem6921730 (y : nat) (x : nat) (z : nat) : (term231 x y z) = (term240 y x z).
Proof. exact (MK_COMB (@lem6921729 x y) (@lem6921719 y x z)). Qed.
Lemma lem6921734 (q : Prop) (p : Prop) (r : Prop) : (term241 p q r) = (term241 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6921735 (y : nat) (x : nat) (z : nat) : (term240 y x z) = (term242 y x z).
Proof. exact (@lem6921734 (y = z) (term238 x y) (term238 x z)). Qed.
Lemma lem6921757 (y : nat) (x : nat) (z : nat) : (term231 x y z) = (term242 y x z).
Proof. exact (TRANS (@lem6921730 y x z) (@lem6921735 y x z)). Qed.
Lemma lem6921758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6921759 (y : nat) (x : nat) (z : nat) : (term243 x y z) = (term244 y x z).
Proof. exact (MK_COMB (@lem6921758) (@lem6921757 y x z)). Qed.
Lemma lem6921781 (y : nat) (x : nat) (z : nat) : (term242 y x z) = (term242 y x z).
Proof. exact (eq_refl (term242 y x z)). Qed.
Lemma lem6921782 (y : nat) (x : nat) (z : nat) : ((term231 x y z) = (term242 y x z)) = ((term242 y x z) = (term242 y x z)).
Proof. exact (MK_COMB (@lem6921759 y x z) (@lem6921781 y x z)). Qed.
Lemma lem6921784 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6921785 (x : Prop) : (x = x) = True.
Proof. exact (@lem6921784 Prop x). Qed.
Lemma lem6921786 (y : nat) (x : nat) (z : nat) : ((term242 y x z) = (term242 y x z)) = True.
Proof. exact (@lem6921785 (term242 y x z)). Qed.
Lemma lem6921787 (y : nat) (x : nat) (z : nat) : ((term231 x y z) = (term242 y x z)) = True.
Proof. exact (TRANS (@lem6921782 y x z) (@lem6921786 y x z)). Qed.
Lemma lem6921788 (y : nat) (x : nat) (z : nat) : True = ((term231 x y z) = (term242 y x z)).
Proof. exact (SYM (@lem6921787 y x z)). Qed.
Lemma lem6921789 (y : nat) (x : nat) (z : nat) : (term231 x y z) = (term242 y x z).
Proof. exact (EQ_MP (@lem6921788 y x z) (@lem0)). Qed.
Lemma lem6921790 (y : nat) (x : nat) (z : nat) : term242 y x z.
Proof. exact (EQ_MP (@lem6921789 y x z) (@lem6921684 x y z)). Qed.
Lemma lem6921792 (b : Prop) (a : Prop) : (a \/ b) = (term245 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6921793 (x : nat) (y : nat) (z : nat) : (term242 y x z) = (term246 x y z).
Proof. exact (@lem6921792 (term247 y x z) (y = z)). Qed.
Lemma lem6921795 (a : Prop) (b : Prop) : (term248 a b) = (term249 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6921796 (y : nat) (x : nat) (z : nat) : (term250 y x z) = (term251 y x z).
Proof. exact (@lem6921795 (term238 x y) (term238 x z)). Qed.
Lemma lem6921798 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6921799 (x : nat) (y : nat) : (term253 x y) = (x = y).
Proof. exact (@lem6921798 (x = y)). Qed.
Lemma lem6921800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6921801 (x : nat) (y : nat) : (term254 x y) = (term255 x y).
Proof. exact (MK_COMB (@lem6921800) (@lem6921799 x y)). Qed.
Lemma lem6921803 (a : Prop) : (term252 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6921804 (x : nat) (z : nat) : (term253 x z) = (x = z).
Proof. exact (@lem6921803 (x = z)). Qed.
Lemma lem6921805 (y : nat) (x : nat) (z : nat) : (term251 y x z) = (term256 y x z).
Proof. exact (MK_COMB (@lem6921801 x y) (@lem6921804 x z)). Qed.
Lemma lem6921806 (y : nat) (x : nat) (z : nat) : (term250 y x z) = (term256 y x z).
Proof. exact (TRANS (@lem6921796 y x z) (@lem6921805 y x z)). Qed.
Lemma lem6921807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6921808 (y : nat) (x : nat) (z : nat) : (term257 y x z) = (term258 y x z).
Proof. exact (MK_COMB (@lem6921807) (@lem6921806 y x z)). Qed.
Lemma lem6921809 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6921810 (x : nat) (y : nat) (z : nat) : (term246 x y z) = (term259 x y z).
Proof. exact (MK_COMB (@lem6921808 y x z) (@lem6921809 y z)). Qed.
Lemma lem6921811 (x : nat) (y : nat) (z : nat) : (term242 y x z) = (term259 x y z).
Proof. exact (TRANS (@lem6921793 x y z) (@lem6921810 x y z)). Qed.
Lemma lem6921813 (y : nat) (h1 : term53) (h2 : term110 y) : term260 y.
Proof. exact (conj (@lem6921692 y h1) (@lem6921700 y h2)). Qed.
Lemma lem6921815 (x : nat) (y : nat) (z : nat) : term259 x y z.
Proof. exact (EQ_MP (@lem6921811 x y z) (@lem6921790 y x z)). Qed.
Lemma lem6921816 (y : nat) : term261 y.
Proof. exact (@lem6921815 (term74 y) y (NUMERAL 0)). Qed.
Lemma lem6921819 (y : nat) (h1 : term53) (h2 : term110 y) : y = (NUMERAL 0).
Proof. exact (@lem6921816 y (@lem6921813 y h1 h2)). Qed.
Lemma lem6921820 (y : nat) (h1 : term53) (h2 : term110 y) : term262 y.
Proof. exact (fun h0 : term104 y => @lem6921819 y h1 h2). Qed.
Lemma lem6921822 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921823 (y : nat) : (term262 y) = (y = (NUMERAL 0)).
Proof. exact (@lem6921822 (y = (NUMERAL 0))). Qed.
Lemma lem6921824 (y : nat) (h1 : term53) (h2 : term110 y) : y = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6921823 y) (@lem6921820 y h1 h2)). Qed.
Lemma lem6921827 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6921829 (y : nat) : (term104 y) = (term263 y).
Proof. exact (@lem6921827 (y = (NUMERAL 0))). Qed.
Lemma lem6921832 (y : nat) (h1 : term110 y) : term263 y.
Proof. exact (EQ_MP (@lem6921829 y) (@lem6921457 y h1)). Qed.
Lemma lem6921835 (y : nat) (h1 : term53) (h2 : term110 y) : False.
Proof. exact (@lem6921832 y h2 (@lem6921824 y h1 h2)). Qed.
Lemma lem6921836 (y : nat) (h1 : term53) (h2 : term110 y) : term264.
Proof. exact (fun h0 : ~ False => @lem6921835 y h1 h2). Qed.
Lemma lem6921838 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921839 : term264 = False.
Proof. exact (@lem6921838 False). Qed.
Lemma lem6921840 (y : nat) (h1 : term53) (h2 : term110 y) : False.
Proof. exact (EQ_MP (@lem6921839) (@lem6921836 y h1 h2)). Qed.
Lemma lem6921875 (_92332 : nat) (h1 : term53) : (term79 _92332) = _92332.
Proof. exact (EQ_MP (@lem6921413 _92332) (@lem6921412 _92332 h1)). Qed.
Lemma lem6921876 (y' : nat) (h1 : term53) : (term79 y') = y'.
Proof. exact (@lem6921875 y' h1). Qed.
Lemma lem6921877 (y' : nat) (h1 : term53) : term265 y'.
Proof. exact (fun h0 : term222 y' => @lem6921876 y' h1). Qed.
Lemma lem6921879 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921880 (y' : nat) : (term265 y') = ((term79 y') = y').
Proof. exact (@lem6921879 ((term79 y') = y')). Qed.
Lemma lem6921881 (y' : nat) (h1 : term53) : (term79 y') = y'.
Proof. exact (EQ_MP (@lem6921880 y') (@lem6921877 y' h1)). Qed.
Lemma lem6921884 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6921886 (y' : nat) : (term222 y') = (term266 y').
Proof. exact (@lem6921884 ((term79 y') = y')). Qed.
Lemma lem6921889 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term180 y' y) : term266 y'.
Proof. exact (EQ_MP (@lem6921886 y') (@lem6921568 y' y h1 h2)). Qed.
Lemma lem6921892 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (@lem6921889 y' y h1 h3 (@lem6921881 y' h2)). Qed.
Lemma lem6921893 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : term264.
Proof. exact (fun h0 : ~ False => @lem6921892 y' y h1 h2 h3). Qed.
Lemma lem6921895 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921896 : term264 = False.
Proof. exact (@lem6921895 False). Qed.
Lemma lem6921932 (_92339 : nat) (h1 : term53) : (term74 _92339) = _92339.
Proof. exact (EQ_MP (@lem6921434 _92339) (@lem6921433 _92339 h1)). Qed.
Lemma lem6921933 (y' : nat) (h1 : term53) : (term74 y') = y'.
Proof. exact (@lem6921932 y' h1). Qed.
Lemma lem6921934 (y' : nat) (h1 : term53) : term232 y'.
Proof. exact (fun h0 : term228 y' => @lem6921933 y' h1). Qed.
Lemma lem6921936 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921937 (y' : nat) : (term232 y') = ((term74 y') = y').
Proof. exact (@lem6921936 ((term74 y') = y')). Qed.
Lemma lem6921938 (y' : nat) (h1 : term53) : (term74 y') = y'.
Proof. exact (EQ_MP (@lem6921937 y') (@lem6921934 y' h1)). Qed.
Lemma lem6921941 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6921943 (y' : nat) : (term228 y') = (term267 y').
Proof. exact (@lem6921941 ((term74 y') = y')). Qed.
Lemma lem6921946 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term180 y' y) : term267 y'.
Proof. exact (EQ_MP (@lem6921943 y') (@lem6921651 y' y h1 h2)). Qed.
Lemma lem6921949 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (@lem6921946 y' y h1 h3 (@lem6921938 y' h2)). Qed.
Lemma lem6921950 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : term264.
Proof. exact (fun h0 : ~ False => @lem6921949 y' y h1 h2 h3). Qed.
Lemma lem6921952 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6921953 : term264 = False.
Proof. exact (@lem6921952 False). Qed.
Lemma lem6921955 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921953) (@lem6921950 y' y h1 h2 h3)). Qed.
Lemma lem6921956 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921896) (@lem6921893 y' y h1 h2 h3)). Qed.
Lemma lem6921957 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : (term95 y y') = False.
Proof. exact (prop_ext (fun h4 : term95 y y' => @lem6921955 y' y h1 h2 h3) (fun h4 : False => @lem6921485 y y' h1)). Qed.
Lemma lem6921958 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921957 y' y h1 h2 h3) (@lem6921485 y y' h1)). Qed.
Lemma lem6921959 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : (term88 y y') = False.
Proof. exact (prop_ext (fun h4 : term88 y y' => @lem6921956 y' y h1 h2 h3) (fun h4 : False => @lem6921473 y y' h1)). Qed.
Lemma lem6921960 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921959 y' y h1 h2 h3) (@lem6921473 y y' h1)). Qed.
Lemma lem6921961 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : (term95 y y') = False.
Proof. exact (prop_ext (fun h4 : term95 y y' => @lem6921958 y' y h1 h2 h3) (fun h4 : False => @lem6921387 y y' h1)). Qed.
Lemma lem6921962 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921961 y' y h1 h2 h3) (@lem6921387 y y' h1)). Qed.
Lemma lem6921963 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : (term88 y y') = False.
Proof. exact (prop_ext (fun h4 : term88 y y' => @lem6921960 y' y h1 h2 h3) (fun h4 : False => @lem6921345 y y' h1)). Qed.
Lemma lem6921964 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921963 y' y h1 h2 h3) (@lem6921345 y y' h1)). Qed.
Lemma lem6921965 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : (term95 y y') = False.
Proof. exact (prop_ext (fun h4 : term95 y y' => @lem6921962 y' y h1 h2 h3) (fun h4 : False => @lem6921387 y y' h1)). Qed.
Lemma lem6921966 (y' : nat) (y : nat) (h1 : term95 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921965 y' y h1 h2 h3) (@lem6921387 y y' h1)). Qed.
Lemma lem6921967 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : (term88 y y') = False.
Proof. exact (prop_ext (fun h4 : term88 y y' => @lem6921964 y' y h1 h2 h3) (fun h4 : False => @lem6921345 y y' h1)). Qed.
Lemma lem6921968 (y' : nat) (y : nat) (h1 : term88 y y') (h2 : term53) (h3 : term180 y' y) : False.
Proof. exact (EQ_MP (@lem6921967 y' y h1 h2 h3) (@lem6921345 y y' h1)). Qed.
Lemma lem6921969 (y' : nat) (y : nat) (h1 : term53) (h2 : term180 y' y) : False.
Proof. exact (or_elim (@lem6921249 y' y h2) (fun h0 : term88 y y' => @lem6921968 y' y h0 h1 h2) (fun h0 : term95 y y' => @lem6921966 y' y h0 h1 h2)). Qed.
Lemma lem6921970 (y' : nat) (y : nat) (h1 : term53) (h2 : term211 y' y) : False.
Proof. exact (or_elim (@lem6921235 y' y h2) (fun h0 : term110 y => @lem6921840 y h1 h0) (fun h0 : term180 y' y => @lem6921969 y' y h1 h0)). Qed.
Lemma lem6921971 (y' : nat) (y : nat) (h1 : term53) (h2 : term211 y' y) : (term211 y' y) = False.
Proof. exact (prop_ext (fun h3 : term211 y' y => @lem6921970 y' y h1 h2) (fun h3 : False => @lem6921235 y' y h2)). Qed.
Lemma lem6921972 (y' : nat) (y : nat) (h1 : term53) (h2 : term211 y' y) : False.
Proof. exact (EQ_MP (@lem6921971 y' y h1 h2) (@lem6921235 y' y h2)). Qed.
Lemma lem6921973 (y' : nat) (y : nat) (h1 : term53) (h2 : term211 y' y) : term53 = False.
Proof. exact (prop_ext (fun h3 : term53 => @lem6921972 y' y h1 h2) (fun h3 : False => @lem6921157 h1)). Qed.
Lemma lem6921974 (y' : nat) (y : nat) (h1 : term53) (h2 : term211 y' y) : False.
Proof. exact (EQ_MP (@lem6921973 y' y h1 h2) (@lem6921157 h1)). Qed.
Lemma lem6921975 (y : nat) (h1 : term214 y) (h2 : term53) : False.
Proof. exact (ex_elim (@lem6921072 y h1) (fun y' : nat => fun h0 : term213 y y' => @lem6921974 y' y h2 h0)). Qed.
Lemma lem6921976 (h1 : term58) (h2 : term53) : False.
Proof. exact (ex_elim (@lem6921011 h1) (fun y : nat => fun h0 : term215 y => @lem6921975 y h0 h2)). Qed.
Lemma lem6921977 (h1 : term58) (h2 : term53) : term53 = False.
Proof. exact (prop_ext (fun h3 : term53 => @lem6921976 h1 h2) (fun h3 : False => @lem6921071 h2)). Qed.
Lemma lem6921978 (h1 : term58) (h2 : term53) : False.
Proof. exact (EQ_MP (@lem6921977 h1 h2) (@lem6921071 h2)). Qed.
Lemma lem6921979 (h1 : term58) : term51.
Proof. exact (fun h0 : term53 => @lem6921978 h1 h0). Qed.
Lemma lem6921980 : term51 = term52.
Proof. exact (@lem69 term53). Qed.
Lemma lem6921981 (h1 : term58) : term52.
Proof. exact (EQ_MP (@lem6921980) (@lem6921979 h1)). Qed.
Lemma lem6921982 : term60.
Proof. exact (fun h0 : term58 => @lem6921981 h0). Qed.
Lemma lem6921983 : term8.
Proof. exact (EQ_MP (@lem6920693) (@lem6921982)). Qed.
Lemma lem6921985 : term8.
Proof. exact (@lem6920455 (@lem6921983)). Qed.
Lemma lem6921986 (h1 : term7) : term51.
Proof. exact (@lem6921985 (@lem6920440 h1)). Qed.
Lemma lem6921987 (h1 : term7) : False.
Proof. exact (@lem6921986 h1 (@lem77629)). Qed.
Lemma lem6921988 (h1 : term7) : term7 = False.
Proof. exact (prop_ext (fun h2 : term7 => @lem6921987 h1) (fun h2 : False => @lem6920440 h1)). Qed.
Lemma lem6921989 (h1 : term7) : False.
Proof. exact (EQ_MP (@lem6921988 h1) (@lem6920440 h1)). Qed.
Lemma lem6921990 : term6.
Proof. exact (fun h0 : term7 => @lem6921989 h0). Qed.
Lemma lem6921991 : term5.
Proof. exact (EQ_MP (@lem6920439) (@lem6921990)). Qed.
Lemma lem6921992 : term268 = (NUMERAL 0).
Proof. exact (@lem6920435 (@lem6921991)). Qed.
