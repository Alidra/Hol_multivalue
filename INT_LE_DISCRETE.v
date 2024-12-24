Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_DISCRETE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2330501 : term0 = term1.
Proof. exact (@lem2318604 term1). Qed.
Lemma lem2330529 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (@lem17646 (int_le x y) (term4 x y)). Qed.
Lemma lem2330530 (P : int -> Prop) : (term5 P) = (term6 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2330531 (x : int) : (term7 x) = (term8 x).
Proof. exact (@lem2330530 (term9 x)). Qed.
Lemma lem2330532 (x : int) (y : int) : (term10 x y) = ((int_le x y) = (term4 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem2330533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2330534 (x : int) (y : int) : (term11 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem2330533) (@lem2330532 x y)). Qed.
Lemma lem2330535 (x : int) (y : int) : (term11 x y) = (term3 x y).
Proof. exact (TRANS (@lem2330534 x y) (@lem2330529 x y)). Qed.
Lemma lem2330536 (x : int) : (term12 x) = (term13 x).
Proof. exact (fun_ext (fun y : int => @lem2330535 x y)). Qed.
Lemma lem2330537 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330538 (x : int) : (term8 x) = (term14 x).
Proof. exact (MK_COMB (@lem2330537) (@lem2330536 x)). Qed.
Lemma lem2330539 (x : int) : (term7 x) = (term14 x).
Proof. exact (TRANS (@lem2330531 x) (@lem2330538 x)). Qed.
Lemma lem2330540 (P : int -> Prop) : (term5 P) = (term6 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2330541 : term15 = term16.
Proof. exact (@lem2330540 term17). Qed.
Lemma lem2330542 (x : int) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2330543 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2330544 (x : int) : (term20 x) = (term7 x).
Proof. exact (MK_COMB (@lem2330543) (@lem2330542 x)). Qed.
Lemma lem2330545 (x : int) : (term20 x) = (term14 x).
Proof. exact (TRANS (@lem2330544 x) (@lem2330539 x)). Qed.
Lemma lem2330546 : term21 = term22.
Proof. exact (fun_ext (fun x : int => @lem2330545 x)). Qed.
Lemma lem2330547 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330548 : term16 = term23.
Proof. exact (MK_COMB (@lem2330547) (@lem2330546)). Qed.
Lemma lem2330550 : term15 = term23.
Proof. exact (TRANS (@lem2330541) (@lem2330548)). Qed.
Lemma lem2330567 (x : int) (y : int) : (term3 x y) = (term3 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2330568 (x : int) : (term13 x) = (term13 x).
Proof. exact (fun_ext (fun y : int => @lem2330567 x y)). Qed.
Lemma lem2330569 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330570 (x : int) : (term14 x) = (term14 x).
Proof. exact (MK_COMB (@lem2330569) (@lem2330568 x)). Qed.
Lemma lem2330571 : term22 = term22.
Proof. exact (fun_ext (fun x : int => @lem2330570 x)). Qed.
Lemma lem2330572 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330573 : term23 = term23.
Proof. exact (MK_COMB (@lem2330572) (@lem2330571)). Qed.
Lemma lem2330574 : term15 = term23.
Proof. exact (TRANS (@lem2330550) (@lem2330573)). Qed.
Lemma lem2330578 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2330580 (y : int) (x : int) : (term25 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2330581 (y : int) (x : int) : (term26 x y) = (term27 y x).
Proof. exact (@lem2330580 (term28 y) x). Qed.
Lemma lem2330583 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2330584 (y : int) (x : int) : (term27 y x) = (term29 y x).
Proof. exact (@lem2330583 (term28 y) x). Qed.
Lemma lem2330586 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2330587 (y : int) : (term32 y) = (term33 y).
Proof. exact (@lem2330586 y term34). Qed.
Lemma lem2330589 (n : nat) : (term35 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2330590 : term36 = term37.
Proof. exact (@lem2330589 term38). Qed.
Lemma lem2330591 (y : int) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem2330592 (y : int) : (term33 y) = (term40 y).
Proof. exact (MK_COMB (@lem2330591 y) (@lem2330590)). Qed.
Lemma lem2330593 (y : int) : (term32 y) = (term40 y).
Proof. exact (TRANS (@lem2330587 y) (@lem2330592 y)). Qed.
Lemma lem2330594 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2330595 (y : int) : (term41 y) = (term42 y).
Proof. exact (MK_COMB (@lem2330594) (@lem2330593 y)). Qed.
Lemma lem2330596 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2330597 (y : int) (x : int) : (term29 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem2330595 y) (@lem2330596 x)). Qed.
Lemma lem2330598 (y : int) (x : int) : (term27 y x) = (term43 y x).
Proof. exact (TRANS (@lem2330584 y x) (@lem2330597 y x)). Qed.
Lemma lem2330599 (y : int) (x : int) : (term26 x y) = (term43 y x).
Proof. exact (TRANS (@lem2330581 y x) (@lem2330598 y x)). Qed.
Lemma lem2330600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2330601 (x : int) (y : int) : (term44 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem2330600) (@lem2330578 x y)). Qed.
Lemma lem2330602 (y : int) (x : int) : (term46 x y) = (term47 y x).
Proof. exact (MK_COMB (@lem2330601 x y) (@lem2330599 y x)). Qed.
Lemma lem2330604 (y : int) (x : int) : (term48 x y) = (term27 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2330606 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2330607 (y : int) (x : int) : (term27 y x) = (term29 y x).
Proof. exact (@lem2330606 (term28 y) x). Qed.
Lemma lem2330609 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2330610 (y : int) : (term32 y) = (term33 y).
Proof. exact (@lem2330609 y term34). Qed.
Lemma lem2330612 (n : nat) : (term35 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2330613 : term36 = term37.
Proof. exact (@lem2330612 term38). Qed.
Lemma lem2330614 (y : int) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem2330615 (y : int) : (term33 y) = (term40 y).
Proof. exact (MK_COMB (@lem2330614 y) (@lem2330613)). Qed.
Lemma lem2330616 (y : int) : (term32 y) = (term40 y).
Proof. exact (TRANS (@lem2330610 y) (@lem2330615 y)). Qed.
Lemma lem2330617 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2330618 (y : int) : (term41 y) = (term42 y).
Proof. exact (MK_COMB (@lem2330617) (@lem2330616 y)). Qed.
Lemma lem2330619 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2330620 (y : int) (x : int) : (term29 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem2330618 y) (@lem2330619 x)). Qed.
Lemma lem2330621 (y : int) (x : int) : (term27 y x) = (term43 y x).
Proof. exact (TRANS (@lem2330607 y x) (@lem2330620 y x)). Qed.
Lemma lem2330622 (y : int) (x : int) : (term48 x y) = (term43 y x).
Proof. exact (TRANS (@lem2330604 y x) (@lem2330621 y x)). Qed.
Lemma lem2330624 (x : int) (y : int) : (int_lt x y) = (term27 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2330625 (x : int) (y : int) : (term4 x y) = (term49 x y).
Proof. exact (@lem2330624 x (term28 y)). Qed.
Lemma lem2330627 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2330628 (x : int) (y : int) : (term49 x y) = (term50 x y).
Proof. exact (@lem2330627 (term28 x) (term28 y)). Qed.
Lemma lem2330630 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2330631 (x : int) : (term32 x) = (term33 x).
Proof. exact (@lem2330630 x term34). Qed.
Lemma lem2330633 (n : nat) : (term35 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2330634 : term36 = term37.
Proof. exact (@lem2330633 term38). Qed.
Lemma lem2330635 (x : int) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem2330636 (x : int) : (term33 x) = (term40 x).
Proof. exact (MK_COMB (@lem2330635 x) (@lem2330634)). Qed.
Lemma lem2330637 (x : int) : (term32 x) = (term40 x).
Proof. exact (TRANS (@lem2330631 x) (@lem2330636 x)). Qed.
Lemma lem2330638 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2330639 (x : int) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem2330638) (@lem2330637 x)). Qed.
Lemma lem2330641 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2330642 (y : int) : (term32 y) = (term33 y).
Proof. exact (@lem2330641 y term34). Qed.
Lemma lem2330644 (n : nat) : (term35 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2330645 : term36 = term37.
Proof. exact (@lem2330644 term38). Qed.
Lemma lem2330646 (y : int) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem2330647 (y : int) : (term33 y) = (term40 y).
Proof. exact (MK_COMB (@lem2330646 y) (@lem2330645)). Qed.
Lemma lem2330648 (y : int) : (term32 y) = (term40 y).
Proof. exact (TRANS (@lem2330642 y) (@lem2330647 y)). Qed.
Lemma lem2330649 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem2330639 x) (@lem2330648 y)). Qed.
Lemma lem2330650 (x : int) (y : int) : (term49 x y) = (term51 x y).
Proof. exact (TRANS (@lem2330628 x y) (@lem2330649 x y)). Qed.
Lemma lem2330651 (x : int) (y : int) : (term4 x y) = (term51 x y).
Proof. exact (TRANS (@lem2330625 x y) (@lem2330650 x y)). Qed.
Lemma lem2330652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2330653 (y : int) (x : int) : (term52 x y) = (term53 y x).
Proof. exact (MK_COMB (@lem2330652) (@lem2330622 y x)). Qed.
Lemma lem2330654 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem2330653 y x) (@lem2330651 x y)). Qed.
Lemma lem2330655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2330656 (y : int) (x : int) : (term56 x y) = (term57 y x).
Proof. exact (MK_COMB (@lem2330655) (@lem2330602 y x)). Qed.
Lemma lem2330657 (x : int) (y : int) : (term3 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem2330656 y x) (@lem2330654 x y)). Qed.
Lemma lem2330658 (x : int) : (term13 x) = (term59 x).
Proof. exact (fun_ext (fun y : int => @lem2330657 x y)). Qed.
Lemma lem2330659 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330660 (x : int) : (term14 x) = (term60 x).
Proof. exact (MK_COMB (@lem2330659) (@lem2330658 x)). Qed.
Lemma lem2330661 : term22 = term61.
Proof. exact (fun_ext (fun x : int => @lem2330660 x)). Qed.
Lemma lem2330662 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330663 : term23 = term62.
Proof. exact (MK_COMB (@lem2330662) (@lem2330661)). Qed.
Lemma lem2330664 : term15 = term62.
Proof. exact (TRANS (@lem2330574) (@lem2330663)). Qed.
Lemma lem2330668 (t : Prop) : (term63 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2330669 : term64 = term62.
Proof. exact (@lem2330668 term62). Qed.
Lemma lem2330675 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2330676 (P : int -> Prop) (Q : int -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem2330675 int P Q). Qed.
Lemma lem2330677 (x : int) : (term69 x) = (term70 x).
Proof. exact (@lem2330676 (term71 x) (term72 x)). Qed.
Lemma lem2330678 (y : int) (x : int) : (term73 x y) = (term47 y x).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem2330679 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2330680 (y : int) (x : int) : (term74 x y) = (term57 y x).
Proof. exact (MK_COMB (@lem2330679) (@lem2330678 y x)). Qed.
Lemma lem2330681 (x : int) (y : int) : (term75 x y) = (term55 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem2330682 (x : int) (y : int) : (term76 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem2330680 y x) (@lem2330681 x y)). Qed.
Lemma lem2330683 (x : int) : (term77 x) = (term59 x).
Proof. exact (fun_ext (fun y : int => @lem2330682 x y)). Qed.
Lemma lem2330684 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330685 (x : int) : (term69 x) = (term60 x).
Proof. exact (MK_COMB (@lem2330684) (@lem2330683 x)). Qed.
Lemma lem2330686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2330687 (x : int) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem2330686) (@lem2330685 x)). Qed.
Lemma lem2330688 (y : int) (x : int) : (term73 x y) = (term47 y x).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem2330689 (x : int) : (term80 x) = (term71 x).
Proof. exact (fun_ext (fun y : int => @lem2330688 y x)). Qed.
Lemma lem2330690 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330691 (x : int) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem2330690) (@lem2330689 x)). Qed.
Lemma lem2330692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2330693 (x : int) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem2330692) (@lem2330691 x)). Qed.
Lemma lem2330694 (x : int) (y : int) : (term75 x y) = (term55 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem2330695 (x : int) : (term85 x) = (term72 x).
Proof. exact (fun_ext (fun y : int => @lem2330694 x y)). Qed.
Lemma lem2330696 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330697 (x : int) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem2330696) (@lem2330695 x)). Qed.
Lemma lem2330698 (x : int) : (term70 x) = (term88 x).
Proof. exact (MK_COMB (@lem2330693 x) (@lem2330697 x)). Qed.
Lemma lem2330699 (x : int) : ((term69 x) = (term70 x)) = ((term60 x) = (term88 x)).
Proof. exact (MK_COMB (@lem2330687 x) (@lem2330698 x)). Qed.
Lemma lem2330700 (x : int) : (term60 x) = (term88 x).
Proof. exact (EQ_MP (@lem2330699 x) (@lem2330677 x)). Qed.
Lemma lem2330803 : term61 = term89.
Proof. exact (fun_ext (fun x : int => @lem2330700 x)). Qed.
Lemma lem2330804 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330805 : term62 = term90.
Proof. exact (MK_COMB (@lem2330804) (@lem2330803)). Qed.
Lemma lem2330807 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2330808 (P : int -> Prop) (Q : int -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem2330807 int P Q). Qed.
Lemma lem2330809 : term91 = term92.
Proof. exact (@lem2330808 term93 term94). Qed.
Lemma lem2330810 (x : int) : (term95 x) = (term82 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem2330811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2330812 (x : int) : (term96 x) = (term84 x).
Proof. exact (MK_COMB (@lem2330811) (@lem2330810 x)). Qed.
Lemma lem2330813 (x : int) : (term97 x) = (term87 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem2330814 (x : int) : (term98 x) = (term88 x).
Proof. exact (MK_COMB (@lem2330812 x) (@lem2330813 x)). Qed.
Lemma lem2330815 : term99 = term89.
Proof. exact (fun_ext (fun x : int => @lem2330814 x)). Qed.
Lemma lem2330816 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330817 : term91 = term90.
Proof. exact (MK_COMB (@lem2330816) (@lem2330815)). Qed.
Lemma lem2330818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2330819 : term100 = term101.
Proof. exact (MK_COMB (@lem2330818) (@lem2330817)). Qed.
Lemma lem2330820 (x : int) : (term95 x) = (term82 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem2330821 : term102 = term93.
Proof. exact (fun_ext (fun x : int => @lem2330820 x)). Qed.
Lemma lem2330822 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330823 : term103 = term104.
Proof. exact (MK_COMB (@lem2330822) (@lem2330821)). Qed.
Lemma lem2330824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2330825 : term105 = term106.
Proof. exact (MK_COMB (@lem2330824) (@lem2330823)). Qed.
Lemma lem2330826 (x : int) : (term97 x) = (term87 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem2330827 : term107 = term94.
Proof. exact (fun_ext (fun x : int => @lem2330826 x)). Qed.
Lemma lem2330828 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330829 : term108 = term109.
Proof. exact (MK_COMB (@lem2330828) (@lem2330827)). Qed.
Lemma lem2330830 : term92 = term110.
Proof. exact (MK_COMB (@lem2330825) (@lem2330829)). Qed.
Lemma lem2330831 : (term91 = term92) = (term90 = term110).
Proof. exact (MK_COMB (@lem2330819) (@lem2330830)). Qed.
Lemma lem2330832 : term90 = term110.
Proof. exact (EQ_MP (@lem2330831) (@lem2330809)). Qed.
Lemma lem2330943 : term62 = term110.
Proof. exact (TRANS (@lem2330805) (@lem2330832)). Qed.
Lemma lem2330945 : term64 = term110.
Proof. exact (TRANS (@lem2330669) (@lem2330943)). Qed.
Lemma lem2330950 (y : int) (x : int) : (term47 y x) = (term47 y x).
Proof. exact (eq_refl (term47 y x)). Qed.
Lemma lem2330951 (x : int) : (term71 x) = (term71 x).
Proof. exact (fun_ext (fun y : int => @lem2330950 y x)). Qed.
Lemma lem2330952 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330953 (x : int) : (term82 x) = (term82 x).
Proof. exact (MK_COMB (@lem2330952) (@lem2330951 x)). Qed.
Lemma lem2330954 : term93 = term93.
Proof. exact (fun_ext (fun x : int => @lem2330953 x)). Qed.
Lemma lem2330955 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330956 : term104 = term104.
Proof. exact (MK_COMB (@lem2330955) (@lem2330954)). Qed.
Lemma lem2330961 (x : int) (y : int) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem2330962 (x : int) : (term72 x) = (term72 x).
Proof. exact (fun_ext (fun y : int => @lem2330961 x y)). Qed.
Lemma lem2330963 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330964 (x : int) : (term87 x) = (term87 x).
Proof. exact (MK_COMB (@lem2330963) (@lem2330962 x)). Qed.
Lemma lem2330965 : term94 = term94.
Proof. exact (fun_ext (fun x : int => @lem2330964 x)). Qed.
Lemma lem2330966 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330967 : term109 = term109.
Proof. exact (MK_COMB (@lem2330966) (@lem2330965)). Qed.
Lemma lem2330968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2330969 : term106 = term106.
Proof. exact (MK_COMB (@lem2330968) (@lem2330956)). Qed.
Lemma lem2330970 : term110 = term110.
Proof. exact (MK_COMB (@lem2330969) (@lem2330967)). Qed.
Lemma lem2330971 : term64 = term110.
Proof. exact (TRANS (@lem2330945) (@lem2330970)). Qed.
Lemma lem2330976 (y : int) (x : int) : (term47 y x) = (term47 y x).
Proof. exact (eq_refl (term47 y x)). Qed.
Lemma lem2330977 (x : int) : (term71 x) = (term71 x).
Proof. exact (fun_ext (fun y : int => @lem2330976 y x)). Qed.
Lemma lem2330978 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330979 (x : int) : (term82 x) = (term82 x).
Proof. exact (MK_COMB (@lem2330978) (@lem2330977 x)). Qed.
Lemma lem2330980 : term93 = term93.
Proof. exact (fun_ext (fun x : int => @lem2330979 x)). Qed.
Lemma lem2330981 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330982 : term104 = term104.
Proof. exact (MK_COMB (@lem2330981) (@lem2330980)). Qed.
Lemma lem2330987 (x : int) (y : int) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem2330988 (x : int) : (term72 x) = (term72 x).
Proof. exact (fun_ext (fun y : int => @lem2330987 x y)). Qed.
Lemma lem2330989 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330990 (x : int) : (term87 x) = (term87 x).
Proof. exact (MK_COMB (@lem2330989) (@lem2330988 x)). Qed.
Lemma lem2330991 : term94 = term94.
Proof. exact (fun_ext (fun x : int => @lem2330990 x)). Qed.
Lemma lem2330992 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2330993 : term109 = term109.
Proof. exact (MK_COMB (@lem2330992) (@lem2330991)). Qed.
Lemma lem2330994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2330995 : term106 = term106.
Proof. exact (MK_COMB (@lem2330994) (@lem2330982)). Qed.
Lemma lem2330996 : term110 = term110.
Proof. exact (MK_COMB (@lem2330995) (@lem2330993)). Qed.
Lemma lem2330997 : term64 = term110.
Proof. exact (TRANS (@lem2330971) (@lem2330996)). Qed.
Lemma lem2330998 (y : int) (x : int) : (term24 x y) = (term111 y x).
Proof. exact (@lem1988287 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2331004 (y : int) (x : int) : (term112 y x) = (term113 y x).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2331009 (x : int) (y : int) : (term113 y x) = (term114 x y).
Proof. exact (@lem1982761 (term115 x) (real_of_int y)). Qed.
Lemma lem2331011 (x : int) (y : int) : (term112 y x) = (term114 x y).
Proof. exact (TRANS (@lem2331004 y x) (@lem2331009 x y)). Qed.
Lemma lem2331012 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2331013 (x : int) (y : int) : (term116 y x) = (term117 x y).
Proof. exact (MK_COMB (@lem2331012) (@lem2331011 x y)). Qed.
Lemma lem2331014 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2331015 (x : int) (y : int) : (term111 y x) = (term119 x y).
Proof. exact (MK_COMB (@lem2331013 x y) (@lem2331014)). Qed.
Lemma lem2331016 (x : int) (y : int) : (term24 x y) = (term119 x y).
Proof. exact (TRANS (@lem2330998 y x) (@lem2331015 x y)). Qed.
Lemma lem2331017 (x : int) (y : int) : (term43 y x) = (term120 x y).
Proof. exact (@lem1988287 (real_of_int x) (term40 y)). Qed.
Lemma lem2331029 (x : int) (y : int) : (term121 x y) = (term122 x y).
Proof. exact (@lem1982792 (real_of_int x) (term40 y)). Qed.
Lemma lem2331030 (y : int) : (term123 y) = (term124 y).
Proof. exact (@lem1982781 (real_of_int y) term125 term37). Qed.
Lemma lem2331032 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331033 : term37 = term127.
Proof. exact (@lem2331032 term38). Qed.
Lemma lem2331035 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2331036 : term125 = term130.
Proof. exact (@lem2331035 term38). Qed.
Lemma lem2331037 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331038 : term131 = term132.
Proof. exact (MK_COMB (@lem2331037) (@lem2331036)). Qed.
Lemma lem2331039 : term133 = term134.
Proof. exact (MK_COMB (@lem2331038) (@lem2331033)). Qed.
Lemma lem2331040 : term134 = term135.
Proof. exact (@lem1981613 term125 term37 term37 term37). Qed.
Lemma lem2331042 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331043 : term138 = term139.
Proof. exact (@lem2331042 term38 term38). Qed.
Lemma lem2331044 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331045 : term141 = term38.
Proof. exact (EQ_MP (@lem2331044) (@lem940073)). Qed.
Lemma lem2331046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331047 : term139 = term37.
Proof. exact (MK_COMB (@lem2331046) (@lem2331045)). Qed.
Lemma lem2331048 : term138 = term37.
Proof. exact (TRANS (@lem2331043) (@lem2331047)). Qed.
Lemma lem2331050 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2331051 : term133 = term144.
Proof. exact (@lem2331050 term38 term38). Qed.
Lemma lem2331052 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331053 : term141 = term38.
Proof. exact (EQ_MP (@lem2331052) (@lem940073)). Qed.
Lemma lem2331054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331055 : term139 = term37.
Proof. exact (MK_COMB (@lem2331054) (@lem2331053)). Qed.
Lemma lem2331056 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2331057 : term144 = term125.
Proof. exact (MK_COMB (@lem2331056) (@lem2331055)). Qed.
Lemma lem2331058 : term133 = term125.
Proof. exact (TRANS (@lem2331051) (@lem2331057)). Qed.
Lemma lem2331059 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2331060 : term145 = term146.
Proof. exact (MK_COMB (@lem2331059) (@lem2331058)). Qed.
Lemma lem2331061 : term135 = term130.
Proof. exact (MK_COMB (@lem2331060) (@lem2331048)). Qed.
Lemma lem2331062 : term134 = term130.
Proof. exact (TRANS (@lem2331040) (@lem2331061)). Qed.
Lemma lem2331063 : term133 = term130.
Proof. exact (TRANS (@lem2331039) (@lem2331062)). Qed.
Lemma lem2331065 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2331066 : term130 = term125.
Proof. exact (@lem2331065 term125). Qed.
Lemma lem2331067 : term133 = term125.
Proof. exact (TRANS (@lem2331063) (@lem2331066)). Qed.
Lemma lem2331070 (y : int) : (term148 y) = (term148 y).
Proof. exact (eq_refl (term148 y)). Qed.
Lemma lem2331071 (y : int) : (term124 y) = (term149 y).
Proof. exact (MK_COMB (@lem2331070 y) (@lem2331067)). Qed.
Lemma lem2331072 (y : int) : (term123 y) = (term149 y).
Proof. exact (TRANS (@lem2331030 y) (@lem2331071 y)). Qed.
Lemma lem2331073 (x : int) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem2331076 (x : int) (y : int) : (term122 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem2331073 x) (@lem2331072 y)). Qed.
Lemma lem2331078 (x : int) (y : int) : (term121 x y) = (term150 x y).
Proof. exact (TRANS (@lem2331029 x y) (@lem2331076 x y)). Qed.
Lemma lem2331079 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2331080 (x : int) (y : int) : (term151 x y) = (term152 x y).
Proof. exact (MK_COMB (@lem2331079) (@lem2331078 x y)). Qed.
Lemma lem2331081 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2331082 (x : int) (y : int) : (term120 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem2331080 x y) (@lem2331081)). Qed.
Lemma lem2331083 (x : int) (y : int) : (term43 y x) = (term153 x y).
Proof. exact (TRANS (@lem2331017 x y) (@lem2331082 x y)). Qed.
Lemma lem2331084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2331085 (x : int) (y : int) : (term45 x y) = (term154 x y).
Proof. exact (MK_COMB (@lem2331084) (@lem2331016 x y)). Qed.
Lemma lem2331086 (x : int) (y : int) : (term47 y x) = (term155 x y).
Proof. exact (MK_COMB (@lem2331085 x y) (@lem2331083 x y)). Qed.
Lemma lem2331087 (x : int) : (term71 x) = (term156 x).
Proof. exact (fun_ext (fun y : int => @lem2331086 x y)). Qed.
Lemma lem2331088 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331089 (x : int) : (term82 x) = (term157 x).
Proof. exact (MK_COMB (@lem2331088) (@lem2331087 x)). Qed.
Lemma lem2331090 : term93 = term158.
Proof. exact (fun_ext (fun x : int => @lem2331089 x)). Qed.
Lemma lem2331091 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331092 : term104 = term159.
Proof. exact (MK_COMB (@lem2331091) (@lem2331090)). Qed.
Lemma lem2331093 (x : int) (y : int) : (term43 y x) = (term120 x y).
Proof. exact (@lem1988287 (real_of_int x) (term40 y)). Qed.
Lemma lem2331105 (x : int) (y : int) : (term121 x y) = (term122 x y).
Proof. exact (@lem1982792 (real_of_int x) (term40 y)). Qed.
Lemma lem2331106 (y : int) : (term123 y) = (term124 y).
Proof. exact (@lem1982781 (real_of_int y) term125 term37). Qed.
Lemma lem2331108 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331109 : term37 = term127.
Proof. exact (@lem2331108 term38). Qed.
Lemma lem2331111 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2331112 : term125 = term130.
Proof. exact (@lem2331111 term38). Qed.
Lemma lem2331113 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331114 : term131 = term132.
Proof. exact (MK_COMB (@lem2331113) (@lem2331112)). Qed.
Lemma lem2331115 : term133 = term134.
Proof. exact (MK_COMB (@lem2331114) (@lem2331109)). Qed.
Lemma lem2331116 : term134 = term135.
Proof. exact (@lem1981613 term125 term37 term37 term37). Qed.
Lemma lem2331118 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331119 : term138 = term139.
Proof. exact (@lem2331118 term38 term38). Qed.
Lemma lem2331120 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331121 : term141 = term38.
Proof. exact (EQ_MP (@lem2331120) (@lem940073)). Qed.
Lemma lem2331122 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331123 : term139 = term37.
Proof. exact (MK_COMB (@lem2331122) (@lem2331121)). Qed.
Lemma lem2331124 : term138 = term37.
Proof. exact (TRANS (@lem2331119) (@lem2331123)). Qed.
Lemma lem2331126 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2331127 : term133 = term144.
Proof. exact (@lem2331126 term38 term38). Qed.
Lemma lem2331128 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331129 : term141 = term38.
Proof. exact (EQ_MP (@lem2331128) (@lem940073)). Qed.
Lemma lem2331130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331131 : term139 = term37.
Proof. exact (MK_COMB (@lem2331130) (@lem2331129)). Qed.
Lemma lem2331132 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2331133 : term144 = term125.
Proof. exact (MK_COMB (@lem2331132) (@lem2331131)). Qed.
Lemma lem2331134 : term133 = term125.
Proof. exact (TRANS (@lem2331127) (@lem2331133)). Qed.
Lemma lem2331135 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2331136 : term145 = term146.
Proof. exact (MK_COMB (@lem2331135) (@lem2331134)). Qed.
Lemma lem2331137 : term135 = term130.
Proof. exact (MK_COMB (@lem2331136) (@lem2331124)). Qed.
Lemma lem2331138 : term134 = term130.
Proof. exact (TRANS (@lem2331116) (@lem2331137)). Qed.
Lemma lem2331139 : term133 = term130.
Proof. exact (TRANS (@lem2331115) (@lem2331138)). Qed.
Lemma lem2331141 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2331142 : term130 = term125.
Proof. exact (@lem2331141 term125). Qed.
Lemma lem2331143 : term133 = term125.
Proof. exact (TRANS (@lem2331139) (@lem2331142)). Qed.
Lemma lem2331146 (y : int) : (term148 y) = (term148 y).
Proof. exact (eq_refl (term148 y)). Qed.
Lemma lem2331147 (y : int) : (term124 y) = (term149 y).
Proof. exact (MK_COMB (@lem2331146 y) (@lem2331143)). Qed.
Lemma lem2331148 (y : int) : (term123 y) = (term149 y).
Proof. exact (TRANS (@lem2331106 y) (@lem2331147 y)). Qed.
Lemma lem2331149 (x : int) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem2331152 (x : int) (y : int) : (term122 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem2331149 x) (@lem2331148 y)). Qed.
Lemma lem2331154 (x : int) (y : int) : (term121 x y) = (term150 x y).
Proof. exact (TRANS (@lem2331105 x y) (@lem2331152 x y)). Qed.
Lemma lem2331155 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2331156 (x : int) (y : int) : (term151 x y) = (term152 x y).
Proof. exact (MK_COMB (@lem2331155) (@lem2331154 x y)). Qed.
Lemma lem2331157 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2331158 (x : int) (y : int) : (term120 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem2331156 x y) (@lem2331157)). Qed.
Lemma lem2331159 (x : int) (y : int) : (term43 y x) = (term153 x y).
Proof. exact (TRANS (@lem2331093 x y) (@lem2331158 x y)). Qed.
Lemma lem2331160 (y : int) (x : int) : (term51 x y) = (term160 y x).
Proof. exact (@lem1988287 (term40 y) (term40 x)). Qed.
Lemma lem2331178 (y : int) (x : int) : (term161 y x) = (term162 y x).
Proof. exact (@lem1982792 (term40 y) (term40 x)). Qed.
Lemma lem2331179 (x : int) : (term123 x) = (term124 x).
Proof. exact (@lem1982781 (real_of_int x) term125 term37). Qed.
Lemma lem2331181 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331182 : term37 = term127.
Proof. exact (@lem2331181 term38). Qed.
Lemma lem2331184 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2331185 : term125 = term130.
Proof. exact (@lem2331184 term38). Qed.
Lemma lem2331186 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331187 : term131 = term132.
Proof. exact (MK_COMB (@lem2331186) (@lem2331185)). Qed.
Lemma lem2331188 : term133 = term134.
Proof. exact (MK_COMB (@lem2331187) (@lem2331182)). Qed.
Lemma lem2331189 : term134 = term135.
Proof. exact (@lem1981613 term125 term37 term37 term37). Qed.
Lemma lem2331191 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331192 : term138 = term139.
Proof. exact (@lem2331191 term38 term38). Qed.
Lemma lem2331193 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331194 : term141 = term38.
Proof. exact (EQ_MP (@lem2331193) (@lem940073)). Qed.
Lemma lem2331195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331196 : term139 = term37.
Proof. exact (MK_COMB (@lem2331195) (@lem2331194)). Qed.
Lemma lem2331197 : term138 = term37.
Proof. exact (TRANS (@lem2331192) (@lem2331196)). Qed.
Lemma lem2331199 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2331200 : term133 = term144.
Proof. exact (@lem2331199 term38 term38). Qed.
Lemma lem2331201 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331202 : term141 = term38.
Proof. exact (EQ_MP (@lem2331201) (@lem940073)). Qed.
Lemma lem2331203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331204 : term139 = term37.
Proof. exact (MK_COMB (@lem2331203) (@lem2331202)). Qed.
Lemma lem2331205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2331206 : term144 = term125.
Proof. exact (MK_COMB (@lem2331205) (@lem2331204)). Qed.
Lemma lem2331207 : term133 = term125.
Proof. exact (TRANS (@lem2331200) (@lem2331206)). Qed.
Lemma lem2331208 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2331209 : term145 = term146.
Proof. exact (MK_COMB (@lem2331208) (@lem2331207)). Qed.
Lemma lem2331210 : term135 = term130.
Proof. exact (MK_COMB (@lem2331209) (@lem2331197)). Qed.
Lemma lem2331211 : term134 = term130.
Proof. exact (TRANS (@lem2331189) (@lem2331210)). Qed.
Lemma lem2331212 : term133 = term130.
Proof. exact (TRANS (@lem2331188) (@lem2331211)). Qed.
Lemma lem2331214 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2331215 : term130 = term125.
Proof. exact (@lem2331214 term125). Qed.
Lemma lem2331216 : term133 = term125.
Proof. exact (TRANS (@lem2331212) (@lem2331215)). Qed.
Lemma lem2331219 (x : int) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem2331220 (x : int) : (term124 x) = (term149 x).
Proof. exact (MK_COMB (@lem2331219 x) (@lem2331216)). Qed.
Lemma lem2331221 (x : int) : (term123 x) = (term149 x).
Proof. exact (TRANS (@lem2331179 x) (@lem2331220 x)). Qed.
Lemma lem2331222 (y : int) : (term163 y) = (term163 y).
Proof. exact (eq_refl (term163 y)). Qed.
Lemma lem2331223 (y : int) (x : int) : (term162 y x) = (term164 y x).
Proof. exact (MK_COMB (@lem2331222 y) (@lem2331221 x)). Qed.
Lemma lem2331224 (x : int) (y : int) : (term164 y x) = (term165 x y).
Proof. exact (@lem1982757 (term115 x) (term40 y) term125). Qed.
Lemma lem2331225 (y : int) : (term166 y) = (term167 y).
Proof. exact (@lem1982755 (real_of_int y) term37 term125). Qed.
Lemma lem2331227 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2331228 : term125 = term130.
Proof. exact (@lem2331227 term38). Qed.
Lemma lem2331230 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331231 : term37 = term127.
Proof. exact (@lem2331230 term38). Qed.
Lemma lem2331232 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331233 : term168 = term169.
Proof. exact (MK_COMB (@lem2331232) (@lem2331231)). Qed.
Lemma lem2331234 : term170 = term171.
Proof. exact (MK_COMB (@lem2331233) (@lem2331228)). Qed.
Lemma lem2331235 : term172.
Proof. exact (@lem1981473 term37 term37 term125 term37 term118 term37). Qed.
Lemma lem2331237 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331238 : term174 = term175.
Proof. exact (@lem2331237 (NUMERAL 0) term38). Qed.
Lemma lem2331239 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331240 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331241 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331240 h1) (fun h1 : term175 = True => @lem2331239)). Qed.
Lemma lem2331242 : term175 = True.
Proof. exact (EQ_MP (@lem2331241) (@lem2331239)). Qed.
Lemma lem2331243 : term174 = True.
Proof. exact (TRANS (@lem2331238) (@lem2331242)). Qed.
Lemma lem2331244 : True = term174.
Proof. exact (SYM (@lem2331243)). Qed.
Lemma lem2331245 : term174.
Proof. exact (EQ_MP (@lem2331244) (@lem0)). Qed.
Lemma lem2331246 : term177.
Proof. exact (@lem2331235 (@lem2331245)). Qed.
Lemma lem2331248 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331249 : term174 = term175.
Proof. exact (@lem2331248 (NUMERAL 0) term38). Qed.
Lemma lem2331250 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331251 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331252 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331251 h1) (fun h1 : term175 = True => @lem2331250)). Qed.
Lemma lem2331253 : term175 = True.
Proof. exact (EQ_MP (@lem2331252) (@lem2331250)). Qed.
Lemma lem2331254 : term174 = True.
Proof. exact (TRANS (@lem2331249) (@lem2331253)). Qed.
Lemma lem2331255 : True = term174.
Proof. exact (SYM (@lem2331254)). Qed.
Lemma lem2331256 : term174.
Proof. exact (EQ_MP (@lem2331255) (@lem0)). Qed.
Lemma lem2331257 : term178.
Proof. exact (@lem2331246 (@lem2331256)). Qed.
Lemma lem2331259 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331260 : term174 = term175.
Proof. exact (@lem2331259 (NUMERAL 0) term38). Qed.
Lemma lem2331261 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331262 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331263 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331262 h1) (fun h1 : term175 = True => @lem2331261)). Qed.
Lemma lem2331264 : term175 = True.
Proof. exact (EQ_MP (@lem2331263) (@lem2331261)). Qed.
Lemma lem2331265 : term174 = True.
Proof. exact (TRANS (@lem2331260) (@lem2331264)). Qed.
Lemma lem2331266 : True = term174.
Proof. exact (SYM (@lem2331265)). Qed.
Lemma lem2331267 : term174.
Proof. exact (EQ_MP (@lem2331266) (@lem0)). Qed.
Lemma lem2331268 : term179.
Proof. exact (@lem2331257 (@lem2331267)). Qed.
Lemma lem2331270 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2331271 : term133 = term144.
Proof. exact (@lem2331270 term38 term38). Qed.
Lemma lem2331272 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331273 : term141 = term38.
Proof. exact (EQ_MP (@lem2331272) (@lem940073)). Qed.
Lemma lem2331274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331275 : term139 = term37.
Proof. exact (MK_COMB (@lem2331274) (@lem2331273)). Qed.
Lemma lem2331276 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2331277 : term144 = term125.
Proof. exact (MK_COMB (@lem2331276) (@lem2331275)). Qed.
Lemma lem2331278 : term133 = term125.
Proof. exact (TRANS (@lem2331271) (@lem2331277)). Qed.
Lemma lem2331280 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331281 : term138 = term139.
Proof. exact (@lem2331280 term38 term38). Qed.
Lemma lem2331282 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331283 : term141 = term38.
Proof. exact (EQ_MP (@lem2331282) (@lem940073)). Qed.
Lemma lem2331284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331285 : term139 = term37.
Proof. exact (MK_COMB (@lem2331284) (@lem2331283)). Qed.
Lemma lem2331286 : term138 = term37.
Proof. exact (TRANS (@lem2331281) (@lem2331285)). Qed.
Lemma lem2331287 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331288 : term180 = term168.
Proof. exact (MK_COMB (@lem2331287) (@lem2331286)). Qed.
Lemma lem2331289 : term181 = term170.
Proof. exact (MK_COMB (@lem2331288) (@lem2331278)). Qed.
Lemma lem2331291 (m : nat) : (term182 m) = term118.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2331292 : term170 = term118.
Proof. exact (@lem2331291 term38). Qed.
Lemma lem2331293 : term181 = term118.
Proof. exact (TRANS (@lem2331289) (@lem2331292)). Qed.
Lemma lem2331294 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331295 : term183 = term184.
Proof. exact (MK_COMB (@lem2331294) (@lem2331293)). Qed.
Lemma lem2331296 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem2331297 : term185 = term186.
Proof. exact (MK_COMB (@lem2331295) (@lem2331296)). Qed.
Lemma lem2331299 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331300 : term186 = term118.
Proof. exact (@lem2331299 term38). Qed.
Lemma lem2331301 : term185 = term118.
Proof. exact (TRANS (@lem2331297) (@lem2331300)). Qed.
Lemma lem2331303 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331304 : term138 = term139.
Proof. exact (@lem2331303 term38 term38). Qed.
Lemma lem2331305 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331306 : term141 = term38.
Proof. exact (EQ_MP (@lem2331305) (@lem940073)). Qed.
Lemma lem2331307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331308 : term139 = term37.
Proof. exact (MK_COMB (@lem2331307) (@lem2331306)). Qed.
Lemma lem2331309 : term138 = term37.
Proof. exact (TRANS (@lem2331304) (@lem2331308)). Qed.
Lemma lem2331310 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2331311 : term188 = term186.
Proof. exact (MK_COMB (@lem2331310) (@lem2331309)). Qed.
Lemma lem2331313 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331314 : term186 = term118.
Proof. exact (@lem2331313 term38). Qed.
Lemma lem2331315 : term188 = term118.
Proof. exact (TRANS (@lem2331311) (@lem2331314)). Qed.
Lemma lem2331316 : term118 = term188.
Proof. exact (SYM (@lem2331315)). Qed.
Lemma lem2331317 : term185 = term188.
Proof. exact (TRANS (@lem2331301) (@lem2331316)). Qed.
Lemma lem2331318 : term171 = term189.
Proof. exact (@lem2331268 (@lem2331317)). Qed.
Lemma lem2331319 : term170 = term189.
Proof. exact (TRANS (@lem2331234) (@lem2331318)). Qed.
Lemma lem2331321 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2331322 : term189 = term118.
Proof. exact (@lem2331321 term118). Qed.
Lemma lem2331323 : term170 = term118.
Proof. exact (TRANS (@lem2331319) (@lem2331322)). Qed.
Lemma lem2331324 (y : int) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem2331325 (y : int) : (term167 y) = (term190 y).
Proof. exact (MK_COMB (@lem2331324 y) (@lem2331323)). Qed.
Lemma lem2331326 (y : int) : (term166 y) = (term190 y).
Proof. exact (TRANS (@lem2331225 y) (@lem2331325 y)). Qed.
Lemma lem2331327 (y : int) : (term190 y) = (real_of_int y).
Proof. exact (@lem1982723 (real_of_int y)). Qed.
Lemma lem2331328 (y : int) : (term166 y) = (real_of_int y).
Proof. exact (TRANS (@lem2331326 y) (@lem2331327 y)). Qed.
Lemma lem2331329 (x : int) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem2331330 (x : int) (y : int) : (term165 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem2331329 x) (@lem2331328 y)). Qed.
Lemma lem2331331 (x : int) (y : int) : (term164 y x) = (term114 x y).
Proof. exact (TRANS (@lem2331224 x y) (@lem2331330 x y)). Qed.
Lemma lem2331332 (x : int) (y : int) : (term162 y x) = (term114 x y).
Proof. exact (TRANS (@lem2331223 y x) (@lem2331331 x y)). Qed.
Lemma lem2331334 (x : int) (y : int) : (term161 y x) = (term114 x y).
Proof. exact (TRANS (@lem2331178 y x) (@lem2331332 x y)). Qed.
Lemma lem2331335 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2331336 (x : int) (y : int) : (term191 y x) = (term117 x y).
Proof. exact (MK_COMB (@lem2331335) (@lem2331334 x y)). Qed.
Lemma lem2331337 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2331338 (x : int) (y : int) : (term160 y x) = (term119 x y).
Proof. exact (MK_COMB (@lem2331336 x y) (@lem2331337)). Qed.
Lemma lem2331339 (x : int) (y : int) : (term51 x y) = (term119 x y).
Proof. exact (TRANS (@lem2331160 y x) (@lem2331338 x y)). Qed.
Lemma lem2331340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2331341 (x : int) (y : int) : (term53 y x) = (term192 x y).
Proof. exact (MK_COMB (@lem2331340) (@lem2331159 x y)). Qed.
Lemma lem2331342 (x : int) (y : int) : (term55 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem2331341 x y) (@lem2331339 x y)). Qed.
Lemma lem2331343 (x : int) : (term72 x) = (term194 x).
Proof. exact (fun_ext (fun y : int => @lem2331342 x y)). Qed.
Lemma lem2331344 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331345 (x : int) : (term87 x) = (term195 x).
Proof. exact (MK_COMB (@lem2331344) (@lem2331343 x)). Qed.
Lemma lem2331346 : term94 = term196.
Proof. exact (fun_ext (fun x : int => @lem2331345 x)). Qed.
Lemma lem2331347 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331348 : term109 = term197.
Proof. exact (MK_COMB (@lem2331347) (@lem2331346)). Qed.
Lemma lem2331349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2331350 : term106 = term198.
Proof. exact (MK_COMB (@lem2331349) (@lem2331092)). Qed.
Lemma lem2331351 : term110 = term199.
Proof. exact (MK_COMB (@lem2331350) (@lem2331348)). Qed.
Lemma lem2331352 : term64 = term199.
Proof. exact (TRANS (@lem2330997) (@lem2331351)). Qed.
Lemma lem2331459 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term65 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2331460 (P : int -> Prop) (Q : int -> Prop) : (term68 P Q) = (term67 P Q).
Proof. exact (@lem2331459 int P Q). Qed.
Lemma lem2331461 : term200 = term201.
Proof. exact (@lem2331460 term158 term196). Qed.
Lemma lem2331462 (x : int) : (term202 x) = (term157 x).
Proof. exact (eq_refl (term202 x)). Qed.
Lemma lem2331463 : term203 = term158.
Proof. exact (fun_ext (fun x : int => @lem2331462 x)). Qed.
Lemma lem2331464 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331465 : term204 = term159.
Proof. exact (MK_COMB (@lem2331464) (@lem2331463)). Qed.
Lemma lem2331466 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2331467 : term205 = term198.
Proof. exact (MK_COMB (@lem2331466) (@lem2331465)). Qed.
Lemma lem2331468 (x : int) : (term206 x) = (term195 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem2331469 : term207 = term196.
Proof. exact (fun_ext (fun x : int => @lem2331468 x)). Qed.
Lemma lem2331470 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331471 : term208 = term197.
Proof. exact (MK_COMB (@lem2331470) (@lem2331469)). Qed.
Lemma lem2331472 : term200 = term199.
Proof. exact (MK_COMB (@lem2331467) (@lem2331471)). Qed.
Lemma lem2331473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2331474 : term209 = term210.
Proof. exact (MK_COMB (@lem2331473) (@lem2331472)). Qed.
Lemma lem2331475 (x : int) : (term202 x) = (term157 x).
Proof. exact (eq_refl (term202 x)). Qed.
Lemma lem2331476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2331477 (x : int) : (term211 x) = (term212 x).
Proof. exact (MK_COMB (@lem2331476) (@lem2331475 x)). Qed.
Lemma lem2331478 (x : int) : (term206 x) = (term195 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem2331479 (x : int) : (term213 x) = (term214 x).
Proof. exact (MK_COMB (@lem2331477 x) (@lem2331478 x)). Qed.
Lemma lem2331480 : term215 = term216.
Proof. exact (fun_ext (fun x : int => @lem2331479 x)). Qed.
Lemma lem2331481 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331482 : term201 = term217.
Proof. exact (MK_COMB (@lem2331481) (@lem2331480)). Qed.
Lemma lem2331483 : (term200 = term201) = (term199 = term217).
Proof. exact (MK_COMB (@lem2331474) (@lem2331482)). Qed.
Lemma lem2331484 : term199 = term217.
Proof. exact (EQ_MP (@lem2331483) (@lem2331461)). Qed.
Lemma lem2331486 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term65 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2331487 (P : int -> Prop) (Q : int -> Prop) : (term68 P Q) = (term67 P Q).
Proof. exact (@lem2331486 int P Q). Qed.
Lemma lem2331488 (x : int) : (term218 x) = (term219 x).
Proof. exact (@lem2331487 (term156 x) (term194 x)). Qed.
Lemma lem2331489 (x : int) (y : int) : (term220 x y) = (term155 x y).
Proof. exact (eq_refl (term220 x y)). Qed.
Lemma lem2331490 (x : int) : (term221 x) = (term156 x).
Proof. exact (fun_ext (fun y : int => @lem2331489 x y)). Qed.
Lemma lem2331491 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331492 (x : int) : (term222 x) = (term157 x).
Proof. exact (MK_COMB (@lem2331491) (@lem2331490 x)). Qed.
Lemma lem2331493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2331494 (x : int) : (term223 x) = (term212 x).
Proof. exact (MK_COMB (@lem2331493) (@lem2331492 x)). Qed.
Lemma lem2331495 (x : int) (y : int) : (term224 x y) = (term193 x y).
Proof. exact (eq_refl (term224 x y)). Qed.
Lemma lem2331496 (x : int) : (term225 x) = (term194 x).
Proof. exact (fun_ext (fun y : int => @lem2331495 x y)). Qed.
Lemma lem2331497 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331498 (x : int) : (term226 x) = (term195 x).
Proof. exact (MK_COMB (@lem2331497) (@lem2331496 x)). Qed.
Lemma lem2331499 (x : int) : (term218 x) = (term214 x).
Proof. exact (MK_COMB (@lem2331494 x) (@lem2331498 x)). Qed.
Lemma lem2331500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2331501 (x : int) : (term227 x) = (term228 x).
Proof. exact (MK_COMB (@lem2331500) (@lem2331499 x)). Qed.
Lemma lem2331502 (x : int) (y : int) : (term220 x y) = (term155 x y).
Proof. exact (eq_refl (term220 x y)). Qed.
Lemma lem2331503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2331504 (x : int) (y : int) : (term229 x y) = (term230 x y).
Proof. exact (MK_COMB (@lem2331503) (@lem2331502 x y)). Qed.
Lemma lem2331505 (x : int) (y : int) : (term224 x y) = (term193 x y).
Proof. exact (eq_refl (term224 x y)). Qed.
Lemma lem2331506 (x : int) (y : int) : (term231 x y) = (term232 x y).
Proof. exact (MK_COMB (@lem2331504 x y) (@lem2331505 x y)). Qed.
Lemma lem2331507 (x : int) : (term233 x) = (term234 x).
Proof. exact (fun_ext (fun y : int => @lem2331506 x y)). Qed.
Lemma lem2331508 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331509 (x : int) : (term219 x) = (term235 x).
Proof. exact (MK_COMB (@lem2331508) (@lem2331507 x)). Qed.
Lemma lem2331510 (x : int) : ((term218 x) = (term219 x)) = ((term214 x) = (term235 x)).
Proof. exact (MK_COMB (@lem2331501 x) (@lem2331509 x)). Qed.
Lemma lem2331511 (x : int) : (term214 x) = (term235 x).
Proof. exact (EQ_MP (@lem2331510 x) (@lem2331488 x)). Qed.
Lemma lem2331512 : term216 = term236.
Proof. exact (fun_ext (fun x : int => @lem2331511 x)). Qed.
Lemma lem2331513 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331514 : term217 = term237.
Proof. exact (MK_COMB (@lem2331513) (@lem2331512)). Qed.
Lemma lem2331516 : term199 = term237.
Proof. exact (TRANS (@lem2331484) (@lem2331514)). Qed.
Lemma lem2331519 : term64 = term237.
Proof. exact (TRANS (@lem2331352) (@lem2331516)). Qed.
Lemma lem2331536 (x : int) (y : int) : (term232 x y) = (term232 x y).
Proof. exact (eq_refl (term232 x y)). Qed.
Lemma lem2331537 (x : int) : (term234 x) = (term234 x).
Proof. exact (fun_ext (fun y : int => @lem2331536 x y)). Qed.
Lemma lem2331538 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331539 (x : int) : (term235 x) = (term235 x).
Proof. exact (MK_COMB (@lem2331538) (@lem2331537 x)). Qed.
Lemma lem2331540 : term236 = term236.
Proof. exact (fun_ext (fun x : int => @lem2331539 x)). Qed.
Lemma lem2331541 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2331542 : term237 = term237.
Proof. exact (MK_COMB (@lem2331541) (@lem2331540)). Qed.
Lemma lem2331543 : term64 = term237.
Proof. exact (TRANS (@lem2331519) (@lem2331542)). Qed.
Lemma lem2331553 (x : int) (y : int) (h1 : term232 x y) : term232 x y.
Proof. exact (h1). Qed.
Lemma lem2331554 (x : int) (y : int) (h1 : term155 x y) : term155 x y.
Proof. exact (h1). Qed.
Lemma lem2331555 (x : int) (y : int) (h1 : term155 x y) : term153 x y.
Proof. exact (proj2 (@lem2331554 x y h1)). Qed.
Lemma lem2331556 (x : int) (y : int) (h1 : term155 x y) : term119 x y.
Proof. exact (proj1 (@lem2331554 x y h1)). Qed.
Lemma lem2331558 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2331559 : term238 = term174.
Proof. exact (@lem2331558 term118 term37). Qed.
Lemma lem2331561 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331562 : term37 = term127.
Proof. exact (@lem2331561 term38). Qed.
Lemma lem2331564 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331565 : term118 = term189.
Proof. exact (@lem2331564 (NUMERAL 0)). Qed.
Lemma lem2331566 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2331567 : term239 = term240.
Proof. exact (MK_COMB (@lem2331566) (@lem2331565)). Qed.
Lemma lem2331568 : term174 = term241.
Proof. exact (MK_COMB (@lem2331567) (@lem2331562)). Qed.
Lemma lem2331569 : term242.
Proof. exact (@lem1980255 term118 term37 term37 term37). Qed.
Lemma lem2331571 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331572 : term174 = term175.
Proof. exact (@lem2331571 (NUMERAL 0) term38). Qed.
Lemma lem2331573 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331574 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331575 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331574 h1) (fun h1 : term175 = True => @lem2331573)). Qed.
Lemma lem2331576 : term175 = True.
Proof. exact (EQ_MP (@lem2331575) (@lem2331573)). Qed.
Lemma lem2331577 : term174 = True.
Proof. exact (TRANS (@lem2331572) (@lem2331576)). Qed.
Lemma lem2331578 : True = term174.
Proof. exact (SYM (@lem2331577)). Qed.
Lemma lem2331579 : term174.
Proof. exact (EQ_MP (@lem2331578) (@lem0)). Qed.
Lemma lem2331580 : term243.
Proof. exact (@lem2331569 (@lem2331579)). Qed.
Lemma lem2331582 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331583 : term174 = term175.
Proof. exact (@lem2331582 (NUMERAL 0) term38). Qed.
Lemma lem2331584 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331585 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331586 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331585 h1) (fun h1 : term175 = True => @lem2331584)). Qed.
Lemma lem2331587 : term175 = True.
Proof. exact (EQ_MP (@lem2331586) (@lem2331584)). Qed.
Lemma lem2331588 : term174 = True.
Proof. exact (TRANS (@lem2331583) (@lem2331587)). Qed.
Lemma lem2331589 : True = term174.
Proof. exact (SYM (@lem2331588)). Qed.
Lemma lem2331590 : term174.
Proof. exact (EQ_MP (@lem2331589) (@lem0)). Qed.
Lemma lem2331591 : term241 = term244.
Proof. exact (@lem2331580 (@lem2331590)). Qed.
Lemma lem2331593 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331594 : term138 = term139.
Proof. exact (@lem2331593 term38 term38). Qed.
Lemma lem2331595 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331596 : term141 = term38.
Proof. exact (EQ_MP (@lem2331595) (@lem940073)). Qed.
Lemma lem2331597 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331598 : term139 = term37.
Proof. exact (MK_COMB (@lem2331597) (@lem2331596)). Qed.
Lemma lem2331599 : term138 = term37.
Proof. exact (TRANS (@lem2331594) (@lem2331598)). Qed.
Lemma lem2331601 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331602 : term186 = term118.
Proof. exact (@lem2331601 term38). Qed.
Lemma lem2331603 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2331604 : term245 = term239.
Proof. exact (MK_COMB (@lem2331603) (@lem2331602)). Qed.
Lemma lem2331605 : term244 = term174.
Proof. exact (MK_COMB (@lem2331604) (@lem2331599)). Qed.
Lemma lem2331607 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331608 : term174 = term175.
Proof. exact (@lem2331607 (NUMERAL 0) term38). Qed.
Lemma lem2331609 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331610 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331611 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331610 h1) (fun h1 : term175 = True => @lem2331609)). Qed.
Lemma lem2331612 : term175 = True.
Proof. exact (EQ_MP (@lem2331611) (@lem2331609)). Qed.
Lemma lem2331613 : term174 = True.
Proof. exact (TRANS (@lem2331608) (@lem2331612)). Qed.
Lemma lem2331614 : term244 = True.
Proof. exact (TRANS (@lem2331605) (@lem2331613)). Qed.
Lemma lem2331615 : term241 = True.
Proof. exact (TRANS (@lem2331591) (@lem2331614)). Qed.
Lemma lem2331616 : term174 = True.
Proof. exact (TRANS (@lem2331568) (@lem2331615)). Qed.
Lemma lem2331617 : term238 = True.
Proof. exact (TRANS (@lem2331559) (@lem2331616)). Qed.
Lemma lem2331618 : True = term238.
Proof. exact (SYM (@lem2331617)). Qed.
Lemma lem2331619 : term238.
Proof. exact (EQ_MP (@lem2331618) (@lem0)). Qed.
Lemma lem2331620 (x : int) (y : int) (h1 : term155 x y) : term246 x y.
Proof. exact (conj (@lem2331619) (@lem2331556 x y h1)). Qed.
Lemma lem2331622 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2331623 (x : int) (y : int) : term248 x y.
Proof. exact (@lem2331622 term37 (term114 x y)). Qed.
Lemma lem2331624 (x : int) (y : int) (h1 : term155 x y) : term249 x y.
Proof. exact (@lem2331623 x y (@lem2331620 x y h1)). Qed.
Lemma lem2331625 (x : int) (y : int) : (term250 x y) = (term114 x y).
Proof. exact (@lem1982733 (term114 x y)). Qed.
Lemma lem2331626 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2331627 (x : int) (y : int) : (term251 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem2331626) (@lem2331625 x y)). Qed.
Lemma lem2331628 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2331629 (x : int) (y : int) : (term249 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem2331627 x y) (@lem2331628)). Qed.
Lemma lem2331630 (x : int) (y : int) (h1 : term155 x y) : term119 x y.
Proof. exact (EQ_MP (@lem2331629 x y) (@lem2331624 x y h1)). Qed.
Lemma lem2331632 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2331633 : term238 = term174.
Proof. exact (@lem2331632 term118 term37). Qed.
Lemma lem2331635 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331636 : term37 = term127.
Proof. exact (@lem2331635 term38). Qed.
Lemma lem2331638 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331639 : term118 = term189.
Proof. exact (@lem2331638 (NUMERAL 0)). Qed.
Lemma lem2331640 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2331641 : term239 = term240.
Proof. exact (MK_COMB (@lem2331640) (@lem2331639)). Qed.
Lemma lem2331642 : term174 = term241.
Proof. exact (MK_COMB (@lem2331641) (@lem2331636)). Qed.
Lemma lem2331643 : term242.
Proof. exact (@lem1980255 term118 term37 term37 term37). Qed.
Lemma lem2331645 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331646 : term174 = term175.
Proof. exact (@lem2331645 (NUMERAL 0) term38). Qed.
Lemma lem2331647 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331648 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331649 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331648 h1) (fun h1 : term175 = True => @lem2331647)). Qed.
Lemma lem2331650 : term175 = True.
Proof. exact (EQ_MP (@lem2331649) (@lem2331647)). Qed.
Lemma lem2331651 : term174 = True.
Proof. exact (TRANS (@lem2331646) (@lem2331650)). Qed.
Lemma lem2331652 : True = term174.
Proof. exact (SYM (@lem2331651)). Qed.
Lemma lem2331653 : term174.
Proof. exact (EQ_MP (@lem2331652) (@lem0)). Qed.
Lemma lem2331654 : term243.
Proof. exact (@lem2331643 (@lem2331653)). Qed.
Lemma lem2331656 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331657 : term174 = term175.
Proof. exact (@lem2331656 (NUMERAL 0) term38). Qed.
Lemma lem2331658 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331659 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331660 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331659 h1) (fun h1 : term175 = True => @lem2331658)). Qed.
Lemma lem2331661 : term175 = True.
Proof. exact (EQ_MP (@lem2331660) (@lem2331658)). Qed.
Lemma lem2331662 : term174 = True.
Proof. exact (TRANS (@lem2331657) (@lem2331661)). Qed.
Lemma lem2331663 : True = term174.
Proof. exact (SYM (@lem2331662)). Qed.
Lemma lem2331664 : term174.
Proof. exact (EQ_MP (@lem2331663) (@lem0)). Qed.
Lemma lem2331665 : term241 = term244.
Proof. exact (@lem2331654 (@lem2331664)). Qed.
Lemma lem2331667 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331668 : term138 = term139.
Proof. exact (@lem2331667 term38 term38). Qed.
Lemma lem2331669 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331670 : term141 = term38.
Proof. exact (EQ_MP (@lem2331669) (@lem940073)). Qed.
Lemma lem2331671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331672 : term139 = term37.
Proof. exact (MK_COMB (@lem2331671) (@lem2331670)). Qed.
Lemma lem2331673 : term138 = term37.
Proof. exact (TRANS (@lem2331668) (@lem2331672)). Qed.
Lemma lem2331675 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331676 : term186 = term118.
Proof. exact (@lem2331675 term38). Qed.
Lemma lem2331677 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2331678 : term245 = term239.
Proof. exact (MK_COMB (@lem2331677) (@lem2331676)). Qed.
Lemma lem2331679 : term244 = term174.
Proof. exact (MK_COMB (@lem2331678) (@lem2331673)). Qed.
Lemma lem2331681 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331682 : term174 = term175.
Proof. exact (@lem2331681 (NUMERAL 0) term38). Qed.
Lemma lem2331683 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331684 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331685 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331684 h1) (fun h1 : term175 = True => @lem2331683)). Qed.
Lemma lem2331686 : term175 = True.
Proof. exact (EQ_MP (@lem2331685) (@lem2331683)). Qed.
Lemma lem2331687 : term174 = True.
Proof. exact (TRANS (@lem2331682) (@lem2331686)). Qed.
Lemma lem2331688 : term244 = True.
Proof. exact (TRANS (@lem2331679) (@lem2331687)). Qed.
Lemma lem2331689 : term241 = True.
Proof. exact (TRANS (@lem2331665) (@lem2331688)). Qed.
Lemma lem2331690 : term174 = True.
Proof. exact (TRANS (@lem2331642) (@lem2331689)). Qed.
Lemma lem2331691 : term238 = True.
Proof. exact (TRANS (@lem2331633) (@lem2331690)). Qed.
Lemma lem2331692 : True = term238.
Proof. exact (SYM (@lem2331691)). Qed.
Lemma lem2331693 : term238.
Proof. exact (EQ_MP (@lem2331692) (@lem0)). Qed.
Lemma lem2331694 (x : int) (y : int) (h1 : term155 x y) : term252 x y.
Proof. exact (conj (@lem2331693) (@lem2331555 x y h1)). Qed.
Lemma lem2331696 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2331697 (x : int) (y : int) : term253 x y.
Proof. exact (@lem2331696 term37 (term150 x y)). Qed.
Lemma lem2331698 (x : int) (y : int) (h1 : term155 x y) : term254 x y.
Proof. exact (@lem2331697 x y (@lem2331694 x y h1)). Qed.
Lemma lem2331699 (x : int) (y : int) : (term255 x y) = (term150 x y).
Proof. exact (@lem1982733 (term150 x y)). Qed.
Lemma lem2331700 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2331701 (x : int) (y : int) : (term256 x y) = (term152 x y).
Proof. exact (MK_COMB (@lem2331700) (@lem2331699 x y)). Qed.
Lemma lem2331702 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2331703 (x : int) (y : int) : (term254 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem2331701 x y) (@lem2331702)). Qed.
Lemma lem2331704 (x : int) (y : int) (h1 : term155 x y) : term153 x y.
Proof. exact (EQ_MP (@lem2331703 x y) (@lem2331698 x y h1)). Qed.
Lemma lem2331705 (x : int) (y : int) (h1 : term155 x y) : term193 x y.
Proof. exact (conj (@lem2331704 x y h1) (@lem2331630 x y h1)). Qed.
Lemma lem2331707 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2331708 (x : int) (y : int) : term258 x y.
Proof. exact (@lem2331707 (term150 x y) (term114 x y)). Qed.
Lemma lem2331709 (x : int) (y : int) (h1 : term155 x y) : term259 x y.
Proof. exact (@lem2331708 x y (@lem2331705 x y h1)). Qed.
Lemma lem2331710 (x : int) (y : int) : (term260 x y) = (term261 x y).
Proof. exact (@lem1982753 (real_of_int x) (term115 x) (term149 y) (real_of_int y)). Qed.
Lemma lem2331711 (x : int) : (term262 x) = (term263 x).
Proof. exact (@lem1982715 term125 (real_of_int x)). Qed.
Lemma lem2331713 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331714 : term37 = term127.
Proof. exact (@lem2331713 term38). Qed.
Lemma lem2331716 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2331717 : term125 = term130.
Proof. exact (@lem2331716 term38). Qed.
Lemma lem2331718 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331719 : term264 = term265.
Proof. exact (MK_COMB (@lem2331718) (@lem2331717)). Qed.
Lemma lem2331720 : term266 = term267.
Proof. exact (MK_COMB (@lem2331719) (@lem2331714)). Qed.
Lemma lem2331721 : term268.
Proof. exact (@lem1981473 term125 term37 term37 term37 term118 term37). Qed.
Lemma lem2331723 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331724 : term174 = term175.
Proof. exact (@lem2331723 (NUMERAL 0) term38). Qed.
Lemma lem2331725 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331726 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331727 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331726 h1) (fun h1 : term175 = True => @lem2331725)). Qed.
Lemma lem2331728 : term175 = True.
Proof. exact (EQ_MP (@lem2331727) (@lem2331725)). Qed.
Lemma lem2331729 : term174 = True.
Proof. exact (TRANS (@lem2331724) (@lem2331728)). Qed.
Lemma lem2331730 : True = term174.
Proof. exact (SYM (@lem2331729)). Qed.
Lemma lem2331731 : term174.
Proof. exact (EQ_MP (@lem2331730) (@lem0)). Qed.
Lemma lem2331732 : term269.
Proof. exact (@lem2331721 (@lem2331731)). Qed.
Lemma lem2331734 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331735 : term174 = term175.
Proof. exact (@lem2331734 (NUMERAL 0) term38). Qed.
Lemma lem2331736 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331737 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331738 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331737 h1) (fun h1 : term175 = True => @lem2331736)). Qed.
Lemma lem2331739 : term175 = True.
Proof. exact (EQ_MP (@lem2331738) (@lem2331736)). Qed.
Lemma lem2331740 : term174 = True.
Proof. exact (TRANS (@lem2331735) (@lem2331739)). Qed.
Lemma lem2331741 : True = term174.
Proof. exact (SYM (@lem2331740)). Qed.
Lemma lem2331742 : term174.
Proof. exact (EQ_MP (@lem2331741) (@lem0)). Qed.
Lemma lem2331743 : term270.
Proof. exact (@lem2331732 (@lem2331742)). Qed.
Lemma lem2331745 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331746 : term174 = term175.
Proof. exact (@lem2331745 (NUMERAL 0) term38). Qed.
Lemma lem2331747 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331748 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331749 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331748 h1) (fun h1 : term175 = True => @lem2331747)). Qed.
Lemma lem2331750 : term175 = True.
Proof. exact (EQ_MP (@lem2331749) (@lem2331747)). Qed.
Lemma lem2331751 : term174 = True.
Proof. exact (TRANS (@lem2331746) (@lem2331750)). Qed.
Lemma lem2331752 : True = term174.
Proof. exact (SYM (@lem2331751)). Qed.
Lemma lem2331753 : term174.
Proof. exact (EQ_MP (@lem2331752) (@lem0)). Qed.
Lemma lem2331754 : term271.
Proof. exact (@lem2331743 (@lem2331753)). Qed.
Lemma lem2331756 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331757 : term138 = term139.
Proof. exact (@lem2331756 term38 term38). Qed.
Lemma lem2331758 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331759 : term141 = term38.
Proof. exact (EQ_MP (@lem2331758) (@lem940073)). Qed.
Lemma lem2331760 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331761 : term139 = term37.
Proof. exact (MK_COMB (@lem2331760) (@lem2331759)). Qed.
Lemma lem2331762 : term138 = term37.
Proof. exact (TRANS (@lem2331757) (@lem2331761)). Qed.
Lemma lem2331764 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2331765 : term133 = term144.
Proof. exact (@lem2331764 term38 term38). Qed.
Lemma lem2331766 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331767 : term141 = term38.
Proof. exact (EQ_MP (@lem2331766) (@lem940073)). Qed.
Lemma lem2331768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331769 : term139 = term37.
Proof. exact (MK_COMB (@lem2331768) (@lem2331767)). Qed.
Lemma lem2331770 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2331771 : term144 = term125.
Proof. exact (MK_COMB (@lem2331770) (@lem2331769)). Qed.
Lemma lem2331772 : term133 = term125.
Proof. exact (TRANS (@lem2331765) (@lem2331771)). Qed.
Lemma lem2331773 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331774 : term272 = term264.
Proof. exact (MK_COMB (@lem2331773) (@lem2331772)). Qed.
Lemma lem2331775 : term273 = term266.
Proof. exact (MK_COMB (@lem2331774) (@lem2331762)). Qed.
Lemma lem2331777 (m : nat) : (term274 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2331778 : term266 = term118.
Proof. exact (@lem2331777 term38). Qed.
Lemma lem2331779 : term273 = term118.
Proof. exact (TRANS (@lem2331775) (@lem2331778)). Qed.
Lemma lem2331780 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331781 : term275 = term184.
Proof. exact (MK_COMB (@lem2331780) (@lem2331779)). Qed.
Lemma lem2331782 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem2331783 : term276 = term186.
Proof. exact (MK_COMB (@lem2331781) (@lem2331782)). Qed.
Lemma lem2331785 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331786 : term186 = term118.
Proof. exact (@lem2331785 term38). Qed.
Lemma lem2331787 : term276 = term118.
Proof. exact (TRANS (@lem2331783) (@lem2331786)). Qed.
Lemma lem2331789 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331790 : term138 = term139.
Proof. exact (@lem2331789 term38 term38). Qed.
Lemma lem2331791 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331792 : term141 = term38.
Proof. exact (EQ_MP (@lem2331791) (@lem940073)). Qed.
Lemma lem2331793 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331794 : term139 = term37.
Proof. exact (MK_COMB (@lem2331793) (@lem2331792)). Qed.
Lemma lem2331795 : term138 = term37.
Proof. exact (TRANS (@lem2331790) (@lem2331794)). Qed.
Lemma lem2331796 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2331797 : term188 = term186.
Proof. exact (MK_COMB (@lem2331796) (@lem2331795)). Qed.
Lemma lem2331799 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331800 : term186 = term118.
Proof. exact (@lem2331799 term38). Qed.
Lemma lem2331801 : term188 = term118.
Proof. exact (TRANS (@lem2331797) (@lem2331800)). Qed.
Lemma lem2331802 : term118 = term188.
Proof. exact (SYM (@lem2331801)). Qed.
Lemma lem2331803 : term276 = term188.
Proof. exact (TRANS (@lem2331787) (@lem2331802)). Qed.
Lemma lem2331804 : term267 = term189.
Proof. exact (@lem2331754 (@lem2331803)). Qed.
Lemma lem2331805 : term266 = term189.
Proof. exact (TRANS (@lem2331720) (@lem2331804)). Qed.
Lemma lem2331807 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2331808 : term189 = term118.
Proof. exact (@lem2331807 term118). Qed.
Lemma lem2331809 : term266 = term118.
Proof. exact (TRANS (@lem2331805) (@lem2331808)). Qed.
Lemma lem2331810 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331811 : term277 = term184.
Proof. exact (MK_COMB (@lem2331810) (@lem2331809)). Qed.
Lemma lem2331812 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2331813 (x : int) : (term263 x) = (term278 x).
Proof. exact (MK_COMB (@lem2331811) (@lem2331812 x)). Qed.
Lemma lem2331814 (x : int) : (term262 x) = (term278 x).
Proof. exact (TRANS (@lem2331711 x) (@lem2331813 x)). Qed.
Lemma lem2331815 (x : int) : (term278 x) = term118.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2331816 (x : int) : (term262 x) = term118.
Proof. exact (TRANS (@lem2331814 x) (@lem2331815 x)). Qed.
Lemma lem2331817 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331818 (x : int) : (term279 x) = term280.
Proof. exact (MK_COMB (@lem2331817) (@lem2331816 x)). Qed.
Lemma lem2331819 (y : int) : (term281 y) = (term282 y).
Proof. exact (@lem1982759 (term115 y) (real_of_int y) term125). Qed.
Lemma lem2331820 (y : int) : (term283 y) = (term263 y).
Proof. exact (@lem1982713 term125 (real_of_int y)). Qed.
Lemma lem2331822 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331823 : term37 = term127.
Proof. exact (@lem2331822 term38). Qed.
Lemma lem2331825 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2331826 : term125 = term130.
Proof. exact (@lem2331825 term38). Qed.
Lemma lem2331827 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331828 : term264 = term265.
Proof. exact (MK_COMB (@lem2331827) (@lem2331826)). Qed.
Lemma lem2331829 : term266 = term267.
Proof. exact (MK_COMB (@lem2331828) (@lem2331823)). Qed.
Lemma lem2331830 : term268.
Proof. exact (@lem1981473 term125 term37 term37 term37 term118 term37). Qed.
Lemma lem2331832 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331833 : term174 = term175.
Proof. exact (@lem2331832 (NUMERAL 0) term38). Qed.
Lemma lem2331834 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331835 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331836 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331835 h1) (fun h1 : term175 = True => @lem2331834)). Qed.
Lemma lem2331837 : term175 = True.
Proof. exact (EQ_MP (@lem2331836) (@lem2331834)). Qed.
Lemma lem2331838 : term174 = True.
Proof. exact (TRANS (@lem2331833) (@lem2331837)). Qed.
Lemma lem2331839 : True = term174.
Proof. exact (SYM (@lem2331838)). Qed.
Lemma lem2331840 : term174.
Proof. exact (EQ_MP (@lem2331839) (@lem0)). Qed.
Lemma lem2331841 : term269.
Proof. exact (@lem2331830 (@lem2331840)). Qed.
Lemma lem2331843 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331844 : term174 = term175.
Proof. exact (@lem2331843 (NUMERAL 0) term38). Qed.
Lemma lem2331845 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331846 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331847 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331846 h1) (fun h1 : term175 = True => @lem2331845)). Qed.
Lemma lem2331848 : term175 = True.
Proof. exact (EQ_MP (@lem2331847) (@lem2331845)). Qed.
Lemma lem2331849 : term174 = True.
Proof. exact (TRANS (@lem2331844) (@lem2331848)). Qed.
Lemma lem2331850 : True = term174.
Proof. exact (SYM (@lem2331849)). Qed.
Lemma lem2331851 : term174.
Proof. exact (EQ_MP (@lem2331850) (@lem0)). Qed.
Lemma lem2331852 : term270.
Proof. exact (@lem2331841 (@lem2331851)). Qed.
Lemma lem2331854 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331855 : term174 = term175.
Proof. exact (@lem2331854 (NUMERAL 0) term38). Qed.
Lemma lem2331856 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331857 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331858 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331857 h1) (fun h1 : term175 = True => @lem2331856)). Qed.
Lemma lem2331859 : term175 = True.
Proof. exact (EQ_MP (@lem2331858) (@lem2331856)). Qed.
Lemma lem2331860 : term174 = True.
Proof. exact (TRANS (@lem2331855) (@lem2331859)). Qed.
Lemma lem2331861 : True = term174.
Proof. exact (SYM (@lem2331860)). Qed.
Lemma lem2331862 : term174.
Proof. exact (EQ_MP (@lem2331861) (@lem0)). Qed.
Lemma lem2331863 : term271.
Proof. exact (@lem2331852 (@lem2331862)). Qed.
Lemma lem2331865 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331866 : term138 = term139.
Proof. exact (@lem2331865 term38 term38). Qed.
Lemma lem2331867 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331868 : term141 = term38.
Proof. exact (EQ_MP (@lem2331867) (@lem940073)). Qed.
Lemma lem2331869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331870 : term139 = term37.
Proof. exact (MK_COMB (@lem2331869) (@lem2331868)). Qed.
Lemma lem2331871 : term138 = term37.
Proof. exact (TRANS (@lem2331866) (@lem2331870)). Qed.
Lemma lem2331873 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2331874 : term133 = term144.
Proof. exact (@lem2331873 term38 term38). Qed.
Lemma lem2331875 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331876 : term141 = term38.
Proof. exact (EQ_MP (@lem2331875) (@lem940073)). Qed.
Lemma lem2331877 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331878 : term139 = term37.
Proof. exact (MK_COMB (@lem2331877) (@lem2331876)). Qed.
Lemma lem2331879 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2331880 : term144 = term125.
Proof. exact (MK_COMB (@lem2331879) (@lem2331878)). Qed.
Lemma lem2331881 : term133 = term125.
Proof. exact (TRANS (@lem2331874) (@lem2331880)). Qed.
Lemma lem2331882 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331883 : term272 = term264.
Proof. exact (MK_COMB (@lem2331882) (@lem2331881)). Qed.
Lemma lem2331884 : term273 = term266.
Proof. exact (MK_COMB (@lem2331883) (@lem2331871)). Qed.
Lemma lem2331886 (m : nat) : (term274 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2331887 : term266 = term118.
Proof. exact (@lem2331886 term38). Qed.
Lemma lem2331888 : term273 = term118.
Proof. exact (TRANS (@lem2331884) (@lem2331887)). Qed.
Lemma lem2331889 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331890 : term275 = term184.
Proof. exact (MK_COMB (@lem2331889) (@lem2331888)). Qed.
Lemma lem2331891 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem2331892 : term276 = term186.
Proof. exact (MK_COMB (@lem2331890) (@lem2331891)). Qed.
Lemma lem2331894 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331895 : term186 = term118.
Proof. exact (@lem2331894 term38). Qed.
Lemma lem2331896 : term276 = term118.
Proof. exact (TRANS (@lem2331892) (@lem2331895)). Qed.
Lemma lem2331898 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2331899 : term138 = term139.
Proof. exact (@lem2331898 term38 term38). Qed.
Lemma lem2331900 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331901 : term141 = term38.
Proof. exact (EQ_MP (@lem2331900) (@lem940073)). Qed.
Lemma lem2331902 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331903 : term139 = term37.
Proof. exact (MK_COMB (@lem2331902) (@lem2331901)). Qed.
Lemma lem2331904 : term138 = term37.
Proof. exact (TRANS (@lem2331899) (@lem2331903)). Qed.
Lemma lem2331905 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2331906 : term188 = term186.
Proof. exact (MK_COMB (@lem2331905) (@lem2331904)). Qed.
Lemma lem2331908 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331909 : term186 = term118.
Proof. exact (@lem2331908 term38). Qed.
Lemma lem2331910 : term188 = term118.
Proof. exact (TRANS (@lem2331906) (@lem2331909)). Qed.
Lemma lem2331911 : term118 = term188.
Proof. exact (SYM (@lem2331910)). Qed.
Lemma lem2331912 : term276 = term188.
Proof. exact (TRANS (@lem2331896) (@lem2331911)). Qed.
Lemma lem2331913 : term267 = term189.
Proof. exact (@lem2331863 (@lem2331912)). Qed.
Lemma lem2331914 : term266 = term189.
Proof. exact (TRANS (@lem2331829) (@lem2331913)). Qed.
Lemma lem2331916 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2331917 : term189 = term118.
Proof. exact (@lem2331916 term118). Qed.
Lemma lem2331918 : term266 = term118.
Proof. exact (TRANS (@lem2331914) (@lem2331917)). Qed.
Lemma lem2331919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2331920 : term277 = term184.
Proof. exact (MK_COMB (@lem2331919) (@lem2331918)). Qed.
Lemma lem2331921 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2331922 (y : int) : (term263 y) = (term278 y).
Proof. exact (MK_COMB (@lem2331920) (@lem2331921 y)). Qed.
Lemma lem2331923 (y : int) : (term283 y) = (term278 y).
Proof. exact (TRANS (@lem2331820 y) (@lem2331922 y)). Qed.
Lemma lem2331924 (y : int) : (term278 y) = term118.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2331925 (y : int) : (term283 y) = term118.
Proof. exact (TRANS (@lem2331923 y) (@lem2331924 y)). Qed.
Lemma lem2331926 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2331927 (y : int) : (term284 y) = term280.
Proof. exact (MK_COMB (@lem2331926) (@lem2331925 y)). Qed.
Lemma lem2331928 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem2331929 (y : int) : (term282 y) = term285.
Proof. exact (MK_COMB (@lem2331927 y) (@lem2331928)). Qed.
Lemma lem2331930 (y : int) : (term281 y) = term285.
Proof. exact (TRANS (@lem2331819 y) (@lem2331929 y)). Qed.
Lemma lem2331931 : term285 = term125.
Proof. exact (@lem1982721 term125). Qed.
Lemma lem2331932 (y : int) : (term281 y) = term125.
Proof. exact (TRANS (@lem2331930 y) (@lem2331931)). Qed.
Lemma lem2331933 (x : int) (y : int) : (term261 x y) = term285.
Proof. exact (MK_COMB (@lem2331818 x) (@lem2331932 y)). Qed.
Lemma lem2331934 (x : int) (y : int) : (term260 x y) = term285.
Proof. exact (TRANS (@lem2331710 x y) (@lem2331933 x y)). Qed.
Lemma lem2331935 : term285 = term125.
Proof. exact (@lem1982721 term125). Qed.
Lemma lem2331936 (x : int) (y : int) : (term260 x y) = term125.
Proof. exact (TRANS (@lem2331934 x y) (@lem2331935)). Qed.
Lemma lem2331937 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2331938 (x : int) (y : int) : (term286 x y) = term287.
Proof. exact (MK_COMB (@lem2331937) (@lem2331936 x y)). Qed.
Lemma lem2331939 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2331940 (x : int) (y : int) : (term259 x y) = term288.
Proof. exact (MK_COMB (@lem2331938 x y) (@lem2331939)). Qed.
Lemma lem2331941 (x : int) (y : int) (h1 : term155 x y) : term288.
Proof. exact (EQ_MP (@lem2331940 x y) (@lem2331709 x y h1)). Qed.
Lemma lem2331943 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2331944 : term288 = term289.
Proof. exact (@lem2331943 term118 term125). Qed.
Lemma lem2331946 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2331947 : term125 = term130.
Proof. exact (@lem2331946 term38). Qed.
Lemma lem2331949 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2331950 : term118 = term189.
Proof. exact (@lem2331949 (NUMERAL 0)). Qed.
Lemma lem2331951 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2331952 : term290 = term291.
Proof. exact (MK_COMB (@lem2331951) (@lem2331950)). Qed.
Lemma lem2331953 : term289 = term292.
Proof. exact (MK_COMB (@lem2331952) (@lem2331947)). Qed.
Lemma lem2331954 : term293.
Proof. exact (@lem1980026 term118 term37 term125 term37). Qed.
Lemma lem2331956 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331957 : term174 = term175.
Proof. exact (@lem2331956 (NUMERAL 0) term38). Qed.
Lemma lem2331958 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331959 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331960 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331959 h1) (fun h1 : term175 = True => @lem2331958)). Qed.
Lemma lem2331961 : term175 = True.
Proof. exact (EQ_MP (@lem2331960) (@lem2331958)). Qed.
Lemma lem2331962 : term174 = True.
Proof. exact (TRANS (@lem2331957) (@lem2331961)). Qed.
Lemma lem2331963 : True = term174.
Proof. exact (SYM (@lem2331962)). Qed.
Lemma lem2331964 : term174.
Proof. exact (EQ_MP (@lem2331963) (@lem0)). Qed.
Lemma lem2331965 : term294.
Proof. exact (@lem2331954 (@lem2331964)). Qed.
Lemma lem2331967 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2331968 : term174 = term175.
Proof. exact (@lem2331967 (NUMERAL 0) term38). Qed.
Lemma lem2331969 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331970 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2331971 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331970 h1) (fun h1 : term175 = True => @lem2331969)). Qed.
Lemma lem2331972 : term175 = True.
Proof. exact (EQ_MP (@lem2331971) (@lem2331969)). Qed.
Lemma lem2331973 : term174 = True.
Proof. exact (TRANS (@lem2331968) (@lem2331972)). Qed.
Lemma lem2331974 : True = term174.
Proof. exact (SYM (@lem2331973)). Qed.
Lemma lem2331975 : term174.
Proof. exact (EQ_MP (@lem2331974) (@lem0)). Qed.
Lemma lem2331976 : term292 = term295.
Proof. exact (@lem2331965 (@lem2331975)). Qed.
Lemma lem2331978 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2331979 : term133 = term144.
Proof. exact (@lem2331978 term38 term38). Qed.
Lemma lem2331980 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2331981 : term141 = term38.
Proof. exact (EQ_MP (@lem2331980) (@lem940073)). Qed.
Lemma lem2331982 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2331983 : term139 = term37.
Proof. exact (MK_COMB (@lem2331982) (@lem2331981)). Qed.
Lemma lem2331984 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2331985 : term144 = term125.
Proof. exact (MK_COMB (@lem2331984) (@lem2331983)). Qed.
Lemma lem2331986 : term133 = term125.
Proof. exact (TRANS (@lem2331979) (@lem2331985)). Qed.
Lemma lem2331988 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2331989 : term186 = term118.
Proof. exact (@lem2331988 term38). Qed.
Lemma lem2331990 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2331991 : term296 = term290.
Proof. exact (MK_COMB (@lem2331990) (@lem2331989)). Qed.
Lemma lem2331992 : term295 = term289.
Proof. exact (MK_COMB (@lem2331991) (@lem2331986)). Qed.
Lemma lem2331994 (m : nat) (n : nat) : (term297 m n) = (term298 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2331995 : term289 = term299.
Proof. exact (@lem2331994 (NUMERAL 0) term38). Qed.
Lemma lem2331996 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2331997 (h1 : term176 = (BIT1 0)) : (term38 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2331998 : (term176 = (BIT1 0)) = ((term38 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2331997 h1) (fun h1 : (term38 = (NUMERAL 0)) = False => @lem2331996)). Qed.
Lemma lem2331999 : (term38 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2331998) (@lem2331996)). Qed.
Lemma lem2332000 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2332001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2332002 : term300 = (and True).
Proof. exact (MK_COMB (@lem2332001) (@lem2332000)). Qed.
Lemma lem2332003 : term299 = (True /\ False).
Proof. exact (MK_COMB (@lem2332002) (@lem2331999)). Qed.
Lemma lem2332005 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2332006 : term299 = False.
Proof. exact (TRANS (@lem2332003) (@lem2332005)). Qed.
Lemma lem2332007 : term289 = False.
Proof. exact (TRANS (@lem2331995) (@lem2332006)). Qed.
Lemma lem2332008 : term295 = False.
Proof. exact (TRANS (@lem2331992) (@lem2332007)). Qed.
Lemma lem2332009 : term292 = False.
Proof. exact (TRANS (@lem2331976) (@lem2332008)). Qed.
Lemma lem2332010 : term289 = False.
Proof. exact (TRANS (@lem2331953) (@lem2332009)). Qed.
Lemma lem2332011 : term288 = False.
Proof. exact (TRANS (@lem2331944) (@lem2332010)). Qed.
Lemma lem2332012 (x : int) (y : int) (h1 : term155 x y) : False.
Proof. exact (EQ_MP (@lem2332011) (@lem2331941 x y h1)). Qed.
Lemma lem2332013 (x : int) (y : int) (h1 : term193 x y) : term193 x y.
Proof. exact (h1). Qed.
Lemma lem2332014 (x : int) (y : int) (h1 : term193 x y) : term119 x y.
Proof. exact (proj2 (@lem2332013 x y h1)). Qed.
Lemma lem2332015 (x : int) (y : int) (h1 : term193 x y) : term153 x y.
Proof. exact (proj1 (@lem2332013 x y h1)). Qed.
Lemma lem2332017 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2332018 : term238 = term174.
Proof. exact (@lem2332017 term118 term37). Qed.
Lemma lem2332020 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2332021 : term37 = term127.
Proof. exact (@lem2332020 term38). Qed.
Lemma lem2332023 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2332024 : term118 = term189.
Proof. exact (@lem2332023 (NUMERAL 0)). Qed.
Lemma lem2332025 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2332026 : term239 = term240.
Proof. exact (MK_COMB (@lem2332025) (@lem2332024)). Qed.
Lemma lem2332027 : term174 = term241.
Proof. exact (MK_COMB (@lem2332026) (@lem2332021)). Qed.
Lemma lem2332028 : term242.
Proof. exact (@lem1980255 term118 term37 term37 term37). Qed.
Lemma lem2332030 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332031 : term174 = term175.
Proof. exact (@lem2332030 (NUMERAL 0) term38). Qed.
Lemma lem2332032 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332033 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332034 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332033 h1) (fun h1 : term175 = True => @lem2332032)). Qed.
Lemma lem2332035 : term175 = True.
Proof. exact (EQ_MP (@lem2332034) (@lem2332032)). Qed.
Lemma lem2332036 : term174 = True.
Proof. exact (TRANS (@lem2332031) (@lem2332035)). Qed.
Lemma lem2332037 : True = term174.
Proof. exact (SYM (@lem2332036)). Qed.
Lemma lem2332038 : term174.
Proof. exact (EQ_MP (@lem2332037) (@lem0)). Qed.
Lemma lem2332039 : term243.
Proof. exact (@lem2332028 (@lem2332038)). Qed.
Lemma lem2332041 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332042 : term174 = term175.
Proof. exact (@lem2332041 (NUMERAL 0) term38). Qed.
Lemma lem2332043 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332044 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332045 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332044 h1) (fun h1 : term175 = True => @lem2332043)). Qed.
Lemma lem2332046 : term175 = True.
Proof. exact (EQ_MP (@lem2332045) (@lem2332043)). Qed.
Lemma lem2332047 : term174 = True.
Proof. exact (TRANS (@lem2332042) (@lem2332046)). Qed.
Lemma lem2332048 : True = term174.
Proof. exact (SYM (@lem2332047)). Qed.
Lemma lem2332049 : term174.
Proof. exact (EQ_MP (@lem2332048) (@lem0)). Qed.
Lemma lem2332050 : term241 = term244.
Proof. exact (@lem2332039 (@lem2332049)). Qed.
Lemma lem2332052 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2332053 : term138 = term139.
Proof. exact (@lem2332052 term38 term38). Qed.
Lemma lem2332054 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332055 : term141 = term38.
Proof. exact (EQ_MP (@lem2332054) (@lem940073)). Qed.
Lemma lem2332056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332057 : term139 = term37.
Proof. exact (MK_COMB (@lem2332056) (@lem2332055)). Qed.
Lemma lem2332058 : term138 = term37.
Proof. exact (TRANS (@lem2332053) (@lem2332057)). Qed.
Lemma lem2332060 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2332061 : term186 = term118.
Proof. exact (@lem2332060 term38). Qed.
Lemma lem2332062 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2332063 : term245 = term239.
Proof. exact (MK_COMB (@lem2332062) (@lem2332061)). Qed.
Lemma lem2332064 : term244 = term174.
Proof. exact (MK_COMB (@lem2332063) (@lem2332058)). Qed.
Lemma lem2332066 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332067 : term174 = term175.
Proof. exact (@lem2332066 (NUMERAL 0) term38). Qed.
Lemma lem2332068 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332069 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332070 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332069 h1) (fun h1 : term175 = True => @lem2332068)). Qed.
Lemma lem2332071 : term175 = True.
Proof. exact (EQ_MP (@lem2332070) (@lem2332068)). Qed.
Lemma lem2332072 : term174 = True.
Proof. exact (TRANS (@lem2332067) (@lem2332071)). Qed.
Lemma lem2332073 : term244 = True.
Proof. exact (TRANS (@lem2332064) (@lem2332072)). Qed.
Lemma lem2332074 : term241 = True.
Proof. exact (TRANS (@lem2332050) (@lem2332073)). Qed.
Lemma lem2332075 : term174 = True.
Proof. exact (TRANS (@lem2332027) (@lem2332074)). Qed.
Lemma lem2332076 : term238 = True.
Proof. exact (TRANS (@lem2332018) (@lem2332075)). Qed.
Lemma lem2332077 : True = term238.
Proof. exact (SYM (@lem2332076)). Qed.
Lemma lem2332078 : term238.
Proof. exact (EQ_MP (@lem2332077) (@lem0)). Qed.
Lemma lem2332079 (x : int) (y : int) (h1 : term193 x y) : term246 x y.
Proof. exact (conj (@lem2332078) (@lem2332014 x y h1)). Qed.
Lemma lem2332081 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2332082 (x : int) (y : int) : term248 x y.
Proof. exact (@lem2332081 term37 (term114 x y)). Qed.
Lemma lem2332083 (x : int) (y : int) (h1 : term193 x y) : term249 x y.
Proof. exact (@lem2332082 x y (@lem2332079 x y h1)). Qed.
Lemma lem2332084 (x : int) (y : int) : (term250 x y) = (term114 x y).
Proof. exact (@lem1982733 (term114 x y)). Qed.
Lemma lem2332085 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2332086 (x : int) (y : int) : (term251 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem2332085) (@lem2332084 x y)). Qed.
Lemma lem2332087 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2332088 (x : int) (y : int) : (term249 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem2332086 x y) (@lem2332087)). Qed.
Lemma lem2332089 (x : int) (y : int) (h1 : term193 x y) : term119 x y.
Proof. exact (EQ_MP (@lem2332088 x y) (@lem2332083 x y h1)). Qed.
Lemma lem2332091 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2332092 : term238 = term174.
Proof. exact (@lem2332091 term118 term37). Qed.
Lemma lem2332094 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2332095 : term37 = term127.
Proof. exact (@lem2332094 term38). Qed.
Lemma lem2332097 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2332098 : term118 = term189.
Proof. exact (@lem2332097 (NUMERAL 0)). Qed.
Lemma lem2332099 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2332100 : term239 = term240.
Proof. exact (MK_COMB (@lem2332099) (@lem2332098)). Qed.
Lemma lem2332101 : term174 = term241.
Proof. exact (MK_COMB (@lem2332100) (@lem2332095)). Qed.
Lemma lem2332102 : term242.
Proof. exact (@lem1980255 term118 term37 term37 term37). Qed.
Lemma lem2332104 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332105 : term174 = term175.
Proof. exact (@lem2332104 (NUMERAL 0) term38). Qed.
Lemma lem2332106 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332107 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332108 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332107 h1) (fun h1 : term175 = True => @lem2332106)). Qed.
Lemma lem2332109 : term175 = True.
Proof. exact (EQ_MP (@lem2332108) (@lem2332106)). Qed.
Lemma lem2332110 : term174 = True.
Proof. exact (TRANS (@lem2332105) (@lem2332109)). Qed.
Lemma lem2332111 : True = term174.
Proof. exact (SYM (@lem2332110)). Qed.
Lemma lem2332112 : term174.
Proof. exact (EQ_MP (@lem2332111) (@lem0)). Qed.
Lemma lem2332113 : term243.
Proof. exact (@lem2332102 (@lem2332112)). Qed.
Lemma lem2332115 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332116 : term174 = term175.
Proof. exact (@lem2332115 (NUMERAL 0) term38). Qed.
Lemma lem2332117 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332118 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332119 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332118 h1) (fun h1 : term175 = True => @lem2332117)). Qed.
Lemma lem2332120 : term175 = True.
Proof. exact (EQ_MP (@lem2332119) (@lem2332117)). Qed.
Lemma lem2332121 : term174 = True.
Proof. exact (TRANS (@lem2332116) (@lem2332120)). Qed.
Lemma lem2332122 : True = term174.
Proof. exact (SYM (@lem2332121)). Qed.
Lemma lem2332123 : term174.
Proof. exact (EQ_MP (@lem2332122) (@lem0)). Qed.
Lemma lem2332124 : term241 = term244.
Proof. exact (@lem2332113 (@lem2332123)). Qed.
Lemma lem2332126 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2332127 : term138 = term139.
Proof. exact (@lem2332126 term38 term38). Qed.
Lemma lem2332128 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332129 : term141 = term38.
Proof. exact (EQ_MP (@lem2332128) (@lem940073)). Qed.
Lemma lem2332130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332131 : term139 = term37.
Proof. exact (MK_COMB (@lem2332130) (@lem2332129)). Qed.
Lemma lem2332132 : term138 = term37.
Proof. exact (TRANS (@lem2332127) (@lem2332131)). Qed.
Lemma lem2332134 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2332135 : term186 = term118.
Proof. exact (@lem2332134 term38). Qed.
Lemma lem2332136 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2332137 : term245 = term239.
Proof. exact (MK_COMB (@lem2332136) (@lem2332135)). Qed.
Lemma lem2332138 : term244 = term174.
Proof. exact (MK_COMB (@lem2332137) (@lem2332132)). Qed.
Lemma lem2332140 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332141 : term174 = term175.
Proof. exact (@lem2332140 (NUMERAL 0) term38). Qed.
Lemma lem2332142 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332143 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332144 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332143 h1) (fun h1 : term175 = True => @lem2332142)). Qed.
Lemma lem2332145 : term175 = True.
Proof. exact (EQ_MP (@lem2332144) (@lem2332142)). Qed.
Lemma lem2332146 : term174 = True.
Proof. exact (TRANS (@lem2332141) (@lem2332145)). Qed.
Lemma lem2332147 : term244 = True.
Proof. exact (TRANS (@lem2332138) (@lem2332146)). Qed.
Lemma lem2332148 : term241 = True.
Proof. exact (TRANS (@lem2332124) (@lem2332147)). Qed.
Lemma lem2332149 : term174 = True.
Proof. exact (TRANS (@lem2332101) (@lem2332148)). Qed.
Lemma lem2332150 : term238 = True.
Proof. exact (TRANS (@lem2332092) (@lem2332149)). Qed.
Lemma lem2332151 : True = term238.
Proof. exact (SYM (@lem2332150)). Qed.
Lemma lem2332152 : term238.
Proof. exact (EQ_MP (@lem2332151) (@lem0)). Qed.
Lemma lem2332153 (x : int) (y : int) (h1 : term193 x y) : term252 x y.
Proof. exact (conj (@lem2332152) (@lem2332015 x y h1)). Qed.
Lemma lem2332155 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2332156 (x : int) (y : int) : term253 x y.
Proof. exact (@lem2332155 term37 (term150 x y)). Qed.
Lemma lem2332157 (x : int) (y : int) (h1 : term193 x y) : term254 x y.
Proof. exact (@lem2332156 x y (@lem2332153 x y h1)). Qed.
Lemma lem2332158 (x : int) (y : int) : (term255 x y) = (term150 x y).
Proof. exact (@lem1982733 (term150 x y)). Qed.
Lemma lem2332159 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2332160 (x : int) (y : int) : (term256 x y) = (term152 x y).
Proof. exact (MK_COMB (@lem2332159) (@lem2332158 x y)). Qed.
Lemma lem2332161 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2332162 (x : int) (y : int) : (term254 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem2332160 x y) (@lem2332161)). Qed.
Lemma lem2332163 (x : int) (y : int) (h1 : term193 x y) : term153 x y.
Proof. exact (EQ_MP (@lem2332162 x y) (@lem2332157 x y h1)). Qed.
Lemma lem2332164 (x : int) (y : int) (h1 : term193 x y) : term193 x y.
Proof. exact (conj (@lem2332163 x y h1) (@lem2332089 x y h1)). Qed.
Lemma lem2332166 (x : real) (y : real) : term257 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2332167 (x : int) (y : int) : term258 x y.
Proof. exact (@lem2332166 (term150 x y) (term114 x y)). Qed.
Lemma lem2332168 (x : int) (y : int) (h1 : term193 x y) : term259 x y.
Proof. exact (@lem2332167 x y (@lem2332164 x y h1)). Qed.
Lemma lem2332169 (x : int) (y : int) : (term260 x y) = (term261 x y).
Proof. exact (@lem1982753 (real_of_int x) (term115 x) (term149 y) (real_of_int y)). Qed.
Lemma lem2332170 (x : int) : (term262 x) = (term263 x).
Proof. exact (@lem1982715 term125 (real_of_int x)). Qed.
Lemma lem2332172 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2332173 : term37 = term127.
Proof. exact (@lem2332172 term38). Qed.
Lemma lem2332175 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2332176 : term125 = term130.
Proof. exact (@lem2332175 term38). Qed.
Lemma lem2332177 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2332178 : term264 = term265.
Proof. exact (MK_COMB (@lem2332177) (@lem2332176)). Qed.
Lemma lem2332179 : term266 = term267.
Proof. exact (MK_COMB (@lem2332178) (@lem2332173)). Qed.
Lemma lem2332180 : term268.
Proof. exact (@lem1981473 term125 term37 term37 term37 term118 term37). Qed.
Lemma lem2332182 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332183 : term174 = term175.
Proof. exact (@lem2332182 (NUMERAL 0) term38). Qed.
Lemma lem2332184 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332185 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332186 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332185 h1) (fun h1 : term175 = True => @lem2332184)). Qed.
Lemma lem2332187 : term175 = True.
Proof. exact (EQ_MP (@lem2332186) (@lem2332184)). Qed.
Lemma lem2332188 : term174 = True.
Proof. exact (TRANS (@lem2332183) (@lem2332187)). Qed.
Lemma lem2332189 : True = term174.
Proof. exact (SYM (@lem2332188)). Qed.
Lemma lem2332190 : term174.
Proof. exact (EQ_MP (@lem2332189) (@lem0)). Qed.
Lemma lem2332191 : term269.
Proof. exact (@lem2332180 (@lem2332190)). Qed.
Lemma lem2332193 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332194 : term174 = term175.
Proof. exact (@lem2332193 (NUMERAL 0) term38). Qed.
Lemma lem2332195 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332196 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332197 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332196 h1) (fun h1 : term175 = True => @lem2332195)). Qed.
Lemma lem2332198 : term175 = True.
Proof. exact (EQ_MP (@lem2332197) (@lem2332195)). Qed.
Lemma lem2332199 : term174 = True.
Proof. exact (TRANS (@lem2332194) (@lem2332198)). Qed.
Lemma lem2332200 : True = term174.
Proof. exact (SYM (@lem2332199)). Qed.
Lemma lem2332201 : term174.
Proof. exact (EQ_MP (@lem2332200) (@lem0)). Qed.
Lemma lem2332202 : term270.
Proof. exact (@lem2332191 (@lem2332201)). Qed.
Lemma lem2332204 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332205 : term174 = term175.
Proof. exact (@lem2332204 (NUMERAL 0) term38). Qed.
Lemma lem2332206 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332207 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332208 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332207 h1) (fun h1 : term175 = True => @lem2332206)). Qed.
Lemma lem2332209 : term175 = True.
Proof. exact (EQ_MP (@lem2332208) (@lem2332206)). Qed.
Lemma lem2332210 : term174 = True.
Proof. exact (TRANS (@lem2332205) (@lem2332209)). Qed.
Lemma lem2332211 : True = term174.
Proof. exact (SYM (@lem2332210)). Qed.
Lemma lem2332212 : term174.
Proof. exact (EQ_MP (@lem2332211) (@lem0)). Qed.
Lemma lem2332213 : term271.
Proof. exact (@lem2332202 (@lem2332212)). Qed.
Lemma lem2332215 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2332216 : term138 = term139.
Proof. exact (@lem2332215 term38 term38). Qed.
Lemma lem2332217 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332218 : term141 = term38.
Proof. exact (EQ_MP (@lem2332217) (@lem940073)). Qed.
Lemma lem2332219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332220 : term139 = term37.
Proof. exact (MK_COMB (@lem2332219) (@lem2332218)). Qed.
Lemma lem2332221 : term138 = term37.
Proof. exact (TRANS (@lem2332216) (@lem2332220)). Qed.
Lemma lem2332223 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2332224 : term133 = term144.
Proof. exact (@lem2332223 term38 term38). Qed.
Lemma lem2332225 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332226 : term141 = term38.
Proof. exact (EQ_MP (@lem2332225) (@lem940073)). Qed.
Lemma lem2332227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332228 : term139 = term37.
Proof. exact (MK_COMB (@lem2332227) (@lem2332226)). Qed.
Lemma lem2332229 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2332230 : term144 = term125.
Proof. exact (MK_COMB (@lem2332229) (@lem2332228)). Qed.
Lemma lem2332231 : term133 = term125.
Proof. exact (TRANS (@lem2332224) (@lem2332230)). Qed.
Lemma lem2332232 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2332233 : term272 = term264.
Proof. exact (MK_COMB (@lem2332232) (@lem2332231)). Qed.
Lemma lem2332234 : term273 = term266.
Proof. exact (MK_COMB (@lem2332233) (@lem2332221)). Qed.
Lemma lem2332236 (m : nat) : (term274 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2332237 : term266 = term118.
Proof. exact (@lem2332236 term38). Qed.
Lemma lem2332238 : term273 = term118.
Proof. exact (TRANS (@lem2332234) (@lem2332237)). Qed.
Lemma lem2332239 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2332240 : term275 = term184.
Proof. exact (MK_COMB (@lem2332239) (@lem2332238)). Qed.
Lemma lem2332241 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem2332242 : term276 = term186.
Proof. exact (MK_COMB (@lem2332240) (@lem2332241)). Qed.
Lemma lem2332244 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2332245 : term186 = term118.
Proof. exact (@lem2332244 term38). Qed.
Lemma lem2332246 : term276 = term118.
Proof. exact (TRANS (@lem2332242) (@lem2332245)). Qed.
Lemma lem2332248 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2332249 : term138 = term139.
Proof. exact (@lem2332248 term38 term38). Qed.
Lemma lem2332250 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332251 : term141 = term38.
Proof. exact (EQ_MP (@lem2332250) (@lem940073)). Qed.
Lemma lem2332252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332253 : term139 = term37.
Proof. exact (MK_COMB (@lem2332252) (@lem2332251)). Qed.
Lemma lem2332254 : term138 = term37.
Proof. exact (TRANS (@lem2332249) (@lem2332253)). Qed.
Lemma lem2332255 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2332256 : term188 = term186.
Proof. exact (MK_COMB (@lem2332255) (@lem2332254)). Qed.
Lemma lem2332258 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2332259 : term186 = term118.
Proof. exact (@lem2332258 term38). Qed.
Lemma lem2332260 : term188 = term118.
Proof. exact (TRANS (@lem2332256) (@lem2332259)). Qed.
Lemma lem2332261 : term118 = term188.
Proof. exact (SYM (@lem2332260)). Qed.
Lemma lem2332262 : term276 = term188.
Proof. exact (TRANS (@lem2332246) (@lem2332261)). Qed.
Lemma lem2332263 : term267 = term189.
Proof. exact (@lem2332213 (@lem2332262)). Qed.
Lemma lem2332264 : term266 = term189.
Proof. exact (TRANS (@lem2332179) (@lem2332263)). Qed.
Lemma lem2332266 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2332267 : term189 = term118.
Proof. exact (@lem2332266 term118). Qed.
Lemma lem2332268 : term266 = term118.
Proof. exact (TRANS (@lem2332264) (@lem2332267)). Qed.
Lemma lem2332269 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2332270 : term277 = term184.
Proof. exact (MK_COMB (@lem2332269) (@lem2332268)). Qed.
Lemma lem2332271 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2332272 (x : int) : (term263 x) = (term278 x).
Proof. exact (MK_COMB (@lem2332270) (@lem2332271 x)). Qed.
Lemma lem2332273 (x : int) : (term262 x) = (term278 x).
Proof. exact (TRANS (@lem2332170 x) (@lem2332272 x)). Qed.
Lemma lem2332274 (x : int) : (term278 x) = term118.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2332275 (x : int) : (term262 x) = term118.
Proof. exact (TRANS (@lem2332273 x) (@lem2332274 x)). Qed.
Lemma lem2332276 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2332277 (x : int) : (term279 x) = term280.
Proof. exact (MK_COMB (@lem2332276) (@lem2332275 x)). Qed.
Lemma lem2332278 (y : int) : (term281 y) = (term282 y).
Proof. exact (@lem1982759 (term115 y) (real_of_int y) term125). Qed.
Lemma lem2332279 (y : int) : (term283 y) = (term263 y).
Proof. exact (@lem1982713 term125 (real_of_int y)). Qed.
Lemma lem2332281 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2332282 : term37 = term127.
Proof. exact (@lem2332281 term38). Qed.
Lemma lem2332284 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2332285 : term125 = term130.
Proof. exact (@lem2332284 term38). Qed.
Lemma lem2332286 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2332287 : term264 = term265.
Proof. exact (MK_COMB (@lem2332286) (@lem2332285)). Qed.
Lemma lem2332288 : term266 = term267.
Proof. exact (MK_COMB (@lem2332287) (@lem2332282)). Qed.
Lemma lem2332289 : term268.
Proof. exact (@lem1981473 term125 term37 term37 term37 term118 term37). Qed.
Lemma lem2332291 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332292 : term174 = term175.
Proof. exact (@lem2332291 (NUMERAL 0) term38). Qed.
Lemma lem2332293 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332294 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332295 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332294 h1) (fun h1 : term175 = True => @lem2332293)). Qed.
Lemma lem2332296 : term175 = True.
Proof. exact (EQ_MP (@lem2332295) (@lem2332293)). Qed.
Lemma lem2332297 : term174 = True.
Proof. exact (TRANS (@lem2332292) (@lem2332296)). Qed.
Lemma lem2332298 : True = term174.
Proof. exact (SYM (@lem2332297)). Qed.
Lemma lem2332299 : term174.
Proof. exact (EQ_MP (@lem2332298) (@lem0)). Qed.
Lemma lem2332300 : term269.
Proof. exact (@lem2332289 (@lem2332299)). Qed.
Lemma lem2332302 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332303 : term174 = term175.
Proof. exact (@lem2332302 (NUMERAL 0) term38). Qed.
Lemma lem2332304 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332305 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332306 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332305 h1) (fun h1 : term175 = True => @lem2332304)). Qed.
Lemma lem2332307 : term175 = True.
Proof. exact (EQ_MP (@lem2332306) (@lem2332304)). Qed.
Lemma lem2332308 : term174 = True.
Proof. exact (TRANS (@lem2332303) (@lem2332307)). Qed.
Lemma lem2332309 : True = term174.
Proof. exact (SYM (@lem2332308)). Qed.
Lemma lem2332310 : term174.
Proof. exact (EQ_MP (@lem2332309) (@lem0)). Qed.
Lemma lem2332311 : term270.
Proof. exact (@lem2332300 (@lem2332310)). Qed.
Lemma lem2332313 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332314 : term174 = term175.
Proof. exact (@lem2332313 (NUMERAL 0) term38). Qed.
Lemma lem2332315 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332316 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332317 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332316 h1) (fun h1 : term175 = True => @lem2332315)). Qed.
Lemma lem2332318 : term175 = True.
Proof. exact (EQ_MP (@lem2332317) (@lem2332315)). Qed.
Lemma lem2332319 : term174 = True.
Proof. exact (TRANS (@lem2332314) (@lem2332318)). Qed.
Lemma lem2332320 : True = term174.
Proof. exact (SYM (@lem2332319)). Qed.
Lemma lem2332321 : term174.
Proof. exact (EQ_MP (@lem2332320) (@lem0)). Qed.
Lemma lem2332322 : term271.
Proof. exact (@lem2332311 (@lem2332321)). Qed.
Lemma lem2332324 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2332325 : term138 = term139.
Proof. exact (@lem2332324 term38 term38). Qed.
Lemma lem2332326 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332327 : term141 = term38.
Proof. exact (EQ_MP (@lem2332326) (@lem940073)). Qed.
Lemma lem2332328 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332329 : term139 = term37.
Proof. exact (MK_COMB (@lem2332328) (@lem2332327)). Qed.
Lemma lem2332330 : term138 = term37.
Proof. exact (TRANS (@lem2332325) (@lem2332329)). Qed.
Lemma lem2332332 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2332333 : term133 = term144.
Proof. exact (@lem2332332 term38 term38). Qed.
Lemma lem2332334 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332335 : term141 = term38.
Proof. exact (EQ_MP (@lem2332334) (@lem940073)). Qed.
Lemma lem2332336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332337 : term139 = term37.
Proof. exact (MK_COMB (@lem2332336) (@lem2332335)). Qed.
Lemma lem2332338 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2332339 : term144 = term125.
Proof. exact (MK_COMB (@lem2332338) (@lem2332337)). Qed.
Lemma lem2332340 : term133 = term125.
Proof. exact (TRANS (@lem2332333) (@lem2332339)). Qed.
Lemma lem2332341 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2332342 : term272 = term264.
Proof. exact (MK_COMB (@lem2332341) (@lem2332340)). Qed.
Lemma lem2332343 : term273 = term266.
Proof. exact (MK_COMB (@lem2332342) (@lem2332330)). Qed.
Lemma lem2332345 (m : nat) : (term274 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2332346 : term266 = term118.
Proof. exact (@lem2332345 term38). Qed.
Lemma lem2332347 : term273 = term118.
Proof. exact (TRANS (@lem2332343) (@lem2332346)). Qed.
Lemma lem2332348 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2332349 : term275 = term184.
Proof. exact (MK_COMB (@lem2332348) (@lem2332347)). Qed.
Lemma lem2332350 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem2332351 : term276 = term186.
Proof. exact (MK_COMB (@lem2332349) (@lem2332350)). Qed.
Lemma lem2332353 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2332354 : term186 = term118.
Proof. exact (@lem2332353 term38). Qed.
Lemma lem2332355 : term276 = term118.
Proof. exact (TRANS (@lem2332351) (@lem2332354)). Qed.
Lemma lem2332357 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2332358 : term138 = term139.
Proof. exact (@lem2332357 term38 term38). Qed.
Lemma lem2332359 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332360 : term141 = term38.
Proof. exact (EQ_MP (@lem2332359) (@lem940073)). Qed.
Lemma lem2332361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332362 : term139 = term37.
Proof. exact (MK_COMB (@lem2332361) (@lem2332360)). Qed.
Lemma lem2332363 : term138 = term37.
Proof. exact (TRANS (@lem2332358) (@lem2332362)). Qed.
Lemma lem2332364 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2332365 : term188 = term186.
Proof. exact (MK_COMB (@lem2332364) (@lem2332363)). Qed.
Lemma lem2332367 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2332368 : term186 = term118.
Proof. exact (@lem2332367 term38). Qed.
Lemma lem2332369 : term188 = term118.
Proof. exact (TRANS (@lem2332365) (@lem2332368)). Qed.
Lemma lem2332370 : term118 = term188.
Proof. exact (SYM (@lem2332369)). Qed.
Lemma lem2332371 : term276 = term188.
Proof. exact (TRANS (@lem2332355) (@lem2332370)). Qed.
Lemma lem2332372 : term267 = term189.
Proof. exact (@lem2332322 (@lem2332371)). Qed.
Lemma lem2332373 : term266 = term189.
Proof. exact (TRANS (@lem2332288) (@lem2332372)). Qed.
Lemma lem2332375 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2332376 : term189 = term118.
Proof. exact (@lem2332375 term118). Qed.
Lemma lem2332377 : term266 = term118.
Proof. exact (TRANS (@lem2332373) (@lem2332376)). Qed.
Lemma lem2332378 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2332379 : term277 = term184.
Proof. exact (MK_COMB (@lem2332378) (@lem2332377)). Qed.
Lemma lem2332380 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2332381 (y : int) : (term263 y) = (term278 y).
Proof. exact (MK_COMB (@lem2332379) (@lem2332380 y)). Qed.
Lemma lem2332382 (y : int) : (term283 y) = (term278 y).
Proof. exact (TRANS (@lem2332279 y) (@lem2332381 y)). Qed.
Lemma lem2332383 (y : int) : (term278 y) = term118.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2332384 (y : int) : (term283 y) = term118.
Proof. exact (TRANS (@lem2332382 y) (@lem2332383 y)). Qed.
Lemma lem2332385 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2332386 (y : int) : (term284 y) = term280.
Proof. exact (MK_COMB (@lem2332385) (@lem2332384 y)). Qed.
Lemma lem2332387 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem2332388 (y : int) : (term282 y) = term285.
Proof. exact (MK_COMB (@lem2332386 y) (@lem2332387)). Qed.
Lemma lem2332389 (y : int) : (term281 y) = term285.
Proof. exact (TRANS (@lem2332278 y) (@lem2332388 y)). Qed.
Lemma lem2332390 : term285 = term125.
Proof. exact (@lem1982721 term125). Qed.
Lemma lem2332391 (y : int) : (term281 y) = term125.
Proof. exact (TRANS (@lem2332389 y) (@lem2332390)). Qed.
Lemma lem2332392 (x : int) (y : int) : (term261 x y) = term285.
Proof. exact (MK_COMB (@lem2332277 x) (@lem2332391 y)). Qed.
Lemma lem2332393 (x : int) (y : int) : (term260 x y) = term285.
Proof. exact (TRANS (@lem2332169 x y) (@lem2332392 x y)). Qed.
Lemma lem2332394 : term285 = term125.
Proof. exact (@lem1982721 term125). Qed.
Lemma lem2332395 (x : int) (y : int) : (term260 x y) = term125.
Proof. exact (TRANS (@lem2332393 x y) (@lem2332394)). Qed.
Lemma lem2332396 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2332397 (x : int) (y : int) : (term286 x y) = term287.
Proof. exact (MK_COMB (@lem2332396) (@lem2332395 x y)). Qed.
Lemma lem2332398 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem2332399 (x : int) (y : int) : (term259 x y) = term288.
Proof. exact (MK_COMB (@lem2332397 x y) (@lem2332398)). Qed.
Lemma lem2332400 (x : int) (y : int) (h1 : term193 x y) : term288.
Proof. exact (EQ_MP (@lem2332399 x y) (@lem2332168 x y h1)). Qed.
Lemma lem2332402 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2332403 : term288 = term289.
Proof. exact (@lem2332402 term118 term125). Qed.
Lemma lem2332405 (x : nat) : (term128 x) = (term129 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2332406 : term125 = term130.
Proof. exact (@lem2332405 term38). Qed.
Lemma lem2332408 (x : nat) : (real_of_num x) = (term126 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2332409 : term118 = term189.
Proof. exact (@lem2332408 (NUMERAL 0)). Qed.
Lemma lem2332410 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2332411 : term290 = term291.
Proof. exact (MK_COMB (@lem2332410) (@lem2332409)). Qed.
Lemma lem2332412 : term289 = term292.
Proof. exact (MK_COMB (@lem2332411) (@lem2332406)). Qed.
Lemma lem2332413 : term293.
Proof. exact (@lem1980026 term118 term37 term125 term37). Qed.
Lemma lem2332415 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332416 : term174 = term175.
Proof. exact (@lem2332415 (NUMERAL 0) term38). Qed.
Lemma lem2332417 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332418 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332419 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332418 h1) (fun h1 : term175 = True => @lem2332417)). Qed.
Lemma lem2332420 : term175 = True.
Proof. exact (EQ_MP (@lem2332419) (@lem2332417)). Qed.
Lemma lem2332421 : term174 = True.
Proof. exact (TRANS (@lem2332416) (@lem2332420)). Qed.
Lemma lem2332422 : True = term174.
Proof. exact (SYM (@lem2332421)). Qed.
Lemma lem2332423 : term174.
Proof. exact (EQ_MP (@lem2332422) (@lem0)). Qed.
Lemma lem2332424 : term294.
Proof. exact (@lem2332413 (@lem2332423)). Qed.
Lemma lem2332426 (m : nat) (n : nat) : (term173 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2332427 : term174 = term175.
Proof. exact (@lem2332426 (NUMERAL 0) term38). Qed.
Lemma lem2332428 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332429 (h1 : term176 = (BIT1 0)) : term175 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2332430 : (term176 = (BIT1 0)) = (term175 = True).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332429 h1) (fun h1 : term175 = True => @lem2332428)). Qed.
Lemma lem2332431 : term175 = True.
Proof. exact (EQ_MP (@lem2332430) (@lem2332428)). Qed.
Lemma lem2332432 : term174 = True.
Proof. exact (TRANS (@lem2332427) (@lem2332431)). Qed.
Lemma lem2332433 : True = term174.
Proof. exact (SYM (@lem2332432)). Qed.
Lemma lem2332434 : term174.
Proof. exact (EQ_MP (@lem2332433) (@lem0)). Qed.
Lemma lem2332435 : term292 = term295.
Proof. exact (@lem2332424 (@lem2332434)). Qed.
Lemma lem2332437 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2332438 : term133 = term144.
Proof. exact (@lem2332437 term38 term38). Qed.
Lemma lem2332439 : (term140 = (BIT1 0)) = (term141 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2332440 : term141 = term38.
Proof. exact (EQ_MP (@lem2332439) (@lem940073)). Qed.
Lemma lem2332441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2332442 : term139 = term37.
Proof. exact (MK_COMB (@lem2332441) (@lem2332440)). Qed.
Lemma lem2332443 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2332444 : term144 = term125.
Proof. exact (MK_COMB (@lem2332443) (@lem2332442)). Qed.
Lemma lem2332445 : term133 = term125.
Proof. exact (TRANS (@lem2332438) (@lem2332444)). Qed.
Lemma lem2332447 (x : nat) : (term187 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2332448 : term186 = term118.
Proof. exact (@lem2332447 term38). Qed.
Lemma lem2332449 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2332450 : term296 = term290.
Proof. exact (MK_COMB (@lem2332449) (@lem2332448)). Qed.
Lemma lem2332451 : term295 = term289.
Proof. exact (MK_COMB (@lem2332450) (@lem2332445)). Qed.
Lemma lem2332453 (m : nat) (n : nat) : (term297 m n) = (term298 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2332454 : term289 = term299.
Proof. exact (@lem2332453 (NUMERAL 0) term38). Qed.
Lemma lem2332455 : term176 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2332456 (h1 : term176 = (BIT1 0)) : (term38 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2332457 : (term176 = (BIT1 0)) = ((term38 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term176 = (BIT1 0) => @lem2332456 h1) (fun h1 : (term38 = (NUMERAL 0)) = False => @lem2332455)). Qed.
Lemma lem2332458 : (term38 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2332457) (@lem2332455)). Qed.
Lemma lem2332459 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2332460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2332461 : term300 = (and True).
Proof. exact (MK_COMB (@lem2332460) (@lem2332459)). Qed.
Lemma lem2332462 : term299 = (True /\ False).
Proof. exact (MK_COMB (@lem2332461) (@lem2332458)). Qed.
Lemma lem2332464 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2332465 : term299 = False.
Proof. exact (TRANS (@lem2332462) (@lem2332464)). Qed.
Lemma lem2332466 : term289 = False.
Proof. exact (TRANS (@lem2332454) (@lem2332465)). Qed.
Lemma lem2332467 : term295 = False.
Proof. exact (TRANS (@lem2332451) (@lem2332466)). Qed.
Lemma lem2332468 : term292 = False.
Proof. exact (TRANS (@lem2332435) (@lem2332467)). Qed.
Lemma lem2332469 : term289 = False.
Proof. exact (TRANS (@lem2332412) (@lem2332468)). Qed.
Lemma lem2332470 : term288 = False.
Proof. exact (TRANS (@lem2332403) (@lem2332469)). Qed.
Lemma lem2332471 (x : int) (y : int) (h1 : term193 x y) : False.
Proof. exact (EQ_MP (@lem2332470) (@lem2332400 x y h1)). Qed.
Lemma lem2332472 (x : int) (y : int) (h1 : term232 x y) : False.
Proof. exact (or_elim (@lem2331553 x y h1) (fun h0 : term155 x y => @lem2332012 x y h0) (fun h0 : term193 x y => @lem2332471 x y h0)). Qed.
Lemma lem2332474 (x : int) (y : int) (h1 : term232 x y) : term232 x y.
Proof. exact (h1). Qed.
Lemma lem2332475 (x : int) (y : int) (h1 : term232 x y) : (term232 x y) = False.
Proof. exact (prop_ext (fun h2 : term232 x y => @lem2332472 x y h1) (fun h2 : False => @lem2332474 x y h1)). Qed.
Lemma lem2332476 (x : int) (y : int) (h1 : term232 x y) : False.
Proof. exact (EQ_MP (@lem2332475 x y h1) (@lem2332474 x y h1)). Qed.
Lemma lem2332477 (x : int) (h1 : term235 x) : term235 x.
Proof. exact (h1). Qed.
Lemma lem2332478 (x : int) (h1 : term235 x) : False.
Proof. exact (ex_elim (@lem2332477 x h1) (fun y : int => fun h0 : term234 x y => @lem2332476 x y h0)). Qed.
Lemma lem2332479 (h1 : term237) : term237.
Proof. exact (h1). Qed.
Lemma lem2332480 (h1 : term237) : False.
Proof. exact (ex_elim (@lem2332479 h1) (fun x : int => fun h0 : term236 x => @lem2332478 x h0)). Qed.
Lemma lem2332481 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem2332482 (h1 : term64) : term237.
Proof. exact (EQ_MP (@lem2331543) (@lem2332481 h1)). Qed.
Lemma lem2332483 (h1 : term64) : term237 = False.
Proof. exact (prop_ext (fun h2 : term237 => @lem2332480 h2) (fun h2 : False => @lem2332482 h1)). Qed.
Lemma lem2332484 (h1 : term64) : False.
Proof. exact (EQ_MP (@lem2332483 h1) (@lem2332482 h1)). Qed.
Lemma lem2332485 : term301.
Proof. exact (fun h0 : term64 => @lem2332484 h0). Qed.
Lemma lem2332486 : term302.
Proof. exact (@lem1386578 term303). Qed.
Lemma lem2332489 : term303.
Proof. exact (@lem2332486 (@lem2332485)). Qed.
Lemma lem2332490 : term62 = term15.
Proof. exact (SYM (@lem2330664)). Qed.
Lemma lem2332491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2332492 : term303 = term0.
Proof. exact (MK_COMB (@lem2332491) (@lem2332490)). Qed.
Lemma lem2332493 : term0.
Proof. exact (EQ_MP (@lem2332492) (@lem2332489)). Qed.
Lemma lem2332494 : term1.
Proof. exact (EQ_MP (@lem2330501) (@lem2332493)). Qed.
