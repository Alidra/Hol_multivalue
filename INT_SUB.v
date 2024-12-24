Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_term_abbrevs.
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
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318497_spec.
Require Import thm2318526_spec.
Require Import thm2318527_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318541_spec.
Require Import thm2318542_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2318605 : term0 = term1.
Proof. exact (@lem2318604 term1). Qed.
Lemma lem2318620 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2318621 (x : int) : (term4 x) = (term5 x).
Proof. exact (@lem2318620 (term6 x)). Qed.
Lemma lem2318622 (x : int) (y : int) : (term7 x y) = ((int_sub x y) = (term8 x y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem2318623 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2318625 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2318623) (@lem2318622 x y)). Qed.
Lemma lem2318626 (x : int) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : int => @lem2318625 x y)). Qed.
Lemma lem2318627 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318628 (x : int) : (term5 x) = (term13 x).
Proof. exact (MK_COMB (@lem2318627) (@lem2318626 x)). Qed.
Lemma lem2318629 (x : int) : (term4 x) = (term13 x).
Proof. exact (TRANS (@lem2318621 x) (@lem2318628 x)). Qed.
Lemma lem2318630 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2318631 : term14 = term15.
Proof. exact (@lem2318630 term16). Qed.
Lemma lem2318632 (x : int) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem2318633 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2318634 (x : int) : (term19 x) = (term4 x).
Proof. exact (MK_COMB (@lem2318633) (@lem2318632 x)). Qed.
Lemma lem2318635 (x : int) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem2318634 x) (@lem2318629 x)). Qed.
Lemma lem2318636 : term20 = term21.
Proof. exact (fun_ext (fun x : int => @lem2318635 x)). Qed.
Lemma lem2318637 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318638 : term15 = term22.
Proof. exact (MK_COMB (@lem2318637) (@lem2318636)). Qed.
Lemma lem2318640 : term14 = term22.
Proof. exact (TRANS (@lem2318631) (@lem2318638)). Qed.
Lemma lem2318643 (x : int) (y : int) : (term10 x y) = (term10 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem2318644 (x : int) : (term12 x) = (term12 x).
Proof. exact (fun_ext (fun y : int => @lem2318643 x y)). Qed.
Lemma lem2318645 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318646 (x : int) : (term13 x) = (term13 x).
Proof. exact (MK_COMB (@lem2318645) (@lem2318644 x)). Qed.
Lemma lem2318647 : term21 = term21.
Proof. exact (fun_ext (fun x : int => @lem2318646 x)). Qed.
Lemma lem2318648 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318649 : term22 = term22.
Proof. exact (MK_COMB (@lem2318648) (@lem2318647)). Qed.
Lemma lem2318650 : term14 = term22.
Proof. exact (TRANS (@lem2318640) (@lem2318649)). Qed.
Lemma lem2318652 (y : int) (x : int) : (term23 x y) = (term24 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2318653 (x : int) (y : int) : (term10 x y) = (term25 x y).
Proof. exact (@lem2318652 (term8 x y) (int_sub x y)). Qed.
Lemma lem2318655 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2318656 (x : int) (y : int) : (term27 x y) = (term28 x y).
Proof. exact (@lem2318655 (term29 x y) (term8 x y)). Qed.
Lemma lem2318658 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2318659 (x : int) (y : int) : (term32 x y) = (term33 x y).
Proof. exact (@lem2318658 (int_sub x y) term34). Qed.
Lemma lem2318661 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2318662 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2318663 (x : int) (y : int) : (term37 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem2318662) (@lem2318661 x y)). Qed.
Lemma lem2318665 (n : nat) : (term39 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2318666 : term40 = term41.
Proof. exact (@lem2318665 term42). Qed.
Lemma lem2318667 (x : int) (y : int) : (term33 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem2318663 x y) (@lem2318666)). Qed.
Lemma lem2318668 (x : int) (y : int) : (term32 x y) = (term43 x y).
Proof. exact (TRANS (@lem2318659 x y) (@lem2318667 x y)). Qed.
Lemma lem2318669 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2318670 (x : int) (y : int) : (term44 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem2318669) (@lem2318668 x y)). Qed.
Lemma lem2318672 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2318673 (x : int) (y : int) : (term46 x y) = (term47 x y).
Proof. exact (@lem2318672 x (int_neg y)). Qed.
Lemma lem2318675 (x : int) : (term48 x) = (term49 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2318676 (y : int) : (term48 y) = (term49 y).
Proof. exact (@lem2318675 y). Qed.
Lemma lem2318677 (x : int) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem2318678 (x : int) (y : int) : (term47 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem2318677 x) (@lem2318676 y)). Qed.
Lemma lem2318679 (x : int) (y : int) : (term46 x y) = (term51 x y).
Proof. exact (TRANS (@lem2318673 x y) (@lem2318678 x y)). Qed.
Lemma lem2318680 (x : int) (y : int) : (term28 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem2318670 x y) (@lem2318679 x y)). Qed.
Lemma lem2318681 (x : int) (y : int) : (term27 x y) = (term52 x y).
Proof. exact (TRANS (@lem2318656 x y) (@lem2318680 x y)). Qed.
Lemma lem2318682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318683 (x : int) (y : int) : (term53 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem2318682) (@lem2318681 x y)). Qed.
Lemma lem2318685 (x : int) (y : int) : (int_le x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2318686 (x : int) (y : int) : (term55 x y) = (term56 x y).
Proof. exact (@lem2318685 (term57 x y) (int_sub x y)). Qed.
Lemma lem2318688 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2318689 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (@lem2318688 (term8 x y) term34). Qed.
Lemma lem2318691 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2318692 (x : int) (y : int) : (term46 x y) = (term47 x y).
Proof. exact (@lem2318691 x (int_neg y)). Qed.
Lemma lem2318694 (x : int) : (term48 x) = (term49 x).
Proof. exact (EQ_MP (@lem2318542 x) (@lem2318541 x)). Qed.
Lemma lem2318695 (y : int) : (term48 y) = (term49 y).
Proof. exact (@lem2318694 y). Qed.
Lemma lem2318696 (x : int) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem2318697 (x : int) (y : int) : (term47 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem2318696 x) (@lem2318695 y)). Qed.
Lemma lem2318698 (x : int) (y : int) : (term46 x y) = (term51 x y).
Proof. exact (TRANS (@lem2318692 x y) (@lem2318697 x y)). Qed.
Lemma lem2318699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2318700 (x : int) (y : int) : (term60 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem2318699) (@lem2318698 x y)). Qed.
Lemma lem2318702 (n : nat) : (term39 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2318703 : term40 = term41.
Proof. exact (@lem2318702 term42). Qed.
Lemma lem2318704 (x : int) (y : int) : (term59 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem2318700 x y) (@lem2318703)). Qed.
Lemma lem2318705 (x : int) (y : int) : (term58 x y) = (term62 x y).
Proof. exact (TRANS (@lem2318689 x y) (@lem2318704 x y)). Qed.
Lemma lem2318706 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2318707 (x : int) (y : int) : (term63 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem2318706) (@lem2318705 x y)). Qed.
Lemma lem2318709 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2318710 (x : int) (y : int) : (term56 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem2318707 x y) (@lem2318709 x y)). Qed.
Lemma lem2318711 (x : int) (y : int) : (term55 x y) = (term65 x y).
Proof. exact (TRANS (@lem2318686 x y) (@lem2318710 x y)). Qed.
Lemma lem2318712 (x : int) (y : int) : (term25 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem2318683 x y) (@lem2318711 x y)). Qed.
Lemma lem2318713 (x : int) (y : int) : (term10 x y) = (term66 x y).
Proof. exact (TRANS (@lem2318653 x y) (@lem2318712 x y)). Qed.
Lemma lem2318714 (x : int) : (term12 x) = (term67 x).
Proof. exact (fun_ext (fun y : int => @lem2318713 x y)). Qed.
Lemma lem2318715 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318716 (x : int) : (term13 x) = (term68 x).
Proof. exact (MK_COMB (@lem2318715) (@lem2318714 x)). Qed.
Lemma lem2318717 : term21 = term69.
Proof. exact (fun_ext (fun x : int => @lem2318716 x)). Qed.
Lemma lem2318718 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318719 : term22 = term70.
Proof. exact (MK_COMB (@lem2318718) (@lem2318717)). Qed.
Lemma lem2318720 : term14 = term70.
Proof. exact (TRANS (@lem2318650) (@lem2318719)). Qed.
Lemma lem2318724 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2318725 : term72 = term70.
Proof. exact (@lem2318724 term70). Qed.
Lemma lem2318731 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2318732 (P : int -> Prop) (Q : int -> Prop) : (term75 P Q) = (term76 P Q).
Proof. exact (@lem2318731 int P Q). Qed.
Lemma lem2318733 (x : int) : (term77 x) = (term78 x).
Proof. exact (@lem2318732 (term79 x) (term80 x)). Qed.
Lemma lem2318734 (x : int) (y : int) : (term81 x y) = (term52 x y).
Proof. exact (eq_refl (term81 x y)). Qed.
Lemma lem2318735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318736 (x : int) (y : int) : (term82 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem2318735) (@lem2318734 x y)). Qed.
Lemma lem2318737 (x : int) (y : int) : (term83 x y) = (term65 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem2318738 (x : int) (y : int) : (term84 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem2318736 x y) (@lem2318737 x y)). Qed.
Lemma lem2318739 (x : int) : (term85 x) = (term67 x).
Proof. exact (fun_ext (fun y : int => @lem2318738 x y)). Qed.
Lemma lem2318740 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318741 (x : int) : (term77 x) = (term68 x).
Proof. exact (MK_COMB (@lem2318740) (@lem2318739 x)). Qed.
Lemma lem2318742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318743 (x : int) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem2318742) (@lem2318741 x)). Qed.
Lemma lem2318744 (x : int) (y : int) : (term81 x y) = (term52 x y).
Proof. exact (eq_refl (term81 x y)). Qed.
Lemma lem2318745 (x : int) : (term88 x) = (term79 x).
Proof. exact (fun_ext (fun y : int => @lem2318744 x y)). Qed.
Lemma lem2318746 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318747 (x : int) : (term89 x) = (term90 x).
Proof. exact (MK_COMB (@lem2318746) (@lem2318745 x)). Qed.
Lemma lem2318748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318749 (x : int) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem2318748) (@lem2318747 x)). Qed.
Lemma lem2318750 (x : int) (y : int) : (term83 x y) = (term65 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem2318751 (x : int) : (term93 x) = (term80 x).
Proof. exact (fun_ext (fun y : int => @lem2318750 x y)). Qed.
Lemma lem2318752 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318753 (x : int) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem2318752) (@lem2318751 x)). Qed.
Lemma lem2318754 (x : int) : (term78 x) = (term96 x).
Proof. exact (MK_COMB (@lem2318749 x) (@lem2318753 x)). Qed.
Lemma lem2318755 (x : int) : ((term77 x) = (term78 x)) = ((term68 x) = (term96 x)).
Proof. exact (MK_COMB (@lem2318743 x) (@lem2318754 x)). Qed.
Lemma lem2318756 (x : int) : (term68 x) = (term96 x).
Proof. exact (EQ_MP (@lem2318755 x) (@lem2318733 x)). Qed.
Lemma lem2318767 : term69 = term97.
Proof. exact (fun_ext (fun x : int => @lem2318756 x)). Qed.
Lemma lem2318768 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318769 : term70 = term98.
Proof. exact (MK_COMB (@lem2318768) (@lem2318767)). Qed.
Lemma lem2318771 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2318772 (P : int -> Prop) (Q : int -> Prop) : (term75 P Q) = (term76 P Q).
Proof. exact (@lem2318771 int P Q). Qed.
Lemma lem2318773 : term99 = term100.
Proof. exact (@lem2318772 term101 term102). Qed.
Lemma lem2318774 (x : int) : (term103 x) = (term90 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem2318775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318776 (x : int) : (term104 x) = (term92 x).
Proof. exact (MK_COMB (@lem2318775) (@lem2318774 x)). Qed.
Lemma lem2318777 (x : int) : (term105 x) = (term95 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2318778 (x : int) : (term106 x) = (term96 x).
Proof. exact (MK_COMB (@lem2318776 x) (@lem2318777 x)). Qed.
Lemma lem2318779 : term107 = term97.
Proof. exact (fun_ext (fun x : int => @lem2318778 x)). Qed.
Lemma lem2318780 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318781 : term99 = term98.
Proof. exact (MK_COMB (@lem2318780) (@lem2318779)). Qed.
Lemma lem2318782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318783 : term108 = term109.
Proof. exact (MK_COMB (@lem2318782) (@lem2318781)). Qed.
Lemma lem2318784 (x : int) : (term103 x) = (term90 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem2318785 : term110 = term101.
Proof. exact (fun_ext (fun x : int => @lem2318784 x)). Qed.
Lemma lem2318786 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318787 : term111 = term112.
Proof. exact (MK_COMB (@lem2318786) (@lem2318785)). Qed.
Lemma lem2318788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318789 : term113 = term114.
Proof. exact (MK_COMB (@lem2318788) (@lem2318787)). Qed.
Lemma lem2318790 (x : int) : (term105 x) = (term95 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2318791 : term115 = term102.
Proof. exact (fun_ext (fun x : int => @lem2318790 x)). Qed.
Lemma lem2318792 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318793 : term116 = term117.
Proof. exact (MK_COMB (@lem2318792) (@lem2318791)). Qed.
Lemma lem2318794 : term100 = term118.
Proof. exact (MK_COMB (@lem2318789) (@lem2318793)). Qed.
Lemma lem2318795 : (term99 = term100) = (term98 = term118).
Proof. exact (MK_COMB (@lem2318783) (@lem2318794)). Qed.
Lemma lem2318796 : term98 = term118.
Proof. exact (EQ_MP (@lem2318795) (@lem2318773)). Qed.
Lemma lem2318815 : term70 = term118.
Proof. exact (TRANS (@lem2318769) (@lem2318796)). Qed.
Lemma lem2318817 : term72 = term118.
Proof. exact (TRANS (@lem2318725) (@lem2318815)). Qed.
Lemma lem2318818 (x : int) (y : int) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem2318819 (x : int) : (term79 x) = (term79 x).
Proof. exact (fun_ext (fun y : int => @lem2318818 x y)). Qed.
Lemma lem2318820 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318821 (x : int) : (term90 x) = (term90 x).
Proof. exact (MK_COMB (@lem2318820) (@lem2318819 x)). Qed.
Lemma lem2318822 : term101 = term101.
Proof. exact (fun_ext (fun x : int => @lem2318821 x)). Qed.
Lemma lem2318823 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318824 : term112 = term112.
Proof. exact (MK_COMB (@lem2318823) (@lem2318822)). Qed.
Lemma lem2318825 (x : int) (y : int) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem2318826 (x : int) : (term80 x) = (term80 x).
Proof. exact (fun_ext (fun y : int => @lem2318825 x y)). Qed.
Lemma lem2318827 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318828 (x : int) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2318827) (@lem2318826 x)). Qed.
Lemma lem2318829 : term102 = term102.
Proof. exact (fun_ext (fun x : int => @lem2318828 x)). Qed.
Lemma lem2318830 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318831 : term117 = term117.
Proof. exact (MK_COMB (@lem2318830) (@lem2318829)). Qed.
Lemma lem2318832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318833 : term114 = term114.
Proof. exact (MK_COMB (@lem2318832) (@lem2318824)). Qed.
Lemma lem2318834 : term118 = term118.
Proof. exact (MK_COMB (@lem2318833) (@lem2318831)). Qed.
Lemma lem2318835 : term72 = term118.
Proof. exact (TRANS (@lem2318817) (@lem2318834)). Qed.
Lemma lem2318836 (x : int) (y : int) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem2318837 (x : int) : (term79 x) = (term79 x).
Proof. exact (fun_ext (fun y : int => @lem2318836 x y)). Qed.
Lemma lem2318838 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318839 (x : int) : (term90 x) = (term90 x).
Proof. exact (MK_COMB (@lem2318838) (@lem2318837 x)). Qed.
Lemma lem2318840 : term101 = term101.
Proof. exact (fun_ext (fun x : int => @lem2318839 x)). Qed.
Lemma lem2318841 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318842 : term112 = term112.
Proof. exact (MK_COMB (@lem2318841) (@lem2318840)). Qed.
Lemma lem2318843 (x : int) (y : int) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem2318844 (x : int) : (term80 x) = (term80 x).
Proof. exact (fun_ext (fun y : int => @lem2318843 x y)). Qed.
Lemma lem2318845 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318846 (x : int) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2318845) (@lem2318844 x)). Qed.
Lemma lem2318847 : term102 = term102.
Proof. exact (fun_ext (fun x : int => @lem2318846 x)). Qed.
Lemma lem2318848 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2318849 : term117 = term117.
Proof. exact (MK_COMB (@lem2318848) (@lem2318847)). Qed.
Lemma lem2318850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2318851 : term114 = term114.
Proof. exact (MK_COMB (@lem2318850) (@lem2318842)). Qed.
Lemma lem2318852 : term118 = term118.
Proof. exact (MK_COMB (@lem2318851) (@lem2318849)). Qed.
Lemma lem2318853 : term72 = term118.
Proof. exact (TRANS (@lem2318835) (@lem2318852)). Qed.
Lemma lem2318854 (x : int) (y : int) : (term52 x y) = (term119 x y).
Proof. exact (@lem1988287 (term51 x y) (term43 x y)). Qed.
Lemma lem2318855 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem2318868 (x : int) (y : int) : (term36 x y) = (term120 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2318869 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2318870 (x : int) (y : int) : (term38 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem2318869) (@lem2318868 x y)). Qed.
Lemma lem2318871 (x : int) (y : int) : (term43 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem2318870 x y) (@lem2318855)). Qed.
Lemma lem2318876 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (@lem1982755 (real_of_int x) (term124 y) term41). Qed.
Lemma lem2318877 (x : int) (y : int) : (term43 x y) = (term123 x y).
Proof. exact (TRANS (@lem2318871 x y) (@lem2318876 x y)). Qed.
Lemma lem2318884 (y : int) : (term49 y) = (term124 y).
Proof. exact (@lem1982785 (real_of_int y)). Qed.
Lemma lem2318887 (x : int) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem2318890 (x : int) (y : int) : (term51 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem2318887 x) (@lem2318884 y)). Qed.
Lemma lem2318891 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2318892 (x : int) (y : int) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem2318891) (@lem2318890 x y)). Qed.
Lemma lem2318893 (x : int) (y : int) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem2318892 x y) (@lem2318877 x y)). Qed.
Lemma lem2318894 (x : int) (y : int) : (term128 x y) = (term129 x y).
Proof. exact (@lem1982792 (term120 x y) (term123 x y)). Qed.
Lemma lem2318895 (x : int) (y : int) : (term130 x y) = (term131 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term133 y)). Qed.
Lemma lem2318896 (y : int) : (term134 y) = (term135 y).
Proof. exact (@lem1982781 (term124 y) term132 term41). Qed.
Lemma lem2318898 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2318899 : term41 = term137.
Proof. exact (@lem2318898 term42). Qed.
Lemma lem2318901 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2318902 : term132 = term140.
Proof. exact (@lem2318901 term42). Qed.
Lemma lem2318903 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2318904 : term141 = term142.
Proof. exact (MK_COMB (@lem2318903) (@lem2318902)). Qed.
Lemma lem2318905 : term143 = term144.
Proof. exact (MK_COMB (@lem2318904) (@lem2318899)). Qed.
Lemma lem2318906 : term144 = term145.
Proof. exact (@lem1981613 term132 term41 term41 term41). Qed.
Lemma lem2318908 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2318909 : term148 = term149.
Proof. exact (@lem2318908 term42 term42). Qed.
Lemma lem2318910 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2318911 : term151 = term42.
Proof. exact (EQ_MP (@lem2318910) (@lem940073)). Qed.
Lemma lem2318912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2318913 : term149 = term41.
Proof. exact (MK_COMB (@lem2318912) (@lem2318911)). Qed.
Lemma lem2318914 : term148 = term41.
Proof. exact (TRANS (@lem2318909) (@lem2318913)). Qed.
Lemma lem2318916 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2318917 : term143 = term154.
Proof. exact (@lem2318916 term42 term42). Qed.
Lemma lem2318918 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2318919 : term151 = term42.
Proof. exact (EQ_MP (@lem2318918) (@lem940073)). Qed.
Lemma lem2318920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2318921 : term149 = term41.
Proof. exact (MK_COMB (@lem2318920) (@lem2318919)). Qed.
Lemma lem2318922 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2318923 : term154 = term132.
Proof. exact (MK_COMB (@lem2318922) (@lem2318921)). Qed.
Lemma lem2318924 : term143 = term132.
Proof. exact (TRANS (@lem2318917) (@lem2318923)). Qed.
Lemma lem2318925 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2318926 : term155 = term156.
Proof. exact (MK_COMB (@lem2318925) (@lem2318924)). Qed.
Lemma lem2318927 : term145 = term140.
Proof. exact (MK_COMB (@lem2318926) (@lem2318914)). Qed.
Lemma lem2318928 : term144 = term140.
Proof. exact (TRANS (@lem2318906) (@lem2318927)). Qed.
Lemma lem2318929 : term143 = term140.
Proof. exact (TRANS (@lem2318905) (@lem2318928)). Qed.
Lemma lem2318931 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2318932 : term140 = term132.
Proof. exact (@lem2318931 term132). Qed.
Lemma lem2318933 : term143 = term132.
Proof. exact (TRANS (@lem2318929) (@lem2318932)). Qed.
Lemma lem2318934 (y : int) : (term158 y) = (term159 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2318936 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2318937 : term132 = term140.
Proof. exact (@lem2318936 term42). Qed.
Lemma lem2318939 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2318940 : term132 = term140.
Proof. exact (@lem2318939 term42). Qed.
Lemma lem2318941 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2318942 : term141 = term142.
Proof. exact (MK_COMB (@lem2318941) (@lem2318940)). Qed.
Lemma lem2318943 : term160 = term161.
Proof. exact (MK_COMB (@lem2318942) (@lem2318937)). Qed.
Lemma lem2318944 : term161 = term162.
Proof. exact (@lem1981613 term132 term132 term41 term41). Qed.
Lemma lem2318946 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2318947 : term148 = term149.
Proof. exact (@lem2318946 term42 term42). Qed.
Lemma lem2318948 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2318949 : term151 = term42.
Proof. exact (EQ_MP (@lem2318948) (@lem940073)). Qed.
Lemma lem2318950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2318951 : term149 = term41.
Proof. exact (MK_COMB (@lem2318950) (@lem2318949)). Qed.
Lemma lem2318952 : term148 = term41.
Proof. exact (TRANS (@lem2318947) (@lem2318951)). Qed.
Lemma lem2318954 (m : nat) (n : nat) : (term163 m n) = (term147 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2318955 : term160 = term149.
Proof. exact (@lem2318954 term42 term42). Qed.
Lemma lem2318956 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2318957 : term151 = term42.
Proof. exact (EQ_MP (@lem2318956) (@lem940073)). Qed.
Lemma lem2318958 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2318959 : term149 = term41.
Proof. exact (MK_COMB (@lem2318958) (@lem2318957)). Qed.
Lemma lem2318960 : term160 = term41.
Proof. exact (TRANS (@lem2318955) (@lem2318959)). Qed.
Lemma lem2318961 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2318962 : term164 = term165.
Proof. exact (MK_COMB (@lem2318961) (@lem2318960)). Qed.
Lemma lem2318963 : term162 = term137.
Proof. exact (MK_COMB (@lem2318962) (@lem2318952)). Qed.
Lemma lem2318964 : term161 = term137.
Proof. exact (TRANS (@lem2318944) (@lem2318963)). Qed.
Lemma lem2318965 : term160 = term137.
Proof. exact (TRANS (@lem2318943) (@lem2318964)). Qed.
Lemma lem2318967 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2318968 : term137 = term41.
Proof. exact (@lem2318967 term41). Qed.
Lemma lem2318969 : term160 = term41.
Proof. exact (TRANS (@lem2318965) (@lem2318968)). Qed.
Lemma lem2318970 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2318971 : term166 = term167.
Proof. exact (MK_COMB (@lem2318970) (@lem2318969)). Qed.
Lemma lem2318972 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2318973 (y : int) : (term159 y) = (term168 y).
Proof. exact (MK_COMB (@lem2318971) (@lem2318972 y)). Qed.
Lemma lem2318974 (y : int) : (term158 y) = (term168 y).
Proof. exact (TRANS (@lem2318934 y) (@lem2318973 y)). Qed.
Lemma lem2318975 (y : int) : (term168 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2318976 (y : int) : (term158 y) = (real_of_int y).
Proof. exact (TRANS (@lem2318974 y) (@lem2318975 y)). Qed.
Lemma lem2318977 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2318978 (y : int) : (term169 y) = (term50 y).
Proof. exact (MK_COMB (@lem2318977) (@lem2318976 y)). Qed.
Lemma lem2318979 (y : int) : (term135 y) = (term170 y).
Proof. exact (MK_COMB (@lem2318978 y) (@lem2318933)). Qed.
Lemma lem2318980 (y : int) : (term134 y) = (term170 y).
Proof. exact (TRANS (@lem2318896 y) (@lem2318979 y)). Qed.
Lemma lem2318983 (x : int) : (term171 x) = (term171 x).
Proof. exact (eq_refl (term171 x)). Qed.
Lemma lem2318984 (x : int) (y : int) : (term131 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem2318983 x) (@lem2318980 y)). Qed.
Lemma lem2318985 (x : int) (y : int) : (term130 x y) = (term172 x y).
Proof. exact (TRANS (@lem2318895 x y) (@lem2318984 x y)). Qed.
Lemma lem2318986 (x : int) (y : int) : (term121 x y) = (term121 x y).
Proof. exact (eq_refl (term121 x y)). Qed.
Lemma lem2318987 (x : int) (y : int) : (term129 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem2318986 x y) (@lem2318985 x y)). Qed.
Lemma lem2318988 (x : int) (y : int) : (term173 x y) = (term174 x y).
Proof. exact (@lem1982753 (real_of_int x) (term124 x) (term124 y) (term170 y)). Qed.
Lemma lem2318989 (x : int) : (term175 x) = (term176 x).
Proof. exact (@lem1982715 term132 (real_of_int x)). Qed.
Lemma lem2318991 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2318992 : term41 = term137.
Proof. exact (@lem2318991 term42). Qed.
Lemma lem2318994 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2318995 : term132 = term140.
Proof. exact (@lem2318994 term42). Qed.
Lemma lem2318996 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2318997 : term177 = term178.
Proof. exact (MK_COMB (@lem2318996) (@lem2318995)). Qed.
Lemma lem2318998 : term179 = term180.
Proof. exact (MK_COMB (@lem2318997) (@lem2318992)). Qed.
Lemma lem2318999 : term181.
Proof. exact (@lem1981473 term132 term41 term41 term41 term182 term41). Qed.
Lemma lem2319001 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319002 : term184 = term185.
Proof. exact (@lem2319001 (NUMERAL 0) term42). Qed.
Lemma lem2319003 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319004 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319005 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319004 h1) (fun h1 : term185 = True => @lem2319003)). Qed.
Lemma lem2319006 : term185 = True.
Proof. exact (EQ_MP (@lem2319005) (@lem2319003)). Qed.
Lemma lem2319007 : term184 = True.
Proof. exact (TRANS (@lem2319002) (@lem2319006)). Qed.
Lemma lem2319008 : True = term184.
Proof. exact (SYM (@lem2319007)). Qed.
Lemma lem2319009 : term184.
Proof. exact (EQ_MP (@lem2319008) (@lem0)). Qed.
Lemma lem2319010 : term187.
Proof. exact (@lem2318999 (@lem2319009)). Qed.
Lemma lem2319012 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319013 : term184 = term185.
Proof. exact (@lem2319012 (NUMERAL 0) term42). Qed.
Lemma lem2319014 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319015 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319016 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319015 h1) (fun h1 : term185 = True => @lem2319014)). Qed.
Lemma lem2319017 : term185 = True.
Proof. exact (EQ_MP (@lem2319016) (@lem2319014)). Qed.
Lemma lem2319018 : term184 = True.
Proof. exact (TRANS (@lem2319013) (@lem2319017)). Qed.
Lemma lem2319019 : True = term184.
Proof. exact (SYM (@lem2319018)). Qed.
Lemma lem2319020 : term184.
Proof. exact (EQ_MP (@lem2319019) (@lem0)). Qed.
Lemma lem2319021 : term188.
Proof. exact (@lem2319010 (@lem2319020)). Qed.
Lemma lem2319023 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319024 : term184 = term185.
Proof. exact (@lem2319023 (NUMERAL 0) term42). Qed.
Lemma lem2319025 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319026 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319027 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319026 h1) (fun h1 : term185 = True => @lem2319025)). Qed.
Lemma lem2319028 : term185 = True.
Proof. exact (EQ_MP (@lem2319027) (@lem2319025)). Qed.
Lemma lem2319029 : term184 = True.
Proof. exact (TRANS (@lem2319024) (@lem2319028)). Qed.
Lemma lem2319030 : True = term184.
Proof. exact (SYM (@lem2319029)). Qed.
Lemma lem2319031 : term184.
Proof. exact (EQ_MP (@lem2319030) (@lem0)). Qed.
Lemma lem2319032 : term189.
Proof. exact (@lem2319021 (@lem2319031)). Qed.
Lemma lem2319034 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319035 : term148 = term149.
Proof. exact (@lem2319034 term42 term42). Qed.
Lemma lem2319036 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319037 : term151 = term42.
Proof. exact (EQ_MP (@lem2319036) (@lem940073)). Qed.
Lemma lem2319038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319039 : term149 = term41.
Proof. exact (MK_COMB (@lem2319038) (@lem2319037)). Qed.
Lemma lem2319040 : term148 = term41.
Proof. exact (TRANS (@lem2319035) (@lem2319039)). Qed.
Lemma lem2319042 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2319043 : term143 = term154.
Proof. exact (@lem2319042 term42 term42). Qed.
Lemma lem2319044 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319045 : term151 = term42.
Proof. exact (EQ_MP (@lem2319044) (@lem940073)). Qed.
Lemma lem2319046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319047 : term149 = term41.
Proof. exact (MK_COMB (@lem2319046) (@lem2319045)). Qed.
Lemma lem2319048 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2319049 : term154 = term132.
Proof. exact (MK_COMB (@lem2319048) (@lem2319047)). Qed.
Lemma lem2319050 : term143 = term132.
Proof. exact (TRANS (@lem2319043) (@lem2319049)). Qed.
Lemma lem2319051 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319052 : term190 = term177.
Proof. exact (MK_COMB (@lem2319051) (@lem2319050)). Qed.
Lemma lem2319053 : term191 = term179.
Proof. exact (MK_COMB (@lem2319052) (@lem2319040)). Qed.
Lemma lem2319055 (m : nat) : (term192 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2319056 : term179 = term182.
Proof. exact (@lem2319055 term42). Qed.
Lemma lem2319057 : term191 = term182.
Proof. exact (TRANS (@lem2319053) (@lem2319056)). Qed.
Lemma lem2319058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319059 : term193 = term194.
Proof. exact (MK_COMB (@lem2319058) (@lem2319057)). Qed.
Lemma lem2319060 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem2319061 : term195 = term196.
Proof. exact (MK_COMB (@lem2319059) (@lem2319060)). Qed.
Lemma lem2319063 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319064 : term196 = term182.
Proof. exact (@lem2319063 term42). Qed.
Lemma lem2319065 : term195 = term182.
Proof. exact (TRANS (@lem2319061) (@lem2319064)). Qed.
Lemma lem2319067 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319068 : term148 = term149.
Proof. exact (@lem2319067 term42 term42). Qed.
Lemma lem2319069 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319070 : term151 = term42.
Proof. exact (EQ_MP (@lem2319069) (@lem940073)). Qed.
Lemma lem2319071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319072 : term149 = term41.
Proof. exact (MK_COMB (@lem2319071) (@lem2319070)). Qed.
Lemma lem2319073 : term148 = term41.
Proof. exact (TRANS (@lem2319068) (@lem2319072)). Qed.
Lemma lem2319074 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem2319075 : term198 = term196.
Proof. exact (MK_COMB (@lem2319074) (@lem2319073)). Qed.
Lemma lem2319077 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319078 : term196 = term182.
Proof. exact (@lem2319077 term42). Qed.
Lemma lem2319079 : term198 = term182.
Proof. exact (TRANS (@lem2319075) (@lem2319078)). Qed.
Lemma lem2319080 : term182 = term198.
Proof. exact (SYM (@lem2319079)). Qed.
Lemma lem2319081 : term195 = term198.
Proof. exact (TRANS (@lem2319065) (@lem2319080)). Qed.
Lemma lem2319082 : term180 = term199.
Proof. exact (@lem2319032 (@lem2319081)). Qed.
Lemma lem2319083 : term179 = term199.
Proof. exact (TRANS (@lem2318998) (@lem2319082)). Qed.
Lemma lem2319085 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2319086 : term199 = term182.
Proof. exact (@lem2319085 term182). Qed.
Lemma lem2319087 : term179 = term182.
Proof. exact (TRANS (@lem2319083) (@lem2319086)). Qed.
Lemma lem2319088 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319089 : term200 = term194.
Proof. exact (MK_COMB (@lem2319088) (@lem2319087)). Qed.
Lemma lem2319090 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2319091 (x : int) : (term176 x) = (term201 x).
Proof. exact (MK_COMB (@lem2319089) (@lem2319090 x)). Qed.
Lemma lem2319092 (x : int) : (term175 x) = (term201 x).
Proof. exact (TRANS (@lem2318989 x) (@lem2319091 x)). Qed.
Lemma lem2319093 (x : int) : (term201 x) = term182.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2319094 (x : int) : (term175 x) = term182.
Proof. exact (TRANS (@lem2319092 x) (@lem2319093 x)). Qed.
Lemma lem2319095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319096 (x : int) : (term202 x) = term203.
Proof. exact (MK_COMB (@lem2319095) (@lem2319094 x)). Qed.
Lemma lem2319097 (y : int) : (term204 y) = (term205 y).
Proof. exact (@lem1982763 (term124 y) (real_of_int y) term132). Qed.
Lemma lem2319098 (y : int) : (term206 y) = (term176 y).
Proof. exact (@lem1982713 term132 (real_of_int y)). Qed.
Lemma lem2319100 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2319101 : term41 = term137.
Proof. exact (@lem2319100 term42). Qed.
Lemma lem2319103 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319104 : term132 = term140.
Proof. exact (@lem2319103 term42). Qed.
Lemma lem2319105 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319106 : term177 = term178.
Proof. exact (MK_COMB (@lem2319105) (@lem2319104)). Qed.
Lemma lem2319107 : term179 = term180.
Proof. exact (MK_COMB (@lem2319106) (@lem2319101)). Qed.
Lemma lem2319108 : term181.
Proof. exact (@lem1981473 term132 term41 term41 term41 term182 term41). Qed.
Lemma lem2319110 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319111 : term184 = term185.
Proof. exact (@lem2319110 (NUMERAL 0) term42). Qed.
Lemma lem2319112 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319113 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319114 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319113 h1) (fun h1 : term185 = True => @lem2319112)). Qed.
Lemma lem2319115 : term185 = True.
Proof. exact (EQ_MP (@lem2319114) (@lem2319112)). Qed.
Lemma lem2319116 : term184 = True.
Proof. exact (TRANS (@lem2319111) (@lem2319115)). Qed.
Lemma lem2319117 : True = term184.
Proof. exact (SYM (@lem2319116)). Qed.
Lemma lem2319118 : term184.
Proof. exact (EQ_MP (@lem2319117) (@lem0)). Qed.
Lemma lem2319119 : term187.
Proof. exact (@lem2319108 (@lem2319118)). Qed.
Lemma lem2319121 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319122 : term184 = term185.
Proof. exact (@lem2319121 (NUMERAL 0) term42). Qed.
Lemma lem2319123 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319124 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319125 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319124 h1) (fun h1 : term185 = True => @lem2319123)). Qed.
Lemma lem2319126 : term185 = True.
Proof. exact (EQ_MP (@lem2319125) (@lem2319123)). Qed.
Lemma lem2319127 : term184 = True.
Proof. exact (TRANS (@lem2319122) (@lem2319126)). Qed.
Lemma lem2319128 : True = term184.
Proof. exact (SYM (@lem2319127)). Qed.
Lemma lem2319129 : term184.
Proof. exact (EQ_MP (@lem2319128) (@lem0)). Qed.
Lemma lem2319130 : term188.
Proof. exact (@lem2319119 (@lem2319129)). Qed.
Lemma lem2319132 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319133 : term184 = term185.
Proof. exact (@lem2319132 (NUMERAL 0) term42). Qed.
Lemma lem2319134 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319135 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319136 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319135 h1) (fun h1 : term185 = True => @lem2319134)). Qed.
Lemma lem2319137 : term185 = True.
Proof. exact (EQ_MP (@lem2319136) (@lem2319134)). Qed.
Lemma lem2319138 : term184 = True.
Proof. exact (TRANS (@lem2319133) (@lem2319137)). Qed.
Lemma lem2319139 : True = term184.
Proof. exact (SYM (@lem2319138)). Qed.
Lemma lem2319140 : term184.
Proof. exact (EQ_MP (@lem2319139) (@lem0)). Qed.
Lemma lem2319141 : term189.
Proof. exact (@lem2319130 (@lem2319140)). Qed.
Lemma lem2319143 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319144 : term148 = term149.
Proof. exact (@lem2319143 term42 term42). Qed.
Lemma lem2319145 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319146 : term151 = term42.
Proof. exact (EQ_MP (@lem2319145) (@lem940073)). Qed.
Lemma lem2319147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319148 : term149 = term41.
Proof. exact (MK_COMB (@lem2319147) (@lem2319146)). Qed.
Lemma lem2319149 : term148 = term41.
Proof. exact (TRANS (@lem2319144) (@lem2319148)). Qed.
Lemma lem2319151 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2319152 : term143 = term154.
Proof. exact (@lem2319151 term42 term42). Qed.
Lemma lem2319153 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319154 : term151 = term42.
Proof. exact (EQ_MP (@lem2319153) (@lem940073)). Qed.
Lemma lem2319155 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319156 : term149 = term41.
Proof. exact (MK_COMB (@lem2319155) (@lem2319154)). Qed.
Lemma lem2319157 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2319158 : term154 = term132.
Proof. exact (MK_COMB (@lem2319157) (@lem2319156)). Qed.
Lemma lem2319159 : term143 = term132.
Proof. exact (TRANS (@lem2319152) (@lem2319158)). Qed.
Lemma lem2319160 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319161 : term190 = term177.
Proof. exact (MK_COMB (@lem2319160) (@lem2319159)). Qed.
Lemma lem2319162 : term191 = term179.
Proof. exact (MK_COMB (@lem2319161) (@lem2319149)). Qed.
Lemma lem2319164 (m : nat) : (term192 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2319165 : term179 = term182.
Proof. exact (@lem2319164 term42). Qed.
Lemma lem2319166 : term191 = term182.
Proof. exact (TRANS (@lem2319162) (@lem2319165)). Qed.
Lemma lem2319167 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319168 : term193 = term194.
Proof. exact (MK_COMB (@lem2319167) (@lem2319166)). Qed.
Lemma lem2319169 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem2319170 : term195 = term196.
Proof. exact (MK_COMB (@lem2319168) (@lem2319169)). Qed.
Lemma lem2319172 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319173 : term196 = term182.
Proof. exact (@lem2319172 term42). Qed.
Lemma lem2319174 : term195 = term182.
Proof. exact (TRANS (@lem2319170) (@lem2319173)). Qed.
Lemma lem2319176 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319177 : term148 = term149.
Proof. exact (@lem2319176 term42 term42). Qed.
Lemma lem2319178 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319179 : term151 = term42.
Proof. exact (EQ_MP (@lem2319178) (@lem940073)). Qed.
Lemma lem2319180 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319181 : term149 = term41.
Proof. exact (MK_COMB (@lem2319180) (@lem2319179)). Qed.
Lemma lem2319182 : term148 = term41.
Proof. exact (TRANS (@lem2319177) (@lem2319181)). Qed.
Lemma lem2319183 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem2319184 : term198 = term196.
Proof. exact (MK_COMB (@lem2319183) (@lem2319182)). Qed.
Lemma lem2319186 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319187 : term196 = term182.
Proof. exact (@lem2319186 term42). Qed.
Lemma lem2319188 : term198 = term182.
Proof. exact (TRANS (@lem2319184) (@lem2319187)). Qed.
Lemma lem2319189 : term182 = term198.
Proof. exact (SYM (@lem2319188)). Qed.
Lemma lem2319190 : term195 = term198.
Proof. exact (TRANS (@lem2319174) (@lem2319189)). Qed.
Lemma lem2319191 : term180 = term199.
Proof. exact (@lem2319141 (@lem2319190)). Qed.
Lemma lem2319192 : term179 = term199.
Proof. exact (TRANS (@lem2319107) (@lem2319191)). Qed.
Lemma lem2319194 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2319195 : term199 = term182.
Proof. exact (@lem2319194 term182). Qed.
Lemma lem2319196 : term179 = term182.
Proof. exact (TRANS (@lem2319192) (@lem2319195)). Qed.
Lemma lem2319197 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319198 : term200 = term194.
Proof. exact (MK_COMB (@lem2319197) (@lem2319196)). Qed.
Lemma lem2319199 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2319200 (y : int) : (term176 y) = (term201 y).
Proof. exact (MK_COMB (@lem2319198) (@lem2319199 y)). Qed.
Lemma lem2319201 (y : int) : (term206 y) = (term201 y).
Proof. exact (TRANS (@lem2319098 y) (@lem2319200 y)). Qed.
Lemma lem2319202 (y : int) : (term201 y) = term182.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2319203 (y : int) : (term206 y) = term182.
Proof. exact (TRANS (@lem2319201 y) (@lem2319202 y)). Qed.
Lemma lem2319204 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319205 (y : int) : (term207 y) = term203.
Proof. exact (MK_COMB (@lem2319204) (@lem2319203 y)). Qed.
Lemma lem2319206 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2319207 (y : int) : (term205 y) = term208.
Proof. exact (MK_COMB (@lem2319205 y) (@lem2319206)). Qed.
Lemma lem2319208 (y : int) : (term204 y) = term208.
Proof. exact (TRANS (@lem2319097 y) (@lem2319207 y)). Qed.
Lemma lem2319209 : term208 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2319210 (y : int) : (term204 y) = term132.
Proof. exact (TRANS (@lem2319208 y) (@lem2319209)). Qed.
Lemma lem2319211 (x : int) (y : int) : (term174 x y) = term208.
Proof. exact (MK_COMB (@lem2319096 x) (@lem2319210 y)). Qed.
Lemma lem2319212 (x : int) (y : int) : (term173 x y) = term208.
Proof. exact (TRANS (@lem2318988 x y) (@lem2319211 x y)). Qed.
Lemma lem2319213 : term208 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2319214 (x : int) (y : int) : (term173 x y) = term132.
Proof. exact (TRANS (@lem2319212 x y) (@lem2319213)). Qed.
Lemma lem2319215 (x : int) (y : int) : (term129 x y) = term132.
Proof. exact (TRANS (@lem2318987 x y) (@lem2319214 x y)). Qed.
Lemma lem2319216 (x : int) (y : int) : (term128 x y) = term132.
Proof. exact (TRANS (@lem2318894 x y) (@lem2319215 x y)). Qed.
Lemma lem2319217 (x : int) (y : int) : (term127 x y) = term132.
Proof. exact (TRANS (@lem2318893 x y) (@lem2319216 x y)). Qed.
Lemma lem2319218 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2319219 (x : int) (y : int) : (term209 x y) = term210.
Proof. exact (MK_COMB (@lem2319218) (@lem2319217 x y)). Qed.
Lemma lem2319220 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2319221 (x : int) (y : int) : (term119 x y) = term211.
Proof. exact (MK_COMB (@lem2319219 x y) (@lem2319220)). Qed.
Lemma lem2319222 (x : int) (y : int) : (term52 x y) = term211.
Proof. exact (TRANS (@lem2318854 x y) (@lem2319221 x y)). Qed.
Lemma lem2319223 (x : int) : (term79 x) = term212.
Proof. exact (fun_ext (fun y : int => @lem2319222 x y)). Qed.
Lemma lem2319224 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319225 (x : int) : (term90 x) = term213.
Proof. exact (MK_COMB (@lem2319224) (@lem2319223 x)). Qed.
Lemma lem2319226 : term101 = term214.
Proof. exact (fun_ext (fun x : int => @lem2319225 x)). Qed.
Lemma lem2319227 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319228 : term112 = term215.
Proof. exact (MK_COMB (@lem2319227) (@lem2319226)). Qed.
Lemma lem2319229 (x : int) (y : int) : (term65 x y) = (term216 x y).
Proof. exact (@lem1988287 (term36 x y) (term62 x y)). Qed.
Lemma lem2319230 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem2319237 (y : int) : (term49 y) = (term124 y).
Proof. exact (@lem1982785 (real_of_int y)). Qed.
Lemma lem2319240 (x : int) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem2319243 (x : int) (y : int) : (term51 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem2319240 x) (@lem2319237 y)). Qed.
Lemma lem2319244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319245 (x : int) (y : int) : (term61 x y) = (term121 x y).
Proof. exact (MK_COMB (@lem2319244) (@lem2319243 x y)). Qed.
Lemma lem2319246 (x : int) (y : int) : (term62 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem2319245 x y) (@lem2319230)). Qed.
Lemma lem2319251 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (@lem1982755 (real_of_int x) (term124 y) term41). Qed.
Lemma lem2319252 (x : int) (y : int) : (term62 x y) = (term123 x y).
Proof. exact (TRANS (@lem2319246 x y) (@lem2319251 x y)). Qed.
Lemma lem2319265 (x : int) (y : int) : (term36 x y) = (term120 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2319266 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2319267 (x : int) (y : int) : (term217 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem2319266) (@lem2319265 x y)). Qed.
Lemma lem2319268 (x : int) (y : int) : (term218 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem2319267 x y) (@lem2319252 x y)). Qed.
Lemma lem2319269 (x : int) (y : int) : (term128 x y) = (term129 x y).
Proof. exact (@lem1982792 (term120 x y) (term123 x y)). Qed.
Lemma lem2319270 (x : int) (y : int) : (term130 x y) = (term131 x y).
Proof. exact (@lem1982781 (real_of_int x) term132 (term133 y)). Qed.
Lemma lem2319271 (y : int) : (term134 y) = (term135 y).
Proof. exact (@lem1982781 (term124 y) term132 term41). Qed.
Lemma lem2319273 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2319274 : term41 = term137.
Proof. exact (@lem2319273 term42). Qed.
Lemma lem2319276 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319277 : term132 = term140.
Proof. exact (@lem2319276 term42). Qed.
Lemma lem2319278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319279 : term141 = term142.
Proof. exact (MK_COMB (@lem2319278) (@lem2319277)). Qed.
Lemma lem2319280 : term143 = term144.
Proof. exact (MK_COMB (@lem2319279) (@lem2319274)). Qed.
Lemma lem2319281 : term144 = term145.
Proof. exact (@lem1981613 term132 term41 term41 term41). Qed.
Lemma lem2319283 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319284 : term148 = term149.
Proof. exact (@lem2319283 term42 term42). Qed.
Lemma lem2319285 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319286 : term151 = term42.
Proof. exact (EQ_MP (@lem2319285) (@lem940073)). Qed.
Lemma lem2319287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319288 : term149 = term41.
Proof. exact (MK_COMB (@lem2319287) (@lem2319286)). Qed.
Lemma lem2319289 : term148 = term41.
Proof. exact (TRANS (@lem2319284) (@lem2319288)). Qed.
Lemma lem2319291 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2319292 : term143 = term154.
Proof. exact (@lem2319291 term42 term42). Qed.
Lemma lem2319293 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319294 : term151 = term42.
Proof. exact (EQ_MP (@lem2319293) (@lem940073)). Qed.
Lemma lem2319295 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319296 : term149 = term41.
Proof. exact (MK_COMB (@lem2319295) (@lem2319294)). Qed.
Lemma lem2319297 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2319298 : term154 = term132.
Proof. exact (MK_COMB (@lem2319297) (@lem2319296)). Qed.
Lemma lem2319299 : term143 = term132.
Proof. exact (TRANS (@lem2319292) (@lem2319298)). Qed.
Lemma lem2319300 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2319301 : term155 = term156.
Proof. exact (MK_COMB (@lem2319300) (@lem2319299)). Qed.
Lemma lem2319302 : term145 = term140.
Proof. exact (MK_COMB (@lem2319301) (@lem2319289)). Qed.
Lemma lem2319303 : term144 = term140.
Proof. exact (TRANS (@lem2319281) (@lem2319302)). Qed.
Lemma lem2319304 : term143 = term140.
Proof. exact (TRANS (@lem2319280) (@lem2319303)). Qed.
Lemma lem2319306 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2319307 : term140 = term132.
Proof. exact (@lem2319306 term132). Qed.
Lemma lem2319308 : term143 = term132.
Proof. exact (TRANS (@lem2319304) (@lem2319307)). Qed.
Lemma lem2319309 (y : int) : (term158 y) = (term159 y).
Proof. exact (@lem1982749 term132 term132 (real_of_int y)). Qed.
Lemma lem2319311 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319312 : term132 = term140.
Proof. exact (@lem2319311 term42). Qed.
Lemma lem2319314 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319315 : term132 = term140.
Proof. exact (@lem2319314 term42). Qed.
Lemma lem2319316 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319317 : term141 = term142.
Proof. exact (MK_COMB (@lem2319316) (@lem2319315)). Qed.
Lemma lem2319318 : term160 = term161.
Proof. exact (MK_COMB (@lem2319317) (@lem2319312)). Qed.
Lemma lem2319319 : term161 = term162.
Proof. exact (@lem1981613 term132 term132 term41 term41). Qed.
Lemma lem2319321 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319322 : term148 = term149.
Proof. exact (@lem2319321 term42 term42). Qed.
Lemma lem2319323 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319324 : term151 = term42.
Proof. exact (EQ_MP (@lem2319323) (@lem940073)). Qed.
Lemma lem2319325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319326 : term149 = term41.
Proof. exact (MK_COMB (@lem2319325) (@lem2319324)). Qed.
Lemma lem2319327 : term148 = term41.
Proof. exact (TRANS (@lem2319322) (@lem2319326)). Qed.
Lemma lem2319329 (m : nat) (n : nat) : (term163 m n) = (term147 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2319330 : term160 = term149.
Proof. exact (@lem2319329 term42 term42). Qed.
Lemma lem2319331 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319332 : term151 = term42.
Proof. exact (EQ_MP (@lem2319331) (@lem940073)). Qed.
Lemma lem2319333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319334 : term149 = term41.
Proof. exact (MK_COMB (@lem2319333) (@lem2319332)). Qed.
Lemma lem2319335 : term160 = term41.
Proof. exact (TRANS (@lem2319330) (@lem2319334)). Qed.
Lemma lem2319336 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2319337 : term164 = term165.
Proof. exact (MK_COMB (@lem2319336) (@lem2319335)). Qed.
Lemma lem2319338 : term162 = term137.
Proof. exact (MK_COMB (@lem2319337) (@lem2319327)). Qed.
Lemma lem2319339 : term161 = term137.
Proof. exact (TRANS (@lem2319319) (@lem2319338)). Qed.
Lemma lem2319340 : term160 = term137.
Proof. exact (TRANS (@lem2319318) (@lem2319339)). Qed.
Lemma lem2319342 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2319343 : term137 = term41.
Proof. exact (@lem2319342 term41). Qed.
Lemma lem2319344 : term160 = term41.
Proof. exact (TRANS (@lem2319340) (@lem2319343)). Qed.
Lemma lem2319345 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319346 : term166 = term167.
Proof. exact (MK_COMB (@lem2319345) (@lem2319344)). Qed.
Lemma lem2319347 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2319348 (y : int) : (term159 y) = (term168 y).
Proof. exact (MK_COMB (@lem2319346) (@lem2319347 y)). Qed.
Lemma lem2319349 (y : int) : (term158 y) = (term168 y).
Proof. exact (TRANS (@lem2319309 y) (@lem2319348 y)). Qed.
Lemma lem2319350 (y : int) : (term168 y) = (real_of_int y).
Proof. exact (@lem1982709 (real_of_int y)). Qed.
Lemma lem2319351 (y : int) : (term158 y) = (real_of_int y).
Proof. exact (TRANS (@lem2319349 y) (@lem2319350 y)). Qed.
Lemma lem2319352 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319353 (y : int) : (term169 y) = (term50 y).
Proof. exact (MK_COMB (@lem2319352) (@lem2319351 y)). Qed.
Lemma lem2319354 (y : int) : (term135 y) = (term170 y).
Proof. exact (MK_COMB (@lem2319353 y) (@lem2319308)). Qed.
Lemma lem2319355 (y : int) : (term134 y) = (term170 y).
Proof. exact (TRANS (@lem2319271 y) (@lem2319354 y)). Qed.
Lemma lem2319358 (x : int) : (term171 x) = (term171 x).
Proof. exact (eq_refl (term171 x)). Qed.
Lemma lem2319359 (x : int) (y : int) : (term131 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem2319358 x) (@lem2319355 y)). Qed.
Lemma lem2319360 (x : int) (y : int) : (term130 x y) = (term172 x y).
Proof. exact (TRANS (@lem2319270 x y) (@lem2319359 x y)). Qed.
Lemma lem2319361 (x : int) (y : int) : (term121 x y) = (term121 x y).
Proof. exact (eq_refl (term121 x y)). Qed.
Lemma lem2319362 (x : int) (y : int) : (term129 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem2319361 x y) (@lem2319360 x y)). Qed.
Lemma lem2319363 (x : int) (y : int) : (term173 x y) = (term174 x y).
Proof. exact (@lem1982753 (real_of_int x) (term124 x) (term124 y) (term170 y)). Qed.
Lemma lem2319364 (x : int) : (term175 x) = (term176 x).
Proof. exact (@lem1982715 term132 (real_of_int x)). Qed.
Lemma lem2319366 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2319367 : term41 = term137.
Proof. exact (@lem2319366 term42). Qed.
Lemma lem2319369 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319370 : term132 = term140.
Proof. exact (@lem2319369 term42). Qed.
Lemma lem2319371 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319372 : term177 = term178.
Proof. exact (MK_COMB (@lem2319371) (@lem2319370)). Qed.
Lemma lem2319373 : term179 = term180.
Proof. exact (MK_COMB (@lem2319372) (@lem2319367)). Qed.
Lemma lem2319374 : term181.
Proof. exact (@lem1981473 term132 term41 term41 term41 term182 term41). Qed.
Lemma lem2319376 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319377 : term184 = term185.
Proof. exact (@lem2319376 (NUMERAL 0) term42). Qed.
Lemma lem2319378 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319379 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319380 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319379 h1) (fun h1 : term185 = True => @lem2319378)). Qed.
Lemma lem2319381 : term185 = True.
Proof. exact (EQ_MP (@lem2319380) (@lem2319378)). Qed.
Lemma lem2319382 : term184 = True.
Proof. exact (TRANS (@lem2319377) (@lem2319381)). Qed.
Lemma lem2319383 : True = term184.
Proof. exact (SYM (@lem2319382)). Qed.
Lemma lem2319384 : term184.
Proof. exact (EQ_MP (@lem2319383) (@lem0)). Qed.
Lemma lem2319385 : term187.
Proof. exact (@lem2319374 (@lem2319384)). Qed.
Lemma lem2319387 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319388 : term184 = term185.
Proof. exact (@lem2319387 (NUMERAL 0) term42). Qed.
Lemma lem2319389 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319390 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319391 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319390 h1) (fun h1 : term185 = True => @lem2319389)). Qed.
Lemma lem2319392 : term185 = True.
Proof. exact (EQ_MP (@lem2319391) (@lem2319389)). Qed.
Lemma lem2319393 : term184 = True.
Proof. exact (TRANS (@lem2319388) (@lem2319392)). Qed.
Lemma lem2319394 : True = term184.
Proof. exact (SYM (@lem2319393)). Qed.
Lemma lem2319395 : term184.
Proof. exact (EQ_MP (@lem2319394) (@lem0)). Qed.
Lemma lem2319396 : term188.
Proof. exact (@lem2319385 (@lem2319395)). Qed.
Lemma lem2319398 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319399 : term184 = term185.
Proof. exact (@lem2319398 (NUMERAL 0) term42). Qed.
Lemma lem2319400 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319401 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319402 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319401 h1) (fun h1 : term185 = True => @lem2319400)). Qed.
Lemma lem2319403 : term185 = True.
Proof. exact (EQ_MP (@lem2319402) (@lem2319400)). Qed.
Lemma lem2319404 : term184 = True.
Proof. exact (TRANS (@lem2319399) (@lem2319403)). Qed.
Lemma lem2319405 : True = term184.
Proof. exact (SYM (@lem2319404)). Qed.
Lemma lem2319406 : term184.
Proof. exact (EQ_MP (@lem2319405) (@lem0)). Qed.
Lemma lem2319407 : term189.
Proof. exact (@lem2319396 (@lem2319406)). Qed.
Lemma lem2319409 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319410 : term148 = term149.
Proof. exact (@lem2319409 term42 term42). Qed.
Lemma lem2319411 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319412 : term151 = term42.
Proof. exact (EQ_MP (@lem2319411) (@lem940073)). Qed.
Lemma lem2319413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319414 : term149 = term41.
Proof. exact (MK_COMB (@lem2319413) (@lem2319412)). Qed.
Lemma lem2319415 : term148 = term41.
Proof. exact (TRANS (@lem2319410) (@lem2319414)). Qed.
Lemma lem2319417 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2319418 : term143 = term154.
Proof. exact (@lem2319417 term42 term42). Qed.
Lemma lem2319419 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319420 : term151 = term42.
Proof. exact (EQ_MP (@lem2319419) (@lem940073)). Qed.
Lemma lem2319421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319422 : term149 = term41.
Proof. exact (MK_COMB (@lem2319421) (@lem2319420)). Qed.
Lemma lem2319423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2319424 : term154 = term132.
Proof. exact (MK_COMB (@lem2319423) (@lem2319422)). Qed.
Lemma lem2319425 : term143 = term132.
Proof. exact (TRANS (@lem2319418) (@lem2319424)). Qed.
Lemma lem2319426 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319427 : term190 = term177.
Proof. exact (MK_COMB (@lem2319426) (@lem2319425)). Qed.
Lemma lem2319428 : term191 = term179.
Proof. exact (MK_COMB (@lem2319427) (@lem2319415)). Qed.
Lemma lem2319430 (m : nat) : (term192 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2319431 : term179 = term182.
Proof. exact (@lem2319430 term42). Qed.
Lemma lem2319432 : term191 = term182.
Proof. exact (TRANS (@lem2319428) (@lem2319431)). Qed.
Lemma lem2319433 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319434 : term193 = term194.
Proof. exact (MK_COMB (@lem2319433) (@lem2319432)). Qed.
Lemma lem2319435 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem2319436 : term195 = term196.
Proof. exact (MK_COMB (@lem2319434) (@lem2319435)). Qed.
Lemma lem2319438 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319439 : term196 = term182.
Proof. exact (@lem2319438 term42). Qed.
Lemma lem2319440 : term195 = term182.
Proof. exact (TRANS (@lem2319436) (@lem2319439)). Qed.
Lemma lem2319442 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319443 : term148 = term149.
Proof. exact (@lem2319442 term42 term42). Qed.
Lemma lem2319444 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319445 : term151 = term42.
Proof. exact (EQ_MP (@lem2319444) (@lem940073)). Qed.
Lemma lem2319446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319447 : term149 = term41.
Proof. exact (MK_COMB (@lem2319446) (@lem2319445)). Qed.
Lemma lem2319448 : term148 = term41.
Proof. exact (TRANS (@lem2319443) (@lem2319447)). Qed.
Lemma lem2319449 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem2319450 : term198 = term196.
Proof. exact (MK_COMB (@lem2319449) (@lem2319448)). Qed.
Lemma lem2319452 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319453 : term196 = term182.
Proof. exact (@lem2319452 term42). Qed.
Lemma lem2319454 : term198 = term182.
Proof. exact (TRANS (@lem2319450) (@lem2319453)). Qed.
Lemma lem2319455 : term182 = term198.
Proof. exact (SYM (@lem2319454)). Qed.
Lemma lem2319456 : term195 = term198.
Proof. exact (TRANS (@lem2319440) (@lem2319455)). Qed.
Lemma lem2319457 : term180 = term199.
Proof. exact (@lem2319407 (@lem2319456)). Qed.
Lemma lem2319458 : term179 = term199.
Proof. exact (TRANS (@lem2319373) (@lem2319457)). Qed.
Lemma lem2319460 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2319461 : term199 = term182.
Proof. exact (@lem2319460 term182). Qed.
Lemma lem2319462 : term179 = term182.
Proof. exact (TRANS (@lem2319458) (@lem2319461)). Qed.
Lemma lem2319463 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319464 : term200 = term194.
Proof. exact (MK_COMB (@lem2319463) (@lem2319462)). Qed.
Lemma lem2319465 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2319466 (x : int) : (term176 x) = (term201 x).
Proof. exact (MK_COMB (@lem2319464) (@lem2319465 x)). Qed.
Lemma lem2319467 (x : int) : (term175 x) = (term201 x).
Proof. exact (TRANS (@lem2319364 x) (@lem2319466 x)). Qed.
Lemma lem2319468 (x : int) : (term201 x) = term182.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2319469 (x : int) : (term175 x) = term182.
Proof. exact (TRANS (@lem2319467 x) (@lem2319468 x)). Qed.
Lemma lem2319470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319471 (x : int) : (term202 x) = term203.
Proof. exact (MK_COMB (@lem2319470) (@lem2319469 x)). Qed.
Lemma lem2319472 (y : int) : (term204 y) = (term205 y).
Proof. exact (@lem1982763 (term124 y) (real_of_int y) term132). Qed.
Lemma lem2319473 (y : int) : (term206 y) = (term176 y).
Proof. exact (@lem1982713 term132 (real_of_int y)). Qed.
Lemma lem2319475 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2319476 : term41 = term137.
Proof. exact (@lem2319475 term42). Qed.
Lemma lem2319478 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319479 : term132 = term140.
Proof. exact (@lem2319478 term42). Qed.
Lemma lem2319480 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319481 : term177 = term178.
Proof. exact (MK_COMB (@lem2319480) (@lem2319479)). Qed.
Lemma lem2319482 : term179 = term180.
Proof. exact (MK_COMB (@lem2319481) (@lem2319476)). Qed.
Lemma lem2319483 : term181.
Proof. exact (@lem1981473 term132 term41 term41 term41 term182 term41). Qed.
Lemma lem2319485 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319486 : term184 = term185.
Proof. exact (@lem2319485 (NUMERAL 0) term42). Qed.
Lemma lem2319487 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319488 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319489 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319488 h1) (fun h1 : term185 = True => @lem2319487)). Qed.
Lemma lem2319490 : term185 = True.
Proof. exact (EQ_MP (@lem2319489) (@lem2319487)). Qed.
Lemma lem2319491 : term184 = True.
Proof. exact (TRANS (@lem2319486) (@lem2319490)). Qed.
Lemma lem2319492 : True = term184.
Proof. exact (SYM (@lem2319491)). Qed.
Lemma lem2319493 : term184.
Proof. exact (EQ_MP (@lem2319492) (@lem0)). Qed.
Lemma lem2319494 : term187.
Proof. exact (@lem2319483 (@lem2319493)). Qed.
Lemma lem2319496 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319497 : term184 = term185.
Proof. exact (@lem2319496 (NUMERAL 0) term42). Qed.
Lemma lem2319498 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319499 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319500 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319499 h1) (fun h1 : term185 = True => @lem2319498)). Qed.
Lemma lem2319501 : term185 = True.
Proof. exact (EQ_MP (@lem2319500) (@lem2319498)). Qed.
Lemma lem2319502 : term184 = True.
Proof. exact (TRANS (@lem2319497) (@lem2319501)). Qed.
Lemma lem2319503 : True = term184.
Proof. exact (SYM (@lem2319502)). Qed.
Lemma lem2319504 : term184.
Proof. exact (EQ_MP (@lem2319503) (@lem0)). Qed.
Lemma lem2319505 : term188.
Proof. exact (@lem2319494 (@lem2319504)). Qed.
Lemma lem2319507 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319508 : term184 = term185.
Proof. exact (@lem2319507 (NUMERAL 0) term42). Qed.
Lemma lem2319509 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319510 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319511 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319510 h1) (fun h1 : term185 = True => @lem2319509)). Qed.
Lemma lem2319512 : term185 = True.
Proof. exact (EQ_MP (@lem2319511) (@lem2319509)). Qed.
Lemma lem2319513 : term184 = True.
Proof. exact (TRANS (@lem2319508) (@lem2319512)). Qed.
Lemma lem2319514 : True = term184.
Proof. exact (SYM (@lem2319513)). Qed.
Lemma lem2319515 : term184.
Proof. exact (EQ_MP (@lem2319514) (@lem0)). Qed.
Lemma lem2319516 : term189.
Proof. exact (@lem2319505 (@lem2319515)). Qed.
Lemma lem2319518 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319519 : term148 = term149.
Proof. exact (@lem2319518 term42 term42). Qed.
Lemma lem2319520 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319521 : term151 = term42.
Proof. exact (EQ_MP (@lem2319520) (@lem940073)). Qed.
Lemma lem2319522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319523 : term149 = term41.
Proof. exact (MK_COMB (@lem2319522) (@lem2319521)). Qed.
Lemma lem2319524 : term148 = term41.
Proof. exact (TRANS (@lem2319519) (@lem2319523)). Qed.
Lemma lem2319526 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2319527 : term143 = term154.
Proof. exact (@lem2319526 term42 term42). Qed.
Lemma lem2319528 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319529 : term151 = term42.
Proof. exact (EQ_MP (@lem2319528) (@lem940073)). Qed.
Lemma lem2319530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319531 : term149 = term41.
Proof. exact (MK_COMB (@lem2319530) (@lem2319529)). Qed.
Lemma lem2319532 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2319533 : term154 = term132.
Proof. exact (MK_COMB (@lem2319532) (@lem2319531)). Qed.
Lemma lem2319534 : term143 = term132.
Proof. exact (TRANS (@lem2319527) (@lem2319533)). Qed.
Lemma lem2319535 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319536 : term190 = term177.
Proof. exact (MK_COMB (@lem2319535) (@lem2319534)). Qed.
Lemma lem2319537 : term191 = term179.
Proof. exact (MK_COMB (@lem2319536) (@lem2319524)). Qed.
Lemma lem2319539 (m : nat) : (term192 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2319540 : term179 = term182.
Proof. exact (@lem2319539 term42). Qed.
Lemma lem2319541 : term191 = term182.
Proof. exact (TRANS (@lem2319537) (@lem2319540)). Qed.
Lemma lem2319542 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319543 : term193 = term194.
Proof. exact (MK_COMB (@lem2319542) (@lem2319541)). Qed.
Lemma lem2319544 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem2319545 : term195 = term196.
Proof. exact (MK_COMB (@lem2319543) (@lem2319544)). Qed.
Lemma lem2319547 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319548 : term196 = term182.
Proof. exact (@lem2319547 term42). Qed.
Lemma lem2319549 : term195 = term182.
Proof. exact (TRANS (@lem2319545) (@lem2319548)). Qed.
Lemma lem2319551 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2319552 : term148 = term149.
Proof. exact (@lem2319551 term42 term42). Qed.
Lemma lem2319553 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319554 : term151 = term42.
Proof. exact (EQ_MP (@lem2319553) (@lem940073)). Qed.
Lemma lem2319555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319556 : term149 = term41.
Proof. exact (MK_COMB (@lem2319555) (@lem2319554)). Qed.
Lemma lem2319557 : term148 = term41.
Proof. exact (TRANS (@lem2319552) (@lem2319556)). Qed.
Lemma lem2319558 : term194 = term194.
Proof. exact (eq_refl term194). Qed.
Lemma lem2319559 : term198 = term196.
Proof. exact (MK_COMB (@lem2319558) (@lem2319557)). Qed.
Lemma lem2319561 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319562 : term196 = term182.
Proof. exact (@lem2319561 term42). Qed.
Lemma lem2319563 : term198 = term182.
Proof. exact (TRANS (@lem2319559) (@lem2319562)). Qed.
Lemma lem2319564 : term182 = term198.
Proof. exact (SYM (@lem2319563)). Qed.
Lemma lem2319565 : term195 = term198.
Proof. exact (TRANS (@lem2319549) (@lem2319564)). Qed.
Lemma lem2319566 : term180 = term199.
Proof. exact (@lem2319516 (@lem2319565)). Qed.
Lemma lem2319567 : term179 = term199.
Proof. exact (TRANS (@lem2319482) (@lem2319566)). Qed.
Lemma lem2319569 (x : real) : (term157 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2319570 : term199 = term182.
Proof. exact (@lem2319569 term182). Qed.
Lemma lem2319571 : term179 = term182.
Proof. exact (TRANS (@lem2319567) (@lem2319570)). Qed.
Lemma lem2319572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2319573 : term200 = term194.
Proof. exact (MK_COMB (@lem2319572) (@lem2319571)). Qed.
Lemma lem2319574 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2319575 (y : int) : (term176 y) = (term201 y).
Proof. exact (MK_COMB (@lem2319573) (@lem2319574 y)). Qed.
Lemma lem2319576 (y : int) : (term206 y) = (term201 y).
Proof. exact (TRANS (@lem2319473 y) (@lem2319575 y)). Qed.
Lemma lem2319577 (y : int) : (term201 y) = term182.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2319578 (y : int) : (term206 y) = term182.
Proof. exact (TRANS (@lem2319576 y) (@lem2319577 y)). Qed.
Lemma lem2319579 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2319580 (y : int) : (term207 y) = term203.
Proof. exact (MK_COMB (@lem2319579) (@lem2319578 y)). Qed.
Lemma lem2319581 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem2319582 (y : int) : (term205 y) = term208.
Proof. exact (MK_COMB (@lem2319580 y) (@lem2319581)). Qed.
Lemma lem2319583 (y : int) : (term204 y) = term208.
Proof. exact (TRANS (@lem2319472 y) (@lem2319582 y)). Qed.
Lemma lem2319584 : term208 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2319585 (y : int) : (term204 y) = term132.
Proof. exact (TRANS (@lem2319583 y) (@lem2319584)). Qed.
Lemma lem2319586 (x : int) (y : int) : (term174 x y) = term208.
Proof. exact (MK_COMB (@lem2319471 x) (@lem2319585 y)). Qed.
Lemma lem2319587 (x : int) (y : int) : (term173 x y) = term208.
Proof. exact (TRANS (@lem2319363 x y) (@lem2319586 x y)). Qed.
Lemma lem2319588 : term208 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem2319589 (x : int) (y : int) : (term173 x y) = term132.
Proof. exact (TRANS (@lem2319587 x y) (@lem2319588)). Qed.
Lemma lem2319590 (x : int) (y : int) : (term129 x y) = term132.
Proof. exact (TRANS (@lem2319362 x y) (@lem2319589 x y)). Qed.
Lemma lem2319591 (x : int) (y : int) : (term128 x y) = term132.
Proof. exact (TRANS (@lem2319269 x y) (@lem2319590 x y)). Qed.
Lemma lem2319592 (x : int) (y : int) : (term218 x y) = term132.
Proof. exact (TRANS (@lem2319268 x y) (@lem2319591 x y)). Qed.
Lemma lem2319593 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2319594 (x : int) (y : int) : (term219 x y) = term210.
Proof. exact (MK_COMB (@lem2319593) (@lem2319592 x y)). Qed.
Lemma lem2319595 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2319596 (x : int) (y : int) : (term216 x y) = term211.
Proof. exact (MK_COMB (@lem2319594 x y) (@lem2319595)). Qed.
Lemma lem2319597 (x : int) (y : int) : (term65 x y) = term211.
Proof. exact (TRANS (@lem2319229 x y) (@lem2319596 x y)). Qed.
Lemma lem2319598 (x : int) : (term80 x) = term212.
Proof. exact (fun_ext (fun y : int => @lem2319597 x y)). Qed.
Lemma lem2319599 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319600 (x : int) : (term95 x) = term213.
Proof. exact (MK_COMB (@lem2319599) (@lem2319598 x)). Qed.
Lemma lem2319601 : term102 = term214.
Proof. exact (fun_ext (fun x : int => @lem2319600 x)). Qed.
Lemma lem2319602 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2319603 : term117 = term215.
Proof. exact (MK_COMB (@lem2319602) (@lem2319601)). Qed.
Lemma lem2319604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2319605 : term114 = term220.
Proof. exact (MK_COMB (@lem2319604) (@lem2319228)). Qed.
Lemma lem2319606 : term118 = term221.
Proof. exact (MK_COMB (@lem2319605) (@lem2319603)). Qed.
Lemma lem2319607 : term72 = term221.
Proof. exact (TRANS (@lem2318853) (@lem2319606)). Qed.
Lemma lem2319609 {A : Type'} (t : Prop) : (term222 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2319610 (t : Prop) : (term223 t) = t.
Proof. exact (@lem2319609 int t). Qed.
Lemma lem2319611 : term215 = term213.
Proof. exact (@lem2319610 term213). Qed.
Lemma lem2319613 {A : Type'} (t : Prop) : (term222 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2319614 (t : Prop) : (term223 t) = t.
Proof. exact (@lem2319613 int t). Qed.
Lemma lem2319615 : term213 = term211.
Proof. exact (@lem2319614 term211). Qed.
Lemma lem2319616 : term215 = term211.
Proof. exact (TRANS (@lem2319611) (@lem2319615)). Qed.
Lemma lem2319617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2319618 : term220 = term224.
Proof. exact (MK_COMB (@lem2319617) (@lem2319616)). Qed.
Lemma lem2319620 {A : Type'} (t : Prop) : (term222 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2319621 (t : Prop) : (term223 t) = t.
Proof. exact (@lem2319620 int t). Qed.
Lemma lem2319622 : term215 = term213.
Proof. exact (@lem2319621 term213). Qed.
Lemma lem2319624 {A : Type'} (t : Prop) : (term222 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2319625 (t : Prop) : (term223 t) = t.
Proof. exact (@lem2319624 int t). Qed.
Lemma lem2319626 : term213 = term211.
Proof. exact (@lem2319625 term211). Qed.
Lemma lem2319627 : term215 = term211.
Proof. exact (TRANS (@lem2319622) (@lem2319626)). Qed.
Lemma lem2319630 : term221 = term225.
Proof. exact (MK_COMB (@lem2319618) (@lem2319627)). Qed.
Lemma lem2319639 : term72 = term225.
Proof. exact (TRANS (@lem2319607) (@lem2319630)). Qed.
Lemma lem2319649 (h1 : term225) : term225.
Proof. exact (h1). Qed.
Lemma lem2319650 (h1 : term211) : term211.
Proof. exact (h1). Qed.
Lemma lem2319652 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2319653 : term211 = term226.
Proof. exact (@lem2319652 term182 term132). Qed.
Lemma lem2319655 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319656 : term132 = term140.
Proof. exact (@lem2319655 term42). Qed.
Lemma lem2319658 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2319659 : term182 = term199.
Proof. exact (@lem2319658 (NUMERAL 0)). Qed.
Lemma lem2319660 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2319661 : term227 = term228.
Proof. exact (MK_COMB (@lem2319660) (@lem2319659)). Qed.
Lemma lem2319662 : term226 = term229.
Proof. exact (MK_COMB (@lem2319661) (@lem2319656)). Qed.
Lemma lem2319663 : term230.
Proof. exact (@lem1980026 term182 term41 term132 term41). Qed.
Lemma lem2319665 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319666 : term184 = term185.
Proof. exact (@lem2319665 (NUMERAL 0) term42). Qed.
Lemma lem2319667 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319668 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319669 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319668 h1) (fun h1 : term185 = True => @lem2319667)). Qed.
Lemma lem2319670 : term185 = True.
Proof. exact (EQ_MP (@lem2319669) (@lem2319667)). Qed.
Lemma lem2319671 : term184 = True.
Proof. exact (TRANS (@lem2319666) (@lem2319670)). Qed.
Lemma lem2319672 : True = term184.
Proof. exact (SYM (@lem2319671)). Qed.
Lemma lem2319673 : term184.
Proof. exact (EQ_MP (@lem2319672) (@lem0)). Qed.
Lemma lem2319674 : term231.
Proof. exact (@lem2319663 (@lem2319673)). Qed.
Lemma lem2319676 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319677 : term184 = term185.
Proof. exact (@lem2319676 (NUMERAL 0) term42). Qed.
Lemma lem2319678 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319679 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319680 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319679 h1) (fun h1 : term185 = True => @lem2319678)). Qed.
Lemma lem2319681 : term185 = True.
Proof. exact (EQ_MP (@lem2319680) (@lem2319678)). Qed.
Lemma lem2319682 : term184 = True.
Proof. exact (TRANS (@lem2319677) (@lem2319681)). Qed.
Lemma lem2319683 : True = term184.
Proof. exact (SYM (@lem2319682)). Qed.
Lemma lem2319684 : term184.
Proof. exact (EQ_MP (@lem2319683) (@lem0)). Qed.
Lemma lem2319685 : term229 = term232.
Proof. exact (@lem2319674 (@lem2319684)). Qed.
Lemma lem2319687 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2319688 : term143 = term154.
Proof. exact (@lem2319687 term42 term42). Qed.
Lemma lem2319689 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319690 : term151 = term42.
Proof. exact (EQ_MP (@lem2319689) (@lem940073)). Qed.
Lemma lem2319691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319692 : term149 = term41.
Proof. exact (MK_COMB (@lem2319691) (@lem2319690)). Qed.
Lemma lem2319693 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2319694 : term154 = term132.
Proof. exact (MK_COMB (@lem2319693) (@lem2319692)). Qed.
Lemma lem2319695 : term143 = term132.
Proof. exact (TRANS (@lem2319688) (@lem2319694)). Qed.
Lemma lem2319697 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319698 : term196 = term182.
Proof. exact (@lem2319697 term42). Qed.
Lemma lem2319699 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2319700 : term233 = term227.
Proof. exact (MK_COMB (@lem2319699) (@lem2319698)). Qed.
Lemma lem2319701 : term232 = term226.
Proof. exact (MK_COMB (@lem2319700) (@lem2319695)). Qed.
Lemma lem2319703 (m : nat) (n : nat) : (term234 m n) = (term235 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2319704 : term226 = term236.
Proof. exact (@lem2319703 (NUMERAL 0) term42). Qed.
Lemma lem2319705 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319706 (h1 : term186 = (BIT1 0)) : (term42 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2319707 : (term186 = (BIT1 0)) = ((term42 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319706 h1) (fun h1 : (term42 = (NUMERAL 0)) = False => @lem2319705)). Qed.
Lemma lem2319708 : (term42 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2319707) (@lem2319705)). Qed.
Lemma lem2319709 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2319710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2319711 : term237 = (and True).
Proof. exact (MK_COMB (@lem2319710) (@lem2319709)). Qed.
Lemma lem2319712 : term236 = (True /\ False).
Proof. exact (MK_COMB (@lem2319711) (@lem2319708)). Qed.
Lemma lem2319714 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2319715 : term236 = False.
Proof. exact (TRANS (@lem2319712) (@lem2319714)). Qed.
Lemma lem2319716 : term226 = False.
Proof. exact (TRANS (@lem2319704) (@lem2319715)). Qed.
Lemma lem2319717 : term232 = False.
Proof. exact (TRANS (@lem2319701) (@lem2319716)). Qed.
Lemma lem2319718 : term229 = False.
Proof. exact (TRANS (@lem2319685) (@lem2319717)). Qed.
Lemma lem2319719 : term226 = False.
Proof. exact (TRANS (@lem2319662) (@lem2319718)). Qed.
Lemma lem2319720 : term211 = False.
Proof. exact (TRANS (@lem2319653) (@lem2319719)). Qed.
Lemma lem2319721 (h1 : term211) : False.
Proof. exact (EQ_MP (@lem2319720) (@lem2319650 h1)). Qed.
Lemma lem2319722 (h1 : term211) : term211.
Proof. exact (h1). Qed.
Lemma lem2319724 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2319725 : term211 = term226.
Proof. exact (@lem2319724 term182 term132). Qed.
Lemma lem2319727 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2319728 : term132 = term140.
Proof. exact (@lem2319727 term42). Qed.
Lemma lem2319730 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2319731 : term182 = term199.
Proof. exact (@lem2319730 (NUMERAL 0)). Qed.
Lemma lem2319732 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2319733 : term227 = term228.
Proof. exact (MK_COMB (@lem2319732) (@lem2319731)). Qed.
Lemma lem2319734 : term226 = term229.
Proof. exact (MK_COMB (@lem2319733) (@lem2319728)). Qed.
Lemma lem2319735 : term230.
Proof. exact (@lem1980026 term182 term41 term132 term41). Qed.
Lemma lem2319737 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319738 : term184 = term185.
Proof. exact (@lem2319737 (NUMERAL 0) term42). Qed.
Lemma lem2319739 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319740 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319741 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319740 h1) (fun h1 : term185 = True => @lem2319739)). Qed.
Lemma lem2319742 : term185 = True.
Proof. exact (EQ_MP (@lem2319741) (@lem2319739)). Qed.
Lemma lem2319743 : term184 = True.
Proof. exact (TRANS (@lem2319738) (@lem2319742)). Qed.
Lemma lem2319744 : True = term184.
Proof. exact (SYM (@lem2319743)). Qed.
Lemma lem2319745 : term184.
Proof. exact (EQ_MP (@lem2319744) (@lem0)). Qed.
Lemma lem2319746 : term231.
Proof. exact (@lem2319735 (@lem2319745)). Qed.
Lemma lem2319748 (m : nat) (n : nat) : (term183 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2319749 : term184 = term185.
Proof. exact (@lem2319748 (NUMERAL 0) term42). Qed.
Lemma lem2319750 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319751 (h1 : term186 = (BIT1 0)) : term185 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2319752 : (term186 = (BIT1 0)) = (term185 = True).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319751 h1) (fun h1 : term185 = True => @lem2319750)). Qed.
Lemma lem2319753 : term185 = True.
Proof. exact (EQ_MP (@lem2319752) (@lem2319750)). Qed.
Lemma lem2319754 : term184 = True.
Proof. exact (TRANS (@lem2319749) (@lem2319753)). Qed.
Lemma lem2319755 : True = term184.
Proof. exact (SYM (@lem2319754)). Qed.
Lemma lem2319756 : term184.
Proof. exact (EQ_MP (@lem2319755) (@lem0)). Qed.
Lemma lem2319757 : term229 = term232.
Proof. exact (@lem2319746 (@lem2319756)). Qed.
Lemma lem2319759 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2319760 : term143 = term154.
Proof. exact (@lem2319759 term42 term42). Qed.
Lemma lem2319761 : (term150 = (BIT1 0)) = (term151 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2319762 : term151 = term42.
Proof. exact (EQ_MP (@lem2319761) (@lem940073)). Qed.
Lemma lem2319763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2319764 : term149 = term41.
Proof. exact (MK_COMB (@lem2319763) (@lem2319762)). Qed.
Lemma lem2319765 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2319766 : term154 = term132.
Proof. exact (MK_COMB (@lem2319765) (@lem2319764)). Qed.
Lemma lem2319767 : term143 = term132.
Proof. exact (TRANS (@lem2319760) (@lem2319766)). Qed.
Lemma lem2319769 (x : nat) : (term197 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2319770 : term196 = term182.
Proof. exact (@lem2319769 term42). Qed.
Lemma lem2319771 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2319772 : term233 = term227.
Proof. exact (MK_COMB (@lem2319771) (@lem2319770)). Qed.
Lemma lem2319773 : term232 = term226.
Proof. exact (MK_COMB (@lem2319772) (@lem2319767)). Qed.
Lemma lem2319775 (m : nat) (n : nat) : (term234 m n) = (term235 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2319776 : term226 = term236.
Proof. exact (@lem2319775 (NUMERAL 0) term42). Qed.
Lemma lem2319777 : term186 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2319778 (h1 : term186 = (BIT1 0)) : (term42 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2319779 : (term186 = (BIT1 0)) = ((term42 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term186 = (BIT1 0) => @lem2319778 h1) (fun h1 : (term42 = (NUMERAL 0)) = False => @lem2319777)). Qed.
Lemma lem2319780 : (term42 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2319779) (@lem2319777)). Qed.
Lemma lem2319781 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2319782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2319783 : term237 = (and True).
Proof. exact (MK_COMB (@lem2319782) (@lem2319781)). Qed.
Lemma lem2319784 : term236 = (True /\ False).
Proof. exact (MK_COMB (@lem2319783) (@lem2319780)). Qed.
Lemma lem2319786 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2319787 : term236 = False.
Proof. exact (TRANS (@lem2319784) (@lem2319786)). Qed.
Lemma lem2319788 : term226 = False.
Proof. exact (TRANS (@lem2319776) (@lem2319787)). Qed.
Lemma lem2319789 : term232 = False.
Proof. exact (TRANS (@lem2319773) (@lem2319788)). Qed.
Lemma lem2319790 : term229 = False.
Proof. exact (TRANS (@lem2319757) (@lem2319789)). Qed.
Lemma lem2319791 : term226 = False.
Proof. exact (TRANS (@lem2319734) (@lem2319790)). Qed.
Lemma lem2319792 : term211 = False.
Proof. exact (TRANS (@lem2319725) (@lem2319791)). Qed.
Lemma lem2319793 (h1 : term211) : False.
Proof. exact (EQ_MP (@lem2319792) (@lem2319722 h1)). Qed.
Lemma lem2319794 (h1 : term225) : False.
Proof. exact (or_elim (@lem2319649 h1) (fun h0 : term211 => @lem2319721 h0) (fun h0 : term211 => @lem2319793 h0)). Qed.
Lemma lem2319796 (h1 : term225) : term225.
Proof. exact (h1). Qed.
Lemma lem2319797 (h1 : term225) : term225 = False.
Proof. exact (prop_ext (fun h2 : term225 => @lem2319794 h1) (fun h2 : False => @lem2319796 h1)). Qed.
Lemma lem2319798 (h1 : term225) : False.
Proof. exact (EQ_MP (@lem2319797 h1) (@lem2319796 h1)). Qed.
Lemma lem2319799 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem2319800 (h1 : term72) : term225.
Proof. exact (EQ_MP (@lem2319639) (@lem2319799 h1)). Qed.
Lemma lem2319801 (h1 : term72) : term225 = False.
Proof. exact (prop_ext (fun h2 : term225 => @lem2319798 h2) (fun h2 : False => @lem2319800 h1)). Qed.
Lemma lem2319802 (h1 : term72) : False.
Proof. exact (EQ_MP (@lem2319801 h1) (@lem2319800 h1)). Qed.
Lemma lem2319803 : term238.
Proof. exact (fun h0 : term72 => @lem2319802 h0). Qed.
Lemma lem2319804 : term239.
Proof. exact (@lem1386578 term240). Qed.
Lemma lem2319807 : term240.
Proof. exact (@lem2319804 (@lem2319803)). Qed.
Lemma lem2319808 : term70 = term14.
Proof. exact (SYM (@lem2318720)). Qed.
Lemma lem2319809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2319810 : term240 = term0.
Proof. exact (MK_COMB (@lem2319809) (@lem2319808)). Qed.
Lemma lem2319811 : term0.
Proof. exact (EQ_MP (@lem2319810) (@lem2319807)). Qed.
Lemma lem2319812 : term1.
Proof. exact (EQ_MP (@lem2318605) (@lem2319811)). Qed.
