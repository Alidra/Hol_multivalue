Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_NONZERO_term_abbrevs.
Require Import ADD1_spec.
Require Import ADD_CLAUSES_spec.
Require Import LE_SUC_LT_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_ARCH_MULT_spec.
Require Import NADD_MUL_spec.
Require Import NADD_OF_NUM_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_LE_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1299582 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.lt m n)) : (term0 m n) = (Peano.lt m n).
Proof. exact (h1). Qed.
Lemma lem1299583 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.lt m n)) : (Peano.lt m n) = (term0 m n).
Proof. exact (SYM (@lem1299582 m n h1)). Qed.
Lemma lem1299584 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term0 m n)) : (Peano.lt m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem1299585 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term0 m n)) : (term0 m n) = (Peano.lt m n).
Proof. exact (SYM (@lem1299584 m n h1)). Qed.
Lemma lem1299586 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt m n) => @lem1299583 m n h1) (fun h1 : (Peano.lt m n) = (term0 m n) => @lem1299585 m n h1)). Qed.
Lemma lem1299587 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem1299586 m n)). Qed.
Lemma lem1299588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299589 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem1299588) (@lem1299587 m)). Qed.
Lemma lem1299590 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem1299589 m)). Qed.
Lemma lem1299591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299592 : term7 = term8.
Proof. exact (MK_COMB (@lem1299591) (@lem1299590)). Qed.
Lemma lem1299593 : term8.
Proof. exact (EQ_MP (@lem1299592) (@lem91144)). Qed.
Lemma lem1299594 (m : nat) : term9 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem1299595 (m : nat) : (term9 m) = ((S m) = (term10 m)).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1299597 (m : nat) : term11 m.
Proof. exact (@lem1299593 m). Qed.
Lemma lem1299598 (m : nat) : (term11 m) = (term4 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem1299599 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1299598 m) (@lem1299597 m)). Qed.
Lemma lem1299600 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1299599 m n). Qed.
Lemma lem1299601 (m : nat) (n : nat) : (term12 m n) = ((Peano.lt m n) = (term0 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1299603 (m : nat) : term13 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1299604 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1299605 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1299604 m) (@lem1299603 m)). Qed.
Lemma lem1299606 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1299605 m n). Qed.
Lemma lem1299607 (n : nat) (m : nat) : (term15 m n) = ((term16 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1299609 {A : Type'} (P : A -> Prop) : term17 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem1299610 {A : Type'} (P : A -> Prop) : (term17 A P) = ((term18 A P) = (term19 A P)).
Proof. exact (eq_refl (term17 A P)). Qed.
Lemma lem1299612 : term20.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1299613 : term21.
Proof. exact (proj2 (@lem1299612)). Qed.
Lemma lem1299634 : term22.
Proof. exact (proj1 (@lem1299613)). Qed.
Lemma lem1299635 (n : nat) : term23 n.
Proof. exact (@lem1299634 n). Qed.
Lemma lem1299636 (n : nat) : (term23 n) = ((term24 n) = n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem1299646 (k : nat) : term25 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1299647 (k : nat) : (term25 k) = ((term26 k) = (term27 k)).
Proof. exact (eq_refl (term25 k)). Qed.
Lemma lem1299649 (x : nadd) : term28 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1299650 (x : nadd) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1299651 (x : nadd) : term29 x.
Proof. exact (EQ_MP (@lem1299650 x) (@lem1299649 x)). Qed.
Lemma lem1299652 (x : nadd) (y : nadd) : term30 x y.
Proof. exact (@lem1299651 x y). Qed.
Lemma lem1299653 (x : nadd) (y : nadd) : (term30 x y) = ((term31 x y) = (term32 x y)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1299655 (x : nadd) : term33 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1299656 (x : nadd) : (term33 x) = (term34 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1299657 (x : nadd) : term34 x.
Proof. exact (EQ_MP (@lem1299656 x) (@lem1299655 x)). Qed.
Lemma lem1299658 (x : nadd) (y : nadd) : term35 x y.
Proof. exact (@lem1299657 x y). Qed.
Lemma lem1299659 (x : nadd) (y : nadd) : (term35 x y) = ((nadd_le x y) = (term36 x y)).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem1299661 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1299662 (x : nadd) (h1 : term37) : term38 x.
Proof. exact (@lem1299661 h1 x). Qed.
Lemma lem1299663 (x : nadd) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1299664 (x : nadd) (h1 : term37) : term39 x.
Proof. exact (EQ_MP (@lem1299663 x) (@lem1299662 x h1)). Qed.
Lemma lem1299665 (x : nadd) (k : nat) (h1 : term37) : term40 x k.
Proof. exact (@lem1299664 x h1 k). Qed.
Lemma lem1299666 (k : nat) (x : nadd) : (term40 x k) = (term41 k x).
Proof. exact (eq_refl (term40 x k)). Qed.
Lemma lem1299667 (k : nat) (x : nadd) (h1 : term37) : term41 k x.
Proof. exact (EQ_MP (@lem1299666 k x) (@lem1299665 x k h1)). Qed.
Lemma lem1299668 (x : nadd) (h1 : term42 x) : term42 x.
Proof. exact (h1). Qed.
Lemma lem1299669 (k : nat) (x : nadd) (h1 : term37) (h2 : term42 x) : term43 k x.
Proof. exact (@lem1299667 k x h1 (@lem1299668 x h2)). Qed.
Lemma lem1299670 (x : nadd) (h1 : term37) (h2 : term42 x) : term44 x.
Proof. exact (fun k : nat => @lem1299669 k x h1 h2). Qed.
Lemma lem1299671 (x : nadd) (h1 : term37) : term45 x.
Proof. exact (fun h0 : term42 x => @lem1299670 x h1 h0). Qed.
Lemma lem1299672 (h1 : term37) : term46.
Proof. exact (fun x : nadd => @lem1299671 x h1). Qed.
Lemma lem1299673 : term47.
Proof. exact (fun h0 : term37 => @lem1299672 h0). Qed.
Lemma lem1299674 : term46.
Proof. exact (@lem1299673 (@lem1286557)). Qed.
Lemma lem1299675 (x : nadd) : term48 x.
Proof. exact (@lem1299674 x). Qed.
Lemma lem1299676 (x : nadd) : (term48 x) = (term45 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1299678 (x : nadd) (h1 : term42 x) : term42 x.
Proof. exact (h1). Qed.
Lemma lem1299680 (x : nadd) : term45 x.
Proof. exact (EQ_MP (@lem1299676 x) (@lem1299675 x)). Qed.
Lemma lem1299681 (x : nadd) (h1 : term42 x) : term44 x.
Proof. exact (@lem1299680 x (@lem1299678 x h1)). Qed.
Lemma lem1299682 (x : nadd) (h1 : term44 x) : term44 x.
Proof. exact (h1). Qed.
Lemma lem1299683 (x : nadd) (h1 : term44 x) : term49 x.
Proof. exact (@lem1299682 x h1 term50). Qed.
Lemma lem1299684 (x : nadd) : (term49 x) = (term51 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1299685 (x : nadd) (h1 : term44 x) : term51 x.
Proof. exact (EQ_MP (@lem1299684 x) (@lem1299683 x h1)). Qed.
Lemma lem1299693 (x : nadd) (y : nadd) : (nadd_le x y) = (term36 x y).
Proof. exact (EQ_MP (@lem1299659 x y) (@lem1299658 x y)). Qed.
Lemma lem1299694 (N : nat) (x : nadd) : (term52 N x) = (term53 N x).
Proof. exact (@lem1299693 term54 (term55 N x)). Qed.
Lemma lem1299704 (k : nat) : (term26 k) = (term27 k).
Proof. exact (EQ_MP (@lem1299647 k) (@lem1299646 k)). Qed.
Lemma lem1299705 : term56 = term57.
Proof. exact (@lem1299704 term50). Qed.
Lemma lem1299707 (n : nat) : (term24 n) = n.
Proof. exact (EQ_MP (@lem1299636 n) (@lem1299635 n)). Qed.
Lemma lem1299708 : term57 = term58.
Proof. exact (fun_ext (fun n : nat => @lem1299707 n)). Qed.
Lemma lem1299709 : term56 = term58.
Proof. exact (TRANS (@lem1299705) (@lem1299708)). Qed.
Lemma lem1299710 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1299711 (n : nat) : (term59 n) = (term60 n).
Proof. exact (MK_COMB (@lem1299709) (@lem1299710 n)). Qed.
Lemma lem1299713 {A B : Type'} (f : A -> B) (y : A) : (term61 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299714 (f : nat -> nat) (y : nat) : (term62 f y) = (f y).
Proof. exact (@lem1299713 nat nat f y). Qed.
Lemma lem1299715 (n : nat) : (term63 n) = (term60 n).
Proof. exact (@lem1299714 term58 n). Qed.
Lemma lem1299716 (n : nat) : (term60 n) = n.
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem1299717 : term64 = term58.
Proof. exact (fun_ext (fun n : nat => @lem1299716 n)). Qed.
Lemma lem1299718 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1299719 (n : nat) : (term63 n) = (term60 n).
Proof. exact (MK_COMB (@lem1299717) (@lem1299718 n)). Qed.
Lemma lem1299720 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299721 (n : nat) : (term65 n) = (term66 n).
Proof. exact (MK_COMB (@lem1299720) (@lem1299719 n)). Qed.
Lemma lem1299722 (n : nat) : (term60 n) = n.
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem1299723 (n : nat) : ((term63 n) = (term60 n)) = ((term60 n) = n).
Proof. exact (MK_COMB (@lem1299721 n) (@lem1299722 n)). Qed.
Lemma lem1299724 (n : nat) : (term60 n) = n.
Proof. exact (EQ_MP (@lem1299723 n) (@lem1299715 n)). Qed.
Lemma lem1299725 (n : nat) : (term59 n) = n.
Proof. exact (TRANS (@lem1299711 n) (@lem1299724 n)). Qed.
Lemma lem1299726 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1299727 (n : nat) : (term67 n) = (Peano.le n).
Proof. exact (MK_COMB (@lem1299726) (@lem1299725 n)). Qed.
Lemma lem1299729 (x : nadd) (y : nadd) : (term31 x y) = (term32 x y).
Proof. exact (EQ_MP (@lem1299653 x y) (@lem1299652 x y)). Qed.
Lemma lem1299730 (N : nat) (x : nadd) : (term68 N x) = (term69 N x).
Proof. exact (@lem1299729 (nadd_of_num N) x). Qed.
Lemma lem1299732 (k : nat) : (term26 k) = (term27 k).
Proof. exact (EQ_MP (@lem1299647 k) (@lem1299646 k)). Qed.
Lemma lem1299733 (N : nat) : (term26 N) = (term27 N).
Proof. exact (@lem1299732 N). Qed.
Lemma lem1299734 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1299735 (N : nat) (x : nadd) (n : nat) : (term70 N x n) = (term71 N x n).
Proof. exact (MK_COMB (@lem1299733 N) (@lem1299734 x n)). Qed.
Lemma lem1299737 {A B : Type'} (f : A -> B) (y : A) : (term61 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299738 (f : nat -> nat) (y : nat) : (term62 f y) = (f y).
Proof. exact (@lem1299737 nat nat f y). Qed.
Lemma lem1299739 (N : nat) (x : nadd) (n : nat) : (term72 N x n) = (term71 N x n).
Proof. exact (@lem1299738 (term27 N) (dest_nadd x n)). Qed.
Lemma lem1299740 (N : nat) (n : nat) : (term73 N n) = (Nat.mul N n).
Proof. exact (eq_refl (term73 N n)). Qed.
Lemma lem1299741 (N : nat) : (term74 N) = (term27 N).
Proof. exact (fun_ext (fun n : nat => @lem1299740 N n)). Qed.
Lemma lem1299742 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1299743 (N : nat) (x : nadd) (n : nat) : (term72 N x n) = (term71 N x n).
Proof. exact (MK_COMB (@lem1299741 N) (@lem1299742 x n)). Qed.
Lemma lem1299744 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299745 (N : nat) (x : nadd) (n : nat) : (term75 N x n) = (term76 N x n).
Proof. exact (MK_COMB (@lem1299744) (@lem1299743 N x n)). Qed.
Lemma lem1299746 (N : nat) (x : nadd) (n : nat) : (term71 N x n) = (term77 N x n).
Proof. exact (eq_refl (term71 N x n)). Qed.
Lemma lem1299747 (N : nat) (x : nadd) (n : nat) : ((term72 N x n) = (term71 N x n)) = ((term71 N x n) = (term77 N x n)).
Proof. exact (MK_COMB (@lem1299745 N x n) (@lem1299746 N x n)). Qed.
Lemma lem1299748 (N : nat) (x : nadd) (n : nat) : (term71 N x n) = (term77 N x n).
Proof. exact (EQ_MP (@lem1299747 N x n) (@lem1299739 N x n)). Qed.
Lemma lem1299749 (N : nat) (x : nadd) (n : nat) : (term70 N x n) = (term77 N x n).
Proof. exact (TRANS (@lem1299735 N x n) (@lem1299748 N x n)). Qed.
Lemma lem1299750 (N : nat) (x : nadd) : (term69 N x) = (term78 N x).
Proof. exact (fun_ext (fun n : nat => @lem1299749 N x n)). Qed.
Lemma lem1299751 (N : nat) (x : nadd) : (term68 N x) = (term78 N x).
Proof. exact (TRANS (@lem1299730 N x) (@lem1299750 N x)). Qed.
Lemma lem1299752 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1299753 (N : nat) (x : nadd) (n : nat) : (term79 N x n) = (term80 N x n).
Proof. exact (MK_COMB (@lem1299751 N x) (@lem1299752 n)). Qed.
Lemma lem1299755 {A B : Type'} (f : A -> B) (y : A) : (term61 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299756 (f : nat -> nat) (y : nat) : (term62 f y) = (f y).
Proof. exact (@lem1299755 nat nat f y). Qed.
Lemma lem1299757 (N : nat) (x : nadd) (n : nat) : (term81 N x n) = (term80 N x n).
Proof. exact (@lem1299756 (term78 N x) n). Qed.
Lemma lem1299758 (N : nat) (x : nadd) (n : nat) : (term80 N x n) = (term77 N x n).
Proof. exact (eq_refl (term80 N x n)). Qed.
Lemma lem1299759 (N : nat) (x : nadd) : (term82 N x) = (term78 N x).
Proof. exact (fun_ext (fun n : nat => @lem1299758 N x n)). Qed.
Lemma lem1299760 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1299761 (N : nat) (x : nadd) (n : nat) : (term81 N x n) = (term80 N x n).
Proof. exact (MK_COMB (@lem1299759 N x) (@lem1299760 n)). Qed.
Lemma lem1299762 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299763 (N : nat) (x : nadd) (n : nat) : (term83 N x n) = (term84 N x n).
Proof. exact (MK_COMB (@lem1299762) (@lem1299761 N x n)). Qed.
Lemma lem1299764 (N : nat) (x : nadd) (n : nat) : (term80 N x n) = (term77 N x n).
Proof. exact (eq_refl (term80 N x n)). Qed.
Lemma lem1299765 (N : nat) (x : nadd) (n : nat) : ((term81 N x n) = (term80 N x n)) = ((term80 N x n) = (term77 N x n)).
Proof. exact (MK_COMB (@lem1299763 N x n) (@lem1299764 N x n)). Qed.
Lemma lem1299766 (N : nat) (x : nadd) (n : nat) : (term80 N x n) = (term77 N x n).
Proof. exact (EQ_MP (@lem1299765 N x n) (@lem1299757 N x n)). Qed.
Lemma lem1299767 (N : nat) (x : nadd) (n : nat) : (term79 N x n) = (term77 N x n).
Proof. exact (TRANS (@lem1299753 N x n) (@lem1299766 N x n)). Qed.
Lemma lem1299768 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1299769 (N : nat) (x : nadd) (n : nat) : (term85 N x n) = (term86 N x n).
Proof. exact (MK_COMB (@lem1299768) (@lem1299767 N x n)). Qed.
Lemma lem1299770 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1299771 (N : nat) (x : nadd) (n : nat) (B : nat) : (term87 N x n B) = (term88 N x n B).
Proof. exact (MK_COMB (@lem1299769 N x n) (@lem1299770 B)). Qed.
Lemma lem1299772 (N : nat) (x : nadd) (n : nat) (B : nat) : (term89 N x n B) = (term90 N x n B).
Proof. exact (MK_COMB (@lem1299727 n) (@lem1299771 N x n B)). Qed.
Lemma lem1299773 (N : nat) (x : nadd) (B : nat) : (term91 N x B) = (term92 N x B).
Proof. exact (fun_ext (fun n : nat => @lem1299772 N x n B)). Qed.
Lemma lem1299774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299775 (N : nat) (x : nadd) (B : nat) : (term93 N x B) = (term94 N x B).
Proof. exact (MK_COMB (@lem1299774) (@lem1299773 N x B)). Qed.
Lemma lem1299780 (N : nat) (x : nadd) : (term95 N x) = (term96 N x).
Proof. exact (fun_ext (fun B : nat => @lem1299775 N x B)). Qed.
Lemma lem1299781 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1299782 (N : nat) (x : nadd) : (term53 N x) = (term97 N x).
Proof. exact (MK_COMB (@lem1299781) (@lem1299780 N x)). Qed.
Lemma lem1299787 (N : nat) (x : nadd) : (term52 N x) = (term97 N x).
Proof. exact (TRANS (@lem1299694 N x) (@lem1299782 N x)). Qed.
Lemma lem1299788 (x : nadd) : (term98 x) = (term99 x).
Proof. exact (fun_ext (fun N : nat => @lem1299787 N x)). Qed.
Lemma lem1299789 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1299790 (x : nadd) : (term51 x) = (term100 x).
Proof. exact (MK_COMB (@lem1299789) (@lem1299788 x)). Qed.
Lemma lem1299795 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1299796 (x : nadd) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1299795) (@lem1299790 x)). Qed.
Lemma lem1299809 (x : nadd) : (term103 x) = (term103 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1299810 (x : nadd) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem1299796 x) (@lem1299809 x)). Qed.
Lemma lem1299813 (x : nadd) : (term105 x) = (term104 x).
Proof. exact (SYM (@lem1299810 x)). Qed.
Lemma lem1299814 (x : nadd) (h1 : term100 x) : term100 x.
Proof. exact (h1). Qed.
Lemma lem1299815 (A1 : nat) (x : nadd) (h1 : term97 A1 x) : term97 A1 x.
Proof. exact (h1). Qed.
Lemma lem1299816 (A1 : nat) (x : nadd) (A2 : nat) (h1 : term94 A1 x A2) : term94 A1 x A2.
Proof. exact (h1). Qed.
Lemma lem1299817 (A2 : nat) (n : nat) (h1 : term106 A2 n) : term106 A2 n.
Proof. exact (h1). Qed.
Lemma lem1299820 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1299821 (A1 : nat) (x : nadd) (A2 : nat) : (term107 A1 x A2) = (term108 A1 x A2).
Proof. exact (@lem1299820 (term94 A1 x A2)). Qed.
Lemma lem1299823 {A : Type'} (P : A -> Prop) : (term18 A P) = (term19 A P).
Proof. exact (EQ_MP (@lem1299610 A P) (@lem1299609 A P)). Qed.
Lemma lem1299824 (P : nat -> Prop) : (term109 P) = (term110 P).
Proof. exact (@lem1299823 nat P). Qed.
Lemma lem1299825 (A1 : nat) (x : nadd) (A2 : nat) : (term111 A1 x A2) = (term112 A1 x A2).
Proof. exact (@lem1299824 (term92 A1 x A2)). Qed.
Lemma lem1299826 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term113 A1 x A2 n) = (term90 A1 x n A2).
Proof. exact (eq_refl (term113 A1 x A2 n)). Qed.
Lemma lem1299827 (A1 : nat) (x : nadd) (A2 : nat) : (term114 A1 x A2) = (term92 A1 x A2).
Proof. exact (fun_ext (fun n : nat => @lem1299826 A1 x n A2)). Qed.
Lemma lem1299828 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299829 (A1 : nat) (x : nadd) (A2 : nat) : (term115 A1 x A2) = (term94 A1 x A2).
Proof. exact (MK_COMB (@lem1299828) (@lem1299827 A1 x A2)). Qed.
Lemma lem1299830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1299831 (A1 : nat) (x : nadd) (A2 : nat) : (term111 A1 x A2) = (term108 A1 x A2).
Proof. exact (MK_COMB (@lem1299830) (@lem1299829 A1 x A2)). Qed.
Lemma lem1299832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1299833 (A1 : nat) (x : nadd) (A2 : nat) : (term116 A1 x A2) = (term117 A1 x A2).
Proof. exact (MK_COMB (@lem1299832) (@lem1299831 A1 x A2)). Qed.
Lemma lem1299834 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term113 A1 x A2 n) = (term90 A1 x n A2).
Proof. exact (eq_refl (term113 A1 x A2 n)). Qed.
Lemma lem1299835 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1299836 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term118 A1 x A2 n) = (term119 A1 x n A2).
Proof. exact (MK_COMB (@lem1299835) (@lem1299834 A1 x n A2)). Qed.
Lemma lem1299837 (A1 : nat) (x : nadd) (A2 : nat) : (term120 A1 x A2) = (term121 A1 x A2).
Proof. exact (fun_ext (fun n : nat => @lem1299836 A1 x n A2)). Qed.
Lemma lem1299838 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1299839 (A1 : nat) (x : nadd) (A2 : nat) : (term112 A1 x A2) = (term122 A1 x A2).
Proof. exact (MK_COMB (@lem1299838) (@lem1299837 A1 x A2)). Qed.
Lemma lem1299840 (A1 : nat) (x : nadd) (A2 : nat) : ((term111 A1 x A2) = (term112 A1 x A2)) = ((term108 A1 x A2) = (term122 A1 x A2)).
Proof. exact (MK_COMB (@lem1299833 A1 x A2) (@lem1299839 A1 x A2)). Qed.
Lemma lem1299841 (A1 : nat) (x : nadd) (A2 : nat) : (term108 A1 x A2) = (term122 A1 x A2).
Proof. exact (EQ_MP (@lem1299840 A1 x A2) (@lem1299825 A1 x A2)). Qed.
Lemma lem1299846 (A1 : nat) (x : nadd) (A2 : nat) : (term107 A1 x A2) = (term122 A1 x A2).
Proof. exact (TRANS (@lem1299821 A1 x A2) (@lem1299841 A1 x A2)). Qed.
Lemma lem1299848 (n : nat) (m : nat) : (term16 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1299607 n m) (@lem1299606 m n)). Qed.
Lemma lem1299849 (A1 : nat) (x : nadd) (A2 : nat) (n : nat) : (term119 A1 x n A2) = (term123 A1 x A2 n).
Proof. exact (@lem1299848 (term88 A1 x n A2) n). Qed.
Lemma lem1299851 (m : nat) (n : nat) : (Peano.lt m n) = (term0 m n).
Proof. exact (EQ_MP (@lem1299601 m n) (@lem1299600 m n)). Qed.
Lemma lem1299852 (A1 : nat) (x : nadd) (A2 : nat) (n : nat) : (term123 A1 x A2 n) = (term124 A1 x A2 n).
Proof. exact (@lem1299851 (term88 A1 x n A2) n). Qed.
Lemma lem1299853 (A1 : nat) (x : nadd) (A2 : nat) (n : nat) : (term119 A1 x n A2) = (term124 A1 x A2 n).
Proof. exact (TRANS (@lem1299849 A1 x A2 n) (@lem1299852 A1 x A2 n)). Qed.
Lemma lem1299855 (m : nat) : (S m) = (term10 m).
Proof. exact (EQ_MP (@lem1299595 m) (@lem1299594 m)). Qed.
Lemma lem1299856 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term125 A1 x n A2) = (term126 A1 x n A2).
Proof. exact (@lem1299855 (term88 A1 x n A2)). Qed.
Lemma lem1299857 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1299858 (A1 : nat) (x : nadd) (n : nat) (A2 : nat) : (term127 A1 x n A2) = (term128 A1 x n A2).
Proof. exact (MK_COMB (@lem1299857) (@lem1299856 A1 x n A2)). Qed.
Lemma lem1299859 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1299860 (A1 : nat) (x : nadd) (A2 : nat) (n : nat) : (term124 A1 x A2 n) = (term129 A1 x A2 n).
Proof. exact (MK_COMB (@lem1299858 A1 x n A2) (@lem1299859 n)). Qed.
Lemma lem1299861 (A1 : nat) (x : nadd) (A2 : nat) (n : nat) : (term119 A1 x n A2) = (term129 A1 x A2 n).
Proof. exact (TRANS (@lem1299853 A1 x A2 n) (@lem1299860 A1 x A2 n)). Qed.
Lemma lem1299862 (A1 : nat) (x : nadd) (A2 : nat) : (term121 A1 x A2) = (term130 A1 x A2).
Proof. exact (fun_ext (fun n : nat => @lem1299861 A1 x A2 n)). Qed.
Lemma lem1299863 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1299864 (A1 : nat) (x : nadd) (A2 : nat) : (term122 A1 x A2) = (term131 A1 x A2).
Proof. exact (MK_COMB (@lem1299863) (@lem1299862 A1 x A2)). Qed.
Lemma lem1299869 (A1 : nat) (x : nadd) (A2 : nat) : (term107 A1 x A2) = (term131 A1 x A2).
Proof. exact (TRANS (@lem1299846 A1 x A2) (@lem1299864 A1 x A2)). Qed.
Lemma lem1299870 (A1 : nat) (x : nadd) (A2 : nat) : (term131 A1 x A2) = (term107 A1 x A2).
Proof. exact (SYM (@lem1299869 A1 x A2)). Qed.
Lemma lem1299891 : term132.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1299892 (n : nat) : term133 n.
Proof. exact (@lem1299891 n). Qed.
Lemma lem1299893 (n : nat) : (term133 n) = ((term134 n) = n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem1299895 : term20.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1299921 : term135.
Proof. exact (proj1 (@lem1299895)). Qed.
Lemma lem1299922 (m : nat) : term136 m.
Proof. exact (@lem1299921 m). Qed.
Lemma lem1299923 (m : nat) : (term136 m) = ((term137 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem1299929 (A2 : nat) (n : nat) : (term106 A2 n) = ((term106 A2 n) = True).
Proof. exact (@lem7 (term106 A2 n)). Qed.
Lemma lem1299932 (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (dest_nadd x n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1299933 (A1 : nat) : (Nat.mul A1) = (Nat.mul A1).
Proof. exact (eq_refl (Nat.mul A1)). Qed.
Lemma lem1299934 (A1 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term77 A1 x n) = (term137 A1).
Proof. exact (MK_COMB (@lem1299933 A1) (@lem1299932 x n h1)). Qed.
Lemma lem1299936 (m : nat) : (term137 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1299923 m) (@lem1299922 m)). Qed.
Lemma lem1299937 (A1 : nat) : (term137 A1) = (NUMERAL 0).
Proof. exact (@lem1299936 A1). Qed.
Lemma lem1299938 (A1 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term77 A1 x n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1299934 A1 x n h1) (@lem1299937 A1)). Qed.
Lemma lem1299939 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1299940 (A1 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term86 A1 x n) = term138.
Proof. exact (MK_COMB (@lem1299939) (@lem1299938 A1 x n h1)). Qed.
Lemma lem1299941 (A2 : nat) : A2 = A2.
Proof. exact (eq_refl A2). Qed.
Lemma lem1299942 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term88 A1 x n A2) = (term134 A2).
Proof. exact (MK_COMB (@lem1299940 A1 x n h1) (@lem1299941 A2)). Qed.
Lemma lem1299944 (n : nat) : (term134 n) = n.
Proof. exact (EQ_MP (@lem1299893 n) (@lem1299892 n)). Qed.
Lemma lem1299945 (A2 : nat) : (term134 A2) = A2.
Proof. exact (@lem1299944 A2). Qed.
Lemma lem1299946 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term88 A1 x n A2) = A2.
Proof. exact (TRANS (@lem1299942 A1 A2 x n h1) (@lem1299945 A2)). Qed.
Lemma lem1299947 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1299948 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term139 A1 x n A2) = (Nat.add A2).
Proof. exact (MK_COMB (@lem1299947) (@lem1299946 A1 A2 x n h1)). Qed.
Lemma lem1299949 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1299950 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term126 A1 x n A2) = (term10 A2).
Proof. exact (MK_COMB (@lem1299948 A1 A2 x n h1) (@lem1299949)). Qed.
Lemma lem1299951 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1299952 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term128 A1 x n A2) = (term140 A2).
Proof. exact (MK_COMB (@lem1299951) (@lem1299950 A1 A2 x n h1)). Qed.
Lemma lem1299953 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1299954 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : (dest_nadd x n) = (NUMERAL 0)) : (term129 A1 x A2 n) = (term106 A2 n).
Proof. exact (MK_COMB (@lem1299952 A1 A2 x n h1) (@lem1299953 n)). Qed.
Lemma lem1299956 (A2 : nat) (n : nat) (h1 : term106 A2 n) : (term106 A2 n) = True.
Proof. exact (EQ_MP (@lem1299929 A2 n) (@lem1299817 A2 n h1)). Qed.
Lemma lem1299957 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : term106 A2 n) (h2 : (dest_nadd x n) = (NUMERAL 0)) : (term129 A1 x A2 n) = True.
Proof. exact (TRANS (@lem1299954 A1 A2 x n h2) (@lem1299956 A2 n h1)). Qed.
Lemma lem1299958 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : term106 A2 n) (h2 : (dest_nadd x n) = (NUMERAL 0)) : True = (term129 A1 x A2 n).
Proof. exact (SYM (@lem1299957 A1 A2 x n h1 h2)). Qed.
Lemma lem1299959 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : term106 A2 n) (h2 : (dest_nadd x n) = (NUMERAL 0)) : term129 A1 x A2 n.
Proof. exact (EQ_MP (@lem1299958 A1 A2 x n h1 h2) (@lem0)). Qed.
Lemma lem1299960 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : term106 A2 n) (h2 : (dest_nadd x n) = (NUMERAL 0)) : term131 A1 x A2.
Proof. exact (ex_intro (term130 A1 x A2) n (@lem1299959 A1 A2 x n h1 h2)). Qed.
Lemma lem1299961 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : term106 A2 n) (h2 : (dest_nadd x n) = (NUMERAL 0)) : term107 A1 x A2.
Proof. exact (EQ_MP (@lem1299870 A1 x A2) (@lem1299960 A1 A2 x n h1 h2)). Qed.
Lemma lem1299962 (A1 : nat) (A2 : nat) (x : nadd) (n : nat) (h1 : term94 A1 x A2) (h2 : term106 A2 n) (h3 : (dest_nadd x n) = (NUMERAL 0)) : False.
Proof. exact (@lem1299961 A1 A2 x n h2 h3 (@lem1299816 A1 x A2 h1)). Qed.
Lemma lem1299963 (A1 : nat) (x : nadd) (A2 : nat) (n : nat) (h1 : term94 A1 x A2) (h2 : term106 A2 n) : term141 x n.
Proof. exact (fun h0 : (dest_nadd x n) = (NUMERAL 0) => @lem1299962 A1 A2 x n h1 h2 h0). Qed.
Lemma lem1299964 (x : nadd) (n : nat) : (term141 x n) = (term142 x n).
Proof. exact (@lem69 ((dest_nadd x n) = (NUMERAL 0))). Qed.
Lemma lem1299965 (A1 : nat) (x : nadd) (A2 : nat) (n : nat) (h1 : term94 A1 x A2) (h2 : term106 A2 n) : term142 x n.
Proof. exact (EQ_MP (@lem1299964 x n) (@lem1299963 A1 x A2 n h1 h2)). Qed.
Lemma lem1299966 (n : nat) (A1 : nat) (x : nadd) (A2 : nat) (h1 : term94 A1 x A2) : term143 A2 x n.
Proof. exact (fun h0 : term106 A2 n => @lem1299965 A1 x A2 n h1 h0). Qed.
Lemma lem1299971 (A1 : nat) (x : nadd) (A2 : nat) (h1 : term94 A1 x A2) : term144 A2 x.
Proof. exact (fun n : nat => @lem1299966 n A1 x A2 h1). Qed.
Lemma lem1299972 (A1 : nat) (x : nadd) (A2 : nat) (h1 : term94 A1 x A2) : term103 x.
Proof. exact (ex_intro (term145 x) (term10 A2) (@lem1299971 A1 x A2 h1)). Qed.
Lemma lem1299973 (A1 : nat) (x : nadd) (h1 : term97 A1 x) : term103 x.
Proof. exact (ex_elim (@lem1299815 A1 x h1) (fun A2 : nat => fun h0 : term96 A1 x A2 => @lem1299972 A1 x A2 h0)). Qed.
Lemma lem1299974 (x : nadd) (h1 : term100 x) : term103 x.
Proof. exact (ex_elim (@lem1299814 x h1) (fun A1 : nat => fun h0 : term99 x A1 => @lem1299973 A1 x h0)). Qed.
Lemma lem1299975 (x : nadd) : term105 x.
Proof. exact (fun h0 : term100 x => @lem1299974 x h0). Qed.
Lemma lem1299976 (x : nadd) : term104 x.
Proof. exact (EQ_MP (@lem1299813 x) (@lem1299975 x)). Qed.
Lemma lem1299977 (x : nadd) (h1 : term44 x) : term103 x.
Proof. exact (@lem1299976 x (@lem1299685 x h1)). Qed.
Lemma lem1299978 (x : nadd) : term146 x.
Proof. exact (fun h0 : term44 x => @lem1299977 x h0). Qed.
Lemma lem1299979 (x : nadd) (h1 : term42 x) : term103 x.
Proof. exact (@lem1299978 x (@lem1299681 x h1)). Qed.
Lemma lem1299980 (x : nadd) : term147 x.
Proof. exact (fun h0 : term42 x => @lem1299979 x h0). Qed.
Lemma lem1299985 : term148.
Proof. exact (fun x : nadd => @lem1299980 x). Qed.
