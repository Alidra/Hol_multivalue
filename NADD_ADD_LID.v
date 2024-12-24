Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ADD_LID_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DIST_REFL_spec.
Require Import LE_0_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_ADD_spec.
Require Import NADD_OF_NUM_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1274593 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1274594 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1274595 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1274594 n) (@lem1274593 n)). Qed.
Lemma lem1274596 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1274598 (n : nat) : term2 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1274599 (n : nat) : (term2 n) = ((term3 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1274621 : term4.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1274622 (n : nat) : term5 n.
Proof. exact (@lem1274621 n). Qed.
Lemma lem1274623 (n : nat) : (term5 n) = ((term6 n) = n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1274655 : term7.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1274656 (n : nat) : term8 n.
Proof. exact (@lem1274655 n). Qed.
Lemma lem1274657 (n : nat) : (term8 n) = ((term9 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem1274659 (k : nat) : term10 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1274660 (k : nat) : (term10 k) = ((term11 k) = (term12 k)).
Proof. exact (eq_refl (term10 k)). Qed.
Lemma lem1274662 (x : nadd) : term13 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1274663 (x : nadd) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1274664 (x : nadd) : term14 x.
Proof. exact (EQ_MP (@lem1274663 x) (@lem1274662 x)). Qed.
Lemma lem1274665 (x : nadd) (y : nadd) : term15 x y.
Proof. exact (@lem1274664 x y). Qed.
Lemma lem1274666 (x : nadd) (y : nadd) : (term15 x y) = ((term16 x y) = (term17 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1274668 (x : nadd) : term18 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1274669 (x : nadd) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1274670 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1274669 x) (@lem1274668 x)). Qed.
Lemma lem1274671 (x : nadd) (y : nadd) : term20 x y.
Proof. exact (@lem1274670 x y). Qed.
Lemma lem1274672 (x : nadd) (y : nadd) : (term20 x y) = ((nadd_eq x y) = (term21 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1274675 (x : nadd) (y : nadd) : (nadd_eq x y) = (term21 x y).
Proof. exact (EQ_MP (@lem1274672 x y) (@lem1274671 x y)). Qed.
Lemma lem1274676 (x : nadd) : (term22 x) = (term23 x).
Proof. exact (@lem1274675 (term24 x) x). Qed.
Lemma lem1274686 (x : nadd) (y : nadd) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1274666 x y) (@lem1274665 x y)). Qed.
Lemma lem1274687 (x : nadd) : (term25 x) = (term26 x).
Proof. exact (@lem1274686 term27 x). Qed.
Lemma lem1274689 (k : nat) : (term11 k) = (term12 k).
Proof. exact (EQ_MP (@lem1274660 k) (@lem1274659 k)). Qed.
Lemma lem1274690 : term28 = term29.
Proof. exact (@lem1274689 (NUMERAL 0)). Qed.
Lemma lem1274691 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274692 (n : nat) : (term30 n) = (term31 n).
Proof. exact (MK_COMB (@lem1274690) (@lem1274691 n)). Qed.
Lemma lem1274694 {A B : Type'} (f : A -> B) (y : A) : (term32 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274695 (f : nat -> nat) (y : nat) : (term33 f y) = (f y).
Proof. exact (@lem1274694 nat nat f y). Qed.
Lemma lem1274696 (n : nat) : (term34 n) = (term31 n).
Proof. exact (@lem1274695 term29 n). Qed.
Lemma lem1274697 (n : nat) : (term31 n) = (term9 n).
Proof. exact (eq_refl (term31 n)). Qed.
Lemma lem1274698 : term35 = term29.
Proof. exact (fun_ext (fun n : nat => @lem1274697 n)). Qed.
Lemma lem1274699 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274700 (n : nat) : (term34 n) = (term31 n).
Proof. exact (MK_COMB (@lem1274698) (@lem1274699 n)). Qed.
Lemma lem1274701 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274702 (n : nat) : (term36 n) = (term37 n).
Proof. exact (MK_COMB (@lem1274701) (@lem1274700 n)). Qed.
Lemma lem1274703 (n : nat) : (term31 n) = (term9 n).
Proof. exact (eq_refl (term31 n)). Qed.
Lemma lem1274704 (n : nat) : ((term34 n) = (term31 n)) = ((term31 n) = (term9 n)).
Proof. exact (MK_COMB (@lem1274702 n) (@lem1274703 n)). Qed.
Lemma lem1274705 (n : nat) : (term31 n) = (term9 n).
Proof. exact (EQ_MP (@lem1274704 n) (@lem1274696 n)). Qed.
Lemma lem1274706 (n : nat) : (term30 n) = (term9 n).
Proof. exact (TRANS (@lem1274692 n) (@lem1274705 n)). Qed.
Lemma lem1274707 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1274708 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem1274707) (@lem1274706 n)). Qed.
Lemma lem1274709 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1274710 (x : nadd) (n : nat) : (term40 x n) = (term41 x n).
Proof. exact (MK_COMB (@lem1274708 n) (@lem1274709 x n)). Qed.
Lemma lem1274711 (x : nadd) : (term26 x) = (term42 x).
Proof. exact (fun_ext (fun n : nat => @lem1274710 x n)). Qed.
Lemma lem1274712 (x : nadd) : (term25 x) = (term42 x).
Proof. exact (TRANS (@lem1274687 x) (@lem1274711 x)). Qed.
Lemma lem1274713 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274714 (x : nadd) (n : nat) : (term43 x n) = (term44 x n).
Proof. exact (MK_COMB (@lem1274712 x) (@lem1274713 n)). Qed.
Lemma lem1274716 {A B : Type'} (f : A -> B) (y : A) : (term32 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274717 (f : nat -> nat) (y : nat) : (term33 f y) = (f y).
Proof. exact (@lem1274716 nat nat f y). Qed.
Lemma lem1274718 (x : nadd) (n : nat) : (term45 x n) = (term44 x n).
Proof. exact (@lem1274717 (term42 x) n). Qed.
Lemma lem1274719 (x : nadd) (n : nat) : (term44 x n) = (term41 x n).
Proof. exact (eq_refl (term44 x n)). Qed.
Lemma lem1274720 (x : nadd) : (term46 x) = (term42 x).
Proof. exact (fun_ext (fun n : nat => @lem1274719 x n)). Qed.
Lemma lem1274721 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274722 (x : nadd) (n : nat) : (term45 x n) = (term44 x n).
Proof. exact (MK_COMB (@lem1274720 x) (@lem1274721 n)). Qed.
Lemma lem1274723 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274724 (x : nadd) (n : nat) : (term47 x n) = (term48 x n).
Proof. exact (MK_COMB (@lem1274723) (@lem1274722 x n)). Qed.
Lemma lem1274725 (x : nadd) (n : nat) : (term44 x n) = (term41 x n).
Proof. exact (eq_refl (term44 x n)). Qed.
Lemma lem1274726 (x : nadd) (n : nat) : ((term45 x n) = (term44 x n)) = ((term44 x n) = (term41 x n)).
Proof. exact (MK_COMB (@lem1274724 x n) (@lem1274725 x n)). Qed.
Lemma lem1274727 (x : nadd) (n : nat) : (term44 x n) = (term41 x n).
Proof. exact (EQ_MP (@lem1274726 x n) (@lem1274718 x n)). Qed.
Lemma lem1274728 (x : nadd) (n : nat) : (term43 x n) = (term41 x n).
Proof. exact (TRANS (@lem1274714 x n) (@lem1274727 x n)). Qed.
Lemma lem1274729 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1274730 (x : nadd) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem1274729) (@lem1274728 x n)). Qed.
Lemma lem1274731 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1274732 (x : nadd) (n : nat) : (term51 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem1274730 x n) (@lem1274731 x n)). Qed.
Lemma lem1274733 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1274734 (x : nadd) (n : nat) : (term53 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem1274733) (@lem1274732 x n)). Qed.
Lemma lem1274735 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1274736 (x : nadd) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (MK_COMB (@lem1274735) (@lem1274734 x n)). Qed.
Lemma lem1274737 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1274738 (x : nadd) (n : nat) (B : nat) : (term57 x n B) = (term58 x n B).
Proof. exact (MK_COMB (@lem1274736 x n) (@lem1274737 B)). Qed.
Lemma lem1274739 (x : nadd) (B : nat) : (term59 x B) = (term60 x B).
Proof. exact (fun_ext (fun n : nat => @lem1274738 x n B)). Qed.
Lemma lem1274740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1274741 (x : nadd) (B : nat) : (term61 x B) = (term62 x B).
Proof. exact (MK_COMB (@lem1274740) (@lem1274739 x B)). Qed.
Lemma lem1274746 (x : nadd) : (term63 x) = (term64 x).
Proof. exact (fun_ext (fun B : nat => @lem1274741 x B)). Qed.
Lemma lem1274747 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1274748 (x : nadd) : (term23 x) = (term65 x).
Proof. exact (MK_COMB (@lem1274747) (@lem1274746 x)). Qed.
Lemma lem1274753 (x : nadd) : (term22 x) = (term65 x).
Proof. exact (TRANS (@lem1274676 x) (@lem1274748 x)). Qed.
Lemma lem1274754 (x : nadd) : (term65 x) = (term22 x).
Proof. exact (SYM (@lem1274753 x)). Qed.
Lemma lem1274766 (n : nat) : (term9 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1274657 n) (@lem1274656 n)). Qed.
Lemma lem1274767 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1274768 (n : nat) : (term39 n) = term66.
Proof. exact (MK_COMB (@lem1274767) (@lem1274766 n)). Qed.
Lemma lem1274769 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1274770 (x : nadd) (n : nat) : (term41 x n) = (term67 x n).
Proof. exact (MK_COMB (@lem1274768 n) (@lem1274769 x n)). Qed.
Lemma lem1274772 (n : nat) : (term6 n) = n.
Proof. exact (EQ_MP (@lem1274623 n) (@lem1274622 n)). Qed.
Lemma lem1274773 (x : nadd) (n : nat) : (term67 x n) = (dest_nadd x n).
Proof. exact (@lem1274772 (dest_nadd x n)). Qed.
Lemma lem1274774 (x : nadd) (n : nat) : (term41 x n) = (dest_nadd x n).
Proof. exact (TRANS (@lem1274770 x n) (@lem1274773 x n)). Qed.
Lemma lem1274775 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1274776 (x : nadd) (n : nat) : (term50 x n) = (term68 x n).
Proof. exact (MK_COMB (@lem1274775) (@lem1274774 x n)). Qed.
Lemma lem1274777 (x : nadd) (n : nat) : (dest_nadd x n) = (dest_nadd x n).
Proof. exact (eq_refl (dest_nadd x n)). Qed.
Lemma lem1274778 (x : nadd) (n : nat) : (term52 x n) = (term69 x n).
Proof. exact (MK_COMB (@lem1274776 x n) (@lem1274777 x n)). Qed.
Lemma lem1274779 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1274780 (x : nadd) (n : nat) : (term54 x n) = (term70 x n).
Proof. exact (MK_COMB (@lem1274779) (@lem1274778 x n)). Qed.
Lemma lem1274782 (n : nat) : (term3 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1274599 n) (@lem1274598 n)). Qed.
Lemma lem1274783 (x : nadd) (n : nat) : (term70 x n) = (NUMERAL 0).
Proof. exact (@lem1274782 (dest_nadd x n)). Qed.
Lemma lem1274784 (x : nadd) (n : nat) : (term54 x n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1274780 x n) (@lem1274783 x n)). Qed.
Lemma lem1274785 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1274786 (x : nadd) (n : nat) : (term56 x n) = term71.
Proof. exact (MK_COMB (@lem1274785) (@lem1274784 x n)). Qed.
Lemma lem1274787 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1274788 (x : nadd) (n : nat) (B : nat) : (term58 x n B) = (term1 B).
Proof. exact (MK_COMB (@lem1274786 x n) (@lem1274787 B)). Qed.
Lemma lem1274790 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1274596 n) (@lem1274595 n)). Qed.
Lemma lem1274791 (B : nat) : (term1 B) = True.
Proof. exact (@lem1274790 B). Qed.
Lemma lem1274792 (x : nadd) (n : nat) (B : nat) : (term58 x n B) = True.
Proof. exact (TRANS (@lem1274788 x n B) (@lem1274791 B)). Qed.
Lemma lem1274793 (x : nadd) (B : nat) : (term60 x B) = term72.
Proof. exact (fun_ext (fun n : nat => @lem1274792 x n B)). Qed.
Lemma lem1274794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1274795 (x : nadd) (B : nat) : (term62 x B) = term73.
Proof. exact (MK_COMB (@lem1274794) (@lem1274793 x B)). Qed.
Lemma lem1274797 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1274798 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1274797 nat t). Qed.
Lemma lem1274799 : term73 = True.
Proof. exact (@lem1274798 True). Qed.
Lemma lem1274800 (x : nadd) (B : nat) : (term62 x B) = True.
Proof. exact (TRANS (@lem1274795 x B) (@lem1274799)). Qed.
Lemma lem1274801 (x : nadd) : (term64 x) = term72.
Proof. exact (fun_ext (fun B : nat => @lem1274800 x B)). Qed.
Lemma lem1274802 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1274803 (x : nadd) : (term65 x) = term76.
Proof. exact (MK_COMB (@lem1274802) (@lem1274801 x)). Qed.
Lemma lem1274805 {A : Type'} (t : Prop) : (term77 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1274806 (t : Prop) : (term78 t) = t.
Proof. exact (@lem1274805 nat t). Qed.
Lemma lem1274807 : term76 = True.
Proof. exact (@lem1274806 True). Qed.
Lemma lem1274808 (x : nadd) : (term65 x) = True.
Proof. exact (TRANS (@lem1274803 x) (@lem1274807)). Qed.
Lemma lem1274809 (x : nadd) : True = (term65 x).
Proof. exact (SYM (@lem1274808 x)). Qed.
Lemma lem1274810 (x : nadd) : term65 x.
Proof. exact (EQ_MP (@lem1274809 x) (@lem0)). Qed.
Lemma lem1274811 (x : nadd) : term22 x.
Proof. exact (EQ_MP (@lem1274754 x) (@lem1274810 x)). Qed.
Lemma lem1274816 : term79.
Proof. exact (fun x : nadd => @lem1274811 x). Qed.
