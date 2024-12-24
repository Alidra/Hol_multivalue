Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1320816_term_abbrevs.
Require Import NADD_MUL_ASSOC_spec.
Require Import thm1318030_spec.
Require Import thm1318035_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1320676 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320677 (x : nadd) (y : nadd) (z : nadd) : (term1 x y z) = ((term2 x y z) = (term3 x y z)).
Proof. exact (@lem1320676 (term4 x y z) (term5 x y z)). Qed.
Lemma lem1320681 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320682 (x : nadd) (y : nadd) (z : nadd) : (term2 x y z) = (term8 x y z).
Proof. exact (@lem1320681 x (nadd_mul y z)). Qed.
Lemma lem1320684 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320685 (y : nadd) (z : nadd) : (term6 y z) = (term7 y z).
Proof. exact (@lem1320684 y z). Qed.
Lemma lem1320686 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1320687 (x : nadd) (y : nadd) (z : nadd) : (term8 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1320686 x) (@lem1320685 y z)). Qed.
Lemma lem1320688 (x : nadd) (y : nadd) (z : nadd) : (term2 x y z) = (term10 x y z).
Proof. exact (TRANS (@lem1320682 x y z) (@lem1320687 x y z)). Qed.
Lemma lem1320689 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1320690 (x : nadd) (y : nadd) (z : nadd) : (term11 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem1320689) (@lem1320688 x y z)). Qed.
Lemma lem1320692 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320693 (x : nadd) (y : nadd) (z : nadd) : (term3 x y z) = (term13 x y z).
Proof. exact (@lem1320692 (nadd_mul x y) z). Qed.
Lemma lem1320695 (x : nadd) (y : nadd) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1320696 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1320697 (x : nadd) (y : nadd) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1320696) (@lem1320695 x y)). Qed.
Lemma lem1320698 (z : nadd) : (term0 z) = (term0 z).
Proof. exact (eq_refl (term0 z)). Qed.
Lemma lem1320699 (x : nadd) (y : nadd) (z : nadd) : (term13 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem1320697 x y) (@lem1320698 z)). Qed.
Lemma lem1320700 (x : nadd) (y : nadd) (z : nadd) : (term3 x y z) = (term16 x y z).
Proof. exact (TRANS (@lem1320693 x y z) (@lem1320699 x y z)). Qed.
Lemma lem1320701 (x : nadd) (y : nadd) (z : nadd) : ((term2 x y z) = (term3 x y z)) = ((term10 x y z) = (term16 x y z)).
Proof. exact (MK_COMB (@lem1320690 x y z) (@lem1320700 x y z)). Qed.
Lemma lem1320704 (x : nadd) (y : nadd) (z : nadd) : (term1 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (TRANS (@lem1320677 x y z) (@lem1320701 x y z)). Qed.
Lemma lem1320705 (x : nadd) (y : nadd) : (term17 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1320704 x y z)). Qed.
Lemma lem1320706 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320707 (x : nadd) (y : nadd) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1320706) (@lem1320705 x y)). Qed.
Lemma lem1320713 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320714 (x : nadd) (y : nadd) : (term23 x y) = (term24 x y).
Proof. exact (@lem1320713 (term25 x y)). Qed.
Lemma lem1320715 (x : nadd) (y : nadd) (z : nadd) : (term26 x y z) = ((term10 x y z) = (term16 x y z)).
Proof. exact (eq_refl (term26 x y z)). Qed.
Lemma lem1320716 (x : nadd) (y : nadd) : (term27 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1320715 x y z)). Qed.
Lemma lem1320717 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320718 (x : nadd) (y : nadd) : (term23 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1320717) (@lem1320716 x y)). Qed.
Lemma lem1320719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320720 (x : nadd) (y : nadd) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1320719) (@lem1320718 x y)). Qed.
Lemma lem1320721 (x : nadd) (y : nadd) (z : hreal) : (term30 x y z) = ((term31 x y z) = (term32 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem1320722 (x : nadd) (y : nadd) : (term33 x y) = (term25 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1320721 x y z)). Qed.
Lemma lem1320723 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320724 (x : nadd) (y : nadd) : (term24 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1320723) (@lem1320722 x y)). Qed.
Lemma lem1320725 (x : nadd) (y : nadd) : ((term23 x y) = (term24 x y)) = ((term20 x y) = (term34 x y)).
Proof. exact (MK_COMB (@lem1320720 x y) (@lem1320724 x y)). Qed.
Lemma lem1320726 (x : nadd) (y : nadd) : (term20 x y) = (term34 x y).
Proof. exact (EQ_MP (@lem1320725 x y) (@lem1320714 x y)). Qed.
Lemma lem1320735 (x : nadd) (y : nadd) : (term19 x y) = (term34 x y).
Proof. exact (TRANS (@lem1320707 x y) (@lem1320726 x y)). Qed.
Lemma lem1320736 (x : nadd) : (term35 x) = (term36 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320735 x y)). Qed.
Lemma lem1320737 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320738 (x : nadd) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1320737) (@lem1320736 x)). Qed.
Lemma lem1320744 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320745 (x : nadd) : (term39 x) = (term40 x).
Proof. exact (@lem1320744 (term41 x)). Qed.
Lemma lem1320746 (x : nadd) (y : nadd) : (term42 x y) = (term34 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1320747 (x : nadd) : (term43 x) = (term36 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320746 x y)). Qed.
Lemma lem1320748 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320749 (x : nadd) : (term39 x) = (term38 x).
Proof. exact (MK_COMB (@lem1320748) (@lem1320747 x)). Qed.
Lemma lem1320750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320751 (x : nadd) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1320750) (@lem1320749 x)). Qed.
Lemma lem1320752 (x : nadd) (y : hreal) : (term46 x y) = (term47 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1320753 (x : nadd) : (term48 x) = (term41 x).
Proof. exact (fun_ext (fun y : hreal => @lem1320752 x y)). Qed.
Lemma lem1320754 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320755 (x : nadd) : (term40 x) = (term49 x).
Proof. exact (MK_COMB (@lem1320754) (@lem1320753 x)). Qed.
Lemma lem1320756 (x : nadd) : ((term39 x) = (term40 x)) = ((term38 x) = (term49 x)).
Proof. exact (MK_COMB (@lem1320751 x) (@lem1320755 x)). Qed.
Lemma lem1320757 (x : nadd) : (term38 x) = (term49 x).
Proof. exact (EQ_MP (@lem1320756 x) (@lem1320745 x)). Qed.
Lemma lem1320772 (x : nadd) : (term37 x) = (term49 x).
Proof. exact (TRANS (@lem1320738 x) (@lem1320757 x)). Qed.
Lemma lem1320773 : term50 = term51.
Proof. exact (fun_ext (fun x : nadd => @lem1320772 x)). Qed.
Lemma lem1320774 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320775 : term52 = term53.
Proof. exact (MK_COMB (@lem1320774) (@lem1320773)). Qed.
Lemma lem1320781 (P : hreal -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320782 : term54 = term55.
Proof. exact (@lem1320781 term56). Qed.
Lemma lem1320783 (x : nadd) : (term57 x) = (term49 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1320784 : term58 = term51.
Proof. exact (fun_ext (fun x : nadd => @lem1320783 x)). Qed.
Lemma lem1320785 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320786 : term54 = term53.
Proof. exact (MK_COMB (@lem1320785) (@lem1320784)). Qed.
Lemma lem1320787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320788 : term59 = term60.
Proof. exact (MK_COMB (@lem1320787) (@lem1320786)). Qed.
Lemma lem1320789 (x : hreal) : (term61 x) = (term62 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1320790 : term63 = term56.
Proof. exact (fun_ext (fun x : hreal => @lem1320789 x)). Qed.
Lemma lem1320791 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320792 : term55 = term64.
Proof. exact (MK_COMB (@lem1320791) (@lem1320790)). Qed.
Lemma lem1320793 : (term54 = term55) = (term53 = term64).
Proof. exact (MK_COMB (@lem1320788) (@lem1320792)). Qed.
Lemma lem1320794 : term53 = term64.
Proof. exact (EQ_MP (@lem1320793) (@lem1320782)). Qed.
Lemma lem1320815 : term52 = term64.
Proof. exact (TRANS (@lem1320775) (@lem1320794)). Qed.
Lemma lem1320816 : term64.
Proof. exact (EQ_MP (@lem1320815) (@lem1278498)). Qed.
