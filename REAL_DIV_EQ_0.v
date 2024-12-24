Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_EQ_0_term_abbrevs.
Require Import REAL_ENTIRE_spec.
Require Import REAL_INV_EQ_0_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1595811 (x : real) : term0 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1595812 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1595813 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1595812 x) (@lem1595811 x)). Qed.
Lemma lem1595814 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1595813 x y). Qed.
Lemma lem1595815 (x : real) (y : real) : (term2 x y) = (((real_mul x y) = term3) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1595817 (x : real) : term5 x.
Proof. exact (@lem1588944 x). Qed.
Lemma lem1595818 (x : real) : (term5 x) = (((real_inv x) = term3) = (x = term3)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1595820 (x : real) : term6 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1595821 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1595822 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1595821 x) (@lem1595820 x)). Qed.
Lemma lem1595823 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1595822 x y). Qed.
Lemma lem1595824 (x : real) (y : real) : (term8 x y) = ((real_div x y) = (term9 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1595839 (x : real) (y : real) : (real_div x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1595824 x y) (@lem1595823 x y)). Qed.
Lemma lem1595840 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595841 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1595840) (@lem1595839 x y)). Qed.
Lemma lem1595842 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1595843 (x : real) (y : real) : ((real_div x y) = term3) = ((term9 x y) = term3).
Proof. exact (MK_COMB (@lem1595841 x y) (@lem1595842)). Qed.
Lemma lem1595845 (x : real) (y : real) : ((real_mul x y) = term3) = (term4 x y).
Proof. exact (EQ_MP (@lem1595815 x y) (@lem1595814 x y)). Qed.
Lemma lem1595846 (x : real) (y : real) : ((term9 x y) = term3) = (term12 x y).
Proof. exact (@lem1595845 x (real_inv y)). Qed.
Lemma lem1595852 (x : real) : ((real_inv x) = term3) = (x = term3).
Proof. exact (EQ_MP (@lem1595818 x) (@lem1595817 x)). Qed.
Lemma lem1595853 (y : real) : ((real_inv y) = term3) = (y = term3).
Proof. exact (@lem1595852 y). Qed.
Lemma lem1595856 (x : real) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1595857 (x : real) (y : real) : (term12 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1595856 x) (@lem1595853 y)). Qed.
Lemma lem1595860 (x : real) (y : real) : ((term9 x y) = term3) = (term4 x y).
Proof. exact (TRANS (@lem1595846 x y) (@lem1595857 x y)). Qed.
Lemma lem1595861 (x : real) (y : real) : ((real_div x y) = term3) = (term4 x y).
Proof. exact (TRANS (@lem1595843 x y) (@lem1595860 x y)). Qed.
Lemma lem1595862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1595863 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1595862) (@lem1595861 x y)). Qed.
Lemma lem1595870 (x : real) (y : real) : (term4 x y) = (term4 x y).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1595871 (x : real) (y : real) : (((real_div x y) = term3) = (term4 x y)) = ((term4 x y) = (term4 x y)).
Proof. exact (MK_COMB (@lem1595863 x y) (@lem1595870 x y)). Qed.
Lemma lem1595873 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595874 (x : Prop) : (x = x) = True.
Proof. exact (@lem1595873 Prop x). Qed.
Lemma lem1595875 (x : real) (y : real) : ((term4 x y) = (term4 x y)) = True.
Proof. exact (@lem1595874 (term4 x y)). Qed.
Lemma lem1595876 (x : real) (y : real) : (((real_div x y) = term3) = (term4 x y)) = True.
Proof. exact (TRANS (@lem1595871 x y) (@lem1595875 x y)). Qed.
Lemma lem1595877 (x : real) : (term16 x) = term17.
Proof. exact (fun_ext (fun y : real => @lem1595876 x y)). Qed.
Lemma lem1595878 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1595879 (x : real) : (term18 x) = term19.
Proof. exact (MK_COMB (@lem1595878) (@lem1595877 x)). Qed.
Lemma lem1595881 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595882 (t : Prop) : (term21 t) = t.
Proof. exact (@lem1595881 real t). Qed.
Lemma lem1595883 : term19 = True.
Proof. exact (@lem1595882 True). Qed.
Lemma lem1595884 (x : real) : (term18 x) = True.
Proof. exact (TRANS (@lem1595879 x) (@lem1595883)). Qed.
Lemma lem1595885 : term22 = term17.
Proof. exact (fun_ext (fun x : real => @lem1595884 x)). Qed.
Lemma lem1595886 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1595887 : term23 = term19.
Proof. exact (MK_COMB (@lem1595886) (@lem1595885)). Qed.
Lemma lem1595889 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595890 (t : Prop) : (term21 t) = t.
Proof. exact (@lem1595889 real t). Qed.
Lemma lem1595891 : term19 = True.
Proof. exact (@lem1595890 True). Qed.
Lemma lem1595892 : term23 = True.
Proof. exact (TRANS (@lem1595887) (@lem1595891)). Qed.
Lemma lem1595893 : True = term23.
Proof. exact (SYM (@lem1595892)). Qed.
Lemma lem1595894 : term23.
Proof. exact (EQ_MP (@lem1595893) (@lem0)). Qed.
