Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_NEGTOTAL_term_abbrevs.
Require Import REAL_LE_RNEG_spec.
Require Import thm0_spec.
Require Import thm1338512_spec.
Require Import thm1339697_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1382770 (x : real) : term0 x.
Proof. exact (@lem1339697 x). Qed.
Lemma lem1382771 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1382772 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1382771 x) (@lem1382770 x)). Qed.
Lemma lem1382773 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1382772 x y). Qed.
Lemma lem1382774 (y : real) (x : real) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1382775 (y : real) (x : real) : term3 y x.
Proof. exact (EQ_MP (@lem1382774 y x) (@lem1382773 x y)). Qed.
Lemma lem1382776 (y : real) (x : real) : (term3 y x) = ((term3 y x) = True).
Proof. exact (@lem7 (term3 y x)). Qed.
Lemma lem1382778 (x : real) : term4 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1382779 (x : real) : (term4 x) = ((term5 x) = x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1382781 (x : real) : term6 x.
Proof. exact (@lem1362465 x). Qed.
Lemma lem1382782 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1382783 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1382782 x) (@lem1382781 x)). Qed.
Lemma lem1382784 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1382783 x y). Qed.
Lemma lem1382785 (x : real) (y : real) : (term8 x y) = ((term9 x y) = (term10 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1382796 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1382785 x y) (@lem1382784 x y)). Qed.
Lemma lem1382797 (x : real) : (term11 x) = (term12 x).
Proof. exact (@lem1382796 term13 x). Qed.
Lemma lem1382799 (x : real) : (term5 x) = x.
Proof. exact (EQ_MP (@lem1382779 x) (@lem1382778 x)). Qed.
Lemma lem1382800 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1382801 (x : real) : (term14 x) = (real_le x).
Proof. exact (MK_COMB (@lem1382800) (@lem1382799 x)). Qed.
Lemma lem1382802 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1382803 (x : real) : (term12 x) = (term15 x).
Proof. exact (MK_COMB (@lem1382801 x) (@lem1382802)). Qed.
Lemma lem1382804 (x : real) : (term11 x) = (term15 x).
Proof. exact (TRANS (@lem1382797 x) (@lem1382803 x)). Qed.
Lemma lem1382805 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1382806 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1382805 x) (@lem1382804 x)). Qed.
Lemma lem1382808 (y : real) (x : real) : (term3 y x) = True.
Proof. exact (EQ_MP (@lem1382776 y x) (@lem1382775 y x)). Qed.
Lemma lem1382809 (x : real) : (term18 x) = True.
Proof. exact (@lem1382808 x term13). Qed.
Lemma lem1382810 (x : real) : (term17 x) = True.
Proof. exact (TRANS (@lem1382806 x) (@lem1382809 x)). Qed.
Lemma lem1382811 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1382810 x)). Qed.
Lemma lem1382812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382813 : term21 = term22.
Proof. exact (MK_COMB (@lem1382812) (@lem1382811)). Qed.
Lemma lem1382815 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1382816 (t : Prop) : (term24 t) = t.
Proof. exact (@lem1382815 real t). Qed.
Lemma lem1382817 : term22 = True.
Proof. exact (@lem1382816 True). Qed.
Lemma lem1382818 : term21 = True.
Proof. exact (TRANS (@lem1382813) (@lem1382817)). Qed.
Lemma lem1382819 : True = term21.
Proof. exact (SYM (@lem1382818)). Qed.
Lemma lem1382820 : term21.
Proof. exact (EQ_MP (@lem1382819) (@lem0)). Qed.
