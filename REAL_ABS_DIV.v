Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_DIV_term_abbrevs.
Require Import REAL_ABS_INV_spec.
Require Import REAL_ABS_MUL_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1594833 (x : real) : term0 x.
Proof. exact (@lem1582313 x). Qed.
Lemma lem1594834 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1594835 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1594834 x) (@lem1594833 x)). Qed.
Lemma lem1594836 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1594835 x y). Qed.
Lemma lem1594837 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1594839 (x : real) : term5 x.
Proof. exact (@lem1594832 x). Qed.
Lemma lem1594840 (x : real) : (term5 x) = ((term6 x) = (term7 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1594842 (x : real) : term8 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1594843 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1594844 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1594843 x) (@lem1594842 x)). Qed.
Lemma lem1594845 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1594844 x y). Qed.
Lemma lem1594846 (x : real) (y : real) : (term10 x y) = ((real_div x y) = (term11 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1594859 (x : real) (y : real) : (real_div x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1594846 x y) (@lem1594845 x y)). Qed.
Lemma lem1594860 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1594861 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1594860) (@lem1594859 x y)). Qed.
Lemma lem1594863 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1594837 x y) (@lem1594836 x y)). Qed.
Lemma lem1594864 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (@lem1594863 x (real_inv y)). Qed.
Lemma lem1594866 (x : real) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem1594840 x) (@lem1594839 x)). Qed.
Lemma lem1594867 (y : real) : (term6 y) = (term7 y).
Proof. exact (@lem1594866 y). Qed.
Lemma lem1594868 (x : real) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1594869 (x : real) (y : real) : (term14 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1594868 x) (@lem1594867 y)). Qed.
Lemma lem1594870 (x : real) (y : real) : (term13 x y) = (term16 x y).
Proof. exact (TRANS (@lem1594864 x y) (@lem1594869 x y)). Qed.
Lemma lem1594871 (x : real) (y : real) : (term12 x y) = (term16 x y).
Proof. exact (TRANS (@lem1594861 x y) (@lem1594870 x y)). Qed.
Lemma lem1594872 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594873 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1594872) (@lem1594871 x y)). Qed.
Lemma lem1594875 (x : real) (y : real) : (real_div x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1594846 x y) (@lem1594845 x y)). Qed.
Lemma lem1594876 (x : real) (y : real) : (term19 x y) = (term16 x y).
Proof. exact (@lem1594875 (real_abs x) (real_abs y)). Qed.
Lemma lem1594877 (x : real) (y : real) : ((term12 x y) = (term19 x y)) = ((term16 x y) = (term16 x y)).
Proof. exact (MK_COMB (@lem1594873 x y) (@lem1594876 x y)). Qed.
Lemma lem1594879 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1594880 (x : real) : (x = x) = True.
Proof. exact (@lem1594879 real x). Qed.
Lemma lem1594881 (x : real) (y : real) : ((term16 x y) = (term16 x y)) = True.
Proof. exact (@lem1594880 (term16 x y)). Qed.
Lemma lem1594882 (x : real) (y : real) : ((term12 x y) = (term19 x y)) = True.
Proof. exact (TRANS (@lem1594877 x y) (@lem1594881 x y)). Qed.
Lemma lem1594883 (x : real) : (term20 x) = term21.
Proof. exact (fun_ext (fun y : real => @lem1594882 x y)). Qed.
Lemma lem1594884 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1594885 (x : real) : (term22 x) = term23.
Proof. exact (MK_COMB (@lem1594884) (@lem1594883 x)). Qed.
Lemma lem1594887 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1594888 (t : Prop) : (term25 t) = t.
Proof. exact (@lem1594887 real t). Qed.
Lemma lem1594889 : term23 = True.
Proof. exact (@lem1594888 True). Qed.
Lemma lem1594890 (x : real) : (term22 x) = True.
Proof. exact (TRANS (@lem1594885 x) (@lem1594889)). Qed.
Lemma lem1594891 : term26 = term21.
Proof. exact (fun_ext (fun x : real => @lem1594890 x)). Qed.
Lemma lem1594892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1594893 : term27 = term23.
Proof. exact (MK_COMB (@lem1594892) (@lem1594891)). Qed.
Lemma lem1594895 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1594896 (t : Prop) : (term25 t) = t.
Proof. exact (@lem1594895 real t). Qed.
Lemma lem1594897 : term23 = True.
Proof. exact (@lem1594896 True). Qed.
Lemma lem1594898 : term27 = True.
Proof. exact (TRANS (@lem1594893) (@lem1594897)). Qed.
Lemma lem1594899 : True = term27.
Proof. exact (SYM (@lem1594898)). Qed.
Lemma lem1594900 : term27.
Proof. exact (EQ_MP (@lem1594899) (@lem0)). Qed.
