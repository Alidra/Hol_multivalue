Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_SQUARE_term_abbrevs.
Require Import EQ_SYM_EQ_spec.
Require Import REAL_ENTIRE_spec.
Require Import REAL_LE_SQUARE_spec.
Require Import REAL_LT_LE_spec.
Require Import thm0_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1630836 (x : real) : term0 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1630837 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1630838 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1630837 x) (@lem1630836 x)). Qed.
Lemma lem1630839 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1630838 x y). Qed.
Lemma lem1630840 (x : real) (y : real) : (term2 x y) = (((real_mul x y) = term3) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1630842 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem1630843 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (eq_refl (term5 A x)). Qed.
Lemma lem1630844 {A : Type'} (x : A) : term6 A x.
Proof. exact (EQ_MP (@lem1630843 A x) (@lem1630842 A x)). Qed.
Lemma lem1630845 {A : Type'} (x : A) (y : A) : term7 A x y.
Proof. exact (@lem1630844 A x y). Qed.
Lemma lem1630846 {A : Type'} (y : A) (x : A) : (term7 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term7 A x y)). Qed.
Lemma lem1630848 (x : real) : term8 x.
Proof. exact (@lem1382902 x). Qed.
Lemma lem1630849 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1630850 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1630849 x) (@lem1630848 x)). Qed.
Lemma lem1630851 (x : real) : (term9 x) = ((term9 x) = True).
Proof. exact (@lem7 (term9 x)). Qed.
Lemma lem1630853 (x : real) : term10 x.
Proof. exact (@lem1379381 x). Qed.
Lemma lem1630854 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1630855 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1630854 x) (@lem1630853 x)). Qed.
Lemma lem1630856 (x : real) (y : real) : term12 x y.
Proof. exact (@lem1630855 x y). Qed.
Lemma lem1630857 (x : real) (y : real) : (term12 x y) = ((real_lt x y) = (term13 x y)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1630862 (x : real) (y : real) : (real_lt x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1630857 x y) (@lem1630856 x y)). Qed.
Lemma lem1630863 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1630862 term3 (real_mul x x)). Qed.
Lemma lem1630867 (x : real) : (term9 x) = True.
Proof. exact (EQ_MP (@lem1630851 x) (@lem1630850 x)). Qed.
Lemma lem1630868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1630869 (x : real) : (term16 x) = (and True).
Proof. exact (MK_COMB (@lem1630868) (@lem1630867 x)). Qed.
Lemma lem1630872 (x : real) : (term17 x) = (term17 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1630873 (x : real) : (term15 x) = (term18 x).
Proof. exact (MK_COMB (@lem1630869 x) (@lem1630872 x)). Qed.
Lemma lem1630875 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1630876 (x : real) : (term18 x) = (term17 x).
Proof. exact (@lem1630875 (term17 x)). Qed.
Lemma lem1630879 (x : real) : (term15 x) = (term17 x).
Proof. exact (TRANS (@lem1630873 x) (@lem1630876 x)). Qed.
Lemma lem1630880 (x : real) : (term14 x) = (term17 x).
Proof. exact (TRANS (@lem1630863 x) (@lem1630879 x)). Qed.
Lemma lem1630881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1630882 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1630881) (@lem1630880 x)). Qed.
Lemma lem1630885 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1630886 (x : real) : ((term14 x) = (term21 x)) = ((term17 x) = (term21 x)).
Proof. exact (MK_COMB (@lem1630882 x) (@lem1630885 x)). Qed.
Lemma lem1630889 (x : real) : ((term17 x) = (term21 x)) = ((term14 x) = (term21 x)).
Proof. exact (SYM (@lem1630886 x)). Qed.
Lemma lem1630891 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1630846 A y x) (@lem1630845 A x y)). Qed.
Lemma lem1630892 (y : real) (x : real) : (x = y) = (y = x).
Proof. exact (@lem1630891 real y x). Qed.
Lemma lem1630893 (x : real) : (term3 = (real_mul x x)) = ((real_mul x x) = term3).
Proof. exact (@lem1630892 (real_mul x x) term3). Qed.
Lemma lem1630894 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1630895 (x : real) : (term17 x) = (term22 x).
Proof. exact (MK_COMB (@lem1630894) (@lem1630893 x)). Qed.
Lemma lem1630896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1630897 (x : real) : (term20 x) = (term23 x).
Proof. exact (MK_COMB (@lem1630896) (@lem1630895 x)). Qed.
Lemma lem1630898 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1630899 (x : real) : ((term17 x) = (term21 x)) = ((term22 x) = (term21 x)).
Proof. exact (MK_COMB (@lem1630897 x) (@lem1630898 x)). Qed.
Lemma lem1630900 (x : real) : ((term22 x) = (term21 x)) = ((term17 x) = (term21 x)).
Proof. exact (SYM (@lem1630899 x)). Qed.
Lemma lem1630904 (x : real) (y : real) : ((real_mul x y) = term3) = (term4 x y).
Proof. exact (EQ_MP (@lem1630840 x y) (@lem1630839 x y)). Qed.
Lemma lem1630905 (x : real) : ((real_mul x x) = term3) = (term24 x).
Proof. exact (@lem1630904 x x). Qed.
Lemma lem1630907 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem1630908 (x : real) : (term24 x) = (x = term3).
Proof. exact (@lem1630907 (x = term3)). Qed.
Lemma lem1630911 (x : real) : ((real_mul x x) = term3) = (x = term3).
Proof. exact (TRANS (@lem1630905 x) (@lem1630908 x)). Qed.
Lemma lem1630912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1630913 (x : real) : (term22 x) = (term21 x).
Proof. exact (MK_COMB (@lem1630912) (@lem1630911 x)). Qed.
Lemma lem1630914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1630915 (x : real) : (term23 x) = (term25 x).
Proof. exact (MK_COMB (@lem1630914) (@lem1630913 x)). Qed.
Lemma lem1630918 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1630919 (x : real) : ((term22 x) = (term21 x)) = ((term21 x) = (term21 x)).
Proof. exact (MK_COMB (@lem1630915 x) (@lem1630918 x)). Qed.
Lemma lem1630921 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1630922 (x : Prop) : (x = x) = True.
Proof. exact (@lem1630921 Prop x). Qed.
Lemma lem1630923 (x : real) : ((term21 x) = (term21 x)) = True.
Proof. exact (@lem1630922 (term21 x)). Qed.
Lemma lem1630924 (x : real) : ((term22 x) = (term21 x)) = True.
Proof. exact (TRANS (@lem1630919 x) (@lem1630923 x)). Qed.
Lemma lem1630925 (x : real) : True = ((term22 x) = (term21 x)).
Proof. exact (SYM (@lem1630924 x)). Qed.
Lemma lem1630926 (x : real) : (term22 x) = (term21 x).
Proof. exact (EQ_MP (@lem1630925 x) (@lem0)). Qed.
Lemma lem1630927 (x : real) : (term17 x) = (term21 x).
Proof. exact (EQ_MP (@lem1630900 x) (@lem1630926 x)). Qed.
Lemma lem1630928 (x : real) : (term14 x) = (term21 x).
Proof. exact (EQ_MP (@lem1630889 x) (@lem1630927 x)). Qed.
Lemma lem1630933 : term26.
Proof. exact (fun x : real => @lem1630928 x). Qed.
