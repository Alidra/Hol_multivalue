Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_SGN_ABS_term_abbrevs.
Require Import REAL_EQ_SGN_ABS_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301826 (x : int) : term0 x.
Proof. exact (@lem1720940 (real_of_int x)). Qed.
Lemma lem2301827 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301828 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301827 x) (@lem2301826 x)). Qed.
Lemma lem2301829 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301828 x (real_of_int y)). Qed.
Lemma lem2301830 (x : int) (y : int) : (term2 x y) = (((real_of_int x) = (real_of_int y)) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301831 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (term3 x y).
Proof. exact (EQ_MP (@lem2301830 x y) (@lem2301829 x y)). Qed.
Lemma lem2301833 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301835 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem2301834) (@lem2301833 x y)). Qed.
Lemma lem2301837 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2301838 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301839 (x : int) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem2301838) (@lem2301837 x)). Qed.
Lemma lem2301841 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2301842 (y : int) : (term6 y) = (term7 y).
Proof. exact (@lem2301841 y). Qed.
Lemma lem2301843 (x : int) (y : int) : ((term6 x) = (term6 y)) = ((term7 x) = (term7 y)).
Proof. exact (MK_COMB (@lem2301839 x) (@lem2301842 y)). Qed.
Lemma lem2301845 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301846 (x : int) (y : int) : ((term7 x) = (term7 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (@lem2301845 (int_sgn x) (int_sgn y)). Qed.
Lemma lem2301847 (x : int) (y : int) : ((term6 x) = (term6 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (TRANS (@lem2301843 x y) (@lem2301846 x y)). Qed.
Lemma lem2301848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2301849 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem2301848) (@lem2301847 x y)). Qed.
Lemma lem2301851 (x : int) : (term12 x) = (term13 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2301852 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301853 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2301852) (@lem2301851 x)). Qed.
Lemma lem2301855 (x : int) : (term12 x) = (term13 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2301856 (y : int) : (term12 y) = (term13 y).
Proof. exact (@lem2301855 y). Qed.
Lemma lem2301857 (x : int) (y : int) : ((term12 x) = (term12 y)) = ((term13 x) = (term13 y)).
Proof. exact (MK_COMB (@lem2301853 x) (@lem2301856 y)). Qed.
Lemma lem2301859 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301860 (x : int) (y : int) : ((term13 x) = (term13 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (@lem2301859 (int_abs x) (int_abs y)). Qed.
Lemma lem2301861 (x : int) (y : int) : ((term12 x) = (term12 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (TRANS (@lem2301857 x y) (@lem2301860 x y)). Qed.
Lemma lem2301862 (x : int) (y : int) : (term3 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2301849 x y) (@lem2301861 x y)). Qed.
Lemma lem2301863 (x : int) (y : int) : (((real_of_int x) = (real_of_int y)) = (term3 x y)) = ((x = y) = (term16 x y)).
Proof. exact (MK_COMB (@lem2301835 x y) (@lem2301862 x y)). Qed.
Lemma lem2301864 (x : int) (y : int) : (x = y) = (term16 x y).
Proof. exact (EQ_MP (@lem2301863 x y) (@lem2301831 x y)). Qed.
Lemma lem2301865 (x : int) : term17 x.
Proof. exact (fun y : int => @lem2301864 x y). Qed.
Lemma lem2301866 : term18.
Proof. exact (fun x : int => @lem2301865 x). Qed.
