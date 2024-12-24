Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADDNEG2_term_abbrevs.
Require Import REAL_LT_ADDNEG2_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303845 (x : int) : term0 x.
Proof. exact (@lem1504321 (real_of_int x)). Qed.
Lemma lem2303846 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303847 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303846 x) (@lem2303845 x)). Qed.
Lemma lem2303848 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303847 x (real_of_int y)). Qed.
Lemma lem2303849 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303850 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303849 x y) (@lem2303848 x y)). Qed.
Lemma lem2303851 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303850 x y (real_of_int z)). Qed.
Lemma lem2303852 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303853 (x : int) (z : int) (y : int) : (term5 x y z) = (term6 x z y).
Proof. exact (EQ_MP (@lem2303852 x z y) (@lem2303851 x y z)). Qed.
Lemma lem2303855 (x : int) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2303856 (y : int) : (term7 y) = (term8 y).
Proof. exact (@lem2303855 y). Qed.
Lemma lem2303857 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2303858 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem2303857 x) (@lem2303856 y)). Qed.
Lemma lem2303860 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303861 (x : int) (y : int) : (term11 x y) = (term14 x y).
Proof. exact (@lem2303860 x (int_neg y)). Qed.
Lemma lem2303862 (x : int) (y : int) : (term10 x y) = (term14 x y).
Proof. exact (TRANS (@lem2303858 x y) (@lem2303861 x y)). Qed.
Lemma lem2303863 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303864 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2303863) (@lem2303862 x y)). Qed.
Lemma lem2303865 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2303866 (x : int) (y : int) (z : int) : (term5 x y z) = (term17 x y z).
Proof. exact (MK_COMB (@lem2303864 x y) (@lem2303865 z)). Qed.
Lemma lem2303868 (x : int) (y : int) : (term18 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303869 (x : int) (y : int) (z : int) : (term17 x y z) = (term19 x y z).
Proof. exact (@lem2303868 (term20 x y) z). Qed.
Lemma lem2303870 (x : int) (y : int) (z : int) : (term5 x y z) = (term19 x y z).
Proof. exact (TRANS (@lem2303866 x y z) (@lem2303869 x y z)). Qed.
Lemma lem2303871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303872 (x : int) (y : int) (z : int) : (term21 x y z) = (term22 x y z).
Proof. exact (MK_COMB (@lem2303871) (@lem2303870 x y z)). Qed.
Lemma lem2303874 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303875 (z : int) (y : int) : (term12 z y) = (term13 z y).
Proof. exact (@lem2303874 z y). Qed.
Lemma lem2303876 (x : int) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2303877 (x : int) (z : int) (y : int) : (term6 x z y) = (term24 x z y).
Proof. exact (MK_COMB (@lem2303876 x) (@lem2303875 z y)). Qed.
Lemma lem2303879 (x : int) (y : int) : (term18 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303880 (x : int) (z : int) (y : int) : (term24 x z y) = (term25 x z y).
Proof. exact (@lem2303879 x (int_add z y)). Qed.
Lemma lem2303881 (x : int) (z : int) (y : int) : (term6 x z y) = (term25 x z y).
Proof. exact (TRANS (@lem2303877 x z y) (@lem2303880 x z y)). Qed.
Lemma lem2303882 (x : int) (z : int) (y : int) : ((term5 x y z) = (term6 x z y)) = ((term19 x y z) = (term25 x z y)).
Proof. exact (MK_COMB (@lem2303872 x y z) (@lem2303881 x z y)). Qed.
Lemma lem2303883 (x : int) (z : int) (y : int) : (term19 x y z) = (term25 x z y).
Proof. exact (EQ_MP (@lem2303882 x z y) (@lem2303853 x z y)). Qed.
Lemma lem2303884 (x : int) (y : int) : term26 x y.
Proof. exact (fun z : int => @lem2303883 x z y). Qed.
Lemma lem2303885 (x : int) : term27 x.
Proof. exact (fun y : int => @lem2303884 x y). Qed.
Lemma lem2303886 : term28.
Proof. exact (fun x : int => @lem2303885 x). Qed.
