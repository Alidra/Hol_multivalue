Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_SQUARE_ABS_term_abbrevs.
Require Import REAL_EQ_SQUARE_ABS_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301867 (x : int) : term0 x.
Proof. exact (@lem1646031 (real_of_int x)). Qed.
Lemma lem2301868 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301869 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301868 x) (@lem2301867 x)). Qed.
Lemma lem2301870 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301869 x (real_of_int y)). Qed.
Lemma lem2301871 (x : int) (y : int) : (term2 x y) = (((term3 x) = (term3 y)) = ((term4 x) = (term4 y))).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301872 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((term4 x) = (term4 y)).
Proof. exact (EQ_MP (@lem2301871 x y) (@lem2301870 x y)). Qed.
Lemma lem2301874 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2301875 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301876 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2301875) (@lem2301874 x)). Qed.
Lemma lem2301878 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2301879 (y : int) : (term3 y) = (term5 y).
Proof. exact (@lem2301878 y). Qed.
Lemma lem2301880 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((term5 x) = (term5 y)).
Proof. exact (MK_COMB (@lem2301876 x) (@lem2301879 y)). Qed.
Lemma lem2301882 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301883 (x : int) (y : int) : ((term5 x) = (term5 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (@lem2301882 (int_abs x) (int_abs y)). Qed.
Lemma lem2301884 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (TRANS (@lem2301880 x y) (@lem2301883 x y)). Qed.
Lemma lem2301885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301886 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2301885) (@lem2301884 x y)). Qed.
Lemma lem2301888 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2301889 (x : int) : (term4 x) = (term12 x).
Proof. exact (@lem2301888 x term13). Qed.
Lemma lem2301890 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301891 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2301890) (@lem2301889 x)). Qed.
Lemma lem2301893 (x : int) (n : nat) : (term10 x n) = (term11 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2301894 (y : int) : (term4 y) = (term12 y).
Proof. exact (@lem2301893 y term13). Qed.
Lemma lem2301895 (x : int) (y : int) : ((term4 x) = (term4 y)) = ((term12 x) = (term12 y)).
Proof. exact (MK_COMB (@lem2301891 x) (@lem2301894 y)). Qed.
Lemma lem2301897 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301898 (x : int) (y : int) : ((term12 x) = (term12 y)) = ((term16 x) = (term16 y)).
Proof. exact (@lem2301897 (term16 x) (term16 y)). Qed.
Lemma lem2301899 (x : int) (y : int) : ((term4 x) = (term4 y)) = ((term16 x) = (term16 y)).
Proof. exact (TRANS (@lem2301895 x y) (@lem2301898 x y)). Qed.
Lemma lem2301900 (x : int) (y : int) : (((term3 x) = (term3 y)) = ((term4 x) = (term4 y))) = (((int_abs x) = (int_abs y)) = ((term16 x) = (term16 y))).
Proof. exact (MK_COMB (@lem2301886 x y) (@lem2301899 x y)). Qed.
Lemma lem2301901 (x : int) (y : int) : ((int_abs x) = (int_abs y)) = ((term16 x) = (term16 y)).
Proof. exact (EQ_MP (@lem2301900 x y) (@lem2301872 x y)). Qed.
Lemma lem2301902 (x : int) : term17 x.
Proof. exact (fun y : int => @lem2301901 x y). Qed.
Lemma lem2301903 : term18.
Proof. exact (fun x : int => @lem2301902 x). Qed.
