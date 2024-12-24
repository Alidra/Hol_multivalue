Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_SUB_term_abbrevs.
Require Import REAL_ABS_SUB_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300733 (x : int) : term0 x.
Proof. exact (@lem1533617 (real_of_int x)). Qed.
Lemma lem2300734 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300735 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300734 x) (@lem2300733 x)). Qed.
Lemma lem2300736 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300735 x (real_of_int y)). Qed.
Lemma lem2300737 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300738 (y : int) (x : int) : (term3 x y) = (term3 y x).
Proof. exact (EQ_MP (@lem2300737 y x) (@lem2300736 x y)). Qed.
Lemma lem2300740 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300741 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300742 (x : int) (y : int) : (term3 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2300741) (@lem2300740 x y)). Qed.
Lemma lem2300744 (x : int) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300745 (x : int) (y : int) : (term6 x y) = (term9 x y).
Proof. exact (@lem2300744 (int_sub x y)). Qed.
Lemma lem2300746 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (TRANS (@lem2300742 x y) (@lem2300745 x y)). Qed.
Lemma lem2300747 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300748 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem2300747) (@lem2300746 x y)). Qed.
Lemma lem2300750 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300751 (y : int) (x : int) : (term4 y x) = (term5 y x).
Proof. exact (@lem2300750 y x). Qed.
Lemma lem2300752 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300753 (y : int) (x : int) : (term3 y x) = (term6 y x).
Proof. exact (MK_COMB (@lem2300752) (@lem2300751 y x)). Qed.
Lemma lem2300755 (x : int) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300756 (y : int) (x : int) : (term6 y x) = (term9 y x).
Proof. exact (@lem2300755 (int_sub y x)). Qed.
Lemma lem2300757 (y : int) (x : int) : (term3 y x) = (term9 y x).
Proof. exact (TRANS (@lem2300753 y x) (@lem2300756 y x)). Qed.
Lemma lem2300758 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((term9 x y) = (term9 y x)).
Proof. exact (MK_COMB (@lem2300748 x y) (@lem2300757 y x)). Qed.
Lemma lem2300760 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300761 (y : int) (x : int) : ((term9 x y) = (term9 y x)) = ((term12 x y) = (term12 y x)).
Proof. exact (@lem2300760 (term12 x y) (term12 y x)). Qed.
Lemma lem2300762 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((term12 x y) = (term12 y x)).
Proof. exact (TRANS (@lem2300758 y x) (@lem2300761 y x)). Qed.
Lemma lem2300763 (y : int) (x : int) : (term12 x y) = (term12 y x).
Proof. exact (EQ_MP (@lem2300762 y x) (@lem2300738 y x)). Qed.
Lemma lem2300764 (x : int) : term13 x.
Proof. exact (fun y : int => @lem2300763 y x). Qed.
Lemma lem2300765 : term14.
Proof. exact (fun x : int => @lem2300764 x). Qed.
