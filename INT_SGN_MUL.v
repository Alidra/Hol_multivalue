Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_MUL_term_abbrevs.
Require Import REAL_SGN_MUL_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309855 (x : int) : term0 x.
Proof. exact (@lem1734254 (real_of_int x)). Qed.
Lemma lem2309856 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309857 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2309856 x) (@lem2309855 x)). Qed.
Lemma lem2309858 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2309857 x (real_of_int y)). Qed.
Lemma lem2309859 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2309860 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2309859 x y) (@lem2309858 x y)). Qed.
Lemma lem2309862 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2309863 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem2309864 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2309863) (@lem2309862 x y)). Qed.
Lemma lem2309866 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309867 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2309866 (int_mul x y)). Qed.
Lemma lem2309868 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2309864 x y) (@lem2309867 x y)). Qed.
Lemma lem2309869 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309870 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2309869) (@lem2309868 x y)). Qed.
Lemma lem2309872 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2309874 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2309873) (@lem2309872 x)). Qed.
Lemma lem2309876 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309877 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2309876 y). Qed.
Lemma lem2309878 (x : int) (y : int) : (term4 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2309874 x) (@lem2309877 y)). Qed.
Lemma lem2309880 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2309881 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (@lem2309880 (int_sgn x) (int_sgn y)). Qed.
Lemma lem2309882 (x : int) (y : int) : (term4 x y) = (term16 x y).
Proof. exact (TRANS (@lem2309878 x y) (@lem2309881 x y)). Qed.
Lemma lem2309883 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term10 x y) = (term16 x y)).
Proof. exact (MK_COMB (@lem2309870 x y) (@lem2309882 x y)). Qed.
Lemma lem2309885 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309886 (x : int) (y : int) : ((term10 x y) = (term16 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (@lem2309885 (term17 x y) (term18 x y)). Qed.
Lemma lem2309887 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (TRANS (@lem2309883 x y) (@lem2309886 x y)). Qed.
Lemma lem2309888 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2309887 x y) (@lem2309860 x y)). Qed.
Lemma lem2309889 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2309888 x y). Qed.
Lemma lem2309890 : term20.
Proof. exact (fun x : int => @lem2309889 x). Qed.
