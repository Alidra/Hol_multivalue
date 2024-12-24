Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_LADD_term_abbrevs.
Require Import REAL_LT_LADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304025 (x : int) : term0 x.
Proof. exact (@lem1492692 (real_of_int x)). Qed.
Lemma lem2304026 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304027 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304026 x) (@lem2304025 x)). Qed.
Lemma lem2304028 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304027 x (real_of_int y)). Qed.
Lemma lem2304029 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304030 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304029 x y) (@lem2304028 x y)). Qed.
Lemma lem2304031 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304030 x y (real_of_int z)). Qed.
Lemma lem2304032 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 y x z) = (term6 y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304033 (x : int) (y : int) (z : int) : (term5 y x z) = (term6 y z).
Proof. exact (EQ_MP (@lem2304032 x y z) (@lem2304031 x y z)). Qed.
Lemma lem2304035 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304036 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304037 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2304036) (@lem2304035 x y)). Qed.
Lemma lem2304039 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304040 (x : int) (z : int) : (term7 x z) = (term8 x z).
Proof. exact (@lem2304039 x z). Qed.
Lemma lem2304041 (y : int) (x : int) (z : int) : (term5 y x z) = (term11 y x z).
Proof. exact (MK_COMB (@lem2304037 x y) (@lem2304040 x z)). Qed.
Lemma lem2304043 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304044 (y : int) (x : int) (z : int) : (term11 y x z) = (term12 y x z).
Proof. exact (@lem2304043 (int_add x y) (int_add x z)). Qed.
Lemma lem2304045 (y : int) (x : int) (z : int) : (term5 y x z) = (term12 y x z).
Proof. exact (TRANS (@lem2304041 y x z) (@lem2304044 y x z)). Qed.
Lemma lem2304046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304047 (y : int) (x : int) (z : int) : (term13 y x z) = (term14 y x z).
Proof. exact (MK_COMB (@lem2304046) (@lem2304045 y x z)). Qed.
Lemma lem2304049 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304050 (y : int) (z : int) : (term6 y z) = (int_lt y z).
Proof. exact (@lem2304049 y z). Qed.
Lemma lem2304051 (x : int) (y : int) (z : int) : ((term5 y x z) = (term6 y z)) = ((term12 y x z) = (int_lt y z)).
Proof. exact (MK_COMB (@lem2304047 y x z) (@lem2304050 y z)). Qed.
Lemma lem2304052 (x : int) (y : int) (z : int) : (term12 y x z) = (int_lt y z).
Proof. exact (EQ_MP (@lem2304051 x y z) (@lem2304033 x y z)). Qed.
Lemma lem2304053 (x : int) (y : int) : term15 x y.
Proof. exact (fun z : int => @lem2304052 x y z). Qed.
Lemma lem2304054 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2304053 x y). Qed.
Lemma lem2304055 : term17.
Proof. exact (fun x : int => @lem2304054 x). Qed.
