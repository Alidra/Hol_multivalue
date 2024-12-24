Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_SUB_RADD_term_abbrevs.
Require Import REAL_LT_SUB_RADD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2305007 (x : int) : term0 x.
Proof. exact (@lem1514143 (real_of_int x)). Qed.
Lemma lem2305008 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305009 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305008 x) (@lem2305007 x)). Qed.
Lemma lem2305010 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305009 x (real_of_int y)). Qed.
Lemma lem2305011 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305012 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305011 x y) (@lem2305010 x y)). Qed.
Lemma lem2305013 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305012 x y (real_of_int z)). Qed.
Lemma lem2305014 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305015 (x : int) (z : int) (y : int) : (term5 x y z) = (term6 x z y).
Proof. exact (EQ_MP (@lem2305014 x z y) (@lem2305013 x y z)). Qed.
Lemma lem2305017 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2305018 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2305019 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2305018) (@lem2305017 x y)). Qed.
Lemma lem2305020 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305021 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2305019 x y) (@lem2305020 z)). Qed.
Lemma lem2305023 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305024 (x : int) (y : int) (z : int) : (term11 x y z) = (term13 x y z).
Proof. exact (@lem2305023 (int_sub x y) z). Qed.
Lemma lem2305025 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2305021 x y z) (@lem2305024 x y z)). Qed.
Lemma lem2305026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2305027 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2305026) (@lem2305025 x y z)). Qed.
Lemma lem2305029 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2305030 (z : int) (y : int) : (term16 z y) = (term17 z y).
Proof. exact (@lem2305029 z y). Qed.
Lemma lem2305031 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2305032 (x : int) (z : int) (y : int) : (term6 x z y) = (term19 x z y).
Proof. exact (MK_COMB (@lem2305031 x) (@lem2305030 z y)). Qed.
Lemma lem2305034 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305035 (x : int) (z : int) (y : int) : (term19 x z y) = (term20 x z y).
Proof. exact (@lem2305034 x (int_add z y)). Qed.
Lemma lem2305036 (x : int) (z : int) (y : int) : (term6 x z y) = (term20 x z y).
Proof. exact (TRANS (@lem2305032 x z y) (@lem2305035 x z y)). Qed.
Lemma lem2305037 (x : int) (z : int) (y : int) : ((term5 x y z) = (term6 x z y)) = ((term13 x y z) = (term20 x z y)).
Proof. exact (MK_COMB (@lem2305027 x y z) (@lem2305036 x z y)). Qed.
Lemma lem2305038 (x : int) (z : int) (y : int) : (term13 x y z) = (term20 x z y).
Proof. exact (EQ_MP (@lem2305037 x z y) (@lem2305015 x z y)). Qed.
Lemma lem2305039 (x : int) (y : int) : term21 x y.
Proof. exact (fun z : int => @lem2305038 x z y). Qed.
Lemma lem2305040 (x : int) : term22 x.
Proof. exact (fun y : int => @lem2305039 x y). Qed.
Lemma lem2305041 : term23.
Proof. exact (fun x : int => @lem2305040 x). Qed.
