Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_LADD_IMP_term_abbrevs.
Require Import REAL_LT_LADD_IMP_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304056 (x : int) : term0 x.
Proof. exact (@lem1487294 (real_of_int x)). Qed.
Lemma lem2304057 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304058 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304057 x) (@lem2304056 x)). Qed.
Lemma lem2304059 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304058 x (real_of_int y)). Qed.
Lemma lem2304060 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304061 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2304060 y x) (@lem2304059 x y)). Qed.
Lemma lem2304062 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2304061 y x (real_of_int z)). Qed.
Lemma lem2304063 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2304064 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2304063 y x z) (@lem2304062 y x z)). Qed.
Lemma lem2304066 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304067 (y : int) (z : int) : (term6 y z) = (int_lt y z).
Proof. exact (@lem2304066 y z). Qed.
Lemma lem2304068 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304069 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (MK_COMB (@lem2304068) (@lem2304067 y z)). Qed.
Lemma lem2304071 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304072 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304073 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2304072) (@lem2304071 x y)). Qed.
Lemma lem2304075 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304076 (x : int) (z : int) : (term9 x z) = (term10 x z).
Proof. exact (@lem2304075 x z). Qed.
Lemma lem2304077 (y : int) (x : int) (z : int) : (term13 y x z) = (term14 y x z).
Proof. exact (MK_COMB (@lem2304073 x y) (@lem2304076 x z)). Qed.
Lemma lem2304079 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304080 (y : int) (x : int) (z : int) : (term14 y x z) = (term15 y x z).
Proof. exact (@lem2304079 (int_add x y) (int_add x z)). Qed.
Lemma lem2304081 (y : int) (x : int) (z : int) : (term13 y x z) = (term15 y x z).
Proof. exact (TRANS (@lem2304077 y x z) (@lem2304080 y x z)). Qed.
Lemma lem2304082 (y : int) (x : int) (z : int) : (term5 y x z) = (term16 y x z).
Proof. exact (MK_COMB (@lem2304069 y z) (@lem2304081 y x z)). Qed.
Lemma lem2304083 (y : int) (x : int) (z : int) : term16 y x z.
Proof. exact (EQ_MP (@lem2304082 y x z) (@lem2304064 y x z)). Qed.
Lemma lem2304084 (y : int) (x : int) : term17 y x.
Proof. exact (fun z : int => @lem2304083 y x z). Qed.
Lemma lem2304085 (x : int) : term18 x.
Proof. exact (fun y : int => @lem2304084 y x). Qed.
Lemma lem2304086 : term19.
Proof. exact (fun x : int => @lem2304085 x). Qed.
