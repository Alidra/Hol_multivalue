Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADD_SUB_term_abbrevs.
Require Import REAL_LT_ADD_SUB_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303918 (x : int) : term0 x.
Proof. exact (@lem1513116 (real_of_int x)). Qed.
Lemma lem2303919 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303920 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303919 x) (@lem2303918 x)). Qed.
Lemma lem2303921 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303920 x (real_of_int y)). Qed.
Lemma lem2303922 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303923 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303922 x y) (@lem2303921 x y)). Qed.
Lemma lem2303924 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303923 x y (real_of_int z)). Qed.
Lemma lem2303925 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303926 (x : int) (z : int) (y : int) : (term5 x y z) = (term6 x z y).
Proof. exact (EQ_MP (@lem2303925 x z y) (@lem2303924 x y z)). Qed.
Lemma lem2303928 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303929 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303930 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2303929) (@lem2303928 x y)). Qed.
Lemma lem2303931 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2303932 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2303930 x y) (@lem2303931 z)). Qed.
Lemma lem2303934 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303935 (x : int) (y : int) (z : int) : (term11 x y z) = (term13 x y z).
Proof. exact (@lem2303934 (int_add x y) z). Qed.
Lemma lem2303936 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2303932 x y z) (@lem2303935 x y z)). Qed.
Lemma lem2303937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303938 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2303937) (@lem2303936 x y z)). Qed.
Lemma lem2303940 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2303941 (z : int) (y : int) : (term16 z y) = (term17 z y).
Proof. exact (@lem2303940 z y). Qed.
Lemma lem2303942 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2303943 (x : int) (z : int) (y : int) : (term6 x z y) = (term19 x z y).
Proof. exact (MK_COMB (@lem2303942 x) (@lem2303941 z y)). Qed.
Lemma lem2303945 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303946 (x : int) (z : int) (y : int) : (term19 x z y) = (term20 x z y).
Proof. exact (@lem2303945 x (int_sub z y)). Qed.
Lemma lem2303947 (x : int) (z : int) (y : int) : (term6 x z y) = (term20 x z y).
Proof. exact (TRANS (@lem2303943 x z y) (@lem2303946 x z y)). Qed.
Lemma lem2303948 (x : int) (z : int) (y : int) : ((term5 x y z) = (term6 x z y)) = ((term13 x y z) = (term20 x z y)).
Proof. exact (MK_COMB (@lem2303938 x y z) (@lem2303947 x z y)). Qed.
Lemma lem2303949 (x : int) (z : int) (y : int) : (term13 x y z) = (term20 x z y).
Proof. exact (EQ_MP (@lem2303948 x z y) (@lem2303926 x z y)). Qed.
Lemma lem2303950 (x : int) (y : int) : term21 x y.
Proof. exact (fun z : int => @lem2303949 x z y). Qed.
Lemma lem2303951 (x : int) : term22 x.
Proof. exact (fun y : int => @lem2303950 x y). Qed.
Lemma lem2303952 : term23.
Proof. exact (fun x : int => @lem2303951 x). Qed.
