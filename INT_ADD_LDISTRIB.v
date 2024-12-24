Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_LDISTRIB_term_abbrevs.
Require Import thm1339188_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301068 (x : int) : term0 x.
Proof. exact (@lem1339188 (real_of_int x)). Qed.
Lemma lem2301069 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301070 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301069 x) (@lem2301068 x)). Qed.
Lemma lem2301071 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301070 x (real_of_int y)). Qed.
Lemma lem2301072 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301073 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2301072 y x) (@lem2301071 x y)). Qed.
Lemma lem2301074 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2301073 y x (real_of_int z)). Qed.
Lemma lem2301075 (y : int) (x : int) (z : int) : (term4 y x z) = ((term5 x y z) = (term6 y x z)).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2301076 (y : int) (x : int) (z : int) : (term5 x y z) = (term6 y x z).
Proof. exact (EQ_MP (@lem2301075 y x z) (@lem2301074 y x z)). Qed.
Lemma lem2301078 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301079 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2301078 y z). Qed.
Lemma lem2301080 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2301081 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2301080 x) (@lem2301079 y z)). Qed.
Lemma lem2301083 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301084 (x : int) (y : int) (z : int) : (term10 x y z) = (term13 x y z).
Proof. exact (@lem2301083 x (int_add y z)). Qed.
Lemma lem2301085 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2301081 x y z) (@lem2301084 x y z)). Qed.
Lemma lem2301086 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301087 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2301086) (@lem2301085 x y z)). Qed.
Lemma lem2301089 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301090 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2301091 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2301090) (@lem2301089 x y)). Qed.
Lemma lem2301093 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301094 (x : int) (z : int) : (term11 x z) = (term12 x z).
Proof. exact (@lem2301093 x z). Qed.
Lemma lem2301095 (y : int) (x : int) (z : int) : (term6 y x z) = (term18 y x z).
Proof. exact (MK_COMB (@lem2301091 x y) (@lem2301094 x z)). Qed.
Lemma lem2301097 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301098 (y : int) (x : int) (z : int) : (term18 y x z) = (term19 y x z).
Proof. exact (@lem2301097 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2301099 (y : int) (x : int) (z : int) : (term6 y x z) = (term19 y x z).
Proof. exact (TRANS (@lem2301095 y x z) (@lem2301098 y x z)). Qed.
Lemma lem2301100 (y : int) (x : int) (z : int) : ((term5 x y z) = (term6 y x z)) = ((term13 x y z) = (term19 y x z)).
Proof. exact (MK_COMB (@lem2301087 x y z) (@lem2301099 y x z)). Qed.
Lemma lem2301102 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301103 (y : int) (x : int) (z : int) : ((term13 x y z) = (term19 y x z)) = ((term20 x y z) = (term21 y x z)).
Proof. exact (@lem2301102 (term20 x y z) (term21 y x z)). Qed.
Lemma lem2301104 (y : int) (x : int) (z : int) : ((term5 x y z) = (term6 y x z)) = ((term20 x y z) = (term21 y x z)).
Proof. exact (TRANS (@lem2301100 y x z) (@lem2301103 y x z)). Qed.
Lemma lem2301105 (y : int) (x : int) (z : int) : (term20 x y z) = (term21 y x z).
Proof. exact (EQ_MP (@lem2301104 y x z) (@lem2301076 y x z)). Qed.
Lemma lem2301106 (y : int) (x : int) : term22 y x.
Proof. exact (fun z : int => @lem2301105 y x z). Qed.
Lemma lem2301107 (x : int) : term23 x.
Proof. exact (fun y : int => @lem2301106 y x). Qed.
Lemma lem2301108 : term24.
Proof. exact (fun x : int => @lem2301107 x). Qed.
