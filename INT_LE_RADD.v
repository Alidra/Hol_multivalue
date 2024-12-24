Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_RADD_term_abbrevs.
Require Import REAL_LE_RADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303074 (x : int) : term0 x.
Proof. exact (@lem1501119 (real_of_int x)). Qed.
Lemma lem2303075 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303076 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303075 x) (@lem2303074 x)). Qed.
Lemma lem2303077 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303076 x (real_of_int y)). Qed.
Lemma lem2303078 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303079 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303078 x y) (@lem2303077 x y)). Qed.
Lemma lem2303080 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303079 x y (real_of_int z)). Qed.
Lemma lem2303081 (z : int) (x : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303082 (z : int) (x : int) (y : int) : (term5 x y z) = (term6 x y).
Proof. exact (EQ_MP (@lem2303081 z x y) (@lem2303080 x y z)). Qed.
Lemma lem2303084 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303085 (x : int) (z : int) : (term7 x z) = (term8 x z).
Proof. exact (@lem2303084 x z). Qed.
Lemma lem2303086 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303087 (x : int) (z : int) : (term9 x z) = (term10 x z).
Proof. exact (MK_COMB (@lem2303086) (@lem2303085 x z)). Qed.
Lemma lem2303089 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303090 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2303089 y z). Qed.
Lemma lem2303091 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2303087 x z) (@lem2303090 y z)). Qed.
Lemma lem2303093 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303094 (x : int) (y : int) (z : int) : (term11 x y z) = (term12 x y z).
Proof. exact (@lem2303093 (int_add x z) (int_add y z)). Qed.
Lemma lem2303095 (x : int) (y : int) (z : int) : (term5 x y z) = (term12 x y z).
Proof. exact (TRANS (@lem2303091 x y z) (@lem2303094 x y z)). Qed.
Lemma lem2303096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303097 (x : int) (y : int) (z : int) : (term13 x y z) = (term14 x y z).
Proof. exact (MK_COMB (@lem2303096) (@lem2303095 x y z)). Qed.
Lemma lem2303099 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303100 (z : int) (x : int) (y : int) : ((term5 x y z) = (term6 x y)) = ((term12 x y z) = (int_le x y)).
Proof. exact (MK_COMB (@lem2303097 x y z) (@lem2303099 x y)). Qed.
Lemma lem2303101 (z : int) (x : int) (y : int) : (term12 x y z) = (int_le x y).
Proof. exact (EQ_MP (@lem2303100 z x y) (@lem2303082 z x y)). Qed.
Lemma lem2303102 (x : int) (y : int) : term15 x y.
Proof. exact (fun z : int => @lem2303101 z x y). Qed.
Lemma lem2303103 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2303102 x y). Qed.
Lemma lem2303104 : term17.
Proof. exact (fun x : int => @lem2303103 x). Qed.
