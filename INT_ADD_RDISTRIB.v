Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_RDISTRIB_term_abbrevs.
Require Import REAL_ADD_RDISTRIB_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301158 (x : int) : term0 x.
Proof. exact (@lem1487144 (real_of_int x)). Qed.
Lemma lem2301159 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301160 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301159 x) (@lem2301158 x)). Qed.
Lemma lem2301161 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301160 x (real_of_int y)). Qed.
Lemma lem2301162 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301163 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301162 x y) (@lem2301161 x y)). Qed.
Lemma lem2301164 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301163 x y (real_of_int z)). Qed.
Lemma lem2301165 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301166 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2301165 x y z) (@lem2301164 x y z)). Qed.
Lemma lem2301168 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301169 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2301170 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2301169) (@lem2301168 x y)). Qed.
Lemma lem2301171 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2301172 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2301170 x y) (@lem2301171 z)). Qed.
Lemma lem2301174 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301175 (x : int) (y : int) (z : int) : (term11 x y z) = (term14 x y z).
Proof. exact (@lem2301174 (int_add x y) z). Qed.
Lemma lem2301176 (x : int) (y : int) (z : int) : (term5 x y z) = (term14 x y z).
Proof. exact (TRANS (@lem2301172 x y z) (@lem2301175 x y z)). Qed.
Lemma lem2301177 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301178 (x : int) (y : int) (z : int) : (term15 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem2301177) (@lem2301176 x y z)). Qed.
Lemma lem2301180 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301181 (x : int) (z : int) : (term12 x z) = (term13 x z).
Proof. exact (@lem2301180 x z). Qed.
Lemma lem2301182 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2301183 (x : int) (z : int) : (term17 x z) = (term18 x z).
Proof. exact (MK_COMB (@lem2301182) (@lem2301181 x z)). Qed.
Lemma lem2301185 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301186 (y : int) (z : int) : (term12 y z) = (term13 y z).
Proof. exact (@lem2301185 y z). Qed.
Lemma lem2301187 (x : int) (y : int) (z : int) : (term6 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2301183 x z) (@lem2301186 y z)). Qed.
Lemma lem2301189 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301190 (x : int) (y : int) (z : int) : (term19 x y z) = (term20 x y z).
Proof. exact (@lem2301189 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2301191 (x : int) (y : int) (z : int) : (term6 x y z) = (term20 x y z).
Proof. exact (TRANS (@lem2301187 x y z) (@lem2301190 x y z)). Qed.
Lemma lem2301192 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term14 x y z) = (term20 x y z)).
Proof. exact (MK_COMB (@lem2301178 x y z) (@lem2301191 x y z)). Qed.
Lemma lem2301194 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301195 (x : int) (y : int) (z : int) : ((term14 x y z) = (term20 x y z)) = ((term21 x y z) = (term22 x y z)).
Proof. exact (@lem2301194 (term21 x y z) (term22 x y z)). Qed.
Lemma lem2301196 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term21 x y z) = (term22 x y z)).
Proof. exact (TRANS (@lem2301192 x y z) (@lem2301195 x y z)). Qed.
Lemma lem2301197 (x : int) (y : int) (z : int) : (term21 x y z) = (term22 x y z).
Proof. exact (EQ_MP (@lem2301196 x y z) (@lem2301166 x y z)). Qed.
Lemma lem2301198 (x : int) (y : int) : term23 x y.
Proof. exact (fun z : int => @lem2301197 x y z). Qed.
Lemma lem2301199 (x : int) : term24 x.
Proof. exact (fun y : int => @lem2301198 x y). Qed.
Lemma lem2301200 : term25.
Proof. exact (fun x : int => @lem2301199 x). Qed.
