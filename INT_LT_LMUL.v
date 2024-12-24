Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_LMUL_term_abbrevs.
Require Import REAL_LT_LMUL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304155 (x : int) : term0 x.
Proof. exact (@lem1584766 (real_of_int x)). Qed.
Lemma lem2304156 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304157 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304156 x) (@lem2304155 x)). Qed.
Lemma lem2304158 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304157 x (real_of_int y)). Qed.
Lemma lem2304159 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304160 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2304159 y x) (@lem2304158 x y)). Qed.
Lemma lem2304161 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2304160 y x (real_of_int z)). Qed.
Lemma lem2304162 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2304163 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2304162 y x z) (@lem2304161 y x z)). Qed.
Lemma lem2304165 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304166 : term7 = term8.
Proof. exact (@lem2304165 (NUMERAL 0)). Qed.
Lemma lem2304167 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304168 : term9 = term10.
Proof. exact (MK_COMB (@lem2304167) (@lem2304166)). Qed.
Lemma lem2304169 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2304170 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2304168) (@lem2304169 x)). Qed.
Lemma lem2304172 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304173 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2304172 term15 x). Qed.
Lemma lem2304174 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2304170 x) (@lem2304173 x)). Qed.
Lemma lem2304175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304176 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2304175) (@lem2304174 x)). Qed.
Lemma lem2304178 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304179 (y : int) (z : int) : (term13 y z) = (int_lt y z).
Proof. exact (@lem2304178 y z). Qed.
Lemma lem2304180 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2304176 x) (@lem2304179 y z)). Qed.
Lemma lem2304181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304182 (x : int) (y : int) (z : int) : (term20 x y z) = (term21 x y z).
Proof. exact (MK_COMB (@lem2304181) (@lem2304180 x y z)). Qed.
Lemma lem2304184 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304185 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304186 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2304185) (@lem2304184 x y)). Qed.
Lemma lem2304188 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304189 (x : int) (z : int) : (term22 x z) = (term23 x z).
Proof. exact (@lem2304188 x z). Qed.
Lemma lem2304190 (y : int) (x : int) (z : int) : (term26 y x z) = (term27 y x z).
Proof. exact (MK_COMB (@lem2304186 x y) (@lem2304189 x z)). Qed.
Lemma lem2304192 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304193 (y : int) (x : int) (z : int) : (term27 y x z) = (term28 y x z).
Proof. exact (@lem2304192 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2304194 (y : int) (x : int) (z : int) : (term26 y x z) = (term28 y x z).
Proof. exact (TRANS (@lem2304190 y x z) (@lem2304193 y x z)). Qed.
Lemma lem2304195 (y : int) (x : int) (z : int) : (term5 y x z) = (term29 y x z).
Proof. exact (MK_COMB (@lem2304182 x y z) (@lem2304194 y x z)). Qed.
Lemma lem2304196 (y : int) (x : int) (z : int) : term29 y x z.
Proof. exact (EQ_MP (@lem2304195 y x z) (@lem2304163 y x z)). Qed.
Lemma lem2304197 (y : int) (x : int) : term30 y x.
Proof. exact (fun z : int => @lem2304196 y x z). Qed.
Lemma lem2304198 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2304197 y x). Qed.
Lemma lem2304199 : term32.
Proof. exact (fun x : int => @lem2304198 x). Qed.
