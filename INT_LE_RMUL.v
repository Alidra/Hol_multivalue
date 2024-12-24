Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_RMUL_term_abbrevs.
Require Import REAL_LE_RMUL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303158 (x : int) : term0 x.
Proof. exact (@lem1584226 (real_of_int x)). Qed.
Lemma lem2303159 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303160 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303159 x) (@lem2303158 x)). Qed.
Lemma lem2303161 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303160 x (real_of_int y)). Qed.
Lemma lem2303162 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303163 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303162 x y) (@lem2303161 x y)). Qed.
Lemma lem2303164 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303163 x y (real_of_int z)). Qed.
Lemma lem2303165 (x : int) (y : int) (z : int) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303166 (x : int) (y : int) (z : int) : term5 x y z.
Proof. exact (EQ_MP (@lem2303165 x y z) (@lem2303164 x y z)). Qed.
Lemma lem2303168 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303170 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2303169) (@lem2303168 x y)). Qed.
Lemma lem2303172 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303173 : term10 = term11.
Proof. exact (@lem2303172 (NUMERAL 0)). Qed.
Lemma lem2303174 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303175 : term12 = term13.
Proof. exact (MK_COMB (@lem2303174) (@lem2303173)). Qed.
Lemma lem2303176 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2303177 (z : int) : (term14 z) = (term15 z).
Proof. exact (MK_COMB (@lem2303175) (@lem2303176 z)). Qed.
Lemma lem2303179 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303180 (z : int) : (term15 z) = (term16 z).
Proof. exact (@lem2303179 term17 z). Qed.
Lemma lem2303181 (z : int) : (term14 z) = (term16 z).
Proof. exact (TRANS (@lem2303177 z) (@lem2303180 z)). Qed.
Lemma lem2303182 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2303170 x y) (@lem2303181 z)). Qed.
Lemma lem2303183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303184 (x : int) (y : int) (z : int) : (term20 x y z) = (term21 x y z).
Proof. exact (MK_COMB (@lem2303183) (@lem2303182 x y z)). Qed.
Lemma lem2303186 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2303187 (x : int) (z : int) : (term22 x z) = (term23 x z).
Proof. exact (@lem2303186 x z). Qed.
Lemma lem2303188 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303189 (x : int) (z : int) : (term24 x z) = (term25 x z).
Proof. exact (MK_COMB (@lem2303188) (@lem2303187 x z)). Qed.
Lemma lem2303191 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2303192 (y : int) (z : int) : (term22 y z) = (term23 y z).
Proof. exact (@lem2303191 y z). Qed.
Lemma lem2303193 (x : int) (y : int) (z : int) : (term26 x y z) = (term27 x y z).
Proof. exact (MK_COMB (@lem2303189 x z) (@lem2303192 y z)). Qed.
Lemma lem2303195 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303196 (x : int) (y : int) (z : int) : (term27 x y z) = (term28 x y z).
Proof. exact (@lem2303195 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2303197 (x : int) (y : int) (z : int) : (term26 x y z) = (term28 x y z).
Proof. exact (TRANS (@lem2303193 x y z) (@lem2303196 x y z)). Qed.
Lemma lem2303198 (x : int) (y : int) (z : int) : (term5 x y z) = (term29 x y z).
Proof. exact (MK_COMB (@lem2303184 x y z) (@lem2303197 x y z)). Qed.
Lemma lem2303199 (x : int) (y : int) (z : int) : term29 x y z.
Proof. exact (EQ_MP (@lem2303198 x y z) (@lem2303166 x y z)). Qed.
Lemma lem2303200 (x : int) (y : int) : term30 x y.
Proof. exact (fun z : int => @lem2303199 x y z). Qed.
Lemma lem2303201 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2303200 x y). Qed.
Lemma lem2303202 : term32.
Proof. exact (fun x : int => @lem2303201 x). Qed.
