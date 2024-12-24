Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_RMUL_EQ_term_abbrevs.
Require Import REAL_LE_RMUL_EQ_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303203 (x : int) : term0 x.
Proof. exact (@lem1600741 (real_of_int x)). Qed.
Lemma lem2303204 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303205 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303204 x) (@lem2303203 x)). Qed.
Lemma lem2303206 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303205 x (real_of_int y)). Qed.
Lemma lem2303207 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303208 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303207 x y) (@lem2303206 x y)). Qed.
Lemma lem2303209 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303208 x y (real_of_int z)). Qed.
Lemma lem2303210 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303211 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2303210 z x y) (@lem2303209 x y z)). Qed.
Lemma lem2303213 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303214 : term7 = term8.
Proof. exact (@lem2303213 (NUMERAL 0)). Qed.
Lemma lem2303215 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303216 : term9 = term10.
Proof. exact (MK_COMB (@lem2303215) (@lem2303214)). Qed.
Lemma lem2303217 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2303218 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2303216) (@lem2303217 z)). Qed.
Lemma lem2303220 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303221 (z : int) : (term12 z) = (term14 z).
Proof. exact (@lem2303220 term15 z). Qed.
Lemma lem2303222 (z : int) : (term11 z) = (term14 z).
Proof. exact (TRANS (@lem2303218 z) (@lem2303221 z)). Qed.
Lemma lem2303223 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303224 (z : int) : (term16 z) = (term17 z).
Proof. exact (MK_COMB (@lem2303223) (@lem2303222 z)). Qed.
Lemma lem2303226 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2303227 (x : int) (z : int) : (term18 x z) = (term19 x z).
Proof. exact (@lem2303226 x z). Qed.
Lemma lem2303228 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303229 (x : int) (z : int) : (term20 x z) = (term21 x z).
Proof. exact (MK_COMB (@lem2303228) (@lem2303227 x z)). Qed.
Lemma lem2303231 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2303232 (y : int) (z : int) : (term18 y z) = (term19 y z).
Proof. exact (@lem2303231 y z). Qed.
Lemma lem2303233 (x : int) (y : int) (z : int) : (term22 x y z) = (term23 x y z).
Proof. exact (MK_COMB (@lem2303229 x z) (@lem2303232 y z)). Qed.
Lemma lem2303235 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303236 (x : int) (y : int) (z : int) : (term23 x y z) = (term25 x y z).
Proof. exact (@lem2303235 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2303237 (x : int) (y : int) (z : int) : (term22 x y z) = (term25 x y z).
Proof. exact (TRANS (@lem2303233 x y z) (@lem2303236 x y z)). Qed.
Lemma lem2303238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303239 (x : int) (y : int) (z : int) : (term26 x y z) = (term27 x y z).
Proof. exact (MK_COMB (@lem2303238) (@lem2303237 x y z)). Qed.
Lemma lem2303241 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303242 (z : int) (x : int) (y : int) : ((term22 x y z) = (term24 x y)) = ((term25 x y z) = (int_le x y)).
Proof. exact (MK_COMB (@lem2303239 x y z) (@lem2303241 x y)). Qed.
Lemma lem2303243 (z : int) (x : int) (y : int) : (term5 z x y) = (term28 z x y).
Proof. exact (MK_COMB (@lem2303224 z) (@lem2303242 z x y)). Qed.
Lemma lem2303244 (z : int) (x : int) (y : int) : term28 z x y.
Proof. exact (EQ_MP (@lem2303243 z x y) (@lem2303211 z x y)). Qed.
Lemma lem2303245 (x : int) (y : int) : term29 x y.
Proof. exact (fun z : int => @lem2303244 z x y). Qed.
Lemma lem2303246 (x : int) : term30 x.
Proof. exact (fun y : int => @lem2303245 x y). Qed.
Lemma lem2303247 : term31.
Proof. exact (fun x : int => @lem2303246 x). Qed.
