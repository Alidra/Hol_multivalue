Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_BETWEEN2_term_abbrevs.
Require Import REAL_ABS_BETWEEN2_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2300127 (x0 : int) : term0 x0.
Proof. exact (@lem1550986 (real_of_int x0)). Qed.
Lemma lem2300128 (x0 : int) : (term0 x0) = (term1 x0).
Proof. exact (eq_refl (term0 x0)). Qed.
Lemma lem2300129 (x0 : int) : term1 x0.
Proof. exact (EQ_MP (@lem2300128 x0) (@lem2300127 x0)). Qed.
Lemma lem2300130 (x0 : int) (x : int) : term2 x0 x.
Proof. exact (@lem2300129 x0 (real_of_int x)). Qed.
Lemma lem2300131 (x0 : int) (x : int) : (term2 x0 x) = (term3 x0 x).
Proof. exact (eq_refl (term2 x0 x)). Qed.
Lemma lem2300132 (x0 : int) (x : int) : term3 x0 x.
Proof. exact (EQ_MP (@lem2300131 x0 x) (@lem2300130 x0 x)). Qed.
Lemma lem2300133 (x0 : int) (x : int) (y0 : int) : term4 x0 x y0.
Proof. exact (@lem2300132 x0 x (real_of_int y0)). Qed.
Lemma lem2300134 (y0 : int) (x0 : int) (x : int) : (term4 x0 x y0) = (term5 y0 x0 x).
Proof. exact (eq_refl (term4 x0 x y0)). Qed.
Lemma lem2300135 (y0 : int) (x0 : int) (x : int) : term5 y0 x0 x.
Proof. exact (EQ_MP (@lem2300134 y0 x0 x) (@lem2300133 x0 x y0)). Qed.
Lemma lem2300136 (y0 : int) (x0 : int) (x : int) (y : int) : term6 y0 x0 x y.
Proof. exact (@lem2300135 y0 x0 x (real_of_int y)). Qed.
Lemma lem2300137 (y0 : int) (x0 : int) (x : int) (y : int) : (term6 y0 x0 x y) = (term7 y0 x0 x y).
Proof. exact (eq_refl (term6 y0 x0 x y)). Qed.
Lemma lem2300138 (y0 : int) (x0 : int) (x : int) (y : int) : term7 y0 x0 x y.
Proof. exact (EQ_MP (@lem2300137 y0 x0 x y) (@lem2300136 y0 x0 x y)). Qed.
Lemma lem2300140 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300141 (x0 : int) (y0 : int) : (term8 x0 y0) = (int_lt x0 y0).
Proof. exact (@lem2300140 x0 y0). Qed.
Lemma lem2300142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2300143 (x0 : int) (y0 : int) : (term9 x0 y0) = (term10 x0 y0).
Proof. exact (MK_COMB (@lem2300142) (@lem2300141 x0 y0)). Qed.
Lemma lem2300145 (n : nat) : (real_of_num n) = (term11 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300146 : term12 = term13.
Proof. exact (@lem2300145 term14). Qed.
Lemma lem2300147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2300148 : term15 = term16.
Proof. exact (MK_COMB (@lem2300147) (@lem2300146)). Qed.
Lemma lem2300150 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300151 (x : int) (x0 : int) : (term17 x x0) = (term18 x x0).
Proof. exact (@lem2300150 x x0). Qed.
Lemma lem2300152 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300153 (x : int) (x0 : int) : (term19 x x0) = (term20 x x0).
Proof. exact (MK_COMB (@lem2300152) (@lem2300151 x x0)). Qed.
Lemma lem2300155 (x : int) : (term21 x) = (term22 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300156 (x : int) (x0 : int) : (term20 x x0) = (term23 x x0).
Proof. exact (@lem2300155 (int_sub x x0)). Qed.
Lemma lem2300157 (x : int) (x0 : int) : (term19 x x0) = (term23 x x0).
Proof. exact (TRANS (@lem2300153 x x0) (@lem2300156 x x0)). Qed.
Lemma lem2300158 (x : int) (x0 : int) : (term24 x x0) = (term25 x x0).
Proof. exact (MK_COMB (@lem2300148) (@lem2300157 x x0)). Qed.
Lemma lem2300160 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2300161 (x : int) (x0 : int) : (term25 x x0) = (term28 x x0).
Proof. exact (@lem2300160 term29 (term30 x x0)). Qed.
Lemma lem2300162 (x : int) (x0 : int) : (term24 x x0) = (term28 x x0).
Proof. exact (TRANS (@lem2300158 x x0) (@lem2300161 x x0)). Qed.
Lemma lem2300163 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300164 (x : int) (x0 : int) : (term31 x x0) = (term32 x x0).
Proof. exact (MK_COMB (@lem2300163) (@lem2300162 x x0)). Qed.
Lemma lem2300166 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300167 (y0 : int) (x0 : int) : (term17 y0 x0) = (term18 y0 x0).
Proof. exact (@lem2300166 y0 x0). Qed.
Lemma lem2300168 (x : int) (y0 : int) (x0 : int) : (term33 x y0 x0) = (term34 x y0 x0).
Proof. exact (MK_COMB (@lem2300164 x x0) (@lem2300167 y0 x0)). Qed.
Lemma lem2300170 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300171 (x : int) (y0 : int) (x0 : int) : (term34 x y0 x0) = (term35 x y0 x0).
Proof. exact (@lem2300170 (term36 x x0) (int_sub y0 x0)). Qed.
Lemma lem2300172 (x : int) (y0 : int) (x0 : int) : (term33 x y0 x0) = (term35 x y0 x0).
Proof. exact (TRANS (@lem2300168 x y0 x0) (@lem2300171 x y0 x0)). Qed.
Lemma lem2300173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2300174 (x : int) (y0 : int) (x0 : int) : (term37 x y0 x0) = (term38 x y0 x0).
Proof. exact (MK_COMB (@lem2300173) (@lem2300172 x y0 x0)). Qed.
Lemma lem2300176 (n : nat) : (real_of_num n) = (term11 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300177 : term12 = term13.
Proof. exact (@lem2300176 term14). Qed.
Lemma lem2300178 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2300179 : term15 = term16.
Proof. exact (MK_COMB (@lem2300178) (@lem2300177)). Qed.
Lemma lem2300181 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300182 (y : int) (y0 : int) : (term17 y y0) = (term18 y y0).
Proof. exact (@lem2300181 y y0). Qed.
Lemma lem2300183 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300184 (y : int) (y0 : int) : (term19 y y0) = (term20 y y0).
Proof. exact (MK_COMB (@lem2300183) (@lem2300182 y y0)). Qed.
Lemma lem2300186 (x : int) : (term21 x) = (term22 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300187 (y : int) (y0 : int) : (term20 y y0) = (term23 y y0).
Proof. exact (@lem2300186 (int_sub y y0)). Qed.
Lemma lem2300188 (y : int) (y0 : int) : (term19 y y0) = (term23 y y0).
Proof. exact (TRANS (@lem2300184 y y0) (@lem2300187 y y0)). Qed.
Lemma lem2300189 (y : int) (y0 : int) : (term24 y y0) = (term25 y y0).
Proof. exact (MK_COMB (@lem2300179) (@lem2300188 y y0)). Qed.
Lemma lem2300191 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2300192 (y : int) (y0 : int) : (term25 y y0) = (term28 y y0).
Proof. exact (@lem2300191 term29 (term30 y y0)). Qed.
Lemma lem2300193 (y : int) (y0 : int) : (term24 y y0) = (term28 y y0).
Proof. exact (TRANS (@lem2300189 y y0) (@lem2300192 y y0)). Qed.
Lemma lem2300194 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300195 (y : int) (y0 : int) : (term31 y y0) = (term32 y y0).
Proof. exact (MK_COMB (@lem2300194) (@lem2300193 y y0)). Qed.
Lemma lem2300197 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300198 (y0 : int) (x0 : int) : (term17 y0 x0) = (term18 y0 x0).
Proof. exact (@lem2300197 y0 x0). Qed.
Lemma lem2300199 (y : int) (y0 : int) (x0 : int) : (term39 y y0 x0) = (term40 y y0 x0).
Proof. exact (MK_COMB (@lem2300195 y y0) (@lem2300198 y0 x0)). Qed.
Lemma lem2300201 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300202 (y : int) (y0 : int) (x0 : int) : (term40 y y0 x0) = (term41 y y0 x0).
Proof. exact (@lem2300201 (term36 y y0) (int_sub y0 x0)). Qed.
Lemma lem2300203 (y : int) (y0 : int) (x0 : int) : (term39 y y0 x0) = (term41 y y0 x0).
Proof. exact (TRANS (@lem2300199 y y0 x0) (@lem2300202 y y0 x0)). Qed.
Lemma lem2300204 (x : int) (y : int) (y0 : int) (x0 : int) : (term42 x y y0 x0) = (term43 x y y0 x0).
Proof. exact (MK_COMB (@lem2300174 x y0 x0) (@lem2300203 y y0 x0)). Qed.
Lemma lem2300205 (x : int) (y : int) (y0 : int) (x0 : int) : (term44 x y y0 x0) = (term45 x y y0 x0).
Proof. exact (MK_COMB (@lem2300143 x0 y0) (@lem2300204 x y y0 x0)). Qed.
Lemma lem2300206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2300207 (x : int) (y : int) (y0 : int) (x0 : int) : (term46 x y y0 x0) = (term47 x y y0 x0).
Proof. exact (MK_COMB (@lem2300206) (@lem2300205 x y y0 x0)). Qed.
Lemma lem2300209 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300210 (y0 : int) (x0 : int) (x : int) (y : int) : (term7 y0 x0 x y) = (term48 y0 x0 x y).
Proof. exact (MK_COMB (@lem2300207 x y y0 x0) (@lem2300209 x y)). Qed.
Lemma lem2300211 (y0 : int) (x0 : int) (x : int) (y : int) : term48 y0 x0 x y.
Proof. exact (EQ_MP (@lem2300210 y0 x0 x y) (@lem2300138 y0 x0 x y)). Qed.
Lemma lem2300212 (y0 : int) (x0 : int) (x : int) : term49 y0 x0 x.
Proof. exact (fun y : int => @lem2300211 y0 x0 x y). Qed.
Lemma lem2300213 (x0 : int) (x : int) : term50 x0 x.
Proof. exact (fun y0 : int => @lem2300212 y0 x0 x). Qed.
Lemma lem2300214 (x0 : int) : term51 x0.
Proof. exact (fun x : int => @lem2300213 x0 x). Qed.
Lemma lem2300215 : term52.
Proof. exact (fun x0 : int => @lem2300214 x0). Qed.
