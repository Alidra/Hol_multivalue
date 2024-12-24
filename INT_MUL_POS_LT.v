Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_POS_LT_term_abbrevs.
Require Import REAL_MUL_POS_LT_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2306139 (x : int) : term0 x.
Proof. exact (@lem1614637 (real_of_int x)). Qed.
Lemma lem2306140 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306141 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306140 x) (@lem2306139 x)). Qed.
Lemma lem2306142 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306141 x (real_of_int y)). Qed.
Lemma lem2306143 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306144 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2306143 x y) (@lem2306142 x y)). Qed.
Lemma lem2306146 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306147 : term6 = term7.
Proof. exact (@lem2306146 (NUMERAL 0)). Qed.
Lemma lem2306148 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306149 : term8 = term9.
Proof. exact (MK_COMB (@lem2306148) (@lem2306147)). Qed.
Lemma lem2306151 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306152 (x : int) (y : int) : (term3 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2306149) (@lem2306151 x y)). Qed.
Lemma lem2306154 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306155 (x : int) (y : int) : (term12 x y) = (term14 x y).
Proof. exact (@lem2306154 term15 (int_mul x y)). Qed.
Lemma lem2306156 (x : int) (y : int) : (term3 x y) = (term14 x y).
Proof. exact (TRANS (@lem2306152 x y) (@lem2306155 x y)). Qed.
Lemma lem2306157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306158 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2306157) (@lem2306156 x y)). Qed.
Lemma lem2306160 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306161 : term6 = term7.
Proof. exact (@lem2306160 (NUMERAL 0)). Qed.
Lemma lem2306162 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306163 : term8 = term9.
Proof. exact (MK_COMB (@lem2306162) (@lem2306161)). Qed.
Lemma lem2306164 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306165 (x : int) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem2306163) (@lem2306164 x)). Qed.
Lemma lem2306167 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306168 (x : int) : (term19 x) = (term20 x).
Proof. exact (@lem2306167 term15 x). Qed.
Lemma lem2306169 (x : int) : (term18 x) = (term20 x).
Proof. exact (TRANS (@lem2306165 x) (@lem2306168 x)). Qed.
Lemma lem2306170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2306171 (x : int) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem2306170) (@lem2306169 x)). Qed.
Lemma lem2306173 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306174 : term6 = term7.
Proof. exact (@lem2306173 (NUMERAL 0)). Qed.
Lemma lem2306175 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306176 : term8 = term9.
Proof. exact (MK_COMB (@lem2306175) (@lem2306174)). Qed.
Lemma lem2306177 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2306178 (y : int) : (term18 y) = (term19 y).
Proof. exact (MK_COMB (@lem2306176) (@lem2306177 y)). Qed.
Lemma lem2306180 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306181 (y : int) : (term19 y) = (term20 y).
Proof. exact (@lem2306180 term15 y). Qed.
Lemma lem2306182 (y : int) : (term18 y) = (term20 y).
Proof. exact (TRANS (@lem2306178 y) (@lem2306181 y)). Qed.
Lemma lem2306183 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem2306171 x) (@lem2306182 y)). Qed.
Lemma lem2306184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2306185 (x : int) (y : int) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem2306184) (@lem2306183 x y)). Qed.
Lemma lem2306187 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306188 : term6 = term7.
Proof. exact (@lem2306187 (NUMERAL 0)). Qed.
Lemma lem2306189 (x : int) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem2306190 (x : int) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem2306189 x) (@lem2306188)). Qed.
Lemma lem2306192 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306193 (x : int) : (term29 x) = (term30 x).
Proof. exact (@lem2306192 x term15). Qed.
Lemma lem2306194 (x : int) : (term28 x) = (term30 x).
Proof. exact (TRANS (@lem2306190 x) (@lem2306193 x)). Qed.
Lemma lem2306195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2306196 (x : int) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem2306195) (@lem2306194 x)). Qed.
Lemma lem2306198 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306199 : term6 = term7.
Proof. exact (@lem2306198 (NUMERAL 0)). Qed.
Lemma lem2306200 (y : int) : (term27 y) = (term27 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem2306201 (y : int) : (term28 y) = (term29 y).
Proof. exact (MK_COMB (@lem2306200 y) (@lem2306199)). Qed.
Lemma lem2306203 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306204 (y : int) : (term29 y) = (term30 y).
Proof. exact (@lem2306203 y term15). Qed.
Lemma lem2306205 (y : int) : (term28 y) = (term30 y).
Proof. exact (TRANS (@lem2306201 y) (@lem2306204 y)). Qed.
Lemma lem2306206 (x : int) (y : int) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem2306196 x) (@lem2306205 y)). Qed.
Lemma lem2306207 (x : int) (y : int) : (term4 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem2306185 x y) (@lem2306206 x y)). Qed.
Lemma lem2306208 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term14 x y) = (term35 x y)).
Proof. exact (MK_COMB (@lem2306158 x y) (@lem2306207 x y)). Qed.
Lemma lem2306209 (x : int) (y : int) : (term14 x y) = (term35 x y).
Proof. exact (EQ_MP (@lem2306208 x y) (@lem2306144 x y)). Qed.
Lemma lem2306210 (x : int) : term36 x.
Proof. exact (fun y : int => @lem2306209 x y). Qed.
Lemma lem2306211 : term37.
Proof. exact (fun x : int => @lem2306210 x). Qed.
