Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_REM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_DIVISION_spec.
Require Import INT_LT_REFL_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365720_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482679_spec.
Require Import thm1482981_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm19158_spec.
Require Import thm19490_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982717_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm69_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2400156 (n : int) : (term0 n) = (term1 n).
Proof. exact (@lem2318604 (term1 n)). Qed.
Lemma lem2400179 (n : int) : (term2 n) = (term3 n).
Proof. exact (@lem17362 (term4 n) ((int_abs n) = n)). Qed.
Lemma lem2400181 (x : int) (y : int) : (int_lt x y) = (term5 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2400182 (n : int) : (term4 n) = (term6 n).
Proof. exact (@lem2400181 term7 n). Qed.
Lemma lem2400184 (x : int) (y : int) : (int_le x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2400185 (n : int) : (term6 n) = (term9 n).
Proof. exact (@lem2400184 term10 n). Qed.
Lemma lem2400187 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2400188 : term13 = term14.
Proof. exact (@lem2400187 term7 term15). Qed.
Lemma lem2400190 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2400191 : term17 = term18.
Proof. exact (@lem2400190 (NUMERAL 0)). Qed.
Lemma lem2400192 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400193 : term19 = term20.
Proof. exact (MK_COMB (@lem2400192) (@lem2400191)). Qed.
Lemma lem2400195 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2400196 : term21 = term22.
Proof. exact (@lem2400195 term23). Qed.
Lemma lem2400197 : term14 = term24.
Proof. exact (MK_COMB (@lem2400193) (@lem2400196)). Qed.
Lemma lem2400198 : term13 = term24.
Proof. exact (TRANS (@lem2400188) (@lem2400197)). Qed.
Lemma lem2400199 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2400200 : term25 = term26.
Proof. exact (MK_COMB (@lem2400199) (@lem2400198)). Qed.
Lemma lem2400201 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2400202 (n : int) : (term9 n) = (term27 n).
Proof. exact (MK_COMB (@lem2400200) (@lem2400201 n)). Qed.
Lemma lem2400203 (n : int) : (term6 n) = (term27 n).
Proof. exact (TRANS (@lem2400185 n) (@lem2400202 n)). Qed.
Lemma lem2400204 (n : int) : (term4 n) = (term27 n).
Proof. exact (TRANS (@lem2400182 n) (@lem2400203 n)). Qed.
Lemma lem2400206 (y : int) (x : int) : (term28 x y) = (term29 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2400207 (n : int) : (term30 n) = (term31 n).
Proof. exact (@lem2400206 n (int_abs n)). Qed.
Lemma lem2400209 (x : int) (y : int) : (int_le x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2400210 (n : int) : (term32 n) = (term33 n).
Proof. exact (@lem2400209 (term34 n) n). Qed.
Lemma lem2400212 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2400213 (n : int) : (term35 n) = (term36 n).
Proof. exact (@lem2400212 (int_abs n) term15). Qed.
Lemma lem2400215 (x : int) : (term37 x) = (term38 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2400216 (n : int) : (term37 n) = (term38 n).
Proof. exact (@lem2400215 n). Qed.
Lemma lem2400217 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400218 (n : int) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem2400217) (@lem2400216 n)). Qed.
Lemma lem2400220 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2400221 : term21 = term22.
Proof. exact (@lem2400220 term23). Qed.
Lemma lem2400222 (n : int) : (term36 n) = (term41 n).
Proof. exact (MK_COMB (@lem2400218 n) (@lem2400221)). Qed.
Lemma lem2400223 (n : int) : (term35 n) = (term41 n).
Proof. exact (TRANS (@lem2400213 n) (@lem2400222 n)). Qed.
Lemma lem2400224 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2400225 (n : int) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem2400224) (@lem2400223 n)). Qed.
Lemma lem2400226 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2400227 (n : int) : (term33 n) = (term44 n).
Proof. exact (MK_COMB (@lem2400225 n) (@lem2400226 n)). Qed.
Lemma lem2400228 (n : int) : (term32 n) = (term44 n).
Proof. exact (TRANS (@lem2400210 n) (@lem2400227 n)). Qed.
Lemma lem2400229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2400230 (n : int) : (term45 n) = (term46 n).
Proof. exact (MK_COMB (@lem2400229) (@lem2400228 n)). Qed.
Lemma lem2400232 (x : int) (y : int) : (int_le x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2400233 (n : int) : (term47 n) = (term48 n).
Proof. exact (@lem2400232 (term49 n) (int_abs n)). Qed.
Lemma lem2400235 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2400236 (n : int) : (term50 n) = (term51 n).
Proof. exact (@lem2400235 n term15). Qed.
Lemma lem2400238 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2400239 : term21 = term22.
Proof. exact (@lem2400238 term23). Qed.
Lemma lem2400240 (n : int) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2400241 (n : int) : (term51 n) = (term53 n).
Proof. exact (MK_COMB (@lem2400240 n) (@lem2400239)). Qed.
Lemma lem2400242 (n : int) : (term50 n) = (term53 n).
Proof. exact (TRANS (@lem2400236 n) (@lem2400241 n)). Qed.
Lemma lem2400243 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2400244 (n : int) : (term54 n) = (term55 n).
Proof. exact (MK_COMB (@lem2400243) (@lem2400242 n)). Qed.
Lemma lem2400246 (x : int) : (term37 x) = (term38 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2400247 (n : int) : (term37 n) = (term38 n).
Proof. exact (@lem2400246 n). Qed.
Lemma lem2400248 (n : int) : (term48 n) = (term56 n).
Proof. exact (MK_COMB (@lem2400244 n) (@lem2400247 n)). Qed.
Lemma lem2400249 (n : int) : (term47 n) = (term56 n).
Proof. exact (TRANS (@lem2400233 n) (@lem2400248 n)). Qed.
Lemma lem2400250 (n : int) : (term31 n) = (term57 n).
Proof. exact (MK_COMB (@lem2400230 n) (@lem2400249 n)). Qed.
Lemma lem2400251 (n : int) : (term30 n) = (term57 n).
Proof. exact (TRANS (@lem2400207 n) (@lem2400250 n)). Qed.
Lemma lem2400252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2400253 (n : int) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem2400252) (@lem2400204 n)). Qed.
Lemma lem2400254 (n : int) : (term3 n) = (term60 n).
Proof. exact (MK_COMB (@lem2400253 n) (@lem2400251 n)). Qed.
Lemma lem2400255 (n : int) : (term2 n) = (term60 n).
Proof. exact (TRANS (@lem2400179 n) (@lem2400254 n)). Qed.
Lemma lem2400259 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2400285 (n : int) : (term62 n) = (term60 n).
Proof. exact (@lem2400259 (term60 n)). Qed.
Lemma lem2400286 (n : int) : (term27 n) = (term63 n).
Proof. exact (@lem1988287 (real_of_int n) term24). Qed.
Lemma lem2400293 : term24 = term22.
Proof. exact (@lem1982721 term22). Qed.
Lemma lem2400296 (n : int) : (term64 n) = (term64 n).
Proof. exact (eq_refl (term64 n)). Qed.
Lemma lem2400297 (n : int) : (term65 n) = (term66 n).
Proof. exact (MK_COMB (@lem2400296 n) (@lem2400293)). Qed.
Lemma lem2400298 (n : int) : (term66 n) = (term67 n).
Proof. exact (@lem1982792 (real_of_int n) term22). Qed.
Lemma lem2400300 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400301 : term22 = term69.
Proof. exact (@lem2400300 term23). Qed.
Lemma lem2400303 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400304 : term72 = term73.
Proof. exact (@lem2400303 term23). Qed.
Lemma lem2400305 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400306 : term74 = term75.
Proof. exact (MK_COMB (@lem2400305) (@lem2400304)). Qed.
Lemma lem2400307 : term76 = term77.
Proof. exact (MK_COMB (@lem2400306) (@lem2400301)). Qed.
Lemma lem2400308 : term77 = term78.
Proof. exact (@lem1981613 term72 term22 term22 term22). Qed.
Lemma lem2400310 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400311 : term81 = term82.
Proof. exact (@lem2400310 term23 term23). Qed.
Lemma lem2400312 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400313 : term84 = term23.
Proof. exact (EQ_MP (@lem2400312) (@lem940073)). Qed.
Lemma lem2400314 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400315 : term82 = term22.
Proof. exact (MK_COMB (@lem2400314) (@lem2400313)). Qed.
Lemma lem2400316 : term81 = term22.
Proof. exact (TRANS (@lem2400311) (@lem2400315)). Qed.
Lemma lem2400318 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2400319 : term76 = term87.
Proof. exact (@lem2400318 term23 term23). Qed.
Lemma lem2400320 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400321 : term84 = term23.
Proof. exact (EQ_MP (@lem2400320) (@lem940073)). Qed.
Lemma lem2400322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400323 : term82 = term22.
Proof. exact (MK_COMB (@lem2400322) (@lem2400321)). Qed.
Lemma lem2400324 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2400325 : term87 = term72.
Proof. exact (MK_COMB (@lem2400324) (@lem2400323)). Qed.
Lemma lem2400326 : term76 = term72.
Proof. exact (TRANS (@lem2400319) (@lem2400325)). Qed.
Lemma lem2400327 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2400328 : term88 = term89.
Proof. exact (MK_COMB (@lem2400327) (@lem2400326)). Qed.
Lemma lem2400329 : term78 = term73.
Proof. exact (MK_COMB (@lem2400328) (@lem2400316)). Qed.
Lemma lem2400330 : term77 = term73.
Proof. exact (TRANS (@lem2400308) (@lem2400329)). Qed.
Lemma lem2400331 : term76 = term73.
Proof. exact (TRANS (@lem2400307) (@lem2400330)). Qed.
Lemma lem2400333 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2400334 : term73 = term72.
Proof. exact (@lem2400333 term72). Qed.
Lemma lem2400335 : term76 = term72.
Proof. exact (TRANS (@lem2400331) (@lem2400334)). Qed.
Lemma lem2400336 (n : int) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2400339 (n : int) : (term67 n) = (term91 n).
Proof. exact (MK_COMB (@lem2400336 n) (@lem2400335)). Qed.
Lemma lem2400340 (n : int) : (term66 n) = (term91 n).
Proof. exact (TRANS (@lem2400298 n) (@lem2400339 n)). Qed.
Lemma lem2400341 (n : int) : (term65 n) = (term91 n).
Proof. exact (TRANS (@lem2400297 n) (@lem2400340 n)). Qed.
Lemma lem2400342 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2400343 (n : int) : (term92 n) = (term93 n).
Proof. exact (MK_COMB (@lem2400342) (@lem2400341 n)). Qed.
Lemma lem2400344 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400345 (n : int) : (term63 n) = (term94 n).
Proof. exact (MK_COMB (@lem2400343 n) (@lem2400344)). Qed.
Lemma lem2400346 (n : int) : (term27 n) = (term94 n).
Proof. exact (TRANS (@lem2400286 n) (@lem2400345 n)). Qed.
Lemma lem2400347 (n : int) : (term44 n) = (term95 n).
Proof. exact (@lem1988287 (real_of_int n) (term41 n)). Qed.
Lemma lem2400361 (n : int) : (term96 n) = (term97 n).
Proof. exact (@lem1982792 (real_of_int n) (term41 n)). Qed.
Lemma lem2400362 (n : int) : (term98 n) = (term99 n).
Proof. exact (@lem1982781 (term38 n) term72 term22). Qed.
Lemma lem2400364 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400365 : term22 = term69.
Proof. exact (@lem2400364 term23). Qed.
Lemma lem2400367 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400368 : term72 = term73.
Proof. exact (@lem2400367 term23). Qed.
Lemma lem2400369 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400370 : term74 = term75.
Proof. exact (MK_COMB (@lem2400369) (@lem2400368)). Qed.
Lemma lem2400371 : term76 = term77.
Proof. exact (MK_COMB (@lem2400370) (@lem2400365)). Qed.
Lemma lem2400372 : term77 = term78.
Proof. exact (@lem1981613 term72 term22 term22 term22). Qed.
Lemma lem2400374 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400375 : term81 = term82.
Proof. exact (@lem2400374 term23 term23). Qed.
Lemma lem2400376 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400377 : term84 = term23.
Proof. exact (EQ_MP (@lem2400376) (@lem940073)). Qed.
Lemma lem2400378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400379 : term82 = term22.
Proof. exact (MK_COMB (@lem2400378) (@lem2400377)). Qed.
Lemma lem2400380 : term81 = term22.
Proof. exact (TRANS (@lem2400375) (@lem2400379)). Qed.
Lemma lem2400382 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2400383 : term76 = term87.
Proof. exact (@lem2400382 term23 term23). Qed.
Lemma lem2400384 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400385 : term84 = term23.
Proof. exact (EQ_MP (@lem2400384) (@lem940073)). Qed.
Lemma lem2400386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400387 : term82 = term22.
Proof. exact (MK_COMB (@lem2400386) (@lem2400385)). Qed.
Lemma lem2400388 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2400389 : term87 = term72.
Proof. exact (MK_COMB (@lem2400388) (@lem2400387)). Qed.
Lemma lem2400390 : term76 = term72.
Proof. exact (TRANS (@lem2400383) (@lem2400389)). Qed.
Lemma lem2400391 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2400392 : term88 = term89.
Proof. exact (MK_COMB (@lem2400391) (@lem2400390)). Qed.
Lemma lem2400393 : term78 = term73.
Proof. exact (MK_COMB (@lem2400392) (@lem2400380)). Qed.
Lemma lem2400394 : term77 = term73.
Proof. exact (TRANS (@lem2400372) (@lem2400393)). Qed.
Lemma lem2400395 : term76 = term73.
Proof. exact (TRANS (@lem2400371) (@lem2400394)). Qed.
Lemma lem2400397 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2400398 : term73 = term72.
Proof. exact (@lem2400397 term72). Qed.
Lemma lem2400399 : term76 = term72.
Proof. exact (TRANS (@lem2400395) (@lem2400398)). Qed.
Lemma lem2400402 (n : int) : (term100 n) = (term100 n).
Proof. exact (eq_refl (term100 n)). Qed.
Lemma lem2400403 (n : int) : (term99 n) = (term101 n).
Proof. exact (MK_COMB (@lem2400402 n) (@lem2400399)). Qed.
Lemma lem2400404 (n : int) : (term98 n) = (term101 n).
Proof. exact (TRANS (@lem2400362 n) (@lem2400403 n)). Qed.
Lemma lem2400405 (n : int) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2400406 (n : int) : (term97 n) = (term102 n).
Proof. exact (MK_COMB (@lem2400405 n) (@lem2400404 n)). Qed.
Lemma lem2400411 (n : int) : (term102 n) = (term103 n).
Proof. exact (@lem1982757 (term104 n) (real_of_int n) term72). Qed.
Lemma lem2400412 (n : int) : (term97 n) = (term103 n).
Proof. exact (TRANS (@lem2400406 n) (@lem2400411 n)). Qed.
Lemma lem2400414 (n : int) : (term96 n) = (term103 n).
Proof. exact (TRANS (@lem2400361 n) (@lem2400412 n)). Qed.
Lemma lem2400415 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2400416 (n : int) : (term105 n) = (term106 n).
Proof. exact (MK_COMB (@lem2400415) (@lem2400414 n)). Qed.
Lemma lem2400417 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400418 (n : int) : (term95 n) = (term107 n).
Proof. exact (MK_COMB (@lem2400416 n) (@lem2400417)). Qed.
Lemma lem2400419 (n : int) : (term44 n) = (term107 n).
Proof. exact (TRANS (@lem2400347 n) (@lem2400418 n)). Qed.
Lemma lem2400420 (n : int) : (term56 n) = (term108 n).
Proof. exact (@lem1988287 (term38 n) (term53 n)). Qed.
Lemma lem2400434 (n : int) : (term109 n) = (term110 n).
Proof. exact (@lem1982792 (term38 n) (term53 n)). Qed.
Lemma lem2400435 (n : int) : (term111 n) = (term112 n).
Proof. exact (@lem1982781 (real_of_int n) term72 term22). Qed.
Lemma lem2400437 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400438 : term22 = term69.
Proof. exact (@lem2400437 term23). Qed.
Lemma lem2400440 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400441 : term72 = term73.
Proof. exact (@lem2400440 term23). Qed.
Lemma lem2400442 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400443 : term74 = term75.
Proof. exact (MK_COMB (@lem2400442) (@lem2400441)). Qed.
Lemma lem2400444 : term76 = term77.
Proof. exact (MK_COMB (@lem2400443) (@lem2400438)). Qed.
Lemma lem2400445 : term77 = term78.
Proof. exact (@lem1981613 term72 term22 term22 term22). Qed.
Lemma lem2400447 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400448 : term81 = term82.
Proof. exact (@lem2400447 term23 term23). Qed.
Lemma lem2400449 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400450 : term84 = term23.
Proof. exact (EQ_MP (@lem2400449) (@lem940073)). Qed.
Lemma lem2400451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400452 : term82 = term22.
Proof. exact (MK_COMB (@lem2400451) (@lem2400450)). Qed.
Lemma lem2400453 : term81 = term22.
Proof. exact (TRANS (@lem2400448) (@lem2400452)). Qed.
Lemma lem2400455 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2400456 : term76 = term87.
Proof. exact (@lem2400455 term23 term23). Qed.
Lemma lem2400457 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400458 : term84 = term23.
Proof. exact (EQ_MP (@lem2400457) (@lem940073)). Qed.
Lemma lem2400459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400460 : term82 = term22.
Proof. exact (MK_COMB (@lem2400459) (@lem2400458)). Qed.
Lemma lem2400461 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2400462 : term87 = term72.
Proof. exact (MK_COMB (@lem2400461) (@lem2400460)). Qed.
Lemma lem2400463 : term76 = term72.
Proof. exact (TRANS (@lem2400456) (@lem2400462)). Qed.
Lemma lem2400464 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2400465 : term88 = term89.
Proof. exact (MK_COMB (@lem2400464) (@lem2400463)). Qed.
Lemma lem2400466 : term78 = term73.
Proof. exact (MK_COMB (@lem2400465) (@lem2400453)). Qed.
Lemma lem2400467 : term77 = term73.
Proof. exact (TRANS (@lem2400445) (@lem2400466)). Qed.
Lemma lem2400468 : term76 = term73.
Proof. exact (TRANS (@lem2400444) (@lem2400467)). Qed.
Lemma lem2400470 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2400471 : term73 = term72.
Proof. exact (@lem2400470 term72). Qed.
Lemma lem2400472 : term76 = term72.
Proof. exact (TRANS (@lem2400468) (@lem2400471)). Qed.
Lemma lem2400475 (n : int) : (term113 n) = (term113 n).
Proof. exact (eq_refl (term113 n)). Qed.
Lemma lem2400476 (n : int) : (term112 n) = (term114 n).
Proof. exact (MK_COMB (@lem2400475 n) (@lem2400472)). Qed.
Lemma lem2400477 (n : int) : (term111 n) = (term114 n).
Proof. exact (TRANS (@lem2400435 n) (@lem2400476 n)). Qed.
Lemma lem2400478 (n : int) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem2400481 (n : int) : (term110 n) = (term115 n).
Proof. exact (MK_COMB (@lem2400478 n) (@lem2400477 n)). Qed.
Lemma lem2400483 (n : int) : (term109 n) = (term115 n).
Proof. exact (TRANS (@lem2400434 n) (@lem2400481 n)). Qed.
Lemma lem2400484 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2400485 (n : int) : (term116 n) = (term117 n).
Proof. exact (MK_COMB (@lem2400484) (@lem2400483 n)). Qed.
Lemma lem2400486 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400487 (n : int) : (term108 n) = (term118 n).
Proof. exact (MK_COMB (@lem2400485 n) (@lem2400486)). Qed.
Lemma lem2400488 (n : int) : (term56 n) = (term118 n).
Proof. exact (TRANS (@lem2400420 n) (@lem2400487 n)). Qed.
Lemma lem2400489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2400490 (n : int) : (term46 n) = (term119 n).
Proof. exact (MK_COMB (@lem2400489) (@lem2400419 n)). Qed.
Lemma lem2400491 (n : int) : (term57 n) = (term120 n).
Proof. exact (MK_COMB (@lem2400490 n) (@lem2400488 n)). Qed.
Lemma lem2400492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2400493 (n : int) : (term59 n) = (term121 n).
Proof. exact (MK_COMB (@lem2400492) (@lem2400346 n)). Qed.
Lemma lem2400494 (n : int) : (term60 n) = (term122 n).
Proof. exact (MK_COMB (@lem2400493 n) (@lem2400491 n)). Qed.
Lemma lem2400501 (n : int) : (term62 n) = (term122 n).
Proof. exact (TRANS (@lem2400285 n) (@lem2400494 n)). Qed.
Lemma lem2400518 (n : int) : (term122 n) = (term123 n).
Proof. exact (@lem19158 (term107 n) (term94 n) (term118 n)). Qed.
Lemma lem2400519 (n : int) : (term62 n) = (term123 n).
Proof. exact (TRANS (@lem2400501 n) (@lem2400518 n)). Qed.
Lemma lem2400521 (a : real) (x : real) (r : real) : (term124 x a r) = (term125 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2400522 (n : int) : (term107 n) = (term126 n).
Proof. exact (@lem2400521 (term91 n) (real_of_int n) term18). Qed.
Lemma lem2400529 (n : int) : (term127 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2400538 (n : int) : (term128 n) = (term128 n).
Proof. exact (eq_refl (term128 n)). Qed.
Lemma lem2400539 (n : int) : (term129 n) = (term130 n).
Proof. exact (MK_COMB (@lem2400538 n) (@lem2400529 n)). Qed.
Lemma lem2400540 (n : int) : (term130 n) = (term131 n).
Proof. exact (@lem1982759 (real_of_int n) (real_of_int n) term72). Qed.
Lemma lem2400541 (n : int) : (term132 n) = (term133 n).
Proof. exact (@lem1982717 (real_of_int n)). Qed.
Lemma lem2400543 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400544 : term22 = term69.
Proof. exact (@lem2400543 term23). Qed.
Lemma lem2400546 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400547 : term22 = term69.
Proof. exact (@lem2400546 term23). Qed.
Lemma lem2400548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400549 : term134 = term135.
Proof. exact (MK_COMB (@lem2400548) (@lem2400547)). Qed.
Lemma lem2400550 : term136 = term137.
Proof. exact (MK_COMB (@lem2400549) (@lem2400544)). Qed.
Lemma lem2400551 : term138.
Proof. exact (@lem1981473 term22 term22 term22 term22 term139 term22). Qed.
Lemma lem2400553 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400554 : term141 = term142.
Proof. exact (@lem2400553 (NUMERAL 0) term23). Qed.
Lemma lem2400555 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400556 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400557 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400556 h1) (fun h1 : term142 = True => @lem2400555)). Qed.
Lemma lem2400558 : term142 = True.
Proof. exact (EQ_MP (@lem2400557) (@lem2400555)). Qed.
Lemma lem2400559 : term141 = True.
Proof. exact (TRANS (@lem2400554) (@lem2400558)). Qed.
Lemma lem2400560 : True = term141.
Proof. exact (SYM (@lem2400559)). Qed.
Lemma lem2400561 : term141.
Proof. exact (EQ_MP (@lem2400560) (@lem0)). Qed.
Lemma lem2400562 : term144.
Proof. exact (@lem2400551 (@lem2400561)). Qed.
Lemma lem2400564 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400565 : term141 = term142.
Proof. exact (@lem2400564 (NUMERAL 0) term23). Qed.
Lemma lem2400566 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400567 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400568 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400567 h1) (fun h1 : term142 = True => @lem2400566)). Qed.
Lemma lem2400569 : term142 = True.
Proof. exact (EQ_MP (@lem2400568) (@lem2400566)). Qed.
Lemma lem2400570 : term141 = True.
Proof. exact (TRANS (@lem2400565) (@lem2400569)). Qed.
Lemma lem2400571 : True = term141.
Proof. exact (SYM (@lem2400570)). Qed.
Lemma lem2400572 : term141.
Proof. exact (EQ_MP (@lem2400571) (@lem0)). Qed.
Lemma lem2400573 : term145.
Proof. exact (@lem2400562 (@lem2400572)). Qed.
Lemma lem2400575 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400576 : term141 = term142.
Proof. exact (@lem2400575 (NUMERAL 0) term23). Qed.
Lemma lem2400577 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400578 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400579 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400578 h1) (fun h1 : term142 = True => @lem2400577)). Qed.
Lemma lem2400580 : term142 = True.
Proof. exact (EQ_MP (@lem2400579) (@lem2400577)). Qed.
Lemma lem2400581 : term141 = True.
Proof. exact (TRANS (@lem2400576) (@lem2400580)). Qed.
Lemma lem2400582 : True = term141.
Proof. exact (SYM (@lem2400581)). Qed.
Lemma lem2400583 : term141.
Proof. exact (EQ_MP (@lem2400582) (@lem0)). Qed.
Lemma lem2400584 : term146.
Proof. exact (@lem2400573 (@lem2400583)). Qed.
Lemma lem2400586 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400587 : term81 = term82.
Proof. exact (@lem2400586 term23 term23). Qed.
Lemma lem2400588 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400589 : term84 = term23.
Proof. exact (EQ_MP (@lem2400588) (@lem940073)). Qed.
Lemma lem2400590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400591 : term82 = term22.
Proof. exact (MK_COMB (@lem2400590) (@lem2400589)). Qed.
Lemma lem2400592 : term81 = term22.
Proof. exact (TRANS (@lem2400587) (@lem2400591)). Qed.
Lemma lem2400594 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400595 : term81 = term82.
Proof. exact (@lem2400594 term23 term23). Qed.
Lemma lem2400596 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400597 : term84 = term23.
Proof. exact (EQ_MP (@lem2400596) (@lem940073)). Qed.
Lemma lem2400598 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400599 : term82 = term22.
Proof. exact (MK_COMB (@lem2400598) (@lem2400597)). Qed.
Lemma lem2400600 : term81 = term22.
Proof. exact (TRANS (@lem2400595) (@lem2400599)). Qed.
Lemma lem2400601 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400602 : term147 = term134.
Proof. exact (MK_COMB (@lem2400601) (@lem2400600)). Qed.
Lemma lem2400603 : term148 = term136.
Proof. exact (MK_COMB (@lem2400602) (@lem2400592)). Qed.
Lemma lem2400604 : term136 = term149.
Proof. exact (@lem1367770 term23 term23). Qed.
Lemma lem2400605 : term150 = term151.
Proof. exact (@lem706885). Qed.
Lemma lem2400606 : (term150 = term151) = (term152 = term153).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term151). Qed.
Lemma lem2400607 : term152 = term153.
Proof. exact (EQ_MP (@lem2400606) (@lem2400605)). Qed.
Lemma lem2400608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400609 : term149 = term139.
Proof. exact (MK_COMB (@lem2400608) (@lem2400607)). Qed.
Lemma lem2400610 : term136 = term139.
Proof. exact (TRANS (@lem2400604) (@lem2400609)). Qed.
Lemma lem2400611 : term148 = term139.
Proof. exact (TRANS (@lem2400603) (@lem2400610)). Qed.
Lemma lem2400612 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400613 : term154 = term155.
Proof. exact (MK_COMB (@lem2400612) (@lem2400611)). Qed.
Lemma lem2400614 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem2400615 : term156 = term157.
Proof. exact (MK_COMB (@lem2400613) (@lem2400614)). Qed.
Lemma lem2400617 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400618 : term157 = term158.
Proof. exact (@lem2400617 term153 term23). Qed.
Lemma lem2400619 : term159 = term151.
Proof. exact (@lem996237 term151). Qed.
Lemma lem2400620 : (term159 = term151) = (term160 = term153).
Proof. exact (@lem1007663 term151 (BIT1 0) term151). Qed.
Lemma lem2400621 : term160 = term153.
Proof. exact (EQ_MP (@lem2400620) (@lem2400619)). Qed.
Lemma lem2400622 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400623 : term158 = term139.
Proof. exact (MK_COMB (@lem2400622) (@lem2400621)). Qed.
Lemma lem2400624 : term157 = term139.
Proof. exact (TRANS (@lem2400618) (@lem2400623)). Qed.
Lemma lem2400625 : term156 = term139.
Proof. exact (TRANS (@lem2400615) (@lem2400624)). Qed.
Lemma lem2400627 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400628 : term81 = term82.
Proof. exact (@lem2400627 term23 term23). Qed.
Lemma lem2400629 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400630 : term84 = term23.
Proof. exact (EQ_MP (@lem2400629) (@lem940073)). Qed.
Lemma lem2400631 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400632 : term82 = term22.
Proof. exact (MK_COMB (@lem2400631) (@lem2400630)). Qed.
Lemma lem2400633 : term81 = term22.
Proof. exact (TRANS (@lem2400628) (@lem2400632)). Qed.
Lemma lem2400634 : term155 = term155.
Proof. exact (eq_refl term155). Qed.
Lemma lem2400635 : term161 = term157.
Proof. exact (MK_COMB (@lem2400634) (@lem2400633)). Qed.
Lemma lem2400637 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400638 : term157 = term158.
Proof. exact (@lem2400637 term153 term23). Qed.
Lemma lem2400639 : term159 = term151.
Proof. exact (@lem996237 term151). Qed.
Lemma lem2400640 : (term159 = term151) = (term160 = term153).
Proof. exact (@lem1007663 term151 (BIT1 0) term151). Qed.
Lemma lem2400641 : term160 = term153.
Proof. exact (EQ_MP (@lem2400640) (@lem2400639)). Qed.
Lemma lem2400642 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400643 : term158 = term139.
Proof. exact (MK_COMB (@lem2400642) (@lem2400641)). Qed.
Lemma lem2400644 : term157 = term139.
Proof. exact (TRANS (@lem2400638) (@lem2400643)). Qed.
Lemma lem2400645 : term161 = term139.
Proof. exact (TRANS (@lem2400635) (@lem2400644)). Qed.
Lemma lem2400646 : term139 = term161.
Proof. exact (SYM (@lem2400645)). Qed.
Lemma lem2400647 : term156 = term161.
Proof. exact (TRANS (@lem2400625) (@lem2400646)). Qed.
Lemma lem2400648 : term137 = term162.
Proof. exact (@lem2400584 (@lem2400647)). Qed.
Lemma lem2400649 : term136 = term162.
Proof. exact (TRANS (@lem2400550) (@lem2400648)). Qed.
Lemma lem2400651 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2400652 : term162 = term139.
Proof. exact (@lem2400651 term139). Qed.
Lemma lem2400653 : term136 = term139.
Proof. exact (TRANS (@lem2400649) (@lem2400652)). Qed.
Lemma lem2400654 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400655 : term163 = term155.
Proof. exact (MK_COMB (@lem2400654) (@lem2400653)). Qed.
Lemma lem2400656 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2400657 (n : int) : (term133 n) = (term164 n).
Proof. exact (MK_COMB (@lem2400655) (@lem2400656 n)). Qed.
Lemma lem2400658 (n : int) : (term132 n) = (term164 n).
Proof. exact (TRANS (@lem2400541 n) (@lem2400657 n)). Qed.
Lemma lem2400659 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400660 (n : int) : (term165 n) = (term166 n).
Proof. exact (MK_COMB (@lem2400659) (@lem2400658 n)). Qed.
Lemma lem2400661 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem2400662 (n : int) : (term131 n) = (term167 n).
Proof. exact (MK_COMB (@lem2400660 n) (@lem2400661)). Qed.
Lemma lem2400663 (n : int) : (term130 n) = (term167 n).
Proof. exact (TRANS (@lem2400540 n) (@lem2400662 n)). Qed.
Lemma lem2400664 (n : int) : (term129 n) = (term167 n).
Proof. exact (TRANS (@lem2400539 n) (@lem2400663 n)). Qed.
Lemma lem2400665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2400666 (n : int) : (term168 n) = (term169 n).
Proof. exact (MK_COMB (@lem2400665) (@lem2400664 n)). Qed.
Lemma lem2400667 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400668 (n : int) : (term170 n) = (term171 n).
Proof. exact (MK_COMB (@lem2400666 n) (@lem2400667)). Qed.
Lemma lem2400686 (n : int) : (term172 n) = (term173 n).
Proof. exact (@lem1982759 (real_of_int n) (term174 n) term72). Qed.
Lemma lem2400687 (n : int) : (term175 n) = (term176 n).
Proof. exact (@lem1982715 term72 (real_of_int n)). Qed.
Lemma lem2400689 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400690 : term22 = term69.
Proof. exact (@lem2400689 term23). Qed.
Lemma lem2400692 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400693 : term72 = term73.
Proof. exact (@lem2400692 term23). Qed.
Lemma lem2400694 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400695 : term177 = term178.
Proof. exact (MK_COMB (@lem2400694) (@lem2400693)). Qed.
Lemma lem2400696 : term179 = term180.
Proof. exact (MK_COMB (@lem2400695) (@lem2400690)). Qed.
Lemma lem2400697 : term181.
Proof. exact (@lem1981473 term72 term22 term22 term22 term18 term22). Qed.
Lemma lem2400699 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400700 : term141 = term142.
Proof. exact (@lem2400699 (NUMERAL 0) term23). Qed.
Lemma lem2400701 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400702 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400703 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400702 h1) (fun h1 : term142 = True => @lem2400701)). Qed.
Lemma lem2400704 : term142 = True.
Proof. exact (EQ_MP (@lem2400703) (@lem2400701)). Qed.
Lemma lem2400705 : term141 = True.
Proof. exact (TRANS (@lem2400700) (@lem2400704)). Qed.
Lemma lem2400706 : True = term141.
Proof. exact (SYM (@lem2400705)). Qed.
Lemma lem2400707 : term141.
Proof. exact (EQ_MP (@lem2400706) (@lem0)). Qed.
Lemma lem2400708 : term182.
Proof. exact (@lem2400697 (@lem2400707)). Qed.
Lemma lem2400710 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400711 : term141 = term142.
Proof. exact (@lem2400710 (NUMERAL 0) term23). Qed.
Lemma lem2400712 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400713 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400714 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400713 h1) (fun h1 : term142 = True => @lem2400712)). Qed.
Lemma lem2400715 : term142 = True.
Proof. exact (EQ_MP (@lem2400714) (@lem2400712)). Qed.
Lemma lem2400716 : term141 = True.
Proof. exact (TRANS (@lem2400711) (@lem2400715)). Qed.
Lemma lem2400717 : True = term141.
Proof. exact (SYM (@lem2400716)). Qed.
Lemma lem2400718 : term141.
Proof. exact (EQ_MP (@lem2400717) (@lem0)). Qed.
Lemma lem2400719 : term183.
Proof. exact (@lem2400708 (@lem2400718)). Qed.
Lemma lem2400721 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400722 : term141 = term142.
Proof. exact (@lem2400721 (NUMERAL 0) term23). Qed.
Lemma lem2400723 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400724 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400725 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400724 h1) (fun h1 : term142 = True => @lem2400723)). Qed.
Lemma lem2400726 : term142 = True.
Proof. exact (EQ_MP (@lem2400725) (@lem2400723)). Qed.
Lemma lem2400727 : term141 = True.
Proof. exact (TRANS (@lem2400722) (@lem2400726)). Qed.
Lemma lem2400728 : True = term141.
Proof. exact (SYM (@lem2400727)). Qed.
Lemma lem2400729 : term141.
Proof. exact (EQ_MP (@lem2400728) (@lem0)). Qed.
Lemma lem2400730 : term184.
Proof. exact (@lem2400719 (@lem2400729)). Qed.
Lemma lem2400732 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400733 : term81 = term82.
Proof. exact (@lem2400732 term23 term23). Qed.
Lemma lem2400734 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400735 : term84 = term23.
Proof. exact (EQ_MP (@lem2400734) (@lem940073)). Qed.
Lemma lem2400736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400737 : term82 = term22.
Proof. exact (MK_COMB (@lem2400736) (@lem2400735)). Qed.
Lemma lem2400738 : term81 = term22.
Proof. exact (TRANS (@lem2400733) (@lem2400737)). Qed.
Lemma lem2400740 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2400741 : term76 = term87.
Proof. exact (@lem2400740 term23 term23). Qed.
Lemma lem2400742 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400743 : term84 = term23.
Proof. exact (EQ_MP (@lem2400742) (@lem940073)). Qed.
Lemma lem2400744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400745 : term82 = term22.
Proof. exact (MK_COMB (@lem2400744) (@lem2400743)). Qed.
Lemma lem2400746 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2400747 : term87 = term72.
Proof. exact (MK_COMB (@lem2400746) (@lem2400745)). Qed.
Lemma lem2400748 : term76 = term72.
Proof. exact (TRANS (@lem2400741) (@lem2400747)). Qed.
Lemma lem2400749 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400750 : term185 = term177.
Proof. exact (MK_COMB (@lem2400749) (@lem2400748)). Qed.
Lemma lem2400751 : term186 = term179.
Proof. exact (MK_COMB (@lem2400750) (@lem2400738)). Qed.
Lemma lem2400753 (m : nat) : (term187 m) = term18.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2400754 : term179 = term18.
Proof. exact (@lem2400753 term23). Qed.
Lemma lem2400755 : term186 = term18.
Proof. exact (TRANS (@lem2400751) (@lem2400754)). Qed.
Lemma lem2400756 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400757 : term188 = term189.
Proof. exact (MK_COMB (@lem2400756) (@lem2400755)). Qed.
Lemma lem2400758 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem2400759 : term190 = term191.
Proof. exact (MK_COMB (@lem2400757) (@lem2400758)). Qed.
Lemma lem2400761 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2400762 : term191 = term18.
Proof. exact (@lem2400761 term23). Qed.
Lemma lem2400763 : term190 = term18.
Proof. exact (TRANS (@lem2400759) (@lem2400762)). Qed.
Lemma lem2400765 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400766 : term81 = term82.
Proof. exact (@lem2400765 term23 term23). Qed.
Lemma lem2400767 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400768 : term84 = term23.
Proof. exact (EQ_MP (@lem2400767) (@lem940073)). Qed.
Lemma lem2400769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400770 : term82 = term22.
Proof. exact (MK_COMB (@lem2400769) (@lem2400768)). Qed.
Lemma lem2400771 : term81 = term22.
Proof. exact (TRANS (@lem2400766) (@lem2400770)). Qed.
Lemma lem2400772 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem2400773 : term193 = term191.
Proof. exact (MK_COMB (@lem2400772) (@lem2400771)). Qed.
Lemma lem2400775 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2400776 : term191 = term18.
Proof. exact (@lem2400775 term23). Qed.
Lemma lem2400777 : term193 = term18.
Proof. exact (TRANS (@lem2400773) (@lem2400776)). Qed.
Lemma lem2400778 : term18 = term193.
Proof. exact (SYM (@lem2400777)). Qed.
Lemma lem2400779 : term190 = term193.
Proof. exact (TRANS (@lem2400763) (@lem2400778)). Qed.
Lemma lem2400780 : term180 = term194.
Proof. exact (@lem2400730 (@lem2400779)). Qed.
Lemma lem2400781 : term179 = term194.
Proof. exact (TRANS (@lem2400696) (@lem2400780)). Qed.
Lemma lem2400783 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2400784 : term194 = term18.
Proof. exact (@lem2400783 term18). Qed.
Lemma lem2400785 : term179 = term18.
Proof. exact (TRANS (@lem2400781) (@lem2400784)). Qed.
Lemma lem2400786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400787 : term195 = term189.
Proof. exact (MK_COMB (@lem2400786) (@lem2400785)). Qed.
Lemma lem2400788 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2400789 (n : int) : (term176 n) = (term196 n).
Proof. exact (MK_COMB (@lem2400787) (@lem2400788 n)). Qed.
Lemma lem2400790 (n : int) : (term175 n) = (term196 n).
Proof. exact (TRANS (@lem2400687 n) (@lem2400789 n)). Qed.
Lemma lem2400791 (n : int) : (term196 n) = term18.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2400792 (n : int) : (term175 n) = term18.
Proof. exact (TRANS (@lem2400790 n) (@lem2400791 n)). Qed.
Lemma lem2400793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400794 (n : int) : (term197 n) = term20.
Proof. exact (MK_COMB (@lem2400793) (@lem2400792 n)). Qed.
Lemma lem2400795 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem2400796 (n : int) : (term173 n) = term198.
Proof. exact (MK_COMB (@lem2400794 n) (@lem2400795)). Qed.
Lemma lem2400797 (n : int) : (term172 n) = term198.
Proof. exact (TRANS (@lem2400686 n) (@lem2400796 n)). Qed.
Lemma lem2400798 : term198 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem2400800 (n : int) : (term172 n) = term72.
Proof. exact (TRANS (@lem2400797 n) (@lem2400798)). Qed.
Lemma lem2400801 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2400802 (n : int) : (term199 n) = term200.
Proof. exact (MK_COMB (@lem2400801) (@lem2400800 n)). Qed.
Lemma lem2400803 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400804 (n : int) : (term201 n) = term202.
Proof. exact (MK_COMB (@lem2400802 n) (@lem2400803)). Qed.
Lemma lem2400805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2400806 (n : int) : (term203 n) = term204.
Proof. exact (MK_COMB (@lem2400805) (@lem2400804 n)). Qed.
Lemma lem2400807 (n : int) : (term126 n) = (term205 n).
Proof. exact (MK_COMB (@lem2400806 n) (@lem2400668 n)). Qed.
Lemma lem2400808 (n : int) : (term107 n) = (term205 n).
Proof. exact (TRANS (@lem2400522 n) (@lem2400807 n)). Qed.
Lemma lem2400809 (n : int) : (term121 n) = (term121 n).
Proof. exact (eq_refl (term121 n)). Qed.
Lemma lem2400812 (n : int) : (term206 n) = (term207 n).
Proof. exact (MK_COMB (@lem2400809 n) (@lem2400808 n)). Qed.
Lemma lem2400814 (n : int) : (term208 n) = (term209 n).
Proof. exact (eq_refl (term208 n)). Qed.
Lemma lem2400815 (n : int) : (term209 n) = (term208 n).
Proof. exact (SYM (@lem2400814 n)). Qed.
Lemma lem2400816 (n : int) : (term208 n) = (term210 n).
Proof. exact (@lem1482981 (term211 n) (real_of_int n)). Qed.
Lemma lem2400817 (n : int) : (term209 n) = (term210 n).
Proof. exact (TRANS (@lem2400815 n) (@lem2400816 n)). Qed.
Lemma lem2400818 (n : int) : (term212 n) = (term213 n).
Proof. exact (eq_refl (term212 n)). Qed.
Lemma lem2400819 (n : int) : (term214 n) = (term214 n).
Proof. exact (eq_refl (term214 n)). Qed.
Lemma lem2400820 (n : int) : (term215 n) = (term216 n).
Proof. exact (MK_COMB (@lem2400819 n) (@lem2400818 n)). Qed.
Lemma lem2400821 (n : int) : (term217 n) = (term218 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2400822 (n : int) : (term219 n) = (term219 n).
Proof. exact (eq_refl (term219 n)). Qed.
Lemma lem2400823 (n : int) : (term220 n) = (term221 n).
Proof. exact (MK_COMB (@lem2400822 n) (@lem2400821 n)). Qed.
Lemma lem2400824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2400825 (n : int) : (term222 n) = (term223 n).
Proof. exact (MK_COMB (@lem2400824) (@lem2400823 n)). Qed.
Lemma lem2400826 (n : int) : (term210 n) = (term224 n).
Proof. exact (MK_COMB (@lem2400825 n) (@lem2400820 n)). Qed.
Lemma lem2400827 (n : int) : (term225 n) = (term225 n).
Proof. exact (eq_refl (term225 n)). Qed.
Lemma lem2400828 (n : int) : ((term209 n) = (term210 n)) = ((term209 n) = (term224 n)).
Proof. exact (MK_COMB (@lem2400827 n) (@lem2400826 n)). Qed.
Lemma lem2400829 (n : int) : (term209 n) = (term224 n).
Proof. exact (EQ_MP (@lem2400828 n) (@lem2400817 n)). Qed.
Lemma lem2400830 (n : int) : (term226 n) = (term227 n).
Proof. exact (@lem1988291 (real_of_int n) term18). Qed.
Lemma lem2400836 (n : int) : (term228 n) = (term229 n).
Proof. exact (@lem1982792 (real_of_int n) term18). Qed.
Lemma lem2400838 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400839 : term18 = term194.
Proof. exact (@lem2400838 (NUMERAL 0)). Qed.
Lemma lem2400841 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400842 : term72 = term73.
Proof. exact (@lem2400841 term23). Qed.
Lemma lem2400843 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400844 : term74 = term75.
Proof. exact (MK_COMB (@lem2400843) (@lem2400842)). Qed.
Lemma lem2400845 : term230 = term231.
Proof. exact (MK_COMB (@lem2400844) (@lem2400839)). Qed.
Lemma lem2400846 : term231 = term232.
Proof. exact (@lem1981613 term72 term18 term22 term22). Qed.
Lemma lem2400848 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400849 : term81 = term82.
Proof. exact (@lem2400848 term23 term23). Qed.
Lemma lem2400850 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400851 : term84 = term23.
Proof. exact (EQ_MP (@lem2400850) (@lem940073)). Qed.
Lemma lem2400852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400853 : term82 = term22.
Proof. exact (MK_COMB (@lem2400852) (@lem2400851)). Qed.
Lemma lem2400854 : term81 = term22.
Proof. exact (TRANS (@lem2400849) (@lem2400853)). Qed.
Lemma lem2400856 (x : nat) : (term233 x) = term18.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2400857 : term230 = term18.
Proof. exact (@lem2400856 term23). Qed.
Lemma lem2400858 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2400859 : term234 = term235.
Proof. exact (MK_COMB (@lem2400858) (@lem2400857)). Qed.
Lemma lem2400860 : term232 = term194.
Proof. exact (MK_COMB (@lem2400859) (@lem2400854)). Qed.
Lemma lem2400861 : term231 = term194.
Proof. exact (TRANS (@lem2400846) (@lem2400860)). Qed.
Lemma lem2400862 : term230 = term194.
Proof. exact (TRANS (@lem2400845) (@lem2400861)). Qed.
Lemma lem2400864 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2400865 : term194 = term18.
Proof. exact (@lem2400864 term18). Qed.
Lemma lem2400866 : term230 = term18.
Proof. exact (TRANS (@lem2400862) (@lem2400865)). Qed.
Lemma lem2400867 (n : int) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2400868 (n : int) : (term229 n) = (term236 n).
Proof. exact (MK_COMB (@lem2400867 n) (@lem2400866)). Qed.
Lemma lem2400869 (n : int) : (term236 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2400870 (n : int) : (term229 n) = (real_of_int n).
Proof. exact (TRANS (@lem2400868 n) (@lem2400869 n)). Qed.
Lemma lem2400872 (n : int) : (term228 n) = (real_of_int n).
Proof. exact (TRANS (@lem2400836 n) (@lem2400870 n)). Qed.
Lemma lem2400873 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2400874 (n : int) : (term237 n) = (term238 n).
Proof. exact (MK_COMB (@lem2400873) (@lem2400872 n)). Qed.
Lemma lem2400875 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400876 (n : int) : (term227 n) = (term226 n).
Proof. exact (MK_COMB (@lem2400874 n) (@lem2400875)). Qed.
Lemma lem2400877 (n : int) : (term226 n) = (term226 n).
Proof. exact (TRANS (@lem2400830 n) (@lem2400876 n)). Qed.
Lemma lem2400878 (n : int) : (term94 n) = (term239 n).
Proof. exact (@lem1988291 (term91 n) term18). Qed.
Lemma lem2400890 (n : int) : (term240 n) = (term241 n).
Proof. exact (@lem1982792 (term91 n) term18). Qed.
Lemma lem2400892 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400893 : term18 = term194.
Proof. exact (@lem2400892 (NUMERAL 0)). Qed.
Lemma lem2400895 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400896 : term72 = term73.
Proof. exact (@lem2400895 term23). Qed.
Lemma lem2400897 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2400898 : term74 = term75.
Proof. exact (MK_COMB (@lem2400897) (@lem2400896)). Qed.
Lemma lem2400899 : term230 = term231.
Proof. exact (MK_COMB (@lem2400898) (@lem2400893)). Qed.
Lemma lem2400900 : term231 = term232.
Proof. exact (@lem1981613 term72 term18 term22 term22). Qed.
Lemma lem2400902 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400903 : term81 = term82.
Proof. exact (@lem2400902 term23 term23). Qed.
Lemma lem2400904 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400905 : term84 = term23.
Proof. exact (EQ_MP (@lem2400904) (@lem940073)). Qed.
Lemma lem2400906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400907 : term82 = term22.
Proof. exact (MK_COMB (@lem2400906) (@lem2400905)). Qed.
Lemma lem2400908 : term81 = term22.
Proof. exact (TRANS (@lem2400903) (@lem2400907)). Qed.
Lemma lem2400910 (x : nat) : (term233 x) = term18.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2400911 : term230 = term18.
Proof. exact (@lem2400910 term23). Qed.
Lemma lem2400912 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2400913 : term234 = term235.
Proof. exact (MK_COMB (@lem2400912) (@lem2400911)). Qed.
Lemma lem2400914 : term232 = term194.
Proof. exact (MK_COMB (@lem2400913) (@lem2400908)). Qed.
Lemma lem2400915 : term231 = term194.
Proof. exact (TRANS (@lem2400900) (@lem2400914)). Qed.
Lemma lem2400916 : term230 = term194.
Proof. exact (TRANS (@lem2400899) (@lem2400915)). Qed.
Lemma lem2400918 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2400919 : term194 = term18.
Proof. exact (@lem2400918 term18). Qed.
Lemma lem2400920 : term230 = term18.
Proof. exact (TRANS (@lem2400916) (@lem2400919)). Qed.
Lemma lem2400921 (n : int) : (term128 n) = (term128 n).
Proof. exact (eq_refl (term128 n)). Qed.
Lemma lem2400922 (n : int) : (term241 n) = (term242 n).
Proof. exact (MK_COMB (@lem2400921 n) (@lem2400920)). Qed.
Lemma lem2400923 (n : int) : (term242 n) = (term91 n).
Proof. exact (@lem1982723 (term91 n)). Qed.
Lemma lem2400924 (n : int) : (term241 n) = (term91 n).
Proof. exact (TRANS (@lem2400922 n) (@lem2400923 n)). Qed.
Lemma lem2400926 (n : int) : (term240 n) = (term91 n).
Proof. exact (TRANS (@lem2400890 n) (@lem2400924 n)). Qed.
Lemma lem2400927 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2400928 (n : int) : (term243 n) = (term93 n).
Proof. exact (MK_COMB (@lem2400927) (@lem2400926 n)). Qed.
Lemma lem2400929 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400930 (n : int) : (term239 n) = (term94 n).
Proof. exact (MK_COMB (@lem2400928 n) (@lem2400929)). Qed.
Lemma lem2400931 (n : int) : (term94 n) = (term94 n).
Proof. exact (TRANS (@lem2400878 n) (@lem2400930 n)). Qed.
Lemma lem2400932 (n : int) : (term244 n) = (term245 n).
Proof. exact (@lem1988291 (term246 n) term18). Qed.
Lemma lem2400933 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2400951 (n : int) : (term246 n) = (term173 n).
Proof. exact (@lem1982763 (real_of_int n) (term174 n) term72). Qed.
Lemma lem2400952 (n : int) : (term175 n) = (term176 n).
Proof. exact (@lem1982715 term72 (real_of_int n)). Qed.
Lemma lem2400954 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400955 : term22 = term69.
Proof. exact (@lem2400954 term23). Qed.
Lemma lem2400957 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400958 : term72 = term73.
Proof. exact (@lem2400957 term23). Qed.
Lemma lem2400959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2400960 : term177 = term178.
Proof. exact (MK_COMB (@lem2400959) (@lem2400958)). Qed.
Lemma lem2400961 : term179 = term180.
Proof. exact (MK_COMB (@lem2400960) (@lem2400955)). Qed.
Lemma lem2400962 : term181.
Proof. exact (@lem1981473 term72 term22 term22 term22 term18 term22). Qed.
Lemma lem2400964 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400965 : term141 = term142.
Proof. exact (@lem2400964 (NUMERAL 0) term23). Qed.
Lemma lem2400966 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400967 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400968 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400967 h1) (fun h1 : term142 = True => @lem2400966)). Qed.
Lemma lem2400969 : term142 = True.
Proof. exact (EQ_MP (@lem2400968) (@lem2400966)). Qed.
Lemma lem2400970 : term141 = True.
Proof. exact (TRANS (@lem2400965) (@lem2400969)). Qed.
Lemma lem2400971 : True = term141.
Proof. exact (SYM (@lem2400970)). Qed.
Lemma lem2400972 : term141.
Proof. exact (EQ_MP (@lem2400971) (@lem0)). Qed.
Lemma lem2400973 : term182.
Proof. exact (@lem2400962 (@lem2400972)). Qed.
Lemma lem2400975 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400976 : term141 = term142.
Proof. exact (@lem2400975 (NUMERAL 0) term23). Qed.
Lemma lem2400977 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400978 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400979 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400978 h1) (fun h1 : term142 = True => @lem2400977)). Qed.
Lemma lem2400980 : term142 = True.
Proof. exact (EQ_MP (@lem2400979) (@lem2400977)). Qed.
Lemma lem2400981 : term141 = True.
Proof. exact (TRANS (@lem2400976) (@lem2400980)). Qed.
Lemma lem2400982 : True = term141.
Proof. exact (SYM (@lem2400981)). Qed.
Lemma lem2400983 : term141.
Proof. exact (EQ_MP (@lem2400982) (@lem0)). Qed.
Lemma lem2400984 : term183.
Proof. exact (@lem2400973 (@lem2400983)). Qed.
Lemma lem2400986 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400987 : term141 = term142.
Proof. exact (@lem2400986 (NUMERAL 0) term23). Qed.
Lemma lem2400988 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400989 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400990 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2400989 h1) (fun h1 : term142 = True => @lem2400988)). Qed.
Lemma lem2400991 : term142 = True.
Proof. exact (EQ_MP (@lem2400990) (@lem2400988)). Qed.
Lemma lem2400992 : term141 = True.
Proof. exact (TRANS (@lem2400987) (@lem2400991)). Qed.
Lemma lem2400993 : True = term141.
Proof. exact (SYM (@lem2400992)). Qed.
Lemma lem2400994 : term141.
Proof. exact (EQ_MP (@lem2400993) (@lem0)). Qed.
Lemma lem2400995 : term184.
Proof. exact (@lem2400984 (@lem2400994)). Qed.
Lemma lem2400997 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2400998 : term81 = term82.
Proof. exact (@lem2400997 term23 term23). Qed.
Lemma lem2400999 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401000 : term84 = term23.
Proof. exact (EQ_MP (@lem2400999) (@lem940073)). Qed.
Lemma lem2401001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401002 : term82 = term22.
Proof. exact (MK_COMB (@lem2401001) (@lem2401000)). Qed.
Lemma lem2401003 : term81 = term22.
Proof. exact (TRANS (@lem2400998) (@lem2401002)). Qed.
Lemma lem2401005 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401006 : term76 = term87.
Proof. exact (@lem2401005 term23 term23). Qed.
Lemma lem2401007 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401008 : term84 = term23.
Proof. exact (EQ_MP (@lem2401007) (@lem940073)). Qed.
Lemma lem2401009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401010 : term82 = term22.
Proof. exact (MK_COMB (@lem2401009) (@lem2401008)). Qed.
Lemma lem2401011 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401012 : term87 = term72.
Proof. exact (MK_COMB (@lem2401011) (@lem2401010)). Qed.
Lemma lem2401013 : term76 = term72.
Proof. exact (TRANS (@lem2401006) (@lem2401012)). Qed.
Lemma lem2401014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401015 : term185 = term177.
Proof. exact (MK_COMB (@lem2401014) (@lem2401013)). Qed.
Lemma lem2401016 : term186 = term179.
Proof. exact (MK_COMB (@lem2401015) (@lem2401003)). Qed.
Lemma lem2401018 (m : nat) : (term187 m) = term18.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2401019 : term179 = term18.
Proof. exact (@lem2401018 term23). Qed.
Lemma lem2401020 : term186 = term18.
Proof. exact (TRANS (@lem2401016) (@lem2401019)). Qed.
Lemma lem2401021 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401022 : term188 = term189.
Proof. exact (MK_COMB (@lem2401021) (@lem2401020)). Qed.
Lemma lem2401023 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem2401024 : term190 = term191.
Proof. exact (MK_COMB (@lem2401022) (@lem2401023)). Qed.
Lemma lem2401026 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401027 : term191 = term18.
Proof. exact (@lem2401026 term23). Qed.
Lemma lem2401028 : term190 = term18.
Proof. exact (TRANS (@lem2401024) (@lem2401027)). Qed.
Lemma lem2401030 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401031 : term81 = term82.
Proof. exact (@lem2401030 term23 term23). Qed.
Lemma lem2401032 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401033 : term84 = term23.
Proof. exact (EQ_MP (@lem2401032) (@lem940073)). Qed.
Lemma lem2401034 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401035 : term82 = term22.
Proof. exact (MK_COMB (@lem2401034) (@lem2401033)). Qed.
Lemma lem2401036 : term81 = term22.
Proof. exact (TRANS (@lem2401031) (@lem2401035)). Qed.
Lemma lem2401037 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem2401038 : term193 = term191.
Proof. exact (MK_COMB (@lem2401037) (@lem2401036)). Qed.
Lemma lem2401040 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401041 : term191 = term18.
Proof. exact (@lem2401040 term23). Qed.
Lemma lem2401042 : term193 = term18.
Proof. exact (TRANS (@lem2401038) (@lem2401041)). Qed.
Lemma lem2401043 : term18 = term193.
Proof. exact (SYM (@lem2401042)). Qed.
Lemma lem2401044 : term190 = term193.
Proof. exact (TRANS (@lem2401028) (@lem2401043)). Qed.
Lemma lem2401045 : term180 = term194.
Proof. exact (@lem2400995 (@lem2401044)). Qed.
Lemma lem2401046 : term179 = term194.
Proof. exact (TRANS (@lem2400961) (@lem2401045)). Qed.
Lemma lem2401048 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2401049 : term194 = term18.
Proof. exact (@lem2401048 term18). Qed.
Lemma lem2401050 : term179 = term18.
Proof. exact (TRANS (@lem2401046) (@lem2401049)). Qed.
Lemma lem2401051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401052 : term195 = term189.
Proof. exact (MK_COMB (@lem2401051) (@lem2401050)). Qed.
Lemma lem2401053 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2401054 (n : int) : (term176 n) = (term196 n).
Proof. exact (MK_COMB (@lem2401052) (@lem2401053 n)). Qed.
Lemma lem2401055 (n : int) : (term175 n) = (term196 n).
Proof. exact (TRANS (@lem2400952 n) (@lem2401054 n)). Qed.
Lemma lem2401056 (n : int) : (term196 n) = term18.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2401057 (n : int) : (term175 n) = term18.
Proof. exact (TRANS (@lem2401055 n) (@lem2401056 n)). Qed.
Lemma lem2401058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401059 (n : int) : (term197 n) = term20.
Proof. exact (MK_COMB (@lem2401058) (@lem2401057 n)). Qed.
Lemma lem2401060 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem2401061 (n : int) : (term173 n) = term198.
Proof. exact (MK_COMB (@lem2401059 n) (@lem2401060)). Qed.
Lemma lem2401062 (n : int) : (term246 n) = term198.
Proof. exact (TRANS (@lem2400951 n) (@lem2401061 n)). Qed.
Lemma lem2401063 : term198 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem2401065 (n : int) : (term246 n) = term72.
Proof. exact (TRANS (@lem2401062 n) (@lem2401063)). Qed.
Lemma lem2401066 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2401067 (n : int) : (term247 n) = term248.
Proof. exact (MK_COMB (@lem2401066) (@lem2401065 n)). Qed.
Lemma lem2401068 (n : int) : (term249 n) = term250.
Proof. exact (MK_COMB (@lem2401067 n) (@lem2400933)). Qed.
Lemma lem2401069 : term250 = term251.
Proof. exact (@lem1982792 term72 term18). Qed.
Lemma lem2401071 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401072 : term18 = term194.
Proof. exact (@lem2401071 (NUMERAL 0)). Qed.
Lemma lem2401074 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401075 : term72 = term73.
Proof. exact (@lem2401074 term23). Qed.
Lemma lem2401076 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401077 : term74 = term75.
Proof. exact (MK_COMB (@lem2401076) (@lem2401075)). Qed.
Lemma lem2401078 : term230 = term231.
Proof. exact (MK_COMB (@lem2401077) (@lem2401072)). Qed.
Lemma lem2401079 : term231 = term232.
Proof. exact (@lem1981613 term72 term18 term22 term22). Qed.
Lemma lem2401081 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401082 : term81 = term82.
Proof. exact (@lem2401081 term23 term23). Qed.
Lemma lem2401083 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401084 : term84 = term23.
Proof. exact (EQ_MP (@lem2401083) (@lem940073)). Qed.
Lemma lem2401085 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401086 : term82 = term22.
Proof. exact (MK_COMB (@lem2401085) (@lem2401084)). Qed.
Lemma lem2401087 : term81 = term22.
Proof. exact (TRANS (@lem2401082) (@lem2401086)). Qed.
Lemma lem2401089 (x : nat) : (term233 x) = term18.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2401090 : term230 = term18.
Proof. exact (@lem2401089 term23). Qed.
Lemma lem2401091 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2401092 : term234 = term235.
Proof. exact (MK_COMB (@lem2401091) (@lem2401090)). Qed.
Lemma lem2401093 : term232 = term194.
Proof. exact (MK_COMB (@lem2401092) (@lem2401087)). Qed.
Lemma lem2401094 : term231 = term194.
Proof. exact (TRANS (@lem2401079) (@lem2401093)). Qed.
Lemma lem2401095 : term230 = term194.
Proof. exact (TRANS (@lem2401078) (@lem2401094)). Qed.
Lemma lem2401097 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2401098 : term194 = term18.
Proof. exact (@lem2401097 term18). Qed.
Lemma lem2401099 : term230 = term18.
Proof. exact (TRANS (@lem2401095) (@lem2401098)). Qed.
Lemma lem2401100 : term177 = term177.
Proof. exact (eq_refl term177). Qed.
Lemma lem2401101 : term251 = term252.
Proof. exact (MK_COMB (@lem2401100) (@lem2401099)). Qed.
Lemma lem2401102 : term252 = term72.
Proof. exact (@lem1982723 term72). Qed.
Lemma lem2401103 : term251 = term72.
Proof. exact (TRANS (@lem2401101) (@lem2401102)). Qed.
Lemma lem2401104 : term250 = term72.
Proof. exact (TRANS (@lem2401069) (@lem2401103)). Qed.
Lemma lem2401105 (n : int) : (term249 n) = term72.
Proof. exact (TRANS (@lem2401068 n) (@lem2401104)). Qed.
Lemma lem2401106 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2401107 (n : int) : (term253 n) = term200.
Proof. exact (MK_COMB (@lem2401106) (@lem2401105 n)). Qed.
Lemma lem2401108 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2401109 (n : int) : (term245 n) = term202.
Proof. exact (MK_COMB (@lem2401107 n) (@lem2401108)). Qed.
Lemma lem2401110 (n : int) : (term244 n) = term202.
Proof. exact (TRANS (@lem2400932 n) (@lem2401109 n)). Qed.
Lemma lem2401111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2401112 (n : int) : (term121 n) = (term121 n).
Proof. exact (MK_COMB (@lem2401111) (@lem2400931 n)). Qed.
Lemma lem2401113 (n : int) : (term218 n) = (term254 n).
Proof. exact (MK_COMB (@lem2401112 n) (@lem2401110 n)). Qed.
Lemma lem2401114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2401115 (n : int) : (term219 n) = (term219 n).
Proof. exact (MK_COMB (@lem2401114) (@lem2400877 n)). Qed.
Lemma lem2401116 (n : int) : (term221 n) = (term255 n).
Proof. exact (MK_COMB (@lem2401115 n) (@lem2401113 n)). Qed.
Lemma lem2401117 (n : int) : (term256 n) = (term257 n).
Proof. exact (@lem1988289 term18 (real_of_int n)). Qed.
Lemma lem2401123 (n : int) : (term258 n) = (term259 n).
Proof. exact (@lem1982792 term18 (real_of_int n)). Qed.
Lemma lem2401128 (n : int) : (term259 n) = (term174 n).
Proof. exact (@lem1982721 (term174 n)). Qed.
Lemma lem2401130 (n : int) : (term258 n) = (term174 n).
Proof. exact (TRANS (@lem2401123 n) (@lem2401128 n)). Qed.
Lemma lem2401131 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2401132 (n : int) : (term260 n) = (term261 n).
Proof. exact (MK_COMB (@lem2401131) (@lem2401130 n)). Qed.
Lemma lem2401133 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2401134 (n : int) : (term257 n) = (term262 n).
Proof. exact (MK_COMB (@lem2401132 n) (@lem2401133)). Qed.
Lemma lem2401135 (n : int) : (term256 n) = (term262 n).
Proof. exact (TRANS (@lem2401117 n) (@lem2401134 n)). Qed.
Lemma lem2401136 (n : int) : (term263 n) = (term264 n).
Proof. exact (@lem1988291 (term265 n) term18). Qed.
Lemma lem2401137 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2401150 (n : int) : (term114 n) = (term114 n).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem2401157 (n : int) : (term266 n) = (term174 n).
Proof. exact (@lem1982785 (real_of_int n)). Qed.
Lemma lem2401158 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401159 (n : int) : (term267 n) = (term113 n).
Proof. exact (MK_COMB (@lem2401158) (@lem2401157 n)). Qed.
Lemma lem2401160 (n : int) : (term265 n) = (term268 n).
Proof. exact (MK_COMB (@lem2401159 n) (@lem2401150 n)). Qed.
Lemma lem2401161 (n : int) : (term268 n) = (term269 n).
Proof. exact (@lem1982763 (term174 n) (term174 n) term72). Qed.
Lemma lem2401162 (n : int) : (term270 n) = (term271 n).
Proof. exact (@lem1982711 term72 term72 (real_of_int n)). Qed.
Lemma lem2401164 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401165 : term72 = term73.
Proof. exact (@lem2401164 term23). Qed.
Lemma lem2401167 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401168 : term72 = term73.
Proof. exact (@lem2401167 term23). Qed.
Lemma lem2401169 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401170 : term177 = term178.
Proof. exact (MK_COMB (@lem2401169) (@lem2401168)). Qed.
Lemma lem2401171 : term272 = term273.
Proof. exact (MK_COMB (@lem2401170) (@lem2401165)). Qed.
Lemma lem2401172 : term274.
Proof. exact (@lem1981473 term72 term22 term72 term22 term275 term22). Qed.
Lemma lem2401174 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401175 : term141 = term142.
Proof. exact (@lem2401174 (NUMERAL 0) term23). Qed.
Lemma lem2401176 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401177 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401178 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401177 h1) (fun h1 : term142 = True => @lem2401176)). Qed.
Lemma lem2401179 : term142 = True.
Proof. exact (EQ_MP (@lem2401178) (@lem2401176)). Qed.
Lemma lem2401180 : term141 = True.
Proof. exact (TRANS (@lem2401175) (@lem2401179)). Qed.
Lemma lem2401181 : True = term141.
Proof. exact (SYM (@lem2401180)). Qed.
Lemma lem2401182 : term141.
Proof. exact (EQ_MP (@lem2401181) (@lem0)). Qed.
Lemma lem2401183 : term276.
Proof. exact (@lem2401172 (@lem2401182)). Qed.
Lemma lem2401185 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401186 : term141 = term142.
Proof. exact (@lem2401185 (NUMERAL 0) term23). Qed.
Lemma lem2401187 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401188 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401189 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401188 h1) (fun h1 : term142 = True => @lem2401187)). Qed.
Lemma lem2401190 : term142 = True.
Proof. exact (EQ_MP (@lem2401189) (@lem2401187)). Qed.
Lemma lem2401191 : term141 = True.
Proof. exact (TRANS (@lem2401186) (@lem2401190)). Qed.
Lemma lem2401192 : True = term141.
Proof. exact (SYM (@lem2401191)). Qed.
Lemma lem2401193 : term141.
Proof. exact (EQ_MP (@lem2401192) (@lem0)). Qed.
Lemma lem2401194 : term277.
Proof. exact (@lem2401183 (@lem2401193)). Qed.
Lemma lem2401196 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401197 : term141 = term142.
Proof. exact (@lem2401196 (NUMERAL 0) term23). Qed.
Lemma lem2401198 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401199 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401200 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401199 h1) (fun h1 : term142 = True => @lem2401198)). Qed.
Lemma lem2401201 : term142 = True.
Proof. exact (EQ_MP (@lem2401200) (@lem2401198)). Qed.
Lemma lem2401202 : term141 = True.
Proof. exact (TRANS (@lem2401197) (@lem2401201)). Qed.
Lemma lem2401203 : True = term141.
Proof. exact (SYM (@lem2401202)). Qed.
Lemma lem2401204 : term141.
Proof. exact (EQ_MP (@lem2401203) (@lem0)). Qed.
Lemma lem2401205 : term278.
Proof. exact (@lem2401194 (@lem2401204)). Qed.
Lemma lem2401207 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401208 : term76 = term87.
Proof. exact (@lem2401207 term23 term23). Qed.
Lemma lem2401209 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401210 : term84 = term23.
Proof. exact (EQ_MP (@lem2401209) (@lem940073)). Qed.
Lemma lem2401211 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401212 : term82 = term22.
Proof. exact (MK_COMB (@lem2401211) (@lem2401210)). Qed.
Lemma lem2401213 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401214 : term87 = term72.
Proof. exact (MK_COMB (@lem2401213) (@lem2401212)). Qed.
Lemma lem2401215 : term76 = term72.
Proof. exact (TRANS (@lem2401208) (@lem2401214)). Qed.
Lemma lem2401217 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401218 : term76 = term87.
Proof. exact (@lem2401217 term23 term23). Qed.
Lemma lem2401219 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401220 : term84 = term23.
Proof. exact (EQ_MP (@lem2401219) (@lem940073)). Qed.
Lemma lem2401221 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401222 : term82 = term22.
Proof. exact (MK_COMB (@lem2401221) (@lem2401220)). Qed.
Lemma lem2401223 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401224 : term87 = term72.
Proof. exact (MK_COMB (@lem2401223) (@lem2401222)). Qed.
Lemma lem2401225 : term76 = term72.
Proof. exact (TRANS (@lem2401218) (@lem2401224)). Qed.
Lemma lem2401226 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401227 : term185 = term177.
Proof. exact (MK_COMB (@lem2401226) (@lem2401225)). Qed.
Lemma lem2401228 : term279 = term272.
Proof. exact (MK_COMB (@lem2401227) (@lem2401215)). Qed.
Lemma lem2401229 : term272 = term280.
Proof. exact (@lem1367763 term23 term23). Qed.
Lemma lem2401230 : term150 = term151.
Proof. exact (@lem706885). Qed.
Lemma lem2401231 : (term150 = term151) = (term152 = term153).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term151). Qed.
Lemma lem2401232 : term152 = term153.
Proof. exact (EQ_MP (@lem2401231) (@lem2401230)). Qed.
Lemma lem2401233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401234 : term149 = term139.
Proof. exact (MK_COMB (@lem2401233) (@lem2401232)). Qed.
Lemma lem2401235 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401236 : term280 = term275.
Proof. exact (MK_COMB (@lem2401235) (@lem2401234)). Qed.
Lemma lem2401237 : term272 = term275.
Proof. exact (TRANS (@lem2401229) (@lem2401236)). Qed.
Lemma lem2401238 : term279 = term275.
Proof. exact (TRANS (@lem2401228) (@lem2401237)). Qed.
Lemma lem2401239 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401240 : term281 = term282.
Proof. exact (MK_COMB (@lem2401239) (@lem2401238)). Qed.
Lemma lem2401241 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem2401242 : term283 = term284.
Proof. exact (MK_COMB (@lem2401240) (@lem2401241)). Qed.
Lemma lem2401244 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401245 : term284 = term285.
Proof. exact (@lem2401244 term153 term23). Qed.
Lemma lem2401246 : term159 = term151.
Proof. exact (@lem996237 term151). Qed.
Lemma lem2401247 : (term159 = term151) = (term160 = term153).
Proof. exact (@lem1007663 term151 (BIT1 0) term151). Qed.
Lemma lem2401248 : term160 = term153.
Proof. exact (EQ_MP (@lem2401247) (@lem2401246)). Qed.
Lemma lem2401249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401250 : term158 = term139.
Proof. exact (MK_COMB (@lem2401249) (@lem2401248)). Qed.
Lemma lem2401251 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401252 : term285 = term275.
Proof. exact (MK_COMB (@lem2401251) (@lem2401250)). Qed.
Lemma lem2401253 : term284 = term275.
Proof. exact (TRANS (@lem2401245) (@lem2401252)). Qed.
Lemma lem2401254 : term283 = term275.
Proof. exact (TRANS (@lem2401242) (@lem2401253)). Qed.
Lemma lem2401256 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401257 : term81 = term82.
Proof. exact (@lem2401256 term23 term23). Qed.
Lemma lem2401258 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401259 : term84 = term23.
Proof. exact (EQ_MP (@lem2401258) (@lem940073)). Qed.
Lemma lem2401260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401261 : term82 = term22.
Proof. exact (MK_COMB (@lem2401260) (@lem2401259)). Qed.
Lemma lem2401262 : term81 = term22.
Proof. exact (TRANS (@lem2401257) (@lem2401261)). Qed.
Lemma lem2401263 : term282 = term282.
Proof. exact (eq_refl term282). Qed.
Lemma lem2401264 : term286 = term284.
Proof. exact (MK_COMB (@lem2401263) (@lem2401262)). Qed.
Lemma lem2401266 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401267 : term284 = term285.
Proof. exact (@lem2401266 term153 term23). Qed.
Lemma lem2401268 : term159 = term151.
Proof. exact (@lem996237 term151). Qed.
Lemma lem2401269 : (term159 = term151) = (term160 = term153).
Proof. exact (@lem1007663 term151 (BIT1 0) term151). Qed.
Lemma lem2401270 : term160 = term153.
Proof. exact (EQ_MP (@lem2401269) (@lem2401268)). Qed.
Lemma lem2401271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401272 : term158 = term139.
Proof. exact (MK_COMB (@lem2401271) (@lem2401270)). Qed.
Lemma lem2401273 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401274 : term285 = term275.
Proof. exact (MK_COMB (@lem2401273) (@lem2401272)). Qed.
Lemma lem2401275 : term284 = term275.
Proof. exact (TRANS (@lem2401267) (@lem2401274)). Qed.
Lemma lem2401276 : term286 = term275.
Proof. exact (TRANS (@lem2401264) (@lem2401275)). Qed.
Lemma lem2401277 : term275 = term286.
Proof. exact (SYM (@lem2401276)). Qed.
Lemma lem2401278 : term283 = term286.
Proof. exact (TRANS (@lem2401254) (@lem2401277)). Qed.
Lemma lem2401279 : term273 = term287.
Proof. exact (@lem2401205 (@lem2401278)). Qed.
Lemma lem2401280 : term272 = term287.
Proof. exact (TRANS (@lem2401171) (@lem2401279)). Qed.
Lemma lem2401282 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2401283 : term287 = term275.
Proof. exact (@lem2401282 term275). Qed.
Lemma lem2401284 : term272 = term275.
Proof. exact (TRANS (@lem2401280) (@lem2401283)). Qed.
Lemma lem2401285 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401286 : term288 = term282.
Proof. exact (MK_COMB (@lem2401285) (@lem2401284)). Qed.
Lemma lem2401287 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2401288 (n : int) : (term271 n) = (term289 n).
Proof. exact (MK_COMB (@lem2401286) (@lem2401287 n)). Qed.
Lemma lem2401289 (n : int) : (term270 n) = (term289 n).
Proof. exact (TRANS (@lem2401162 n) (@lem2401288 n)). Qed.
Lemma lem2401290 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401291 (n : int) : (term290 n) = (term291 n).
Proof. exact (MK_COMB (@lem2401290) (@lem2401289 n)). Qed.
Lemma lem2401292 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem2401293 (n : int) : (term269 n) = (term292 n).
Proof. exact (MK_COMB (@lem2401291 n) (@lem2401292)). Qed.
Lemma lem2401294 (n : int) : (term268 n) = (term292 n).
Proof. exact (TRANS (@lem2401161 n) (@lem2401293 n)). Qed.
Lemma lem2401295 (n : int) : (term265 n) = (term292 n).
Proof. exact (TRANS (@lem2401160 n) (@lem2401294 n)). Qed.
Lemma lem2401296 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2401297 (n : int) : (term293 n) = (term294 n).
Proof. exact (MK_COMB (@lem2401296) (@lem2401295 n)). Qed.
Lemma lem2401298 (n : int) : (term295 n) = (term296 n).
Proof. exact (MK_COMB (@lem2401297 n) (@lem2401137)). Qed.
Lemma lem2401299 (n : int) : (term296 n) = (term297 n).
Proof. exact (@lem1982792 (term292 n) term18). Qed.
Lemma lem2401301 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401302 : term18 = term194.
Proof. exact (@lem2401301 (NUMERAL 0)). Qed.
Lemma lem2401304 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401305 : term72 = term73.
Proof. exact (@lem2401304 term23). Qed.
Lemma lem2401306 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401307 : term74 = term75.
Proof. exact (MK_COMB (@lem2401306) (@lem2401305)). Qed.
Lemma lem2401308 : term230 = term231.
Proof. exact (MK_COMB (@lem2401307) (@lem2401302)). Qed.
Lemma lem2401309 : term231 = term232.
Proof. exact (@lem1981613 term72 term18 term22 term22). Qed.
Lemma lem2401311 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401312 : term81 = term82.
Proof. exact (@lem2401311 term23 term23). Qed.
Lemma lem2401313 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401314 : term84 = term23.
Proof. exact (EQ_MP (@lem2401313) (@lem940073)). Qed.
Lemma lem2401315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401316 : term82 = term22.
Proof. exact (MK_COMB (@lem2401315) (@lem2401314)). Qed.
Lemma lem2401317 : term81 = term22.
Proof. exact (TRANS (@lem2401312) (@lem2401316)). Qed.
Lemma lem2401319 (x : nat) : (term233 x) = term18.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2401320 : term230 = term18.
Proof. exact (@lem2401319 term23). Qed.
Lemma lem2401321 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2401322 : term234 = term235.
Proof. exact (MK_COMB (@lem2401321) (@lem2401320)). Qed.
Lemma lem2401323 : term232 = term194.
Proof. exact (MK_COMB (@lem2401322) (@lem2401317)). Qed.
Lemma lem2401324 : term231 = term194.
Proof. exact (TRANS (@lem2401309) (@lem2401323)). Qed.
Lemma lem2401325 : term230 = term194.
Proof. exact (TRANS (@lem2401308) (@lem2401324)). Qed.
Lemma lem2401327 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2401328 : term194 = term18.
Proof. exact (@lem2401327 term18). Qed.
Lemma lem2401329 : term230 = term18.
Proof. exact (TRANS (@lem2401325) (@lem2401328)). Qed.
Lemma lem2401330 (n : int) : (term298 n) = (term298 n).
Proof. exact (eq_refl (term298 n)). Qed.
Lemma lem2401331 (n : int) : (term297 n) = (term299 n).
Proof. exact (MK_COMB (@lem2401330 n) (@lem2401329)). Qed.
Lemma lem2401332 (n : int) : (term299 n) = (term292 n).
Proof. exact (@lem1982723 (term292 n)). Qed.
Lemma lem2401333 (n : int) : (term297 n) = (term292 n).
Proof. exact (TRANS (@lem2401331 n) (@lem2401332 n)). Qed.
Lemma lem2401334 (n : int) : (term296 n) = (term292 n).
Proof. exact (TRANS (@lem2401299 n) (@lem2401333 n)). Qed.
Lemma lem2401335 (n : int) : (term295 n) = (term292 n).
Proof. exact (TRANS (@lem2401298 n) (@lem2401334 n)). Qed.
Lemma lem2401336 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2401337 (n : int) : (term300 n) = (term301 n).
Proof. exact (MK_COMB (@lem2401336) (@lem2401335 n)). Qed.
Lemma lem2401338 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2401339 (n : int) : (term264 n) = (term302 n).
Proof. exact (MK_COMB (@lem2401337 n) (@lem2401338)). Qed.
Lemma lem2401340 (n : int) : (term263 n) = (term302 n).
Proof. exact (TRANS (@lem2401136 n) (@lem2401339 n)). Qed.
Lemma lem2401341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2401342 (n : int) : (term121 n) = (term121 n).
Proof. exact (MK_COMB (@lem2401341) (@lem2400931 n)). Qed.
Lemma lem2401343 (n : int) : (term213 n) = (term303 n).
Proof. exact (MK_COMB (@lem2401342 n) (@lem2401340 n)). Qed.
Lemma lem2401344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2401345 (n : int) : (term214 n) = (term304 n).
Proof. exact (MK_COMB (@lem2401344) (@lem2401135 n)). Qed.
Lemma lem2401346 (n : int) : (term216 n) = (term305 n).
Proof. exact (MK_COMB (@lem2401345 n) (@lem2401343 n)). Qed.
Lemma lem2401347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2401348 (n : int) : (term223 n) = (term306 n).
Proof. exact (MK_COMB (@lem2401347) (@lem2401116 n)). Qed.
Lemma lem2401349 (n : int) : (term224 n) = (term307 n).
Proof. exact (MK_COMB (@lem2401348 n) (@lem2401346 n)). Qed.
Lemma lem2401361 (n : int) : (term209 n) = (term307 n).
Proof. exact (TRANS (@lem2400829 n) (@lem2401349 n)). Qed.
Lemma lem2401362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2401363 (n : int) : (term308 n) = (term309 n).
Proof. exact (MK_COMB (@lem2401362) (@lem2400812 n)). Qed.
Lemma lem2401364 (n : int) : (term123 n) = (term310 n).
Proof. exact (MK_COMB (@lem2401363 n) (@lem2401361 n)). Qed.
Lemma lem2401365 (n : int) (h1 : term310 n) : term310 n.
Proof. exact (h1). Qed.
Lemma lem2401366 (n : int) (h1 : term207 n) : term207 n.
Proof. exact (h1). Qed.
Lemma lem2401367 (n : int) (h1 : term207 n) : term205 n.
Proof. exact (proj2 (@lem2401366 n h1)). Qed.
Lemma lem2401370 (n : int) (h1 : term207 n) : term202.
Proof. exact (proj1 (@lem2401367 n h1)). Qed.
Lemma lem2401372 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2401373 : term202 = term311.
Proof. exact (@lem2401372 term18 term72). Qed.
Lemma lem2401375 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401376 : term72 = term73.
Proof. exact (@lem2401375 term23). Qed.
Lemma lem2401378 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401379 : term18 = term194.
Proof. exact (@lem2401378 (NUMERAL 0)). Qed.
Lemma lem2401380 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2401381 : term312 = term313.
Proof. exact (MK_COMB (@lem2401380) (@lem2401379)). Qed.
Lemma lem2401382 : term311 = term314.
Proof. exact (MK_COMB (@lem2401381) (@lem2401376)). Qed.
Lemma lem2401383 : term315.
Proof. exact (@lem1980026 term18 term22 term72 term22). Qed.
Lemma lem2401385 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401386 : term141 = term142.
Proof. exact (@lem2401385 (NUMERAL 0) term23). Qed.
Lemma lem2401387 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401388 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401389 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401388 h1) (fun h1 : term142 = True => @lem2401387)). Qed.
Lemma lem2401390 : term142 = True.
Proof. exact (EQ_MP (@lem2401389) (@lem2401387)). Qed.
Lemma lem2401391 : term141 = True.
Proof. exact (TRANS (@lem2401386) (@lem2401390)). Qed.
Lemma lem2401392 : True = term141.
Proof. exact (SYM (@lem2401391)). Qed.
Lemma lem2401393 : term141.
Proof. exact (EQ_MP (@lem2401392) (@lem0)). Qed.
Lemma lem2401394 : term316.
Proof. exact (@lem2401383 (@lem2401393)). Qed.
Lemma lem2401396 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401397 : term141 = term142.
Proof. exact (@lem2401396 (NUMERAL 0) term23). Qed.
Lemma lem2401398 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401399 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401400 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401399 h1) (fun h1 : term142 = True => @lem2401398)). Qed.
Lemma lem2401401 : term142 = True.
Proof. exact (EQ_MP (@lem2401400) (@lem2401398)). Qed.
Lemma lem2401402 : term141 = True.
Proof. exact (TRANS (@lem2401397) (@lem2401401)). Qed.
Lemma lem2401403 : True = term141.
Proof. exact (SYM (@lem2401402)). Qed.
Lemma lem2401404 : term141.
Proof. exact (EQ_MP (@lem2401403) (@lem0)). Qed.
Lemma lem2401405 : term314 = term317.
Proof. exact (@lem2401394 (@lem2401404)). Qed.
Lemma lem2401407 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401408 : term76 = term87.
Proof. exact (@lem2401407 term23 term23). Qed.
Lemma lem2401409 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401410 : term84 = term23.
Proof. exact (EQ_MP (@lem2401409) (@lem940073)). Qed.
Lemma lem2401411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401412 : term82 = term22.
Proof. exact (MK_COMB (@lem2401411) (@lem2401410)). Qed.
Lemma lem2401413 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401414 : term87 = term72.
Proof. exact (MK_COMB (@lem2401413) (@lem2401412)). Qed.
Lemma lem2401415 : term76 = term72.
Proof. exact (TRANS (@lem2401408) (@lem2401414)). Qed.
Lemma lem2401417 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401418 : term191 = term18.
Proof. exact (@lem2401417 term23). Qed.
Lemma lem2401419 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2401420 : term318 = term312.
Proof. exact (MK_COMB (@lem2401419) (@lem2401418)). Qed.
Lemma lem2401421 : term317 = term311.
Proof. exact (MK_COMB (@lem2401420) (@lem2401415)). Qed.
Lemma lem2401423 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2401424 : term311 = term321.
Proof. exact (@lem2401423 (NUMERAL 0) term23). Qed.
Lemma lem2401425 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401426 (h1 : term143 = (BIT1 0)) : (term23 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2401427 : (term143 = (BIT1 0)) = ((term23 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401426 h1) (fun h1 : (term23 = (NUMERAL 0)) = False => @lem2401425)). Qed.
Lemma lem2401428 : (term23 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2401427) (@lem2401425)). Qed.
Lemma lem2401429 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2401430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2401431 : term322 = (and True).
Proof. exact (MK_COMB (@lem2401430) (@lem2401429)). Qed.
Lemma lem2401432 : term321 = (True /\ False).
Proof. exact (MK_COMB (@lem2401431) (@lem2401428)). Qed.
Lemma lem2401434 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2401435 : term321 = False.
Proof. exact (TRANS (@lem2401432) (@lem2401434)). Qed.
Lemma lem2401436 : term311 = False.
Proof. exact (TRANS (@lem2401424) (@lem2401435)). Qed.
Lemma lem2401437 : term317 = False.
Proof. exact (TRANS (@lem2401421) (@lem2401436)). Qed.
Lemma lem2401438 : term314 = False.
Proof. exact (TRANS (@lem2401405) (@lem2401437)). Qed.
Lemma lem2401439 : term311 = False.
Proof. exact (TRANS (@lem2401382) (@lem2401438)). Qed.
Lemma lem2401440 : term202 = False.
Proof. exact (TRANS (@lem2401373) (@lem2401439)). Qed.
Lemma lem2401441 (n : int) (h1 : term207 n) : False.
Proof. exact (EQ_MP (@lem2401440) (@lem2401370 n h1)). Qed.
Lemma lem2401442 (n : int) (h1 : term307 n) : term307 n.
Proof. exact (h1). Qed.
Lemma lem2401443 (n : int) (h1 : term255 n) : term255 n.
Proof. exact (h1). Qed.
Lemma lem2401444 (n : int) (h1 : term255 n) : term254 n.
Proof. exact (proj2 (@lem2401443 n h1)). Qed.
Lemma lem2401446 (n : int) (h1 : term255 n) : term202.
Proof. exact (proj2 (@lem2401444 n h1)). Qed.
Lemma lem2401449 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2401450 : term202 = term311.
Proof. exact (@lem2401449 term18 term72). Qed.
Lemma lem2401452 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401453 : term72 = term73.
Proof. exact (@lem2401452 term23). Qed.
Lemma lem2401455 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401456 : term18 = term194.
Proof. exact (@lem2401455 (NUMERAL 0)). Qed.
Lemma lem2401457 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2401458 : term312 = term313.
Proof. exact (MK_COMB (@lem2401457) (@lem2401456)). Qed.
Lemma lem2401459 : term311 = term314.
Proof. exact (MK_COMB (@lem2401458) (@lem2401453)). Qed.
Lemma lem2401460 : term315.
Proof. exact (@lem1980026 term18 term22 term72 term22). Qed.
Lemma lem2401462 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401463 : term141 = term142.
Proof. exact (@lem2401462 (NUMERAL 0) term23). Qed.
Lemma lem2401464 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401465 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401466 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401465 h1) (fun h1 : term142 = True => @lem2401464)). Qed.
Lemma lem2401467 : term142 = True.
Proof. exact (EQ_MP (@lem2401466) (@lem2401464)). Qed.
Lemma lem2401468 : term141 = True.
Proof. exact (TRANS (@lem2401463) (@lem2401467)). Qed.
Lemma lem2401469 : True = term141.
Proof. exact (SYM (@lem2401468)). Qed.
Lemma lem2401470 : term141.
Proof. exact (EQ_MP (@lem2401469) (@lem0)). Qed.
Lemma lem2401471 : term316.
Proof. exact (@lem2401460 (@lem2401470)). Qed.
Lemma lem2401473 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401474 : term141 = term142.
Proof. exact (@lem2401473 (NUMERAL 0) term23). Qed.
Lemma lem2401475 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401476 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401477 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401476 h1) (fun h1 : term142 = True => @lem2401475)). Qed.
Lemma lem2401478 : term142 = True.
Proof. exact (EQ_MP (@lem2401477) (@lem2401475)). Qed.
Lemma lem2401479 : term141 = True.
Proof. exact (TRANS (@lem2401474) (@lem2401478)). Qed.
Lemma lem2401480 : True = term141.
Proof. exact (SYM (@lem2401479)). Qed.
Lemma lem2401481 : term141.
Proof. exact (EQ_MP (@lem2401480) (@lem0)). Qed.
Lemma lem2401482 : term314 = term317.
Proof. exact (@lem2401471 (@lem2401481)). Qed.
Lemma lem2401484 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401485 : term76 = term87.
Proof. exact (@lem2401484 term23 term23). Qed.
Lemma lem2401486 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401487 : term84 = term23.
Proof. exact (EQ_MP (@lem2401486) (@lem940073)). Qed.
Lemma lem2401488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401489 : term82 = term22.
Proof. exact (MK_COMB (@lem2401488) (@lem2401487)). Qed.
Lemma lem2401490 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401491 : term87 = term72.
Proof. exact (MK_COMB (@lem2401490) (@lem2401489)). Qed.
Lemma lem2401492 : term76 = term72.
Proof. exact (TRANS (@lem2401485) (@lem2401491)). Qed.
Lemma lem2401494 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401495 : term191 = term18.
Proof. exact (@lem2401494 term23). Qed.
Lemma lem2401496 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2401497 : term318 = term312.
Proof. exact (MK_COMB (@lem2401496) (@lem2401495)). Qed.
Lemma lem2401498 : term317 = term311.
Proof. exact (MK_COMB (@lem2401497) (@lem2401492)). Qed.
Lemma lem2401500 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2401501 : term311 = term321.
Proof. exact (@lem2401500 (NUMERAL 0) term23). Qed.
Lemma lem2401502 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401503 (h1 : term143 = (BIT1 0)) : (term23 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2401504 : (term143 = (BIT1 0)) = ((term23 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401503 h1) (fun h1 : (term23 = (NUMERAL 0)) = False => @lem2401502)). Qed.
Lemma lem2401505 : (term23 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2401504) (@lem2401502)). Qed.
Lemma lem2401506 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2401507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2401508 : term322 = (and True).
Proof. exact (MK_COMB (@lem2401507) (@lem2401506)). Qed.
Lemma lem2401509 : term321 = (True /\ False).
Proof. exact (MK_COMB (@lem2401508) (@lem2401505)). Qed.
Lemma lem2401511 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2401512 : term321 = False.
Proof. exact (TRANS (@lem2401509) (@lem2401511)). Qed.
Lemma lem2401513 : term311 = False.
Proof. exact (TRANS (@lem2401501) (@lem2401512)). Qed.
Lemma lem2401514 : term317 = False.
Proof. exact (TRANS (@lem2401498) (@lem2401513)). Qed.
Lemma lem2401515 : term314 = False.
Proof. exact (TRANS (@lem2401482) (@lem2401514)). Qed.
Lemma lem2401516 : term311 = False.
Proof. exact (TRANS (@lem2401459) (@lem2401515)). Qed.
Lemma lem2401517 : term202 = False.
Proof. exact (TRANS (@lem2401450) (@lem2401516)). Qed.
Lemma lem2401518 (n : int) (h1 : term255 n) : False.
Proof. exact (EQ_MP (@lem2401517) (@lem2401446 n h1)). Qed.
Lemma lem2401519 (n : int) (h1 : term305 n) : term305 n.
Proof. exact (h1). Qed.
Lemma lem2401520 (n : int) (h1 : term305 n) : term303 n.
Proof. exact (proj2 (@lem2401519 n h1)). Qed.
Lemma lem2401521 (n : int) (h1 : term305 n) : term262 n.
Proof. exact (proj1 (@lem2401519 n h1)). Qed.
Lemma lem2401523 (n : int) (h1 : term305 n) : term94 n.
Proof. exact (proj1 (@lem2401520 n h1)). Qed.
Lemma lem2401525 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2401526 : term323 = term141.
Proof. exact (@lem2401525 term18 term22). Qed.
Lemma lem2401528 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401529 : term22 = term69.
Proof. exact (@lem2401528 term23). Qed.
Lemma lem2401531 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401532 : term18 = term194.
Proof. exact (@lem2401531 (NUMERAL 0)). Qed.
Lemma lem2401533 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2401534 : term324 = term325.
Proof. exact (MK_COMB (@lem2401533) (@lem2401532)). Qed.
Lemma lem2401535 : term141 = term326.
Proof. exact (MK_COMB (@lem2401534) (@lem2401529)). Qed.
Lemma lem2401536 : term327.
Proof. exact (@lem1980255 term18 term22 term22 term22). Qed.
Lemma lem2401538 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401539 : term141 = term142.
Proof. exact (@lem2401538 (NUMERAL 0) term23). Qed.
Lemma lem2401540 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401541 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401542 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401541 h1) (fun h1 : term142 = True => @lem2401540)). Qed.
Lemma lem2401543 : term142 = True.
Proof. exact (EQ_MP (@lem2401542) (@lem2401540)). Qed.
Lemma lem2401544 : term141 = True.
Proof. exact (TRANS (@lem2401539) (@lem2401543)). Qed.
Lemma lem2401545 : True = term141.
Proof. exact (SYM (@lem2401544)). Qed.
Lemma lem2401546 : term141.
Proof. exact (EQ_MP (@lem2401545) (@lem0)). Qed.
Lemma lem2401547 : term328.
Proof. exact (@lem2401536 (@lem2401546)). Qed.
Lemma lem2401549 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401550 : term141 = term142.
Proof. exact (@lem2401549 (NUMERAL 0) term23). Qed.
Lemma lem2401551 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401552 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401553 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401552 h1) (fun h1 : term142 = True => @lem2401551)). Qed.
Lemma lem2401554 : term142 = True.
Proof. exact (EQ_MP (@lem2401553) (@lem2401551)). Qed.
Lemma lem2401555 : term141 = True.
Proof. exact (TRANS (@lem2401550) (@lem2401554)). Qed.
Lemma lem2401556 : True = term141.
Proof. exact (SYM (@lem2401555)). Qed.
Lemma lem2401557 : term141.
Proof. exact (EQ_MP (@lem2401556) (@lem0)). Qed.
Lemma lem2401558 : term326 = term329.
Proof. exact (@lem2401547 (@lem2401557)). Qed.
Lemma lem2401560 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401561 : term81 = term82.
Proof. exact (@lem2401560 term23 term23). Qed.
Lemma lem2401562 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401563 : term84 = term23.
Proof. exact (EQ_MP (@lem2401562) (@lem940073)). Qed.
Lemma lem2401564 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401565 : term82 = term22.
Proof. exact (MK_COMB (@lem2401564) (@lem2401563)). Qed.
Lemma lem2401566 : term81 = term22.
Proof. exact (TRANS (@lem2401561) (@lem2401565)). Qed.
Lemma lem2401568 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401569 : term191 = term18.
Proof. exact (@lem2401568 term23). Qed.
Lemma lem2401570 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2401571 : term330 = term324.
Proof. exact (MK_COMB (@lem2401570) (@lem2401569)). Qed.
Lemma lem2401572 : term329 = term141.
Proof. exact (MK_COMB (@lem2401571) (@lem2401566)). Qed.
Lemma lem2401574 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401575 : term141 = term142.
Proof. exact (@lem2401574 (NUMERAL 0) term23). Qed.
Lemma lem2401576 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401577 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401578 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401577 h1) (fun h1 : term142 = True => @lem2401576)). Qed.
Lemma lem2401579 : term142 = True.
Proof. exact (EQ_MP (@lem2401578) (@lem2401576)). Qed.
Lemma lem2401580 : term141 = True.
Proof. exact (TRANS (@lem2401575) (@lem2401579)). Qed.
Lemma lem2401581 : term329 = True.
Proof. exact (TRANS (@lem2401572) (@lem2401580)). Qed.
Lemma lem2401582 : term326 = True.
Proof. exact (TRANS (@lem2401558) (@lem2401581)). Qed.
Lemma lem2401583 : term141 = True.
Proof. exact (TRANS (@lem2401535) (@lem2401582)). Qed.
Lemma lem2401584 : term323 = True.
Proof. exact (TRANS (@lem2401526) (@lem2401583)). Qed.
Lemma lem2401585 : True = term323.
Proof. exact (SYM (@lem2401584)). Qed.
Lemma lem2401586 : term323.
Proof. exact (EQ_MP (@lem2401585) (@lem0)). Qed.
Lemma lem2401587 (n : int) (h1 : term305 n) : term331 n.
Proof. exact (conj (@lem2401586) (@lem2401523 n h1)). Qed.
Lemma lem2401589 (x : real) (y : real) : term332 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2401590 (n : int) : term333 n.
Proof. exact (@lem2401589 term22 (term91 n)). Qed.
Lemma lem2401591 (n : int) (h1 : term305 n) : term334 n.
Proof. exact (@lem2401590 n (@lem2401587 n h1)). Qed.
Lemma lem2401592 (n : int) : (term335 n) = (term91 n).
Proof. exact (@lem1982733 (term91 n)). Qed.
Lemma lem2401593 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2401594 (n : int) : (term336 n) = (term93 n).
Proof. exact (MK_COMB (@lem2401593) (@lem2401592 n)). Qed.
Lemma lem2401595 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2401596 (n : int) : (term334 n) = (term94 n).
Proof. exact (MK_COMB (@lem2401594 n) (@lem2401595)). Qed.
Lemma lem2401597 (n : int) (h1 : term305 n) : term94 n.
Proof. exact (EQ_MP (@lem2401596 n) (@lem2401591 n h1)). Qed.
Lemma lem2401599 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2401600 : term323 = term141.
Proof. exact (@lem2401599 term18 term22). Qed.
Lemma lem2401602 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401603 : term22 = term69.
Proof. exact (@lem2401602 term23). Qed.
Lemma lem2401605 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401606 : term18 = term194.
Proof. exact (@lem2401605 (NUMERAL 0)). Qed.
Lemma lem2401607 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2401608 : term324 = term325.
Proof. exact (MK_COMB (@lem2401607) (@lem2401606)). Qed.
Lemma lem2401609 : term141 = term326.
Proof. exact (MK_COMB (@lem2401608) (@lem2401603)). Qed.
Lemma lem2401610 : term327.
Proof. exact (@lem1980255 term18 term22 term22 term22). Qed.
Lemma lem2401612 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401613 : term141 = term142.
Proof. exact (@lem2401612 (NUMERAL 0) term23). Qed.
Lemma lem2401614 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401615 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401616 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401615 h1) (fun h1 : term142 = True => @lem2401614)). Qed.
Lemma lem2401617 : term142 = True.
Proof. exact (EQ_MP (@lem2401616) (@lem2401614)). Qed.
Lemma lem2401618 : term141 = True.
Proof. exact (TRANS (@lem2401613) (@lem2401617)). Qed.
Lemma lem2401619 : True = term141.
Proof. exact (SYM (@lem2401618)). Qed.
Lemma lem2401620 : term141.
Proof. exact (EQ_MP (@lem2401619) (@lem0)). Qed.
Lemma lem2401621 : term328.
Proof. exact (@lem2401610 (@lem2401620)). Qed.
Lemma lem2401623 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401624 : term141 = term142.
Proof. exact (@lem2401623 (NUMERAL 0) term23). Qed.
Lemma lem2401625 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401626 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401627 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401626 h1) (fun h1 : term142 = True => @lem2401625)). Qed.
Lemma lem2401628 : term142 = True.
Proof. exact (EQ_MP (@lem2401627) (@lem2401625)). Qed.
Lemma lem2401629 : term141 = True.
Proof. exact (TRANS (@lem2401624) (@lem2401628)). Qed.
Lemma lem2401630 : True = term141.
Proof. exact (SYM (@lem2401629)). Qed.
Lemma lem2401631 : term141.
Proof. exact (EQ_MP (@lem2401630) (@lem0)). Qed.
Lemma lem2401632 : term326 = term329.
Proof. exact (@lem2401621 (@lem2401631)). Qed.
Lemma lem2401634 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401635 : term81 = term82.
Proof. exact (@lem2401634 term23 term23). Qed.
Lemma lem2401636 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401637 : term84 = term23.
Proof. exact (EQ_MP (@lem2401636) (@lem940073)). Qed.
Lemma lem2401638 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401639 : term82 = term22.
Proof. exact (MK_COMB (@lem2401638) (@lem2401637)). Qed.
Lemma lem2401640 : term81 = term22.
Proof. exact (TRANS (@lem2401635) (@lem2401639)). Qed.
Lemma lem2401642 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401643 : term191 = term18.
Proof. exact (@lem2401642 term23). Qed.
Lemma lem2401644 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2401645 : term330 = term324.
Proof. exact (MK_COMB (@lem2401644) (@lem2401643)). Qed.
Lemma lem2401646 : term329 = term141.
Proof. exact (MK_COMB (@lem2401645) (@lem2401640)). Qed.
Lemma lem2401648 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401649 : term141 = term142.
Proof. exact (@lem2401648 (NUMERAL 0) term23). Qed.
Lemma lem2401650 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401651 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401652 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401651 h1) (fun h1 : term142 = True => @lem2401650)). Qed.
Lemma lem2401653 : term142 = True.
Proof. exact (EQ_MP (@lem2401652) (@lem2401650)). Qed.
Lemma lem2401654 : term141 = True.
Proof. exact (TRANS (@lem2401649) (@lem2401653)). Qed.
Lemma lem2401655 : term329 = True.
Proof. exact (TRANS (@lem2401646) (@lem2401654)). Qed.
Lemma lem2401656 : term326 = True.
Proof. exact (TRANS (@lem2401632) (@lem2401655)). Qed.
Lemma lem2401657 : term141 = True.
Proof. exact (TRANS (@lem2401609) (@lem2401656)). Qed.
Lemma lem2401658 : term323 = True.
Proof. exact (TRANS (@lem2401600) (@lem2401657)). Qed.
Lemma lem2401659 : True = term323.
Proof. exact (SYM (@lem2401658)). Qed.
Lemma lem2401660 : term323.
Proof. exact (EQ_MP (@lem2401659) (@lem0)). Qed.
Lemma lem2401661 (n : int) (h1 : term305 n) : term337 n.
Proof. exact (conj (@lem2401660) (@lem2401521 n h1)). Qed.
Lemma lem2401663 (x : real) (y : real) : term338 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2401664 (n : int) : term339 n.
Proof. exact (@lem2401663 term22 (term174 n)). Qed.
Lemma lem2401665 (n : int) (h1 : term305 n) : term340 n.
Proof. exact (@lem2401664 n (@lem2401661 n h1)). Qed.
Lemma lem2401666 (n : int) : (term341 n) = (term174 n).
Proof. exact (@lem1982733 (term174 n)). Qed.
Lemma lem2401667 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2401668 (n : int) : (term342 n) = (term261 n).
Proof. exact (MK_COMB (@lem2401667) (@lem2401666 n)). Qed.
Lemma lem2401669 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2401670 (n : int) : (term340 n) = (term262 n).
Proof. exact (MK_COMB (@lem2401668 n) (@lem2401669)). Qed.
Lemma lem2401671 (n : int) (h1 : term305 n) : term262 n.
Proof. exact (EQ_MP (@lem2401670 n) (@lem2401665 n h1)). Qed.
Lemma lem2401672 (n : int) (h1 : term305 n) : term343 n.
Proof. exact (conj (@lem2401671 n h1) (@lem2401597 n h1)). Qed.
Lemma lem2401674 (x : real) (y : real) : term344 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem2401675 (n : int) : term345 n.
Proof. exact (@lem2401674 (term174 n) (term91 n)). Qed.
Lemma lem2401676 (n : int) (h1 : term305 n) : term346 n.
Proof. exact (@lem2401675 n (@lem2401672 n h1)). Qed.
Lemma lem2401677 (n : int) : (term347 n) = (term348 n).
Proof. exact (@lem1982763 (term174 n) (real_of_int n) term72). Qed.
Lemma lem2401678 (n : int) : (term349 n) = (term176 n).
Proof. exact (@lem1982713 term72 (real_of_int n)). Qed.
Lemma lem2401680 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401681 : term22 = term69.
Proof. exact (@lem2401680 term23). Qed.
Lemma lem2401683 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401684 : term72 = term73.
Proof. exact (@lem2401683 term23). Qed.
Lemma lem2401685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401686 : term177 = term178.
Proof. exact (MK_COMB (@lem2401685) (@lem2401684)). Qed.
Lemma lem2401687 : term179 = term180.
Proof. exact (MK_COMB (@lem2401686) (@lem2401681)). Qed.
Lemma lem2401688 : term181.
Proof. exact (@lem1981473 term72 term22 term22 term22 term18 term22). Qed.
Lemma lem2401690 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401691 : term141 = term142.
Proof. exact (@lem2401690 (NUMERAL 0) term23). Qed.
Lemma lem2401692 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401693 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401694 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401693 h1) (fun h1 : term142 = True => @lem2401692)). Qed.
Lemma lem2401695 : term142 = True.
Proof. exact (EQ_MP (@lem2401694) (@lem2401692)). Qed.
Lemma lem2401696 : term141 = True.
Proof. exact (TRANS (@lem2401691) (@lem2401695)). Qed.
Lemma lem2401697 : True = term141.
Proof. exact (SYM (@lem2401696)). Qed.
Lemma lem2401698 : term141.
Proof. exact (EQ_MP (@lem2401697) (@lem0)). Qed.
Lemma lem2401699 : term182.
Proof. exact (@lem2401688 (@lem2401698)). Qed.
Lemma lem2401701 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401702 : term141 = term142.
Proof. exact (@lem2401701 (NUMERAL 0) term23). Qed.
Lemma lem2401703 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401704 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401705 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401704 h1) (fun h1 : term142 = True => @lem2401703)). Qed.
Lemma lem2401706 : term142 = True.
Proof. exact (EQ_MP (@lem2401705) (@lem2401703)). Qed.
Lemma lem2401707 : term141 = True.
Proof. exact (TRANS (@lem2401702) (@lem2401706)). Qed.
Lemma lem2401708 : True = term141.
Proof. exact (SYM (@lem2401707)). Qed.
Lemma lem2401709 : term141.
Proof. exact (EQ_MP (@lem2401708) (@lem0)). Qed.
Lemma lem2401710 : term183.
Proof. exact (@lem2401699 (@lem2401709)). Qed.
Lemma lem2401712 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401713 : term141 = term142.
Proof. exact (@lem2401712 (NUMERAL 0) term23). Qed.
Lemma lem2401714 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401715 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401716 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401715 h1) (fun h1 : term142 = True => @lem2401714)). Qed.
Lemma lem2401717 : term142 = True.
Proof. exact (EQ_MP (@lem2401716) (@lem2401714)). Qed.
Lemma lem2401718 : term141 = True.
Proof. exact (TRANS (@lem2401713) (@lem2401717)). Qed.
Lemma lem2401719 : True = term141.
Proof. exact (SYM (@lem2401718)). Qed.
Lemma lem2401720 : term141.
Proof. exact (EQ_MP (@lem2401719) (@lem0)). Qed.
Lemma lem2401721 : term184.
Proof. exact (@lem2401710 (@lem2401720)). Qed.
Lemma lem2401723 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401724 : term81 = term82.
Proof. exact (@lem2401723 term23 term23). Qed.
Lemma lem2401725 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401726 : term84 = term23.
Proof. exact (EQ_MP (@lem2401725) (@lem940073)). Qed.
Lemma lem2401727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401728 : term82 = term22.
Proof. exact (MK_COMB (@lem2401727) (@lem2401726)). Qed.
Lemma lem2401729 : term81 = term22.
Proof. exact (TRANS (@lem2401724) (@lem2401728)). Qed.
Lemma lem2401731 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401732 : term76 = term87.
Proof. exact (@lem2401731 term23 term23). Qed.
Lemma lem2401733 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401734 : term84 = term23.
Proof. exact (EQ_MP (@lem2401733) (@lem940073)). Qed.
Lemma lem2401735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401736 : term82 = term22.
Proof. exact (MK_COMB (@lem2401735) (@lem2401734)). Qed.
Lemma lem2401737 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401738 : term87 = term72.
Proof. exact (MK_COMB (@lem2401737) (@lem2401736)). Qed.
Lemma lem2401739 : term76 = term72.
Proof. exact (TRANS (@lem2401732) (@lem2401738)). Qed.
Lemma lem2401740 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401741 : term185 = term177.
Proof. exact (MK_COMB (@lem2401740) (@lem2401739)). Qed.
Lemma lem2401742 : term186 = term179.
Proof. exact (MK_COMB (@lem2401741) (@lem2401729)). Qed.
Lemma lem2401744 (m : nat) : (term187 m) = term18.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2401745 : term179 = term18.
Proof. exact (@lem2401744 term23). Qed.
Lemma lem2401746 : term186 = term18.
Proof. exact (TRANS (@lem2401742) (@lem2401745)). Qed.
Lemma lem2401747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401748 : term188 = term189.
Proof. exact (MK_COMB (@lem2401747) (@lem2401746)). Qed.
Lemma lem2401749 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem2401750 : term190 = term191.
Proof. exact (MK_COMB (@lem2401748) (@lem2401749)). Qed.
Lemma lem2401752 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401753 : term191 = term18.
Proof. exact (@lem2401752 term23). Qed.
Lemma lem2401754 : term190 = term18.
Proof. exact (TRANS (@lem2401750) (@lem2401753)). Qed.
Lemma lem2401756 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2401757 : term81 = term82.
Proof. exact (@lem2401756 term23 term23). Qed.
Lemma lem2401758 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401759 : term84 = term23.
Proof. exact (EQ_MP (@lem2401758) (@lem940073)). Qed.
Lemma lem2401760 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401761 : term82 = term22.
Proof. exact (MK_COMB (@lem2401760) (@lem2401759)). Qed.
Lemma lem2401762 : term81 = term22.
Proof. exact (TRANS (@lem2401757) (@lem2401761)). Qed.
Lemma lem2401763 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem2401764 : term193 = term191.
Proof. exact (MK_COMB (@lem2401763) (@lem2401762)). Qed.
Lemma lem2401766 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401767 : term191 = term18.
Proof. exact (@lem2401766 term23). Qed.
Lemma lem2401768 : term193 = term18.
Proof. exact (TRANS (@lem2401764) (@lem2401767)). Qed.
Lemma lem2401769 : term18 = term193.
Proof. exact (SYM (@lem2401768)). Qed.
Lemma lem2401770 : term190 = term193.
Proof. exact (TRANS (@lem2401754) (@lem2401769)). Qed.
Lemma lem2401771 : term180 = term194.
Proof. exact (@lem2401721 (@lem2401770)). Qed.
Lemma lem2401772 : term179 = term194.
Proof. exact (TRANS (@lem2401687) (@lem2401771)). Qed.
Lemma lem2401774 (x : real) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2401775 : term194 = term18.
Proof. exact (@lem2401774 term18). Qed.
Lemma lem2401776 : term179 = term18.
Proof. exact (TRANS (@lem2401772) (@lem2401775)). Qed.
Lemma lem2401777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2401778 : term195 = term189.
Proof. exact (MK_COMB (@lem2401777) (@lem2401776)). Qed.
Lemma lem2401779 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2401780 (n : int) : (term176 n) = (term196 n).
Proof. exact (MK_COMB (@lem2401778) (@lem2401779 n)). Qed.
Lemma lem2401781 (n : int) : (term349 n) = (term196 n).
Proof. exact (TRANS (@lem2401678 n) (@lem2401780 n)). Qed.
Lemma lem2401782 (n : int) : (term196 n) = term18.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2401783 (n : int) : (term349 n) = term18.
Proof. exact (TRANS (@lem2401781 n) (@lem2401782 n)). Qed.
Lemma lem2401784 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2401785 (n : int) : (term350 n) = term20.
Proof. exact (MK_COMB (@lem2401784) (@lem2401783 n)). Qed.
Lemma lem2401786 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem2401787 (n : int) : (term348 n) = term198.
Proof. exact (MK_COMB (@lem2401785 n) (@lem2401786)). Qed.
Lemma lem2401788 (n : int) : (term347 n) = term198.
Proof. exact (TRANS (@lem2401677 n) (@lem2401787 n)). Qed.
Lemma lem2401789 : term198 = term72.
Proof. exact (@lem1982721 term72). Qed.
Lemma lem2401790 (n : int) : (term347 n) = term72.
Proof. exact (TRANS (@lem2401788 n) (@lem2401789)). Qed.
Lemma lem2401791 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2401792 (n : int) : (term351 n) = term352.
Proof. exact (MK_COMB (@lem2401791) (@lem2401790 n)). Qed.
Lemma lem2401793 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem2401794 (n : int) : (term346 n) = term353.
Proof. exact (MK_COMB (@lem2401792 n) (@lem2401793)). Qed.
Lemma lem2401795 (n : int) (h1 : term305 n) : term353.
Proof. exact (EQ_MP (@lem2401794 n) (@lem2401676 n h1)). Qed.
Lemma lem2401797 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2401798 : term353 = term354.
Proof. exact (@lem2401797 term18 term72). Qed.
Lemma lem2401800 (x : nat) : (term70 x) = (term71 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2401801 : term72 = term73.
Proof. exact (@lem2401800 term23). Qed.
Lemma lem2401803 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2401804 : term18 = term194.
Proof. exact (@lem2401803 (NUMERAL 0)). Qed.
Lemma lem2401805 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2401806 : term324 = term325.
Proof. exact (MK_COMB (@lem2401805) (@lem2401804)). Qed.
Lemma lem2401807 : term354 = term355.
Proof. exact (MK_COMB (@lem2401806) (@lem2401801)). Qed.
Lemma lem2401808 : term356.
Proof. exact (@lem1980255 term18 term22 term72 term22). Qed.
Lemma lem2401810 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401811 : term141 = term142.
Proof. exact (@lem2401810 (NUMERAL 0) term23). Qed.
Lemma lem2401812 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401813 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401814 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401813 h1) (fun h1 : term142 = True => @lem2401812)). Qed.
Lemma lem2401815 : term142 = True.
Proof. exact (EQ_MP (@lem2401814) (@lem2401812)). Qed.
Lemma lem2401816 : term141 = True.
Proof. exact (TRANS (@lem2401811) (@lem2401815)). Qed.
Lemma lem2401817 : True = term141.
Proof. exact (SYM (@lem2401816)). Qed.
Lemma lem2401818 : term141.
Proof. exact (EQ_MP (@lem2401817) (@lem0)). Qed.
Lemma lem2401819 : term357.
Proof. exact (@lem2401808 (@lem2401818)). Qed.
Lemma lem2401821 (m : nat) (n : nat) : (term140 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2401822 : term141 = term142.
Proof. exact (@lem2401821 (NUMERAL 0) term23). Qed.
Lemma lem2401823 : term143 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2401824 (h1 : term143 = (BIT1 0)) : term142 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2401825 : (term143 = (BIT1 0)) = (term142 = True).
Proof. exact (prop_ext (fun h1 : term143 = (BIT1 0) => @lem2401824 h1) (fun h1 : term142 = True => @lem2401823)). Qed.
Lemma lem2401826 : term142 = True.
Proof. exact (EQ_MP (@lem2401825) (@lem2401823)). Qed.
Lemma lem2401827 : term141 = True.
Proof. exact (TRANS (@lem2401822) (@lem2401826)). Qed.
Lemma lem2401828 : True = term141.
Proof. exact (SYM (@lem2401827)). Qed.
Lemma lem2401829 : term141.
Proof. exact (EQ_MP (@lem2401828) (@lem0)). Qed.
Lemma lem2401830 : term355 = term358.
Proof. exact (@lem2401819 (@lem2401829)). Qed.
Lemma lem2401832 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2401833 : term76 = term87.
Proof. exact (@lem2401832 term23 term23). Qed.
Lemma lem2401834 : (term83 = (BIT1 0)) = (term84 = term23).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2401835 : term84 = term23.
Proof. exact (EQ_MP (@lem2401834) (@lem940073)). Qed.
Lemma lem2401836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2401837 : term82 = term22.
Proof. exact (MK_COMB (@lem2401836) (@lem2401835)). Qed.
Lemma lem2401838 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2401839 : term87 = term72.
Proof. exact (MK_COMB (@lem2401838) (@lem2401837)). Qed.
Lemma lem2401840 : term76 = term72.
Proof. exact (TRANS (@lem2401833) (@lem2401839)). Qed.
Lemma lem2401842 (x : nat) : (term192 x) = term18.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2401843 : term191 = term18.
Proof. exact (@lem2401842 term23). Qed.
Lemma lem2401844 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2401845 : term330 = term324.
Proof. exact (MK_COMB (@lem2401844) (@lem2401843)). Qed.
Lemma lem2401846 : term358 = term354.
Proof. exact (MK_COMB (@lem2401845) (@lem2401840)). Qed.
Lemma lem2401848 (m : nat) (n : nat) : (term359 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem2401849 : term354 = False.
Proof. exact (@lem2401848 (NUMERAL 0) term23). Qed.
Lemma lem2401850 : term358 = False.
Proof. exact (TRANS (@lem2401846) (@lem2401849)). Qed.
Lemma lem2401851 : term355 = False.
Proof. exact (TRANS (@lem2401830) (@lem2401850)). Qed.
Lemma lem2401852 : term354 = False.
Proof. exact (TRANS (@lem2401807) (@lem2401851)). Qed.
Lemma lem2401853 : term353 = False.
Proof. exact (TRANS (@lem2401798) (@lem2401852)). Qed.
Lemma lem2401854 (n : int) (h1 : term305 n) : False.
Proof. exact (EQ_MP (@lem2401853) (@lem2401795 n h1)). Qed.
Lemma lem2401855 (n : int) (h1 : term307 n) : False.
Proof. exact (or_elim (@lem2401442 n h1) (fun h0 : term255 n => @lem2401518 n h0) (fun h0 : term305 n => @lem2401854 n h0)). Qed.
Lemma lem2401856 (n : int) (h1 : term310 n) : False.
Proof. exact (or_elim (@lem2401365 n h1) (fun h0 : term207 n => @lem2401441 n h0) (fun h0 : term307 n => @lem2401855 n h0)). Qed.
Lemma lem2401857 (n : int) (h1 : term123 n) : term123 n.
Proof. exact (h1). Qed.
Lemma lem2401858 (n : int) (h1 : term123 n) : term310 n.
Proof. exact (EQ_MP (@lem2401364 n) (@lem2401857 n h1)). Qed.
Lemma lem2401859 (n : int) (h1 : term123 n) : (term310 n) = False.
Proof. exact (prop_ext (fun h2 : term310 n => @lem2401856 n h2) (fun h2 : False => @lem2401858 n h1)). Qed.
Lemma lem2401860 (n : int) (h1 : term123 n) : False.
Proof. exact (EQ_MP (@lem2401859 n h1) (@lem2401858 n h1)). Qed.
Lemma lem2401861 (n : int) (h1 : term62 n) : term62 n.
Proof. exact (h1). Qed.
Lemma lem2401862 (n : int) (h1 : term62 n) : term123 n.
Proof. exact (EQ_MP (@lem2400519 n) (@lem2401861 n h1)). Qed.
Lemma lem2401863 (n : int) (h1 : term62 n) : (term123 n) = False.
Proof. exact (prop_ext (fun h2 : term123 n => @lem2401860 n h2) (fun h2 : False => @lem2401862 n h1)). Qed.
Lemma lem2401864 (n : int) (h1 : term62 n) : False.
Proof. exact (EQ_MP (@lem2401863 n h1) (@lem2401862 n h1)). Qed.
Lemma lem2401865 (n : int) : term360 n.
Proof. exact (fun h0 : term62 n => @lem2401864 n h0). Qed.
Lemma lem2401866 (n : int) : term361 n.
Proof. exact (@lem1386578 (term362 n)). Qed.
Lemma lem2401869 (n : int) : term362 n.
Proof. exact (@lem2401866 n (@lem2401865 n)). Qed.
Lemma lem2401870 (n : int) : (term60 n) = (term2 n).
Proof. exact (SYM (@lem2400255 n)). Qed.
Lemma lem2401871 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2401872 (n : int) : (term362 n) = (term0 n).
Proof. exact (MK_COMB (@lem2401871) (@lem2401870 n)). Qed.
Lemma lem2401873 (n : int) : term0 n.
Proof. exact (EQ_MP (@lem2401872 n) (@lem2401869 n)). Qed.
Lemma lem2401874 (n : int) : term1 n.
Proof. exact (EQ_MP (@lem2400156 n) (@lem2401873 n)). Qed.
Lemma lem2401885 : term363.
Proof. exact (fun n : int => @lem2401874 n). Qed.
Lemma lem2401887 (p : Prop) : p = (term364 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2401888 : term365 = term366.
Proof. exact (@lem2401887 term365). Qed.
Lemma lem2401889 : term366 = term365.
Proof. exact (SYM (@lem2401888)). Qed.
Lemma lem2401890 (h1 : term367) : term367.
Proof. exact (h1). Qed.
Lemma lem2401893 (h1 : term368) : term368.
Proof. exact (h1). Qed.
Lemma lem2401894 : term369.
Proof. exact (fun h0 : term368 => @lem2401893 h0). Qed.
Lemma lem2401895 (h1 : term369) : term369.
Proof. exact (h1). Qed.
Lemma lem2401896 (h1 : term368) : term368.
Proof. exact (h1). Qed.
Lemma lem2401897 (h1 : term368) (h2 : term369) : term368.
Proof. exact (@lem2401895 h2 (@lem2401896 h1)). Qed.
Lemma lem2401898 (h1 : term368) : term370.
Proof. exact (fun h0 : term369 => @lem2401897 h1 h0). Qed.
Lemma lem2401899 (h1 : term369) : term369.
Proof. exact (h1). Qed.
Lemma lem2401900 (h1 : term368) (h2 : term369) : term368.
Proof. exact (@lem2401898 h1 (@lem2401899 h2)). Qed.
Lemma lem2401901 (h1 : term369) : term369.
Proof. exact (fun h0 : term368 => @lem2401900 h0 h1). Qed.
Lemma lem2401902 : term371.
Proof. exact (fun h0 : term369 => @lem2401901 h0). Qed.
Lemma lem2401905 : term369.
Proof. exact (@lem2401902 (@lem2401894)). Qed.
Lemma lem2401933 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2401934 : term372 = term373.
Proof. exact (@lem2401933 term374). Qed.
Lemma lem2401949 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem2401950 : term376 = term377.
Proof. exact (MK_COMB (@lem2401949) (@lem2401934)). Qed.
Lemma lem2401953 : term378 = term378.
Proof. exact (eq_refl term378). Qed.
Lemma lem2401954 : term379 = term380.
Proof. exact (MK_COMB (@lem2401953) (@lem2401950)). Qed.
Lemma lem2401957 : term381 = term381.
Proof. exact (eq_refl term381). Qed.
Lemma lem2401964 : term368 = term382.
Proof. exact (MK_COMB (@lem2401957) (@lem2401954)). Qed.
Lemma lem2401979 (m : int) (n : int) : (term383 m n) = (term383 m n).
Proof. exact (eq_refl (term383 m n)). Qed.
Lemma lem2401980 (m : int) : (term384 m) = (term384 m).
Proof. exact (fun_ext (fun n : int => @lem2401979 m n)). Qed.
Lemma lem2401981 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2401982 (m : int) : (term385 m) = (term385 m).
Proof. exact (MK_COMB (@lem2401981) (@lem2401980 m)). Qed.
Lemma lem2401983 : term386 = term386.
Proof. exact (fun_ext (fun m : int => @lem2401982 m)). Qed.
Lemma lem2401984 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2401985 : term374 = term374.
Proof. exact (MK_COMB (@lem2401984) (@lem2401983)). Qed.
Lemma lem2401986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2401987 : term373 = term373.
Proof. exact (MK_COMB (@lem2401986) (@lem2401985)). Qed.
Lemma lem2401990 (x : int) : (term387 x) = (term387 x).
Proof. exact (eq_refl (term387 x)). Qed.
Lemma lem2401991 : term388 = term388.
Proof. exact (fun_ext (fun x : int => @lem2401990 x)). Qed.
Lemma lem2401992 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2401993 : term389 = term389.
Proof. exact (MK_COMB (@lem2401992) (@lem2401991)). Qed.
Lemma lem2401994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2401995 : term375 = term375.
Proof. exact (MK_COMB (@lem2401994) (@lem2401993)). Qed.
Lemma lem2401996 : term377 = term377.
Proof. exact (MK_COMB (@lem2401995) (@lem2401987)). Qed.
Lemma lem2402001 (n : int) : (term1 n) = (term1 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem2402002 : term390 = term390.
Proof. exact (fun_ext (fun n : int => @lem2402001 n)). Qed.
Lemma lem2402003 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402004 : term363 = term363.
Proof. exact (MK_COMB (@lem2402003) (@lem2402002)). Qed.
Lemma lem2402005 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2402006 : term378 = term378.
Proof. exact (MK_COMB (@lem2402005) (@lem2402004)). Qed.
Lemma lem2402007 : term380 = term380.
Proof. exact (MK_COMB (@lem2402006) (@lem2401996)). Qed.
Lemma lem2402012 (x : int) (n : int) : (term391 x n) = (term391 x n).
Proof. exact (eq_refl (term391 x n)). Qed.
Lemma lem2402013 (x : int) : (term392 x) = (term392 x).
Proof. exact (fun_ext (fun n : int => @lem2402012 x n)). Qed.
Lemma lem2402014 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402015 (x : int) : (term393 x) = (term393 x).
Proof. exact (MK_COMB (@lem2402014) (@lem2402013 x)). Qed.
Lemma lem2402016 : term394 = term394.
Proof. exact (fun_ext (fun x : int => @lem2402015 x)). Qed.
Lemma lem2402017 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402018 : term365 = term365.
Proof. exact (MK_COMB (@lem2402017) (@lem2402016)). Qed.
Lemma lem2402019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2402020 : term367 = term367.
Proof. exact (MK_COMB (@lem2402019) (@lem2402018)). Qed.
Lemma lem2402021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2402022 : term381 = term381.
Proof. exact (MK_COMB (@lem2402021) (@lem2402020)). Qed.
Lemma lem2402023 : term382 = term382.
Proof. exact (MK_COMB (@lem2402022) (@lem2402007)). Qed.
Lemma lem2402078 : term368 = term382.
Proof. exact (TRANS (@lem2401964) (@lem2402023)). Qed.
Lemma lem2402079 : term382 = term368.
Proof. exact (SYM (@lem2402078)). Qed.
Lemma lem2402080 (h1 : term367) : term367.
Proof. exact (h1). Qed.
Lemma lem2402081 (h1 : term363) : term363.
Proof. exact (h1). Qed.
Lemma lem2402082 (h1 : term389) : term389.
Proof. exact (h1). Qed.
Lemma lem2402083 (h1 : term374) : term374.
Proof. exact (h1). Qed.
Lemma lem2402090 (x : int) (n : int) : (term395 x n) = (term396 x n).
Proof. exact (@lem17362 (term4 n) (term397 x n)). Qed.
Lemma lem2402091 (P : int -> Prop) : (term398 P) = (term399 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2402092 (x : int) : (term400 x) = (term401 x).
Proof. exact (@lem2402091 (term392 x)). Qed.
Lemma lem2402093 (x : int) (n : int) : (term402 x n) = (term391 x n).
Proof. exact (eq_refl (term402 x n)). Qed.
Lemma lem2402094 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2402095 (x : int) (n : int) : (term403 x n) = (term395 x n).
Proof. exact (MK_COMB (@lem2402094) (@lem2402093 x n)). Qed.
Lemma lem2402096 (x : int) (n : int) : (term403 x n) = (term396 x n).
Proof. exact (TRANS (@lem2402095 x n) (@lem2402090 x n)). Qed.
Lemma lem2402097 (x : int) : (term404 x) = (term405 x).
Proof. exact (fun_ext (fun n : int => @lem2402096 x n)). Qed.
Lemma lem2402098 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2402099 (x : int) : (term401 x) = (term406 x).
Proof. exact (MK_COMB (@lem2402098) (@lem2402097 x)). Qed.
Lemma lem2402100 (x : int) : (term400 x) = (term406 x).
Proof. exact (TRANS (@lem2402092 x) (@lem2402099 x)). Qed.
Lemma lem2402101 (P : int -> Prop) : (term398 P) = (term399 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2402102 : term367 = term407.
Proof. exact (@lem2402101 term394). Qed.
Lemma lem2402103 (x : int) : (term408 x) = (term393 x).
Proof. exact (eq_refl (term408 x)). Qed.
Lemma lem2402104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2402105 (x : int) : (term409 x) = (term400 x).
Proof. exact (MK_COMB (@lem2402104) (@lem2402103 x)). Qed.
Lemma lem2402106 (x : int) : (term409 x) = (term406 x).
Proof. exact (TRANS (@lem2402105 x) (@lem2402100 x)). Qed.
Lemma lem2402107 : term410 = term411.
Proof. exact (fun_ext (fun x : int => @lem2402106 x)). Qed.
Lemma lem2402108 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2402109 : term407 = term412.
Proof. exact (MK_COMB (@lem2402108) (@lem2402107)). Qed.
Lemma lem2402166 : term367 = term412.
Proof. exact (TRANS (@lem2402102) (@lem2402109)). Qed.
Lemma lem2402167 (h1 : term367) : term412.
Proof. exact (EQ_MP (@lem2402166) (@lem2402080 h1)). Qed.
Lemma lem2402174 (n : int) : (term1 n) = (term413 n).
Proof. exact (@lem17265 (term4 n) ((int_abs n) = n)). Qed.
Lemma lem2402175 : term390 = term414.
Proof. exact (fun_ext (fun n : int => @lem2402174 n)). Qed.
Lemma lem2402176 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402229 : term363 = term415.
Proof. exact (MK_COMB (@lem2402176) (@lem2402175)). Qed.
Lemma lem2402230 (h1 : term363) : term415.
Proof. exact (EQ_MP (@lem2402229) (@lem2402081 h1)). Qed.
Lemma lem2402231 (x : int) : (term387 x) = (term387 x).
Proof. exact (eq_refl (term387 x)). Qed.
Lemma lem2402232 : term388 = term388.
Proof. exact (fun_ext (fun x : int => @lem2402231 x)). Qed.
Lemma lem2402233 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402242 : term389 = term389.
Proof. exact (MK_COMB (@lem2402233) (@lem2402232)). Qed.
Lemma lem2402243 (h1 : term389) : term389.
Proof. exact (EQ_MP (@lem2402242) (@lem2402082 h1)). Qed.
Lemma lem2402246 (n : int) : (term416 n) = (n = term7).
Proof. exact (@lem16933 (n = term7)). Qed.
Lemma lem2402255 (m : int) (n : int) : (term417 m n) = (term417 m n).
Proof. exact (eq_refl (term417 m n)). Qed.
Lemma lem2402256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2402257 (n : int) : (term418 n) = (term419 n).
Proof. exact (MK_COMB (@lem2402256) (@lem2402246 n)). Qed.
Lemma lem2402258 (m : int) (n : int) : (term420 m n) = (term421 m n).
Proof. exact (MK_COMB (@lem2402257 n) (@lem2402255 m n)). Qed.
Lemma lem2402259 (m : int) (n : int) : (term383 m n) = (term420 m n).
Proof. exact (@lem17265 (term422 n) (term417 m n)). Qed.
Lemma lem2402260 (m : int) (n : int) : (term383 m n) = (term421 m n).
Proof. exact (TRANS (@lem2402259 m n) (@lem2402258 m n)). Qed.
Lemma lem2402261 (m : int) : (term384 m) = (term423 m).
Proof. exact (fun_ext (fun n : int => @lem2402260 m n)). Qed.
Lemma lem2402262 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402263 (m : int) : (term385 m) = (term424 m).
Proof. exact (MK_COMB (@lem2402262) (@lem2402261 m)). Qed.
Lemma lem2402264 : term386 = term425.
Proof. exact (fun_ext (fun m : int => @lem2402263 m)). Qed.
Lemma lem2402265 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402322 : term374 = term426.
Proof. exact (MK_COMB (@lem2402265) (@lem2402264)). Qed.
Lemma lem2402323 (h1 : term374) : term426.
Proof. exact (EQ_MP (@lem2402322) (@lem2402083 h1)). Qed.
Lemma lem2402324 (x : int) (h1 : term406 x) : term406 x.
Proof. exact (h1). Qed.
Lemma lem2402346 (n : int) : (term413 n) = (term413 n).
Proof. exact (eq_refl (term413 n)). Qed.
Lemma lem2402347 : term414 = term414.
Proof. exact (fun_ext (fun n : int => @lem2402346 n)). Qed.
Lemma lem2402348 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402349 : term415 = term415.
Proof. exact (MK_COMB (@lem2402348) (@lem2402347)). Qed.
Lemma lem2402350 (h1 : term363) : term415.
Proof. exact (EQ_MP (@lem2402349) (@lem2402230 h1)). Qed.
Lemma lem2402357 (x : int) : (term387 x) = (term387 x).
Proof. exact (eq_refl (term387 x)). Qed.
Lemma lem2402358 : term388 = term388.
Proof. exact (fun_ext (fun x : int => @lem2402357 x)). Qed.
Lemma lem2402359 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402360 : term389 = term389.
Proof. exact (MK_COMB (@lem2402359) (@lem2402358)). Qed.
Lemma lem2402361 (h1 : term389) : term389.
Proof. exact (EQ_MP (@lem2402360) (@lem2402243 h1)). Qed.
Lemma lem2402424 (m : int) (n : int) : (term421 m n) = (term421 m n).
Proof. exact (eq_refl (term421 m n)). Qed.
Lemma lem2402425 (m : int) : (term423 m) = (term423 m).
Proof. exact (fun_ext (fun n : int => @lem2402424 m n)). Qed.
Lemma lem2402426 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402427 (m : int) : (term424 m) = (term424 m).
Proof. exact (MK_COMB (@lem2402426) (@lem2402425 m)). Qed.
Lemma lem2402428 : term425 = term425.
Proof. exact (fun_ext (fun m : int => @lem2402427 m)). Qed.
Lemma lem2402429 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402430 : term426 = term426.
Proof. exact (MK_COMB (@lem2402429) (@lem2402428)). Qed.
Lemma lem2402431 (h1 : term374) : term426.
Proof. exact (EQ_MP (@lem2402430) (@lem2402323 h1)). Qed.
Lemma lem2402455 (x : int) (n : int) (h1 : term396 x n) : term396 x n.
Proof. exact (h1). Qed.
Lemma lem2402465 (n : int) : (term413 n) = (term413 n).
Proof. exact (eq_refl (term413 n)). Qed.
Lemma lem2402466 : term414 = term414.
Proof. exact (fun_ext (fun n : int => @lem2402465 n)). Qed.
Lemma lem2402467 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402469 : term415 = term415.
Proof. exact (MK_COMB (@lem2402467) (@lem2402466)). Qed.
Lemma lem2402470 (h1 : term363) : term415.
Proof. exact (EQ_MP (@lem2402469) (@lem2402350 h1)). Qed.
Lemma lem2402472 (x : int) : (term387 x) = (term387 x).
Proof. exact (eq_refl (term387 x)). Qed.
Lemma lem2402473 : term388 = term388.
Proof. exact (fun_ext (fun x : int => @lem2402472 x)). Qed.
Lemma lem2402474 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402476 : term389 = term389.
Proof. exact (MK_COMB (@lem2402474) (@lem2402473)). Qed.
Lemma lem2402477 (h1 : term389) : term389.
Proof. exact (EQ_MP (@lem2402476) (@lem2402361 h1)). Qed.
Lemma lem2402492 (m : int) (n : int) : (term421 m n) = (term427 m n).
Proof. exact (@lem19490 (m = (term428 m n)) (n = term7) (term429 m n)). Qed.
Lemma lem2402499 (m : int) (n : int) : (term430 m n) = (term431 m n).
Proof. exact (@lem19490 (term432 m n) (n = term7) (term433 m n)). Qed.
Lemma lem2402502 (m : int) (n : int) : (term434 m n) = (term434 m n).
Proof. exact (eq_refl (term434 m n)). Qed.
Lemma lem2402503 (m : int) (n : int) : (term427 m n) = (term435 m n).
Proof. exact (MK_COMB (@lem2402502 m n) (@lem2402499 m n)). Qed.
Lemma lem2402505 (m : int) (n : int) : (term421 m n) = (term435 m n).
Proof. exact (TRANS (@lem2402492 m n) (@lem2402503 m n)). Qed.
Lemma lem2402506 (m : int) : (term423 m) = (term436 m).
Proof. exact (fun_ext (fun n : int => @lem2402505 m n)). Qed.
Lemma lem2402507 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402508 (m : int) : (term424 m) = (term437 m).
Proof. exact (MK_COMB (@lem2402507) (@lem2402506 m)). Qed.
Lemma lem2402509 : term425 = term438.
Proof. exact (fun_ext (fun m : int => @lem2402508 m)). Qed.
Lemma lem2402510 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2402512 : term426 = term439.
Proof. exact (MK_COMB (@lem2402510) (@lem2402509)). Qed.
Lemma lem2402513 (h1 : term374) : term439.
Proof. exact (EQ_MP (@lem2402512) (@lem2402431 h1)). Qed.
Lemma lem2402522 (_29415 : int) (h1 : term363) : term440 _29415.
Proof. exact (@lem2402470 h1 _29415). Qed.
Lemma lem2402523 (_29415 : int) : (term440 _29415) = (term413 _29415).
Proof. exact (eq_refl (term440 _29415)). Qed.
Lemma lem2402525 (_29416 : int) (h1 : term389) : term441 _29416.
Proof. exact (@lem2402477 h1 _29416). Qed.
Lemma lem2402526 (_29416 : int) : (term441 _29416) = (term387 _29416).
Proof. exact (eq_refl (term441 _29416)). Qed.
Lemma lem2402528 (_29417 : int) (h1 : term374) : term442 _29417.
Proof. exact (@lem2402513 h1 _29417). Qed.
Lemma lem2402529 (_29417 : int) : (term442 _29417) = (term437 _29417).
Proof. exact (eq_refl (term442 _29417)). Qed.
Lemma lem2402530 (_29417 : int) (h1 : term374) : term437 _29417.
Proof. exact (EQ_MP (@lem2402529 _29417) (@lem2402528 _29417 h1)). Qed.
Lemma lem2402531 (_29417 : int) (_29418 : int) (h1 : term374) : term443 _29417 _29418.
Proof. exact (@lem2402530 _29417 h1 _29418). Qed.
Lemma lem2402532 (_29417 : int) (_29418 : int) : (term443 _29417 _29418) = (term435 _29417 _29418).
Proof. exact (eq_refl (term443 _29417 _29418)). Qed.
Lemma lem2402533 (_29417 : int) (_29418 : int) (h1 : term374) : term435 _29417 _29418.
Proof. exact (EQ_MP (@lem2402532 _29417 _29418) (@lem2402531 _29417 _29418 h1)). Qed.
Lemma lem2402534 (_29417 : int) (_29418 : int) (h1 : term374) : term431 _29417 _29418.
Proof. exact (proj2 (@lem2402533 _29417 _29418 h1)). Qed.
Lemma lem2402543 (_29415 : int) (h1 : term363) : term413 _29415.
Proof. exact (EQ_MP (@lem2402523 _29415) (@lem2402522 _29415 h1)). Qed.
Lemma lem2402549 (x : int) (n : int) (h1 : term396 x n) : term444 x n.
Proof. exact (proj2 (@lem2402455 x n h1)). Qed.
Lemma lem2402567 (_29417 : int) (_29418 : int) (h1 : term374) : term445 _29417 _29418.
Proof. exact (proj2 (@lem2402534 _29417 _29418 h1)). Qed.
Lemma lem2402587 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem2402588 (_29423 : int) (_29425 : int) (h1 : _29423 = _29425) : _29423 = _29425.
Proof. exact (h1). Qed.
Lemma lem2402589 (_29424 : int) (_29426 : int) (h1 : _29424 = _29426) : _29424 = _29426.
Proof. exact (h1). Qed.
Lemma lem2402590 (_29423 : int) (_29425 : int) (h1 : _29423 = _29425) : (int_lt _29423) = (int_lt _29425).
Proof. exact (MK_COMB (@lem2402587) (@lem2402588 _29423 _29425 h1)). Qed.
Lemma lem2402591 (_29423 : int) (_29425 : int) (_29424 : int) (_29426 : int) (h1 : _29423 = _29425) (h2 : _29424 = _29426) : (int_lt _29423 _29424) = (int_lt _29425 _29426).
Proof. exact (MK_COMB (@lem2402590 _29423 _29425 h1) (@lem2402589 _29424 _29426 h2)). Qed.
Lemma lem2402593 (b : Prop) (a : Prop) : term446 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem2402594 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : term447 _29425 _29426 _29423 _29424.
Proof. exact (@lem2402593 (int_lt _29425 _29426) (int_lt _29423 _29424)). Qed.
Lemma lem2402595 (_29423 : int) (_29425 : int) (_29424 : int) (_29426 : int) (h1 : _29423 = _29425) (h2 : _29424 = _29426) : term448 _29425 _29426 _29423 _29424.
Proof. exact (@lem2402594 _29425 _29426 _29423 _29424 (@lem2402591 _29423 _29425 _29424 _29426 h1 h2)). Qed.
Lemma lem2402596 (_29426 : int) (_29424 : int) (_29423 : int) (_29425 : int) (h1 : _29423 = _29425) : term449 _29425 _29426 _29423 _29424.
Proof. exact (fun h0 : _29424 = _29426 => @lem2402595 _29423 _29425 _29424 _29426 h1 h0). Qed.
Lemma lem2402598 (a : Prop) (b : Prop) : (a -> b) = (term450 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2402599 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term449 _29425 _29426 _29423 _29424) = (term451 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402598 (_29424 = _29426) (term448 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402600 (_29426 : int) (_29424 : int) (_29423 : int) (_29425 : int) (h1 : _29423 = _29425) : term451 _29425 _29426 _29423 _29424.
Proof. exact (EQ_MP (@lem2402599 _29425 _29426 _29423 _29424) (@lem2402596 _29426 _29424 _29423 _29425 h1)). Qed.
Lemma lem2402601 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : term452 _29425 _29426 _29423 _29424.
Proof. exact (fun h0 : _29423 = _29425 => @lem2402600 _29426 _29424 _29423 _29425 h0). Qed.
Lemma lem2402603 (a : Prop) (b : Prop) : (a -> b) = (term450 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2402604 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term452 _29425 _29426 _29423 _29424) = (term453 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402603 (_29423 = _29425) (term451 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402605 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : term453 _29425 _29426 _29423 _29424.
Proof. exact (EQ_MP (@lem2402604 _29425 _29426 _29423 _29424) (@lem2402601 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402695 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2402696 (x : int) (n : int) : (rem x n) = (rem x n).
Proof. exact (@lem2402695 (rem x n)). Qed.
Lemma lem2402697 (x : int) (n : int) : term454 x n.
Proof. exact (fun h0 : term455 x n => @lem2402696 x n). Qed.
Lemma lem2402699 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2402700 (x : int) (n : int) : (term454 x n) = ((rem x n) = (rem x n)).
Proof. exact (@lem2402699 ((rem x n) = (rem x n))). Qed.
Lemma lem2402701 (x : int) (n : int) : (rem x n) = (rem x n).
Proof. exact (EQ_MP (@lem2402700 x n) (@lem2402697 x n)). Qed.
Lemma lem2402703 (x : int) (n : int) (h1 : term396 x n) : term4 n.
Proof. exact (proj1 (@lem2402455 x n h1)). Qed.
Lemma lem2402704 (x : int) (n : int) (h1 : term396 x n) : term457 n.
Proof. exact (fun h0 : term458 n => @lem2402703 x n h1). Qed.
Lemma lem2402706 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2402707 (n : int) : (term457 n) = (term4 n).
Proof. exact (@lem2402706 (term4 n)). Qed.
Lemma lem2402708 (x : int) (n : int) (h1 : term396 x n) : term4 n.
Proof. exact (EQ_MP (@lem2402707 n) (@lem2402704 x n h1)). Qed.
Lemma lem2402714 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2402715 (_29415 : int) : (term413 _29415) = (term459 _29415).
Proof. exact (@lem2402714 ((int_abs _29415) = _29415) (term458 _29415)). Qed.
Lemma lem2402723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2402724 (_29415 : int) : (term460 _29415) = (term461 _29415).
Proof. exact (MK_COMB (@lem2402723) (@lem2402715 _29415)). Qed.
Lemma lem2402732 (_29415 : int) : (term459 _29415) = (term459 _29415).
Proof. exact (eq_refl (term459 _29415)). Qed.
Lemma lem2402733 (_29415 : int) : ((term413 _29415) = (term459 _29415)) = ((term459 _29415) = (term459 _29415)).
Proof. exact (MK_COMB (@lem2402724 _29415) (@lem2402732 _29415)). Qed.
Lemma lem2402735 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2402736 (x : Prop) : (x = x) = True.
Proof. exact (@lem2402735 Prop x). Qed.
Lemma lem2402737 (_29415 : int) : ((term459 _29415) = (term459 _29415)) = True.
Proof. exact (@lem2402736 (term459 _29415)). Qed.
Lemma lem2402738 (_29415 : int) : ((term413 _29415) = (term459 _29415)) = True.
Proof. exact (TRANS (@lem2402733 _29415) (@lem2402737 _29415)). Qed.
Lemma lem2402739 (_29415 : int) : True = ((term413 _29415) = (term459 _29415)).
Proof. exact (SYM (@lem2402738 _29415)). Qed.
Lemma lem2402740 (_29415 : int) : (term413 _29415) = (term459 _29415).
Proof. exact (EQ_MP (@lem2402739 _29415) (@lem0)). Qed.
Lemma lem2402741 (_29415 : int) (h1 : term363) : term459 _29415.
Proof. exact (EQ_MP (@lem2402740 _29415) (@lem2402543 _29415 h1)). Qed.
Lemma lem2402743 (b : Prop) (a : Prop) : (a \/ b) = (term462 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2402744 (_29415 : int) : (term459 _29415) = (term463 _29415).
Proof. exact (@lem2402743 (term458 _29415) ((int_abs _29415) = _29415)). Qed.
Lemma lem2402746 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2402747 (_29415 : int) : (term464 _29415) = (term4 _29415).
Proof. exact (@lem2402746 (term4 _29415)). Qed.
Lemma lem2402748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2402749 (_29415 : int) : (term465 _29415) = (term466 _29415).
Proof. exact (MK_COMB (@lem2402748) (@lem2402747 _29415)). Qed.
Lemma lem2402750 (_29415 : int) : ((int_abs _29415) = _29415) = ((int_abs _29415) = _29415).
Proof. exact (eq_refl ((int_abs _29415) = _29415)). Qed.
Lemma lem2402751 (_29415 : int) : (term463 _29415) = (term1 _29415).
Proof. exact (MK_COMB (@lem2402749 _29415) (@lem2402750 _29415)). Qed.
Lemma lem2402752 (_29415 : int) : (term459 _29415) = (term1 _29415).
Proof. exact (TRANS (@lem2402744 _29415) (@lem2402751 _29415)). Qed.
Lemma lem2402755 (_29415 : int) (h1 : term363) : term1 _29415.
Proof. exact (EQ_MP (@lem2402752 _29415) (@lem2402741 _29415 h1)). Qed.
Lemma lem2402756 (n : int) (h1 : term363) : term1 n.
Proof. exact (@lem2402755 n h1). Qed.
Lemma lem2402759 (x : int) (n : int) (h1 : term363) (h2 : term396 x n) : (int_abs n) = n.
Proof. exact (@lem2402756 n h1 (@lem2402708 x n h2)). Qed.
Lemma lem2402760 (x : int) (n : int) (h1 : term363) (h2 : term396 x n) : term467 n.
Proof. exact (fun h0 : term30 n => @lem2402759 x n h1 h2). Qed.
Lemma lem2402762 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2402763 (n : int) : (term467 n) = ((int_abs n) = n).
Proof. exact (@lem2402762 ((int_abs n) = n)). Qed.
Lemma lem2402764 (x : int) (n : int) (h1 : term363) (h2 : term396 x n) : (int_abs n) = n.
Proof. exact (EQ_MP (@lem2402763 n) (@lem2402760 x n h1 h2)). Qed.
Lemma lem2402766 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2402767 : term7 = term7.
Proof. exact (@lem2402766 term7). Qed.
Lemma lem2402768 : term468.
Proof. exact (fun h0 : term469 => @lem2402767). Qed.
Lemma lem2402770 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2402771 : term468 = (term7 = term7).
Proof. exact (@lem2402770 (term7 = term7)). Qed.
Lemma lem2402772 : term7 = term7.
Proof. exact (EQ_MP (@lem2402771) (@lem2402768)). Qed.
Lemma lem2402774 (_29416 : int) (h1 : term389) : term387 _29416.
Proof. exact (EQ_MP (@lem2402526 _29416) (@lem2402525 _29416 h1)). Qed.
Lemma lem2402775 (h1 : term389) : term470.
Proof. exact (@lem2402774 term7 h1). Qed.
Lemma lem2402776 (h1 : term389) : term471.
Proof. exact (fun h0 : term472 => @lem2402775 h1). Qed.
Lemma lem2402778 (p : Prop) : (term473 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2402779 : term471 = term470.
Proof. exact (@lem2402778 term472). Qed.
Lemma lem2402780 (h1 : term389) : term470.
Proof. exact (EQ_MP (@lem2402779) (@lem2402776 h1)). Qed.
Lemma lem2402782 (x : int) (n : int) (h1 : term396 x n) : term4 n.
Proof. exact (proj1 (@lem2402455 x n h1)). Qed.
Lemma lem2402783 (x : int) (n : int) (h1 : term396 x n) : term457 n.
Proof. exact (fun h0 : term458 n => @lem2402782 x n h1). Qed.
Lemma lem2402785 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2402786 (n : int) : (term457 n) = (term4 n).
Proof. exact (@lem2402785 (term4 n)). Qed.
Lemma lem2402787 (x : int) (n : int) (h1 : term396 x n) : term4 n.
Proof. exact (EQ_MP (@lem2402786 n) (@lem2402783 x n h1)). Qed.
Lemma lem2402805 (q : Prop) (p : Prop) (r : Prop) : (term474 p q r) = (term474 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2402806 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term451 _29425 _29426 _29423 _29424) = (term475 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402805 (int_lt _29425 _29426) (term28 _29424 _29426) (term476 _29423 _29424)). Qed.
Lemma lem2402824 (_29423 : int) (_29425 : int) : (term477 _29423 _29425) = (term477 _29423 _29425).
Proof. exact (eq_refl (term477 _29423 _29425)). Qed.
Lemma lem2402825 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term478 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2402824 _29423 _29425) (@lem2402806 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402829 (q : Prop) (p : Prop) (r : Prop) : (term474 p q r) = (term474 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2402830 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term478 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402829 (int_lt _29425 _29426) (term28 _29423 _29425) (term480 _29426 _29423 _29424)). Qed.
Lemma lem2402860 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2402825 _29425 _29426 _29423 _29424) (@lem2402830 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2402862 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term481 _29425 _29426 _29423 _29424) = (term482 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2402861) (@lem2402860 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402866 (q : Prop) (p : Prop) (r : Prop) : (term474 p q r) = (term474 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2402867 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term483 _29425 _29426 _29423 _29424) = (term453 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402866 (term28 _29423 _29425) (term28 _29424 _29426) (term448 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402883 (q : Prop) (p : Prop) (r : Prop) : (term474 p q r) = (term474 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2402884 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term451 _29425 _29426 _29423 _29424) = (term475 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402883 (int_lt _29425 _29426) (term28 _29424 _29426) (term476 _29423 _29424)). Qed.
Lemma lem2402902 (_29423 : int) (_29425 : int) : (term477 _29423 _29425) = (term477 _29423 _29425).
Proof. exact (eq_refl (term477 _29423 _29425)). Qed.
Lemma lem2402903 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term478 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2402902 _29423 _29425) (@lem2402884 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402907 (q : Prop) (p : Prop) (r : Prop) : (term474 p q r) = (term474 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2402908 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term478 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402907 (int_lt _29425 _29426) (term28 _29423 _29425) (term480 _29426 _29423 _29424)). Qed.
Lemma lem2402938 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2402903 _29425 _29426 _29423 _29424) (@lem2402908 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402939 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term483 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2402867 _29425 _29426 _29423 _29424) (@lem2402938 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402940 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : ((term453 _29425 _29426 _29423 _29424) = (term483 _29425 _29426 _29423 _29424)) = ((term479 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424)).
Proof. exact (MK_COMB (@lem2402862 _29425 _29426 _29423 _29424) (@lem2402939 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2402943 (x : Prop) : (x = x) = True.
Proof. exact (@lem2402942 Prop x). Qed.
Lemma lem2402944 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : ((term479 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424)) = True.
Proof. exact (@lem2402943 (term479 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402945 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : ((term453 _29425 _29426 _29423 _29424) = (term483 _29425 _29426 _29423 _29424)) = True.
Proof. exact (TRANS (@lem2402940 _29425 _29426 _29423 _29424) (@lem2402944 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402946 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : True = ((term453 _29425 _29426 _29423 _29424) = (term483 _29425 _29426 _29423 _29424)).
Proof. exact (SYM (@lem2402945 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402947 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term483 _29425 _29426 _29423 _29424).
Proof. exact (EQ_MP (@lem2402946 _29425 _29426 _29423 _29424) (@lem0)). Qed.
Lemma lem2402948 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : term483 _29425 _29426 _29423 _29424.
Proof. exact (EQ_MP (@lem2402947 _29425 _29426 _29423 _29424) (@lem2402605 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402950 (b : Prop) (a : Prop) : (a \/ b) = (term462 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2402951 (_29425 : int) (_29423 : int) (_29424 : int) (_29426 : int) : (term483 _29425 _29426 _29423 _29424) = (term484 _29425 _29423 _29424 _29426).
Proof. exact (@lem2402950 (term485 _29425 _29426 _29423 _29424) (term28 _29424 _29426)). Qed.
Lemma lem2402953 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2402954 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term488 _29425 _29426 _29423 _29424) = (term489 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402953 (term28 _29423 _29425) (term448 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402956 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2402957 (_29423 : int) (_29425 : int) : (term490 _29423 _29425) = (_29423 = _29425).
Proof. exact (@lem2402956 (_29423 = _29425)). Qed.
Lemma lem2402958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2402959 (_29423 : int) (_29425 : int) : (term491 _29423 _29425) = (term492 _29423 _29425).
Proof. exact (MK_COMB (@lem2402958) (@lem2402957 _29423 _29425)). Qed.
Lemma lem2402961 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2402962 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term493 _29425 _29426 _29423 _29424) = (term494 _29425 _29426 _29423 _29424).
Proof. exact (@lem2402961 (int_lt _29425 _29426) (term476 _29423 _29424)). Qed.
Lemma lem2402964 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2402965 (_29423 : int) (_29424 : int) : (term495 _29423 _29424) = (int_lt _29423 _29424).
Proof. exact (@lem2402964 (int_lt _29423 _29424)). Qed.
Lemma lem2402966 (_29425 : int) (_29426 : int) : (term496 _29425 _29426) = (term496 _29425 _29426).
Proof. exact (eq_refl (term496 _29425 _29426)). Qed.
Lemma lem2402967 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term494 _29425 _29426 _29423 _29424) = (term497 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2402966 _29425 _29426) (@lem2402965 _29423 _29424)). Qed.
Lemma lem2402968 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term493 _29425 _29426 _29423 _29424) = (term497 _29425 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2402962 _29425 _29426 _29423 _29424) (@lem2402967 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402969 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term489 _29425 _29426 _29423 _29424) = (term498 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2402959 _29423 _29425) (@lem2402968 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402970 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term488 _29425 _29426 _29423 _29424) = (term498 _29425 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2402954 _29425 _29426 _29423 _29424) (@lem2402969 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2402972 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term499 _29425 _29426 _29423 _29424) = (term500 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2402971) (@lem2402970 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402973 (_29424 : int) (_29426 : int) : (term28 _29424 _29426) = (term28 _29424 _29426).
Proof. exact (eq_refl (term28 _29424 _29426)). Qed.
Lemma lem2402974 (_29425 : int) (_29423 : int) (_29424 : int) (_29426 : int) : (term484 _29425 _29423 _29424 _29426) = (term501 _29425 _29423 _29424 _29426).
Proof. exact (MK_COMB (@lem2402972 _29425 _29426 _29423 _29424) (@lem2402973 _29424 _29426)). Qed.
Lemma lem2402975 (_29425 : int) (_29423 : int) (_29424 : int) (_29426 : int) : (term483 _29425 _29426 _29423 _29424) = (term501 _29425 _29423 _29424 _29426).
Proof. exact (TRANS (@lem2402951 _29425 _29423 _29424 _29426) (@lem2402974 _29425 _29423 _29424 _29426)). Qed.
Lemma lem2402977 (x : int) (n : int) (h1 : term389) (h2 : term396 x n) : term502 n.
Proof. exact (conj (@lem2402780 h1) (@lem2402787 x n h2)). Qed.
Lemma lem2402978 (x : int) (n : int) (h1 : term389) (h2 : term396 x n) : term503 n.
Proof. exact (conj (@lem2402772) (@lem2402977 x n h1 h2)). Qed.
Lemma lem2402980 (_29425 : int) (_29423 : int) (_29424 : int) (_29426 : int) : term501 _29425 _29423 _29424 _29426.
Proof. exact (EQ_MP (@lem2402975 _29425 _29423 _29424 _29426) (@lem2402948 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2402981 (n : int) : term504 n.
Proof. exact (@lem2402980 term7 term7 n term7). Qed.
Lemma lem2402984 (x : int) (n : int) (h1 : term389) (h2 : term396 x n) : term422 n.
Proof. exact (@lem2402981 n (@lem2402978 x n h1 h2)). Qed.
Lemma lem2402985 (x : int) (n : int) (h1 : term389) (h2 : term396 x n) : term505 n.
Proof. exact (fun h0 : n = term7 => @lem2402984 x n h1 h2). Qed.
Lemma lem2402987 (p : Prop) : (term473 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2402988 (n : int) : (term505 n) = (term422 n).
Proof. exact (@lem2402987 (n = term7)). Qed.
Lemma lem2402989 (x : int) (n : int) (h1 : term389) (h2 : term396 x n) : term422 n.
Proof. exact (EQ_MP (@lem2402988 n) (@lem2402985 x n h1 h2)). Qed.
Lemma lem2403002 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2403003 (_29417 : int) (_29418 : int) : (term506 _29417 _29418) = (term445 _29417 _29418).
Proof. exact (@lem2403002 (_29418 = term7) (term433 _29417 _29418)). Qed.
Lemma lem2403011 (_29417 : int) (_29418 : int) : (term507 _29417 _29418) = (term507 _29417 _29418).
Proof. exact (eq_refl (term507 _29417 _29418)). Qed.
Lemma lem2403012 (_29417 : int) (_29418 : int) : ((term445 _29417 _29418) = (term506 _29417 _29418)) = ((term445 _29417 _29418) = (term445 _29417 _29418)).
Proof. exact (MK_COMB (@lem2403011 _29417 _29418) (@lem2403003 _29417 _29418)). Qed.
Lemma lem2403014 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2403015 (x : Prop) : (x = x) = True.
Proof. exact (@lem2403014 Prop x). Qed.
Lemma lem2403016 (_29417 : int) (_29418 : int) : ((term445 _29417 _29418) = (term445 _29417 _29418)) = True.
Proof. exact (@lem2403015 (term445 _29417 _29418)). Qed.
Lemma lem2403017 (_29417 : int) (_29418 : int) : ((term445 _29417 _29418) = (term506 _29417 _29418)) = True.
Proof. exact (TRANS (@lem2403012 _29417 _29418) (@lem2403016 _29417 _29418)). Qed.
Lemma lem2403018 (_29417 : int) (_29418 : int) : True = ((term445 _29417 _29418) = (term506 _29417 _29418)).
Proof. exact (SYM (@lem2403017 _29417 _29418)). Qed.
Lemma lem2403019 (_29417 : int) (_29418 : int) : (term445 _29417 _29418) = (term506 _29417 _29418).
Proof. exact (EQ_MP (@lem2403018 _29417 _29418) (@lem0)). Qed.
Lemma lem2403020 (_29417 : int) (_29418 : int) (h1 : term374) : term506 _29417 _29418.
Proof. exact (EQ_MP (@lem2403019 _29417 _29418) (@lem2402567 _29417 _29418 h1)). Qed.
Lemma lem2403022 (b : Prop) (a : Prop) : (a \/ b) = (term462 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2403025 (_29417 : int) (_29418 : int) : (term506 _29417 _29418) = (term508 _29417 _29418).
Proof. exact (@lem2403022 (_29418 = term7) (term433 _29417 _29418)). Qed.
Lemma lem2403028 (_29417 : int) (_29418 : int) (h1 : term374) : term508 _29417 _29418.
Proof. exact (EQ_MP (@lem2403025 _29417 _29418) (@lem2403020 _29417 _29418 h1)). Qed.
Lemma lem2403029 (_29417 : int) (n : int) (h1 : term374) : term508 _29417 n.
Proof. exact (@lem2403028 _29417 n h1). Qed.
Lemma lem2403032 (_29417 : int) (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term396 x n) : term433 _29417 n.
Proof. exact (@lem2403029 _29417 n h1 (@lem2402989 x n h2 h3)). Qed.
Lemma lem2403033 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term396 x n) : term433 x n.
Proof. exact (@lem2403032 x x n h1 h2 h3). Qed.
Lemma lem2403034 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term396 x n) : term509 x n.
Proof. exact (fun h0 : term510 x n => @lem2403033 x n h1 h2 h3). Qed.
Lemma lem2403036 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2403037 (x : int) (n : int) : (term509 x n) = (term433 x n).
Proof. exact (@lem2403036 (term433 x n)). Qed.
Lemma lem2403038 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term396 x n) : term433 x n.
Proof. exact (EQ_MP (@lem2403037 x n) (@lem2403034 x n h1 h2 h3)). Qed.
Lemma lem2403056 (q : Prop) (p : Prop) (r : Prop) : (term474 p q r) = (term474 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2403057 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term451 _29425 _29426 _29423 _29424) = (term475 _29425 _29426 _29423 _29424).
Proof. exact (@lem2403056 (int_lt _29425 _29426) (term28 _29424 _29426) (term476 _29423 _29424)). Qed.
Lemma lem2403075 (_29423 : int) (_29425 : int) : (term477 _29423 _29425) = (term477 _29423 _29425).
Proof. exact (eq_refl (term477 _29423 _29425)). Qed.
Lemma lem2403076 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term478 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2403075 _29423 _29425) (@lem2403057 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403080 (q : Prop) (p : Prop) (r : Prop) : (term474 p q r) = (term474 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2403081 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term478 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (@lem2403080 (int_lt _29425 _29426) (term28 _29423 _29425) (term480 _29426 _29423 _29424)). Qed.
Lemma lem2403111 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2403076 _29425 _29426 _29423 _29424) (@lem2403081 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403113 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term481 _29425 _29426 _29423 _29424) = (term482 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2403112) (@lem2403111 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403143 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term479 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (eq_refl (term479 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403144 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : ((term453 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424)) = ((term479 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424)).
Proof. exact (MK_COMB (@lem2403113 _29425 _29426 _29423 _29424) (@lem2403143 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403146 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2403147 (x : Prop) : (x = x) = True.
Proof. exact (@lem2403146 Prop x). Qed.
Lemma lem2403148 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : ((term479 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424)) = True.
Proof. exact (@lem2403147 (term479 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403149 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : ((term453 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424)) = True.
Proof. exact (TRANS (@lem2403144 _29425 _29426 _29423 _29424) (@lem2403148 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403150 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : True = ((term453 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424)).
Proof. exact (SYM (@lem2403149 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403151 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term453 _29425 _29426 _29423 _29424) = (term479 _29425 _29426 _29423 _29424).
Proof. exact (EQ_MP (@lem2403150 _29425 _29426 _29423 _29424) (@lem0)). Qed.
Lemma lem2403152 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : term479 _29425 _29426 _29423 _29424.
Proof. exact (EQ_MP (@lem2403151 _29425 _29426 _29423 _29424) (@lem2402605 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403154 (b : Prop) (a : Prop) : (a \/ b) = (term462 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2403155 (_29423 : int) (_29424 : int) (_29425 : int) (_29426 : int) : (term479 _29425 _29426 _29423 _29424) = (term511 _29423 _29424 _29425 _29426).
Proof. exact (@lem2403154 (term512 _29425 _29426 _29423 _29424) (int_lt _29425 _29426)). Qed.
Lemma lem2403157 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2403158 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term513 _29425 _29426 _29423 _29424) = (term514 _29425 _29426 _29423 _29424).
Proof. exact (@lem2403157 (term28 _29423 _29425) (term480 _29426 _29423 _29424)). Qed.
Lemma lem2403160 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2403161 (_29423 : int) (_29425 : int) : (term490 _29423 _29425) = (_29423 = _29425).
Proof. exact (@lem2403160 (_29423 = _29425)). Qed.
Lemma lem2403162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403163 (_29423 : int) (_29425 : int) : (term491 _29423 _29425) = (term492 _29423 _29425).
Proof. exact (MK_COMB (@lem2403162) (@lem2403161 _29423 _29425)). Qed.
Lemma lem2403165 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2403166 (_29426 : int) (_29423 : int) (_29424 : int) : (term515 _29426 _29423 _29424) = (term516 _29426 _29423 _29424).
Proof. exact (@lem2403165 (term28 _29424 _29426) (term476 _29423 _29424)). Qed.
Lemma lem2403168 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2403169 (_29424 : int) (_29426 : int) : (term490 _29424 _29426) = (_29424 = _29426).
Proof. exact (@lem2403168 (_29424 = _29426)). Qed.
Lemma lem2403170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403171 (_29424 : int) (_29426 : int) : (term491 _29424 _29426) = (term492 _29424 _29426).
Proof. exact (MK_COMB (@lem2403170) (@lem2403169 _29424 _29426)). Qed.
Lemma lem2403173 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2403174 (_29423 : int) (_29424 : int) : (term495 _29423 _29424) = (int_lt _29423 _29424).
Proof. exact (@lem2403173 (int_lt _29423 _29424)). Qed.
Lemma lem2403175 (_29426 : int) (_29423 : int) (_29424 : int) : (term516 _29426 _29423 _29424) = (term517 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2403171 _29424 _29426) (@lem2403174 _29423 _29424)). Qed.
Lemma lem2403176 (_29426 : int) (_29423 : int) (_29424 : int) : (term515 _29426 _29423 _29424) = (term517 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2403166 _29426 _29423 _29424) (@lem2403175 _29426 _29423 _29424)). Qed.
Lemma lem2403177 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term514 _29425 _29426 _29423 _29424) = (term518 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2403163 _29423 _29425) (@lem2403176 _29426 _29423 _29424)). Qed.
Lemma lem2403178 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term513 _29425 _29426 _29423 _29424) = (term518 _29425 _29426 _29423 _29424).
Proof. exact (TRANS (@lem2403158 _29425 _29426 _29423 _29424) (@lem2403177 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2403180 (_29425 : int) (_29426 : int) (_29423 : int) (_29424 : int) : (term519 _29425 _29426 _29423 _29424) = (term520 _29425 _29426 _29423 _29424).
Proof. exact (MK_COMB (@lem2403179) (@lem2403178 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403181 (_29425 : int) (_29426 : int) : (int_lt _29425 _29426) = (int_lt _29425 _29426).
Proof. exact (eq_refl (int_lt _29425 _29426)). Qed.
Lemma lem2403182 (_29423 : int) (_29424 : int) (_29425 : int) (_29426 : int) : (term511 _29423 _29424 _29425 _29426) = (term521 _29423 _29424 _29425 _29426).
Proof. exact (MK_COMB (@lem2403180 _29425 _29426 _29423 _29424) (@lem2403181 _29425 _29426)). Qed.
Lemma lem2403183 (_29423 : int) (_29424 : int) (_29425 : int) (_29426 : int) : (term479 _29425 _29426 _29423 _29424) = (term521 _29423 _29424 _29425 _29426).
Proof. exact (TRANS (@lem2403155 _29423 _29424 _29425 _29426) (@lem2403182 _29423 _29424 _29425 _29426)). Qed.
Lemma lem2403185 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term522 x n.
Proof. exact (conj (@lem2402764 x n h3 h4) (@lem2403038 x n h1 h2 h4)). Qed.
Lemma lem2403186 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term523 x n.
Proof. exact (conj (@lem2402701 x n) (@lem2403185 x n h1 h2 h3 h4)). Qed.
Lemma lem2403188 (_29423 : int) (_29424 : int) (_29425 : int) (_29426 : int) : term521 _29423 _29424 _29425 _29426.
Proof. exact (EQ_MP (@lem2403183 _29423 _29424 _29425 _29426) (@lem2403152 _29425 _29426 _29423 _29424)). Qed.
Lemma lem2403189 (x : int) (n : int) : term524 x n.
Proof. exact (@lem2403188 (rem x n) (int_abs n) (rem x n) n). Qed.
Lemma lem2403192 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term397 x n.
Proof. exact (@lem2403189 x n (@lem2403186 x n h1 h2 h3 h4)). Qed.
Lemma lem2403193 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term525 x n.
Proof. exact (fun h0 : term444 x n => @lem2403192 x n h1 h2 h3 h4). Qed.
Lemma lem2403195 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2403196 (x : int) (n : int) : (term525 x n) = (term397 x n).
Proof. exact (@lem2403195 (term397 x n)). Qed.
Lemma lem2403197 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term397 x n.
Proof. exact (EQ_MP (@lem2403196 x n) (@lem2403193 x n h1 h2 h3 h4)). Qed.
Lemma lem2403200 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2403202 (x : int) (n : int) : (term444 x n) = (term526 x n).
Proof. exact (@lem2403200 (term397 x n)). Qed.
Lemma lem2403205 (x : int) (n : int) (h1 : term396 x n) : term526 x n.
Proof. exact (EQ_MP (@lem2403202 x n) (@lem2402549 x n h1)). Qed.
Lemma lem2403208 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : False.
Proof. exact (@lem2403205 x n h4 (@lem2403197 x n h1 h2 h3 h4)). Qed.
Lemma lem2403209 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term527.
Proof. exact (fun h0 : ~ False => @lem2403208 x n h1 h2 h3 h4). Qed.
Lemma lem2403211 (p : Prop) : (term456 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2403212 : term527 = False.
Proof. exact (@lem2403211 False). Qed.
Lemma lem2403213 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem2403212) (@lem2403209 x n h1 h2 h3 h4)). Qed.
Lemma lem2403214 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term389 = False.
Proof. exact (prop_ext (fun h5 : term389 => @lem2403213 x n h1 h2 h3 h4) (fun h5 : False => @lem2402477 h2)). Qed.
Lemma lem2403215 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem2403214 x n h1 h2 h3 h4) (@lem2402477 h2)). Qed.
Lemma lem2403216 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : (term396 x n) = False.
Proof. exact (prop_ext (fun h5 : term396 x n => @lem2403215 x n h1 h2 h3 h4) (fun h5 : False => @lem2402455 x n h4)). Qed.
Lemma lem2403217 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem2403216 x n h1 h2 h3 h4) (@lem2402455 x n h4)). Qed.
Lemma lem2403218 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : term389 = False.
Proof. exact (prop_ext (fun h5 : term389 => @lem2403217 x n h1 h2 h3 h4) (fun h5 : False => @lem2402361 h2)). Qed.
Lemma lem2403219 (x : int) (n : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term396 x n) : False.
Proof. exact (EQ_MP (@lem2403218 x n h1 h2 h3 h4) (@lem2402361 h2)). Qed.
Lemma lem2403220 (x : int) (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term406 x) : False.
Proof. exact (ex_elim (@lem2402324 x h4) (fun n : int => fun h0 : term405 x n => @lem2403219 x n h1 h2 h3 h0)). Qed.
Lemma lem2403221 (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term367) : False.
Proof. exact (ex_elim (@lem2402167 h4) (fun x : int => fun h0 : term411 x => @lem2403220 x h1 h2 h3 h0)). Qed.
Lemma lem2403222 (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term367) : term389 = False.
Proof. exact (prop_ext (fun h5 : term389 => @lem2403221 h1 h2 h3 h4) (fun h5 : False => @lem2402243 h2)). Qed.
Lemma lem2403223 (h1 : term374) (h2 : term389) (h3 : term363) (h4 : term367) : False.
Proof. exact (EQ_MP (@lem2403222 h1 h2 h3 h4) (@lem2402243 h2)). Qed.
Lemma lem2403224 (h1 : term389) (h2 : term363) (h3 : term367) : term372.
Proof. exact (fun h0 : term374 => @lem2403223 h0 h1 h2 h3). Qed.
Lemma lem2403225 : term372 = term373.
Proof. exact (@lem69 term374). Qed.
Lemma lem2403226 (h1 : term389) (h2 : term363) (h3 : term367) : term373.
Proof. exact (EQ_MP (@lem2403225) (@lem2403224 h1 h2 h3)). Qed.
Lemma lem2403227 (h1 : term363) (h2 : term367) : term377.
Proof. exact (fun h0 : term389 => @lem2403226 h0 h1 h2). Qed.
Lemma lem2403228 (h1 : term367) : term380.
Proof. exact (fun h0 : term363 => @lem2403227 h0 h1). Qed.
Lemma lem2403229 : term382.
Proof. exact (fun h0 : term367 => @lem2403228 h0). Qed.
Lemma lem2403230 : term368.
Proof. exact (EQ_MP (@lem2402079) (@lem2403229)). Qed.
Lemma lem2403232 : term368.
Proof. exact (@lem2401905 (@lem2403230)). Qed.
Lemma lem2403233 (h1 : term367) : term379.
Proof. exact (@lem2403232 (@lem2401890 h1)). Qed.
Lemma lem2403234 (h1 : term367) : term376.
Proof. exact (@lem2403233 h1 (@lem2401885)). Qed.
Lemma lem2403235 (h1 : term367) : term372.
Proof. exact (@lem2403234 h1 (@lem2304778)). Qed.
Lemma lem2403236 (h1 : term367) : False.
Proof. exact (@lem2403235 h1 (@lem2389435)). Qed.
Lemma lem2403237 (h1 : term367) : term367 = False.
Proof. exact (prop_ext (fun h2 : term367 => @lem2403236 h1) (fun h2 : False => @lem2401890 h1)). Qed.
Lemma lem2403238 (h1 : term367) : False.
Proof. exact (EQ_MP (@lem2403237 h1) (@lem2401890 h1)). Qed.
Lemma lem2403239 : term366.
Proof. exact (fun h0 : term367 => @lem2403238 h0). Qed.
Lemma lem2403240 : term365.
Proof. exact (EQ_MP (@lem2401889) (@lem2403239)). Qed.
