Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_IMP_NE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483529_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1509145 (x : real) (y : real) : (term0 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem1509147 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1509148 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (MK_COMB (@lem1509147 x y) (@lem1509145 x y)). Qed.
Lemma lem1509149 (x : real) (y : real) : (term4 x y) = (term2 x y).
Proof. exact (@lem17362 (real_lt x y) (term5 x y)). Qed.
Lemma lem1509150 (x : real) (y : real) : (term4 x y) = (term3 x y).
Proof. exact (TRANS (@lem1509149 x y) (@lem1509148 x y)). Qed.
Lemma lem1509151 (P : real -> Prop) : (term6 P) = (term7 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1509152 (x : real) : (term8 x) = (term9 x).
Proof. exact (@lem1509151 (term10 x)). Qed.
Lemma lem1509153 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1509154 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1509155 (x : real) (y : real) : (term13 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1509154) (@lem1509153 x y)). Qed.
Lemma lem1509156 (x : real) (y : real) : (term13 x y) = (term3 x y).
Proof. exact (TRANS (@lem1509155 x y) (@lem1509150 x y)). Qed.
Lemma lem1509157 (x : real) : (term14 x) = (term15 x).
Proof. exact (fun_ext (fun y : real => @lem1509156 x y)). Qed.
Lemma lem1509158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509159 (x : real) : (term9 x) = (term16 x).
Proof. exact (MK_COMB (@lem1509158) (@lem1509157 x)). Qed.
Lemma lem1509160 (x : real) : (term8 x) = (term16 x).
Proof. exact (TRANS (@lem1509152 x) (@lem1509159 x)). Qed.
Lemma lem1509161 (P : real -> Prop) : (term6 P) = (term7 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1509162 : term17 = term18.
Proof. exact (@lem1509161 term19). Qed.
Lemma lem1509163 (x : real) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1509164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1509165 (x : real) : (term22 x) = (term8 x).
Proof. exact (MK_COMB (@lem1509164) (@lem1509163 x)). Qed.
Lemma lem1509166 (x : real) : (term22 x) = (term16 x).
Proof. exact (TRANS (@lem1509165 x) (@lem1509160 x)). Qed.
Lemma lem1509167 : term23 = term24.
Proof. exact (fun_ext (fun x : real => @lem1509166 x)). Qed.
Lemma lem1509168 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509169 : term18 = term25.
Proof. exact (MK_COMB (@lem1509168) (@lem1509167)). Qed.
Lemma lem1509171 : term17 = term25.
Proof. exact (TRANS (@lem1509162) (@lem1509169)). Qed.
Lemma lem1509176 (x : real) (y : real) : (term3 x y) = (term3 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1509177 (x : real) : (term15 x) = (term15 x).
Proof. exact (fun_ext (fun y : real => @lem1509176 x y)). Qed.
Lemma lem1509178 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509179 (x : real) : (term16 x) = (term16 x).
Proof. exact (MK_COMB (@lem1509178) (@lem1509177 x)). Qed.
Lemma lem1509180 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1509179 x)). Qed.
Lemma lem1509181 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509182 : term25 = term25.
Proof. exact (MK_COMB (@lem1509181) (@lem1509180)). Qed.
Lemma lem1509183 : term17 = term25.
Proof. exact (TRANS (@lem1509171) (@lem1509182)). Qed.
Lemma lem1509184 (y : real) (x : real) : (real_lt x y) = (term26 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1509190 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1509195 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1509197 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1509190 y x) (@lem1509195 x y)). Qed.
Lemma lem1509198 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509199 (x : real) (y : real) : (term30 y x) = (term31 x y).
Proof. exact (MK_COMB (@lem1509198) (@lem1509197 x y)). Qed.
Lemma lem1509200 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509201 (x : real) (y : real) : (term26 y x) = (term33 x y).
Proof. exact (MK_COMB (@lem1509199 x y) (@lem1509200)). Qed.
Lemma lem1509202 (x : real) (y : real) : (real_lt x y) = (term33 x y).
Proof. exact (TRANS (@lem1509184 y x) (@lem1509201 x y)). Qed.
Lemma lem1509203 (x : real) (y : real) : (x = y) = ((real_sub x y) = term32).
Proof. exact (@lem1483529 x y). Qed.
Lemma lem1509216 (x : real) (y : real) : (real_sub x y) = (term27 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1509217 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1509218 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1509217) (@lem1509216 x y)). Qed.
Lemma lem1509219 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509220 (x : real) (y : real) : ((real_sub x y) = term32) = ((term27 x y) = term32).
Proof. exact (MK_COMB (@lem1509218 x y) (@lem1509219)). Qed.
Lemma lem1509221 (x : real) (y : real) : (x = y) = ((term27 x y) = term32).
Proof. exact (TRANS (@lem1509203 x y) (@lem1509220 x y)). Qed.
Lemma lem1509222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1509223 (x : real) (y : real) : (term1 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1509222) (@lem1509202 x y)). Qed.
Lemma lem1509224 (x : real) (y : real) : (term3 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem1509223 x y) (@lem1509221 x y)). Qed.
Lemma lem1509225 (x : real) : (term15 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1509224 x y)). Qed.
Lemma lem1509226 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509227 (x : real) : (term16 x) = (term39 x).
Proof. exact (MK_COMB (@lem1509226) (@lem1509225 x)). Qed.
Lemma lem1509228 : term24 = term40.
Proof. exact (fun_ext (fun x : real => @lem1509227 x)). Qed.
Lemma lem1509229 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509230 : term25 = term41.
Proof. exact (MK_COMB (@lem1509229) (@lem1509228)). Qed.
Lemma lem1509289 : term17 = term41.
Proof. exact (TRANS (@lem1509183) (@lem1509230)). Qed.
Lemma lem1509296 (x : real) (y : real) : (term37 x y) = (term37 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1509297 (x : real) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1509296 x y)). Qed.
Lemma lem1509298 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509299 (x : real) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1509298) (@lem1509297 x)). Qed.
Lemma lem1509300 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1509299 x)). Qed.
Lemma lem1509301 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509302 : term41 = term41.
Proof. exact (MK_COMB (@lem1509301) (@lem1509300)). Qed.
Lemma lem1509303 : term17 = term41.
Proof. exact (TRANS (@lem1509289) (@lem1509302)). Qed.
Lemma lem1509307 (x : real) (y : real) (h1 : term37 x y) : term37 x y.
Proof. exact (h1). Qed.
Lemma lem1509308 (x : real) (y : real) (h1 : term37 x y) : (term27 x y) = term32.
Proof. exact (proj2 (@lem1509307 x y h1)). Qed.
Lemma lem1509309 (x : real) (y : real) (h1 : term37 x y) : term33 x y.
Proof. exact (proj1 (@lem1509307 x y h1)). Qed.
Lemma lem1509311 (n : nat) (m : nat) : (term42 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509312 : term43 = term44.
Proof. exact (@lem1509311 (NUMERAL 0) term45). Qed.
Lemma lem1509313 : term46 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1509314 (h1 : term46 = (BIT1 0)) : term44 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1509315 : (term46 = (BIT1 0)) = (term44 = True).
Proof. exact (prop_ext (fun h1 : term46 = (BIT1 0) => @lem1509314 h1) (fun h1 : term44 = True => @lem1509313)). Qed.
Lemma lem1509316 : term44 = True.
Proof. exact (EQ_MP (@lem1509315) (@lem1509313)). Qed.
Lemma lem1509317 : term43 = True.
Proof. exact (TRANS (@lem1509312) (@lem1509316)). Qed.
Lemma lem1509318 : True = term43.
Proof. exact (SYM (@lem1509317)). Qed.
Lemma lem1509319 : term43.
Proof. exact (EQ_MP (@lem1509318) (@lem0)). Qed.
Lemma lem1509320 (x : real) (y : real) (h1 : term37 x y) : term47 x y.
Proof. exact (conj (@lem1509319) (@lem1509309 x y h1)). Qed.
Lemma lem1509322 (x : real) (y : real) : term48 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1509323 (x : real) (y : real) : term49 x y.
Proof. exact (@lem1509322 term50 (term28 x y)). Qed.
Lemma lem1509324 (x : real) (y : real) (h1 : term37 x y) : term51 x y.
Proof. exact (@lem1509323 x y (@lem1509320 x y h1)). Qed.
Lemma lem1509325 (x : real) (y : real) : (term52 x y) = (term28 x y).
Proof. exact (@lem1483460 (term28 x y)). Qed.
Lemma lem1509326 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509327 (x : real) (y : real) : (term53 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1509326) (@lem1509325 x y)). Qed.
Lemma lem1509328 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509329 (x : real) (y : real) : (term51 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1509327 x y) (@lem1509328)). Qed.
Lemma lem1509330 (x : real) (y : real) (h1 : term37 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1509329 x y) (@lem1509324 x y h1)). Qed.
Lemma lem1509332 (y : real) : term54 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1509333 (x : real) (y : real) : term55 x y.
Proof. exact (@lem1509332 (term27 x y)). Qed.
Lemma lem1509334 (x : real) (y : real) (h1 : term37 x y) : term56 x y.
Proof. exact (@lem1509333 x y (@lem1509308 x y h1)). Qed.
Lemma lem1509335 (x : real) (y : real) (h1 : term37 x y) : term57 x y.
Proof. exact (@lem1509334 x y h1 term50). Qed.
Lemma lem1509336 (x : real) (y : real) : (term57 x y) = ((term58 x y) = term32).
Proof. exact (eq_refl (term57 x y)). Qed.
Lemma lem1509337 (x : real) (y : real) (h1 : term37 x y) : (term58 x y) = term32.
Proof. exact (EQ_MP (@lem1509336 x y) (@lem1509335 x y h1)). Qed.
Lemma lem1509338 (x : real) (y : real) : (term58 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1509339 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1509340 (x : real) (y : real) : (term59 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1509339) (@lem1509338 x y)). Qed.
Lemma lem1509341 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509342 (x : real) (y : real) : ((term58 x y) = term32) = ((term27 x y) = term32).
Proof. exact (MK_COMB (@lem1509340 x y) (@lem1509341)). Qed.
Lemma lem1509343 (x : real) (y : real) (h1 : term37 x y) : (term27 x y) = term32.
Proof. exact (EQ_MP (@lem1509342 x y) (@lem1509337 x y h1)). Qed.
Lemma lem1509344 (x : real) (y : real) (h1 : term37 x y) : term60 x y.
Proof. exact (conj (@lem1509343 x y h1) (@lem1509330 x y h1)). Qed.
Lemma lem1509346 (x : real) (y : real) : term61 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1509347 (x : real) (y : real) : term62 x y.
Proof. exact (@lem1509346 (term27 x y) (term28 x y)). Qed.
Lemma lem1509348 (x : real) (y : real) (h1 : term37 x y) : term63 x y.
Proof. exact (@lem1509347 x y (@lem1509344 x y h1)). Qed.
Lemma lem1509349 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (@lem1483480 x (term29 x) (term29 y) y). Qed.
Lemma lem1509350 (x : real) : (term66 x) = (term67 x).
Proof. exact (@lem1483442 term68 x). Qed.
Lemma lem1509352 (m : nat) : (term69 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1509353 : term70 = term32.
Proof. exact (@lem1509352 term45). Qed.
Lemma lem1509354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1509355 : term71 = term72.
Proof. exact (MK_COMB (@lem1509354) (@lem1509353)). Qed.
Lemma lem1509356 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1509357 (x : real) : (term67 x) = (term73 x).
Proof. exact (MK_COMB (@lem1509355) (@lem1509356 x)). Qed.
Lemma lem1509358 (x : real) : (term66 x) = (term73 x).
Proof. exact (TRANS (@lem1509350 x) (@lem1509357 x)). Qed.
Lemma lem1509359 (x : real) : (term73 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1509360 (x : real) : (term66 x) = term32.
Proof. exact (TRANS (@lem1509358 x) (@lem1509359 x)). Qed.
Lemma lem1509361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1509362 (x : real) : (term74 x) = term75.
Proof. exact (MK_COMB (@lem1509361) (@lem1509360 x)). Qed.
Lemma lem1509363 (y : real) : (term76 y) = (term67 y).
Proof. exact (@lem1483440 term68 y). Qed.
Lemma lem1509365 (m : nat) : (term69 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1509366 : term70 = term32.
Proof. exact (@lem1509365 term45). Qed.
Lemma lem1509367 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1509368 : term71 = term72.
Proof. exact (MK_COMB (@lem1509367) (@lem1509366)). Qed.
Lemma lem1509369 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1509370 (y : real) : (term67 y) = (term73 y).
Proof. exact (MK_COMB (@lem1509368) (@lem1509369 y)). Qed.
Lemma lem1509371 (y : real) : (term76 y) = (term73 y).
Proof. exact (TRANS (@lem1509363 y) (@lem1509370 y)). Qed.
Lemma lem1509372 (y : real) : (term73 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1509373 (y : real) : (term76 y) = term32.
Proof. exact (TRANS (@lem1509371 y) (@lem1509372 y)). Qed.
Lemma lem1509374 (x : real) (y : real) : (term65 x y) = term77.
Proof. exact (MK_COMB (@lem1509362 x) (@lem1509373 y)). Qed.
Lemma lem1509375 (x : real) (y : real) : (term64 x y) = term77.
Proof. exact (TRANS (@lem1509349 x y) (@lem1509374 x y)). Qed.
Lemma lem1509376 : term77 = term32.
Proof. exact (@lem1483448 term32). Qed.
Lemma lem1509377 (x : real) (y : real) : (term64 x y) = term32.
Proof. exact (TRANS (@lem1509375 x y) (@lem1509376)). Qed.
Lemma lem1509378 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509379 (x : real) (y : real) : (term78 x y) = term79.
Proof. exact (MK_COMB (@lem1509378) (@lem1509377 x y)). Qed.
Lemma lem1509380 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509381 (x : real) (y : real) : (term63 x y) = term80.
Proof. exact (MK_COMB (@lem1509379 x y) (@lem1509380)). Qed.
Lemma lem1509382 (x : real) (y : real) (h1 : term37 x y) : term80.
Proof. exact (EQ_MP (@lem1509381 x y) (@lem1509348 x y h1)). Qed.
Lemma lem1509384 (n : nat) (m : nat) : (term42 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509385 : term80 = term81.
Proof. exact (@lem1509384 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1509386 : term81 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1509387 : term80 = False.
Proof. exact (TRANS (@lem1509385) (@lem1509386)). Qed.
Lemma lem1509388 (x : real) (y : real) (h1 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1509387) (@lem1509382 x y h1)). Qed.
Lemma lem1509390 (x : real) (y : real) (h1 : term37 x y) : term37 x y.
Proof. exact (h1). Qed.
Lemma lem1509391 (x : real) (y : real) (h1 : term37 x y) : (term37 x y) = False.
Proof. exact (prop_ext (fun h2 : term37 x y => @lem1509388 x y h1) (fun h2 : False => @lem1509390 x y h1)). Qed.
Lemma lem1509392 (x : real) (y : real) (h1 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1509391 x y h1) (@lem1509390 x y h1)). Qed.
Lemma lem1509393 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1509394 (x : real) (h1 : term39 x) : False.
Proof. exact (ex_elim (@lem1509393 x h1) (fun y : real => fun h0 : term38 x y => @lem1509392 x y h0)). Qed.
Lemma lem1509395 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1509396 (h1 : term41) : False.
Proof. exact (ex_elim (@lem1509395 h1) (fun x : real => fun h0 : term40 x => @lem1509394 x h0)). Qed.
Lemma lem1509397 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1509398 (h1 : term17) : term41.
Proof. exact (EQ_MP (@lem1509303) (@lem1509397 h1)). Qed.
Lemma lem1509399 (h1 : term17) : term41 = False.
Proof. exact (prop_ext (fun h2 : term41 => @lem1509396 h2) (fun h2 : False => @lem1509398 h1)). Qed.
Lemma lem1509400 (h1 : term17) : False.
Proof. exact (EQ_MP (@lem1509399 h1) (@lem1509398 h1)). Qed.
Lemma lem1509401 : term82.
Proof. exact (fun h0 : term17 => @lem1509400 h0). Qed.
Lemma lem1509402 : term83.
Proof. exact (@lem1386578 term84). Qed.
Lemma lem1509403 : term84.
Proof. exact (@lem1509402 (@lem1509401)). Qed.
