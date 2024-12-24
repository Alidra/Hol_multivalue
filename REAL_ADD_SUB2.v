Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ADD_SUB2_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1523212 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1523213 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1523212 (term4 x)). Qed.
Lemma lem1523214 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (real_neg y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1523215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1523217 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1523215) (@lem1523214 x y)). Qed.
Lemma lem1523218 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1523217 x y)). Qed.
Lemma lem1523219 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523220 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1523219) (@lem1523218 x)). Qed.
Lemma lem1523221 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1523213 x) (@lem1523220 x)). Qed.
Lemma lem1523222 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1523223 : term12 = term13.
Proof. exact (@lem1523222 term14). Qed.
Lemma lem1523224 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1523225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1523226 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1523225) (@lem1523224 x)). Qed.
Lemma lem1523227 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1523226 x) (@lem1523221 x)). Qed.
Lemma lem1523228 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1523227 x)). Qed.
Lemma lem1523229 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523230 : term13 = term20.
Proof. exact (MK_COMB (@lem1523229) (@lem1523228)). Qed.
Lemma lem1523232 : term12 = term20.
Proof. exact (TRANS (@lem1523223) (@lem1523230)). Qed.
Lemma lem1523235 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1523236 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1523235 x y)). Qed.
Lemma lem1523237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523238 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1523237) (@lem1523236 x)). Qed.
Lemma lem1523239 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1523238 x)). Qed.
Lemma lem1523240 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523241 : term20 = term20.
Proof. exact (MK_COMB (@lem1523240) (@lem1523239)). Qed.
Lemma lem1523242 : term12 = term20.
Proof. exact (TRANS (@lem1523232) (@lem1523241)). Qed.
Lemma lem1523243 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (term6 x y) (real_neg y)). Qed.
Lemma lem1523250 (y : real) : (real_neg y) = (term22 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1523262 (x : real) (y : real) : (term6 x y) = (term23 x y).
Proof. exact (@lem1483519 x (real_add x y)). Qed.
Lemma lem1523269 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1483508 x term26 y). Qed.
Lemma lem1523270 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1523271 (x : real) (y : real) : (term23 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1523270 x) (@lem1523269 x y)). Qed.
Lemma lem1523272 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (@lem1483490 x (term22 x) (term22 y)). Qed.
Lemma lem1523273 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483442 term26 x). Qed.
Lemma lem1523275 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1523276 : term33 = term32.
Proof. exact (@lem1523275 term34). Qed.
Lemma lem1523277 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523278 : term35 = term36.
Proof. exact (MK_COMB (@lem1523277) (@lem1523276)). Qed.
Lemma lem1523279 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1523280 (x : real) : (term30 x) = (term37 x).
Proof. exact (MK_COMB (@lem1523278) (@lem1523279 x)). Qed.
Lemma lem1523281 (x : real) : (term29 x) = (term37 x).
Proof. exact (TRANS (@lem1523273 x) (@lem1523280 x)). Qed.
Lemma lem1523282 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1523283 (x : real) : (term29 x) = term32.
Proof. exact (TRANS (@lem1523281 x) (@lem1523282 x)). Qed.
Lemma lem1523284 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1523285 (x : real) : (term38 x) = term39.
Proof. exact (MK_COMB (@lem1523284) (@lem1523283 x)). Qed.
Lemma lem1523286 (y : real) : (term22 y) = (term22 y).
Proof. exact (eq_refl (term22 y)). Qed.
Lemma lem1523287 (x : real) (y : real) : (term28 x y) = (term40 y).
Proof. exact (MK_COMB (@lem1523285 x) (@lem1523286 y)). Qed.
Lemma lem1523288 (x : real) (y : real) : (term27 x y) = (term40 y).
Proof. exact (TRANS (@lem1523272 x y) (@lem1523287 x y)). Qed.
Lemma lem1523289 (y : real) : (term40 y) = (term22 y).
Proof. exact (@lem1483448 (term22 y)). Qed.
Lemma lem1523290 (x : real) (y : real) : (term27 x y) = (term22 y).
Proof. exact (TRANS (@lem1523288 x y) (@lem1523289 y)). Qed.
Lemma lem1523291 (x : real) (y : real) : (term23 x y) = (term22 y).
Proof. exact (TRANS (@lem1523271 x y) (@lem1523290 x y)). Qed.
Lemma lem1523293 (x : real) (y : real) : (term6 x y) = (term22 y).
Proof. exact (TRANS (@lem1523262 x y) (@lem1523291 x y)). Qed.
Lemma lem1523294 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1523295 (x : real) (y : real) : (term41 x y) = (term42 y).
Proof. exact (MK_COMB (@lem1523294) (@lem1523293 x y)). Qed.
Lemma lem1523296 (x : real) (y : real) : (term43 x y) = (term44 y).
Proof. exact (MK_COMB (@lem1523295 x y) (@lem1523250 y)). Qed.
Lemma lem1523297 (y : real) : (term44 y) = (term45 y).
Proof. exact (@lem1483519 (term22 y) (term22 y)). Qed.
Lemma lem1523298 (y : real) : (term46 y) = (term47 y).
Proof. exact (@lem1483476 term26 term26 y). Qed.
Lemma lem1523300 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1523301 : term50 = term51.
Proof. exact (@lem1523300 term34 term34). Qed.
Lemma lem1523302 : (term52 = (BIT1 0)) = (term53 = term34).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1523303 : term53 = term34.
Proof. exact (EQ_MP (@lem1523302) (@lem940073)). Qed.
Lemma lem1523304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1523305 : term51 = term54.
Proof. exact (MK_COMB (@lem1523304) (@lem1523303)). Qed.
Lemma lem1523306 : term50 = term54.
Proof. exact (TRANS (@lem1523301) (@lem1523305)). Qed.
Lemma lem1523307 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523308 : term55 = term56.
Proof. exact (MK_COMB (@lem1523307) (@lem1523306)). Qed.
Lemma lem1523309 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523310 (y : real) : (term47 y) = (term57 y).
Proof. exact (MK_COMB (@lem1523308) (@lem1523309 y)). Qed.
Lemma lem1523311 (y : real) : (term46 y) = (term57 y).
Proof. exact (TRANS (@lem1523298 y) (@lem1523310 y)). Qed.
Lemma lem1523312 (y : real) : (term57 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1523313 (y : real) : (term46 y) = y.
Proof. exact (TRANS (@lem1523311 y) (@lem1523312 y)). Qed.
Lemma lem1523314 (y : real) : (term58 y) = (term58 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem1523315 (y : real) : (term45 y) = (term59 y).
Proof. exact (MK_COMB (@lem1523314 y) (@lem1523313 y)). Qed.
Lemma lem1523316 (y : real) : (term59 y) = (term30 y).
Proof. exact (@lem1483440 term26 y). Qed.
Lemma lem1523318 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1523319 : term33 = term32.
Proof. exact (@lem1523318 term34). Qed.
Lemma lem1523320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523321 : term35 = term36.
Proof. exact (MK_COMB (@lem1523320) (@lem1523319)). Qed.
Lemma lem1523322 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523323 (y : real) : (term30 y) = (term37 y).
Proof. exact (MK_COMB (@lem1523321) (@lem1523322 y)). Qed.
Lemma lem1523324 (y : real) : (term59 y) = (term37 y).
Proof. exact (TRANS (@lem1523316 y) (@lem1523323 y)). Qed.
Lemma lem1523325 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1523326 (y : real) : (term59 y) = term32.
Proof. exact (TRANS (@lem1523324 y) (@lem1523325 y)). Qed.
Lemma lem1523327 (y : real) : (term45 y) = term32.
Proof. exact (TRANS (@lem1523315 y) (@lem1523326 y)). Qed.
Lemma lem1523328 (y : real) : (term44 y) = term32.
Proof. exact (TRANS (@lem1523297 y) (@lem1523327 y)). Qed.
Lemma lem1523329 (x : real) (y : real) : (term43 x y) = term32.
Proof. exact (TRANS (@lem1523296 x y) (@lem1523328 y)). Qed.
Lemma lem1523330 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1523331 (x : real) (y : real) : (term60 x y) = term61.
Proof. exact (MK_COMB (@lem1523330) (@lem1523329 x y)). Qed.
Lemma lem1523332 : term61 = term62.
Proof. exact (@lem1483512 term32). Qed.
Lemma lem1523334 (x : nat) : (term63 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1523335 : term62 = term32.
Proof. exact (@lem1523334 term34). Qed.
Lemma lem1523336 : term61 = term32.
Proof. exact (TRANS (@lem1523332) (@lem1523335)). Qed.
Lemma lem1523337 (x : real) (y : real) : (term64 x y) = (term64 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem1523338 (x : real) (y : real) : ((term60 x y) = term61) = ((term60 x y) = term32).
Proof. exact (MK_COMB (@lem1523337 x y) (@lem1523336)). Qed.
Lemma lem1523339 (x : real) (y : real) : (term60 x y) = term32.
Proof. exact (EQ_MP (@lem1523338 x y) (@lem1523331 x y)). Qed.
Lemma lem1523340 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523341 (x : real) (y : real) : (term65 x y) = term66.
Proof. exact (MK_COMB (@lem1523340) (@lem1523339 x y)). Qed.
Lemma lem1523342 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1523343 (x : real) (y : real) : (term67 x y) = term68.
Proof. exact (MK_COMB (@lem1523341 x y) (@lem1523342)). Qed.
Lemma lem1523344 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523345 (x : real) (y : real) : (term69 x y) = term66.
Proof. exact (MK_COMB (@lem1523344) (@lem1523329 x y)). Qed.
Lemma lem1523346 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1523347 (x : real) (y : real) : (term70 x y) = term68.
Proof. exact (MK_COMB (@lem1523345 x y) (@lem1523346)). Qed.
Lemma lem1523348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523349 (x : real) (y : real) : (term71 x y) = term72.
Proof. exact (MK_COMB (@lem1523348) (@lem1523347 x y)). Qed.
Lemma lem1523350 (x : real) (y : real) : (term21 x y) = term73.
Proof. exact (MK_COMB (@lem1523349 x y) (@lem1523343 x y)). Qed.
Lemma lem1523351 (x : real) (y : real) : (term8 x y) = term73.
Proof. exact (TRANS (@lem1523243 x y) (@lem1523350 x y)). Qed.
Lemma lem1523352 (x : real) : (term10 x) = term74.
Proof. exact (fun_ext (fun y : real => @lem1523351 x y)). Qed.
Lemma lem1523353 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523354 (x : real) : (term11 x) = term75.
Proof. exact (MK_COMB (@lem1523353) (@lem1523352 x)). Qed.
Lemma lem1523355 : term19 = term76.
Proof. exact (fun_ext (fun x : real => @lem1523354 x)). Qed.
Lemma lem1523356 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523357 : term20 = term77.
Proof. exact (MK_COMB (@lem1523356) (@lem1523355)). Qed.
Lemma lem1523358 : term12 = term77.
Proof. exact (TRANS (@lem1523242) (@lem1523357)). Qed.
Lemma lem1523360 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1523361 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1523360 real t). Qed.
Lemma lem1523362 : term77 = term75.
Proof. exact (@lem1523361 term75). Qed.
Lemma lem1523364 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1523365 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1523364 real P Q). Qed.
Lemma lem1523366 : term84 = term85.
Proof. exact (@lem1523365 term86 term86). Qed.
Lemma lem1523367 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1523368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523369 (y : real) : (term88 y) = term72.
Proof. exact (MK_COMB (@lem1523368) (@lem1523367 y)). Qed.
Lemma lem1523370 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1523371 (y : real) : (term89 y) = term73.
Proof. exact (MK_COMB (@lem1523369 y) (@lem1523370 y)). Qed.
Lemma lem1523372 : term90 = term74.
Proof. exact (fun_ext (fun y : real => @lem1523371 y)). Qed.
Lemma lem1523373 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523374 : term84 = term75.
Proof. exact (MK_COMB (@lem1523373) (@lem1523372)). Qed.
Lemma lem1523375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1523376 : term91 = term92.
Proof. exact (MK_COMB (@lem1523375) (@lem1523374)). Qed.
Lemma lem1523377 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1523378 : term93 = term86.
Proof. exact (fun_ext (fun y : real => @lem1523377 y)). Qed.
Lemma lem1523379 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523380 : term94 = term95.
Proof. exact (MK_COMB (@lem1523379) (@lem1523378)). Qed.
Lemma lem1523381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523382 : term96 = term97.
Proof. exact (MK_COMB (@lem1523381) (@lem1523380)). Qed.
Lemma lem1523383 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1523384 : term93 = term86.
Proof. exact (fun_ext (fun y : real => @lem1523383 y)). Qed.
Lemma lem1523385 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523386 : term94 = term95.
Proof. exact (MK_COMB (@lem1523385) (@lem1523384)). Qed.
Lemma lem1523387 : term85 = term98.
Proof. exact (MK_COMB (@lem1523382) (@lem1523386)). Qed.
Lemma lem1523388 : (term84 = term85) = (term75 = term98).
Proof. exact (MK_COMB (@lem1523376) (@lem1523387)). Qed.
Lemma lem1523389 : term75 = term98.
Proof. exact (EQ_MP (@lem1523388) (@lem1523366)). Qed.
Lemma lem1523390 : term77 = term98.
Proof. exact (TRANS (@lem1523362) (@lem1523389)). Qed.
Lemma lem1523392 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1523393 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1523392 real t). Qed.
Lemma lem1523394 : term95 = term68.
Proof. exact (@lem1523393 term68). Qed.
Lemma lem1523395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523396 : term97 = term72.
Proof. exact (MK_COMB (@lem1523395) (@lem1523394)). Qed.
Lemma lem1523398 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1523399 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1523398 real t). Qed.
Lemma lem1523400 : term95 = term68.
Proof. exact (@lem1523399 term68). Qed.
Lemma lem1523401 : term98 = term73.
Proof. exact (MK_COMB (@lem1523396) (@lem1523400)). Qed.
Lemma lem1523404 : term77 = term73.
Proof. exact (TRANS (@lem1523390) (@lem1523401)). Qed.
Lemma lem1523413 : term12 = term73.
Proof. exact (TRANS (@lem1523358) (@lem1523404)). Qed.
Lemma lem1523423 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1523424 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem1523426 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523427 : term68 = term100.
Proof. exact (@lem1523426 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1523428 : term100 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1523429 : term68 = False.
Proof. exact (TRANS (@lem1523427) (@lem1523428)). Qed.
Lemma lem1523430 (h1 : term68) : False.
Proof. exact (EQ_MP (@lem1523429) (@lem1523424 h1)). Qed.
Lemma lem1523431 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem1523433 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523434 : term68 = term100.
Proof. exact (@lem1523433 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1523435 : term100 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1523436 : term68 = False.
Proof. exact (TRANS (@lem1523434) (@lem1523435)). Qed.
Lemma lem1523437 (h1 : term68) : False.
Proof. exact (EQ_MP (@lem1523436) (@lem1523431 h1)). Qed.
Lemma lem1523438 (h1 : term73) : False.
Proof. exact (or_elim (@lem1523423 h1) (fun h0 : term68 => @lem1523430 h0) (fun h0 : term68 => @lem1523437 h0)). Qed.
Lemma lem1523440 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1523441 (h1 : term73) : term73 = False.
Proof. exact (prop_ext (fun h2 : term73 => @lem1523438 h1) (fun h2 : False => @lem1523440 h1)). Qed.
Lemma lem1523442 (h1 : term73) : False.
Proof. exact (EQ_MP (@lem1523441 h1) (@lem1523440 h1)). Qed.
Lemma lem1523443 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1523444 (h1 : term12) : term73.
Proof. exact (EQ_MP (@lem1523413) (@lem1523443 h1)). Qed.
Lemma lem1523445 (h1 : term12) : term73 = False.
Proof. exact (prop_ext (fun h2 : term73 => @lem1523442 h2) (fun h2 : False => @lem1523444 h1)). Qed.
Lemma lem1523446 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1523445 h1) (@lem1523444 h1)). Qed.
Lemma lem1523447 : term101.
Proof. exact (fun h0 : term12 => @lem1523446 h0). Qed.
Lemma lem1523448 : term102.
Proof. exact (@lem1386578 term103). Qed.
Lemma lem1523449 : term103.
Proof. exact (@lem1523448 (@lem1523447)). Qed.
