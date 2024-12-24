Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_LMUL_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483472_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1491201 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491202 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1491201 (term4 x)). Qed.
Lemma lem1491203 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (term7 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1491204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491206 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1491204) (@lem1491203 x y)). Qed.
Lemma lem1491207 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1491206 x y)). Qed.
Lemma lem1491208 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491209 (x : real) : (term3 x) = (term12 x).
Proof. exact (MK_COMB (@lem1491208) (@lem1491207 x)). Qed.
Lemma lem1491210 (x : real) : (term2 x) = (term12 x).
Proof. exact (TRANS (@lem1491202 x) (@lem1491209 x)). Qed.
Lemma lem1491211 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491212 : term13 = term14.
Proof. exact (@lem1491211 term15). Qed.
Lemma lem1491213 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1491214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491215 (x : real) : (term18 x) = (term2 x).
Proof. exact (MK_COMB (@lem1491214) (@lem1491213 x)). Qed.
Lemma lem1491216 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1491215 x) (@lem1491210 x)). Qed.
Lemma lem1491217 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1491216 x)). Qed.
Lemma lem1491218 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491219 : term14 = term21.
Proof. exact (MK_COMB (@lem1491218) (@lem1491217)). Qed.
Lemma lem1491221 : term13 = term21.
Proof. exact (TRANS (@lem1491212) (@lem1491219)). Qed.
Lemma lem1491224 (x : real) (y : real) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1491225 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1491224 x y)). Qed.
Lemma lem1491226 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491227 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1491226) (@lem1491225 x)). Qed.
Lemma lem1491228 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1491227 x)). Qed.
Lemma lem1491229 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491230 : term21 = term21.
Proof. exact (MK_COMB (@lem1491229) (@lem1491228)). Qed.
Lemma lem1491231 : term13 = term21.
Proof. exact (TRANS (@lem1491221) (@lem1491230)). Qed.
Lemma lem1491232 (x : real) (y : real) : (term9 x y) = (term22 x y).
Proof. exact (@lem1483554 (term6 x y) (term7 x y)). Qed.
Lemma lem1491233 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1491240 (x : real) : (real_neg x) = (term23 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1491241 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491242 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1491241) (@lem1491240 x)). Qed.
Lemma lem1491243 (x : real) (y : real) : (term7 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1491242 x) (@lem1491233 y)). Qed.
Lemma lem1491248 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483472 term28 x y). Qed.
Lemma lem1491249 (x : real) (y : real) : (term7 x y) = (term27 x y).
Proof. exact (TRANS (@lem1491243 x y) (@lem1491248 x y)). Qed.
Lemma lem1491262 (x : real) (y : real) : (term6 x y) = (term27 x y).
Proof. exact (@lem1483512 (real_mul x y)). Qed.
Lemma lem1491263 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1491264 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1491263) (@lem1491262 x y)). Qed.
Lemma lem1491265 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1491264 x y) (@lem1491249 x y)). Qed.
Lemma lem1491266 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (@lem1483519 (term27 x y) (term27 x y)). Qed.
Lemma lem1491267 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (@lem1483476 term28 term28 (real_mul x y)). Qed.
Lemma lem1491269 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1491270 : term38 = term39.
Proof. exact (@lem1491269 term40 term40). Qed.
Lemma lem1491271 : (term41 = (BIT1 0)) = (term42 = term40).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1491272 : term42 = term40.
Proof. exact (EQ_MP (@lem1491271) (@lem940073)). Qed.
Lemma lem1491273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1491274 : term39 = term43.
Proof. exact (MK_COMB (@lem1491273) (@lem1491272)). Qed.
Lemma lem1491275 : term38 = term43.
Proof. exact (TRANS (@lem1491270) (@lem1491274)). Qed.
Lemma lem1491276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491277 : term44 = term45.
Proof. exact (MK_COMB (@lem1491276) (@lem1491275)). Qed.
Lemma lem1491278 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1491279 (x : real) (y : real) : (term35 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1491277) (@lem1491278 x y)). Qed.
Lemma lem1491280 (x : real) (y : real) : (term34 x y) = (term46 x y).
Proof. exact (TRANS (@lem1491267 x y) (@lem1491279 x y)). Qed.
Lemma lem1491281 (x : real) (y : real) : (term46 x y) = (real_mul x y).
Proof. exact (@lem1483436 (real_mul x y)). Qed.
Lemma lem1491282 (x : real) (y : real) : (term34 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1491280 x y) (@lem1491281 x y)). Qed.
Lemma lem1491283 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1491284 (x : real) (y : real) : (term33 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1491283 x y) (@lem1491282 x y)). Qed.
Lemma lem1491285 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (@lem1483440 term28 (real_mul x y)). Qed.
Lemma lem1491287 (m : nat) : (term50 m) = term51.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491288 : term52 = term51.
Proof. exact (@lem1491287 term40). Qed.
Lemma lem1491289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491290 : term53 = term54.
Proof. exact (MK_COMB (@lem1491289) (@lem1491288)). Qed.
Lemma lem1491291 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1491292 (x : real) (y : real) : (term49 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1491290) (@lem1491291 x y)). Qed.
Lemma lem1491293 (x : real) (y : real) : (term48 x y) = (term55 x y).
Proof. exact (TRANS (@lem1491285 x y) (@lem1491292 x y)). Qed.
Lemma lem1491294 (x : real) (y : real) : (term55 x y) = term51.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1491295 (x : real) (y : real) : (term48 x y) = term51.
Proof. exact (TRANS (@lem1491293 x y) (@lem1491294 x y)). Qed.
Lemma lem1491296 (x : real) (y : real) : (term33 x y) = term51.
Proof. exact (TRANS (@lem1491284 x y) (@lem1491295 x y)). Qed.
Lemma lem1491297 (x : real) (y : real) : (term32 x y) = term51.
Proof. exact (TRANS (@lem1491266 x y) (@lem1491296 x y)). Qed.
Lemma lem1491298 (x : real) (y : real) : (term31 x y) = term51.
Proof. exact (TRANS (@lem1491265 x y) (@lem1491297 x y)). Qed.
Lemma lem1491299 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1491300 (x : real) (y : real) : (term56 x y) = term57.
Proof. exact (MK_COMB (@lem1491299) (@lem1491298 x y)). Qed.
Lemma lem1491301 : term57 = term58.
Proof. exact (@lem1483512 term51). Qed.
Lemma lem1491303 (x : nat) : (term59 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1491304 : term58 = term51.
Proof. exact (@lem1491303 term40). Qed.
Lemma lem1491305 : term57 = term51.
Proof. exact (TRANS (@lem1491301) (@lem1491304)). Qed.
Lemma lem1491306 (x : real) (y : real) : (term60 x y) = (term60 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1491307 (x : real) (y : real) : ((term56 x y) = term57) = ((term56 x y) = term51).
Proof. exact (MK_COMB (@lem1491306 x y) (@lem1491305)). Qed.
Lemma lem1491308 (x : real) (y : real) : (term56 x y) = term51.
Proof. exact (EQ_MP (@lem1491307 x y) (@lem1491300 x y)). Qed.
Lemma lem1491309 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491310 (x : real) (y : real) : (term61 x y) = term62.
Proof. exact (MK_COMB (@lem1491309) (@lem1491308 x y)). Qed.
Lemma lem1491311 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1491312 (x : real) (y : real) : (term63 x y) = term64.
Proof. exact (MK_COMB (@lem1491310 x y) (@lem1491311)). Qed.
Lemma lem1491313 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491314 (x : real) (y : real) : (term65 x y) = term62.
Proof. exact (MK_COMB (@lem1491313) (@lem1491298 x y)). Qed.
Lemma lem1491315 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1491316 (x : real) (y : real) : (term66 x y) = term64.
Proof. exact (MK_COMB (@lem1491314 x y) (@lem1491315)). Qed.
Lemma lem1491317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491318 (x : real) (y : real) : (term67 x y) = term68.
Proof. exact (MK_COMB (@lem1491317) (@lem1491316 x y)). Qed.
Lemma lem1491319 (x : real) (y : real) : (term22 x y) = term69.
Proof. exact (MK_COMB (@lem1491318 x y) (@lem1491312 x y)). Qed.
Lemma lem1491320 (x : real) (y : real) : (term9 x y) = term69.
Proof. exact (TRANS (@lem1491232 x y) (@lem1491319 x y)). Qed.
Lemma lem1491321 (x : real) : (term11 x) = term70.
Proof. exact (fun_ext (fun y : real => @lem1491320 x y)). Qed.
Lemma lem1491322 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491323 (x : real) : (term12 x) = term71.
Proof. exact (MK_COMB (@lem1491322) (@lem1491321 x)). Qed.
Lemma lem1491324 : term20 = term72.
Proof. exact (fun_ext (fun x : real => @lem1491323 x)). Qed.
Lemma lem1491325 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491326 : term21 = term73.
Proof. exact (MK_COMB (@lem1491325) (@lem1491324)). Qed.
Lemma lem1491327 : term13 = term73.
Proof. exact (TRANS (@lem1491231) (@lem1491326)). Qed.
Lemma lem1491329 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491330 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1491329 real t). Qed.
Lemma lem1491331 : term73 = term71.
Proof. exact (@lem1491330 term71). Qed.
Lemma lem1491333 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1491334 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1491333 real P Q). Qed.
Lemma lem1491335 : term80 = term81.
Proof. exact (@lem1491334 term82 term82). Qed.
Lemma lem1491336 (y : real) : (term83 y) = term64.
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1491337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491338 (y : real) : (term84 y) = term68.
Proof. exact (MK_COMB (@lem1491337) (@lem1491336 y)). Qed.
Lemma lem1491339 (y : real) : (term83 y) = term64.
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1491340 (y : real) : (term85 y) = term69.
Proof. exact (MK_COMB (@lem1491338 y) (@lem1491339 y)). Qed.
Lemma lem1491341 : term86 = term70.
Proof. exact (fun_ext (fun y : real => @lem1491340 y)). Qed.
Lemma lem1491342 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491343 : term80 = term71.
Proof. exact (MK_COMB (@lem1491342) (@lem1491341)). Qed.
Lemma lem1491344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1491345 : term87 = term88.
Proof. exact (MK_COMB (@lem1491344) (@lem1491343)). Qed.
Lemma lem1491346 (y : real) : (term83 y) = term64.
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1491347 : term89 = term82.
Proof. exact (fun_ext (fun y : real => @lem1491346 y)). Qed.
Lemma lem1491348 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491349 : term90 = term91.
Proof. exact (MK_COMB (@lem1491348) (@lem1491347)). Qed.
Lemma lem1491350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491351 : term92 = term93.
Proof. exact (MK_COMB (@lem1491350) (@lem1491349)). Qed.
Lemma lem1491352 (y : real) : (term83 y) = term64.
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1491353 : term89 = term82.
Proof. exact (fun_ext (fun y : real => @lem1491352 y)). Qed.
Lemma lem1491354 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491355 : term90 = term91.
Proof. exact (MK_COMB (@lem1491354) (@lem1491353)). Qed.
Lemma lem1491356 : term81 = term94.
Proof. exact (MK_COMB (@lem1491351) (@lem1491355)). Qed.
Lemma lem1491357 : (term80 = term81) = (term71 = term94).
Proof. exact (MK_COMB (@lem1491345) (@lem1491356)). Qed.
Lemma lem1491358 : term71 = term94.
Proof. exact (EQ_MP (@lem1491357) (@lem1491335)). Qed.
Lemma lem1491359 : term73 = term94.
Proof. exact (TRANS (@lem1491331) (@lem1491358)). Qed.
Lemma lem1491361 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491362 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1491361 real t). Qed.
Lemma lem1491363 : term91 = term64.
Proof. exact (@lem1491362 term64). Qed.
Lemma lem1491364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1491365 : term93 = term68.
Proof. exact (MK_COMB (@lem1491364) (@lem1491363)). Qed.
Lemma lem1491367 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1491368 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1491367 real t). Qed.
Lemma lem1491369 : term91 = term64.
Proof. exact (@lem1491368 term64). Qed.
Lemma lem1491370 : term94 = term69.
Proof. exact (MK_COMB (@lem1491365) (@lem1491369)). Qed.
Lemma lem1491373 : term73 = term69.
Proof. exact (TRANS (@lem1491359) (@lem1491370)). Qed.
Lemma lem1491382 : term13 = term69.
Proof. exact (TRANS (@lem1491327) (@lem1491373)). Qed.
Lemma lem1491392 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1491393 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem1491395 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491396 : term64 = term96.
Proof. exact (@lem1491395 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491397 : term96 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491398 : term64 = False.
Proof. exact (TRANS (@lem1491396) (@lem1491397)). Qed.
Lemma lem1491399 (h1 : term64) : False.
Proof. exact (EQ_MP (@lem1491398) (@lem1491393 h1)). Qed.
Lemma lem1491400 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem1491402 (n : nat) (m : nat) : (term95 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491403 : term64 = term96.
Proof. exact (@lem1491402 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491404 : term96 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491405 : term64 = False.
Proof. exact (TRANS (@lem1491403) (@lem1491404)). Qed.
Lemma lem1491406 (h1 : term64) : False.
Proof. exact (EQ_MP (@lem1491405) (@lem1491400 h1)). Qed.
Lemma lem1491407 (h1 : term69) : False.
Proof. exact (or_elim (@lem1491392 h1) (fun h0 : term64 => @lem1491399 h0) (fun h0 : term64 => @lem1491406 h0)). Qed.
Lemma lem1491409 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1491410 (h1 : term69) : term69 = False.
Proof. exact (prop_ext (fun h2 : term69 => @lem1491407 h1) (fun h2 : False => @lem1491409 h1)). Qed.
Lemma lem1491411 (h1 : term69) : False.
Proof. exact (EQ_MP (@lem1491410 h1) (@lem1491409 h1)). Qed.
Lemma lem1491412 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1491413 (h1 : term13) : term69.
Proof. exact (EQ_MP (@lem1491382) (@lem1491412 h1)). Qed.
Lemma lem1491414 (h1 : term13) : term69 = False.
Proof. exact (prop_ext (fun h2 : term69 => @lem1491411 h2) (fun h2 : False => @lem1491413 h1)). Qed.
Lemma lem1491415 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1491414 h1) (@lem1491413 h1)). Qed.
Lemma lem1491416 : term97.
Proof. exact (fun h0 : term13 => @lem1491415 h0). Qed.
Lemma lem1491417 : term98.
Proof. exact (@lem1386578 term99). Qed.
Lemma lem1491418 : term99.
Proof. exact (@lem1491417 (@lem1491416)). Qed.
