Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LNEG_UNIQ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1489188 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17646 ((real_add x y) = term2) (x = (real_neg y))). Qed.
Lemma lem1489189 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1489190 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1489189 (term7 x)). Qed.
Lemma lem1489191 (x : real) (y : real) : (term8 x y) = (((real_add x y) = term2) = (x = (real_neg y))).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1489192 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1489193 (x : real) (y : real) : (term9 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1489192) (@lem1489191 x y)). Qed.
Lemma lem1489194 (x : real) (y : real) : (term9 x y) = (term1 x y).
Proof. exact (TRANS (@lem1489193 x y) (@lem1489188 x y)). Qed.
Lemma lem1489195 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1489194 x y)). Qed.
Lemma lem1489196 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489197 (x : real) : (term6 x) = (term12 x).
Proof. exact (MK_COMB (@lem1489196) (@lem1489195 x)). Qed.
Lemma lem1489198 (x : real) : (term5 x) = (term12 x).
Proof. exact (TRANS (@lem1489190 x) (@lem1489197 x)). Qed.
Lemma lem1489199 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1489200 : term13 = term14.
Proof. exact (@lem1489199 term15). Qed.
Lemma lem1489201 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1489202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1489203 (x : real) : (term18 x) = (term5 x).
Proof. exact (MK_COMB (@lem1489202) (@lem1489201 x)). Qed.
Lemma lem1489204 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1489203 x) (@lem1489198 x)). Qed.
Lemma lem1489205 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1489204 x)). Qed.
Lemma lem1489206 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489207 : term14 = term21.
Proof. exact (MK_COMB (@lem1489206) (@lem1489205)). Qed.
Lemma lem1489209 : term13 = term21.
Proof. exact (TRANS (@lem1489200) (@lem1489207)). Qed.
Lemma lem1489226 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1489227 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1489226 x y)). Qed.
Lemma lem1489228 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489229 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1489228) (@lem1489227 x)). Qed.
Lemma lem1489230 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1489229 x)). Qed.
Lemma lem1489231 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489232 : term21 = term21.
Proof. exact (MK_COMB (@lem1489231) (@lem1489230)). Qed.
Lemma lem1489233 : term13 = term21.
Proof. exact (TRANS (@lem1489209) (@lem1489232)). Qed.
Lemma lem1489234 (x : real) (y : real) : ((real_add x y) = term2) = ((term22 x y) = term2).
Proof. exact (@lem1483529 (real_add x y) term2). Qed.
Lemma lem1489246 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (@lem1483519 (real_add x y) term2). Qed.
Lemma lem1489248 (x : nat) : (term24 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1489249 : term25 = term2.
Proof. exact (@lem1489248 term26). Qed.
Lemma lem1489250 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1489251 (x : real) (y : real) : (term23 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1489250 x y) (@lem1489249)). Qed.
Lemma lem1489252 (x : real) (y : real) : (term28 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1489253 (x : real) (y : real) : (term23 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489251 x y) (@lem1489252 x y)). Qed.
Lemma lem1489255 (x : real) (y : real) : (term22 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489246 x y) (@lem1489253 x y)). Qed.
Lemma lem1489256 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1489257 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1489256) (@lem1489255 x y)). Qed.
Lemma lem1489258 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489259 (x : real) (y : real) : ((term22 x y) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1489257 x y) (@lem1489258)). Qed.
Lemma lem1489260 (x : real) (y : real) : ((real_add x y) = term2) = ((real_add x y) = term2).
Proof. exact (TRANS (@lem1489234 x y) (@lem1489259 x y)). Qed.
Lemma lem1489261 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (@lem1483554 x (real_neg y)). Qed.
Lemma lem1489268 (y : real) : (real_neg y) = (term33 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1489271 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1489272 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1489271 x) (@lem1489268 y)). Qed.
Lemma lem1489273 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem1483519 x (term33 y)). Qed.
Lemma lem1489274 (y : real) : (term37 y) = (term38 y).
Proof. exact (@lem1483476 term39 term39 y). Qed.
Lemma lem1489276 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1489277 : term42 = term43.
Proof. exact (@lem1489276 term26 term26). Qed.
Lemma lem1489278 : (term44 = (BIT1 0)) = (term45 = term26).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1489279 : term45 = term26.
Proof. exact (EQ_MP (@lem1489278) (@lem940073)). Qed.
Lemma lem1489280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1489281 : term43 = term46.
Proof. exact (MK_COMB (@lem1489280) (@lem1489279)). Qed.
Lemma lem1489282 : term42 = term46.
Proof. exact (TRANS (@lem1489277) (@lem1489281)). Qed.
Lemma lem1489283 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489284 : term47 = term48.
Proof. exact (MK_COMB (@lem1489283) (@lem1489282)). Qed.
Lemma lem1489285 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1489286 (y : real) : (term38 y) = (term49 y).
Proof. exact (MK_COMB (@lem1489284) (@lem1489285 y)). Qed.
Lemma lem1489287 (y : real) : (term37 y) = (term49 y).
Proof. exact (TRANS (@lem1489274 y) (@lem1489286 y)). Qed.
Lemma lem1489288 (y : real) : (term49 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1489289 (y : real) : (term37 y) = y.
Proof. exact (TRANS (@lem1489287 y) (@lem1489288 y)). Qed.
Lemma lem1489290 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1489293 (x : real) (y : real) : (term36 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1489290 x) (@lem1489289 y)). Qed.
Lemma lem1489294 (x : real) (y : real) : (term35 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489273 x y) (@lem1489293 x y)). Qed.
Lemma lem1489295 (x : real) (y : real) : (term34 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489272 x y) (@lem1489294 x y)). Qed.
Lemma lem1489296 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1489297 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1489296) (@lem1489295 x y)). Qed.
Lemma lem1489298 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1489305 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1489306 (x : real) (y : real) : (term51 x y) = (term53 x y).
Proof. exact (TRANS (@lem1489298 x y) (@lem1489305 x y)). Qed.
Lemma lem1489307 (x : real) (y : real) : (term54 x y) = (term54 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1489308 (x : real) (y : real) : ((term50 x y) = (term51 x y)) = ((term50 x y) = (term53 x y)).
Proof. exact (MK_COMB (@lem1489307 x y) (@lem1489306 x y)). Qed.
Lemma lem1489309 (x : real) (y : real) : (term50 x y) = (term53 x y).
Proof. exact (EQ_MP (@lem1489308 x y) (@lem1489297 x y)). Qed.
Lemma lem1489310 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489311 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1489310) (@lem1489309 x y)). Qed.
Lemma lem1489312 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489313 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1489311 x y) (@lem1489312)). Qed.
Lemma lem1489314 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489315 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1489314) (@lem1489295 x y)). Qed.
Lemma lem1489316 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489317 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1489315 x y) (@lem1489316)). Qed.
Lemma lem1489318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489319 (x : real) (y : real) : (term63 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1489318) (@lem1489317 x y)). Qed.
Lemma lem1489320 (x : real) (y : real) : (term32 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1489319 x y) (@lem1489313 x y)). Qed.
Lemma lem1489321 (x : real) (y : real) : (term31 x y) = (term65 x y).
Proof. exact (TRANS (@lem1489261 x y) (@lem1489320 x y)). Qed.
Lemma lem1489322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1489323 (x : real) (y : real) : (term66 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1489322) (@lem1489260 x y)). Qed.
Lemma lem1489324 (x : real) (y : real) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1489323 x y) (@lem1489321 x y)). Qed.
Lemma lem1489325 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (@lem1483554 (real_add x y) term2). Qed.
Lemma lem1489337 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (@lem1483519 (real_add x y) term2). Qed.
Lemma lem1489339 (x : nat) : (term24 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1489340 : term25 = term2.
Proof. exact (@lem1489339 term26). Qed.
Lemma lem1489341 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1489342 (x : real) (y : real) : (term23 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1489341 x y) (@lem1489340)). Qed.
Lemma lem1489343 (x : real) (y : real) : (term28 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1489344 (x : real) (y : real) : (term23 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489342 x y) (@lem1489343 x y)). Qed.
Lemma lem1489346 (x : real) (y : real) : (term22 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489337 x y) (@lem1489344 x y)). Qed.
Lemma lem1489347 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1489348 (x : real) (y : real) : (term71 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1489347) (@lem1489346 x y)). Qed.
Lemma lem1489349 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1489356 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1489357 (x : real) (y : real) : (term51 x y) = (term53 x y).
Proof. exact (TRANS (@lem1489349 x y) (@lem1489356 x y)). Qed.
Lemma lem1489358 (x : real) (y : real) : (term72 x y) = (term72 x y).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1489359 (x : real) (y : real) : ((term71 x y) = (term51 x y)) = ((term71 x y) = (term53 x y)).
Proof. exact (MK_COMB (@lem1489358 x y) (@lem1489357 x y)). Qed.
Lemma lem1489360 (x : real) (y : real) : (term71 x y) = (term53 x y).
Proof. exact (EQ_MP (@lem1489359 x y) (@lem1489348 x y)). Qed.
Lemma lem1489361 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489362 (x : real) (y : real) : (term73 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1489361) (@lem1489360 x y)). Qed.
Lemma lem1489363 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489364 (x : real) (y : real) : (term74 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1489362 x y) (@lem1489363)). Qed.
Lemma lem1489365 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489366 (x : real) (y : real) : (term75 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1489365) (@lem1489346 x y)). Qed.
Lemma lem1489367 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489368 (x : real) (y : real) : (term76 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1489366 x y) (@lem1489367)). Qed.
Lemma lem1489369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489370 (x : real) (y : real) : (term77 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1489369) (@lem1489368 x y)). Qed.
Lemma lem1489371 (x : real) (y : real) : (term70 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1489370 x y) (@lem1489364 x y)). Qed.
Lemma lem1489372 (x : real) (y : real) : (term69 x y) = (term65 x y).
Proof. exact (TRANS (@lem1489325 x y) (@lem1489371 x y)). Qed.
Lemma lem1489373 (x : real) (y : real) : (x = (real_neg y)) = ((term34 x y) = term2).
Proof. exact (@lem1483529 x (real_neg y)). Qed.
Lemma lem1489380 (y : real) : (real_neg y) = (term33 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1489383 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1489384 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1489383 x) (@lem1489380 y)). Qed.
Lemma lem1489385 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem1483519 x (term33 y)). Qed.
Lemma lem1489386 (y : real) : (term37 y) = (term38 y).
Proof. exact (@lem1483476 term39 term39 y). Qed.
Lemma lem1489388 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1489389 : term42 = term43.
Proof. exact (@lem1489388 term26 term26). Qed.
Lemma lem1489390 : (term44 = (BIT1 0)) = (term45 = term26).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1489391 : term45 = term26.
Proof. exact (EQ_MP (@lem1489390) (@lem940073)). Qed.
Lemma lem1489392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1489393 : term43 = term46.
Proof. exact (MK_COMB (@lem1489392) (@lem1489391)). Qed.
Lemma lem1489394 : term42 = term46.
Proof. exact (TRANS (@lem1489389) (@lem1489393)). Qed.
Lemma lem1489395 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489396 : term47 = term48.
Proof. exact (MK_COMB (@lem1489395) (@lem1489394)). Qed.
Lemma lem1489397 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1489398 (y : real) : (term38 y) = (term49 y).
Proof. exact (MK_COMB (@lem1489396) (@lem1489397 y)). Qed.
Lemma lem1489399 (y : real) : (term37 y) = (term49 y).
Proof. exact (TRANS (@lem1489386 y) (@lem1489398 y)). Qed.
Lemma lem1489400 (y : real) : (term49 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1489401 (y : real) : (term37 y) = y.
Proof. exact (TRANS (@lem1489399 y) (@lem1489400 y)). Qed.
Lemma lem1489402 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1489405 (x : real) (y : real) : (term36 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1489402 x) (@lem1489401 y)). Qed.
Lemma lem1489406 (x : real) (y : real) : (term35 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489385 x y) (@lem1489405 x y)). Qed.
Lemma lem1489407 (x : real) (y : real) : (term34 x y) = (real_add x y).
Proof. exact (TRANS (@lem1489384 x y) (@lem1489406 x y)). Qed.
Lemma lem1489408 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1489409 (x : real) (y : real) : (term78 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1489408) (@lem1489407 x y)). Qed.
Lemma lem1489410 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489411 (x : real) (y : real) : ((term34 x y) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1489409 x y) (@lem1489410)). Qed.
Lemma lem1489412 (x : real) (y : real) : (x = (real_neg y)) = ((real_add x y) = term2).
Proof. exact (TRANS (@lem1489373 x y) (@lem1489411 x y)). Qed.
Lemma lem1489413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1489414 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1489413) (@lem1489372 x y)). Qed.
Lemma lem1489415 (x : real) (y : real) : (term81 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1489414 x y) (@lem1489412 x y)). Qed.
Lemma lem1489416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489417 (x : real) (y : real) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1489416) (@lem1489324 x y)). Qed.
Lemma lem1489418 (x : real) (y : real) : (term1 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1489417 x y) (@lem1489415 x y)). Qed.
Lemma lem1489419 (x : real) : (term11 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1489418 x y)). Qed.
Lemma lem1489420 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489421 (x : real) : (term12 x) = (term87 x).
Proof. exact (MK_COMB (@lem1489420) (@lem1489419 x)). Qed.
Lemma lem1489422 : term20 = term88.
Proof. exact (fun_ext (fun x : real => @lem1489421 x)). Qed.
Lemma lem1489423 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489424 : term21 = term89.
Proof. exact (MK_COMB (@lem1489423) (@lem1489422)). Qed.
Lemma lem1489425 : term13 = term89.
Proof. exact (TRANS (@lem1489233) (@lem1489424)). Qed.
Lemma lem1489431 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1489432 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1489431 real P Q). Qed.
Lemma lem1489433 (x : real) : (term94 x) = (term95 x).
Proof. exact (@lem1489432 (term96 x) (term97 x)). Qed.
Lemma lem1489434 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1489435 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489436 (x : real) (y : real) : (term99 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1489435) (@lem1489434 x y)). Qed.
Lemma lem1489437 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1489438 (x : real) (y : real) : (term101 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1489436 x y) (@lem1489437 x y)). Qed.
Lemma lem1489439 (x : real) : (term102 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1489438 x y)). Qed.
Lemma lem1489440 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489441 (x : real) : (term94 x) = (term87 x).
Proof. exact (MK_COMB (@lem1489440) (@lem1489439 x)). Qed.
Lemma lem1489442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1489443 (x : real) : (term103 x) = (term104 x).
Proof. exact (MK_COMB (@lem1489442) (@lem1489441 x)). Qed.
Lemma lem1489444 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1489445 (x : real) : (term105 x) = (term96 x).
Proof. exact (fun_ext (fun y : real => @lem1489444 x y)). Qed.
Lemma lem1489446 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489447 (x : real) : (term106 x) = (term107 x).
Proof. exact (MK_COMB (@lem1489446) (@lem1489445 x)). Qed.
Lemma lem1489448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489449 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1489448) (@lem1489447 x)). Qed.
Lemma lem1489450 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1489451 (x : real) : (term110 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1489450 x y)). Qed.
Lemma lem1489452 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489453 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1489452) (@lem1489451 x)). Qed.
Lemma lem1489454 (x : real) : (term95 x) = (term113 x).
Proof. exact (MK_COMB (@lem1489449 x) (@lem1489453 x)). Qed.
Lemma lem1489455 (x : real) : ((term94 x) = (term95 x)) = ((term87 x) = (term113 x)).
Proof. exact (MK_COMB (@lem1489443 x) (@lem1489454 x)). Qed.
Lemma lem1489456 (x : real) : (term87 x) = (term113 x).
Proof. exact (EQ_MP (@lem1489455 x) (@lem1489433 x)). Qed.
Lemma lem1489553 : term88 = term114.
Proof. exact (fun_ext (fun x : real => @lem1489456 x)). Qed.
Lemma lem1489554 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489555 : term89 = term115.
Proof. exact (MK_COMB (@lem1489554) (@lem1489553)). Qed.
Lemma lem1489557 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1489558 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1489557 real P Q). Qed.
Lemma lem1489559 : term116 = term117.
Proof. exact (@lem1489558 term118 term119). Qed.
Lemma lem1489560 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1489561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489562 (x : real) : (term121 x) = (term109 x).
Proof. exact (MK_COMB (@lem1489561) (@lem1489560 x)). Qed.
Lemma lem1489563 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1489564 (x : real) : (term123 x) = (term113 x).
Proof. exact (MK_COMB (@lem1489562 x) (@lem1489563 x)). Qed.
Lemma lem1489565 : term124 = term114.
Proof. exact (fun_ext (fun x : real => @lem1489564 x)). Qed.
Lemma lem1489566 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489567 : term116 = term115.
Proof. exact (MK_COMB (@lem1489566) (@lem1489565)). Qed.
Lemma lem1489568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1489569 : term125 = term126.
Proof. exact (MK_COMB (@lem1489568) (@lem1489567)). Qed.
Lemma lem1489570 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1489571 : term127 = term118.
Proof. exact (fun_ext (fun x : real => @lem1489570 x)). Qed.
Lemma lem1489572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489573 : term128 = term129.
Proof. exact (MK_COMB (@lem1489572) (@lem1489571)). Qed.
Lemma lem1489574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489575 : term130 = term131.
Proof. exact (MK_COMB (@lem1489574) (@lem1489573)). Qed.
Lemma lem1489576 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1489577 : term132 = term119.
Proof. exact (fun_ext (fun x : real => @lem1489576 x)). Qed.
Lemma lem1489578 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489579 : term133 = term134.
Proof. exact (MK_COMB (@lem1489578) (@lem1489577)). Qed.
Lemma lem1489580 : term117 = term135.
Proof. exact (MK_COMB (@lem1489575) (@lem1489579)). Qed.
Lemma lem1489581 : (term116 = term117) = (term115 = term135).
Proof. exact (MK_COMB (@lem1489569) (@lem1489580)). Qed.
Lemma lem1489582 : term115 = term135.
Proof. exact (EQ_MP (@lem1489581) (@lem1489559)). Qed.
Lemma lem1489687 : term89 = term135.
Proof. exact (TRANS (@lem1489555) (@lem1489582)). Qed.
Lemma lem1489689 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1489690 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1489689 real P Q). Qed.
Lemma lem1489691 : term117 = term116.
Proof. exact (@lem1489690 term118 term119). Qed.
Lemma lem1489692 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1489693 : term127 = term118.
Proof. exact (fun_ext (fun x : real => @lem1489692 x)). Qed.
Lemma lem1489694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489695 : term128 = term129.
Proof. exact (MK_COMB (@lem1489694) (@lem1489693)). Qed.
Lemma lem1489696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489697 : term130 = term131.
Proof. exact (MK_COMB (@lem1489696) (@lem1489695)). Qed.
Lemma lem1489698 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1489699 : term132 = term119.
Proof. exact (fun_ext (fun x : real => @lem1489698 x)). Qed.
Lemma lem1489700 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489701 : term133 = term134.
Proof. exact (MK_COMB (@lem1489700) (@lem1489699)). Qed.
Lemma lem1489702 : term117 = term135.
Proof. exact (MK_COMB (@lem1489697) (@lem1489701)). Qed.
Lemma lem1489703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1489704 : term136 = term137.
Proof. exact (MK_COMB (@lem1489703) (@lem1489702)). Qed.
Lemma lem1489705 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1489706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489707 (x : real) : (term121 x) = (term109 x).
Proof. exact (MK_COMB (@lem1489706) (@lem1489705 x)). Qed.
Lemma lem1489708 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1489709 (x : real) : (term123 x) = (term113 x).
Proof. exact (MK_COMB (@lem1489707 x) (@lem1489708 x)). Qed.
Lemma lem1489710 : term124 = term114.
Proof. exact (fun_ext (fun x : real => @lem1489709 x)). Qed.
Lemma lem1489711 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489712 : term116 = term115.
Proof. exact (MK_COMB (@lem1489711) (@lem1489710)). Qed.
Lemma lem1489713 : (term117 = term116) = (term135 = term115).
Proof. exact (MK_COMB (@lem1489704) (@lem1489712)). Qed.
Lemma lem1489714 : term135 = term115.
Proof. exact (EQ_MP (@lem1489713) (@lem1489691)). Qed.
Lemma lem1489716 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1489717 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1489716 real P Q). Qed.
Lemma lem1489718 (x : real) : (term95 x) = (term94 x).
Proof. exact (@lem1489717 (term96 x) (term97 x)). Qed.
Lemma lem1489719 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1489720 (x : real) : (term105 x) = (term96 x).
Proof. exact (fun_ext (fun y : real => @lem1489719 x y)). Qed.
Lemma lem1489721 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489722 (x : real) : (term106 x) = (term107 x).
Proof. exact (MK_COMB (@lem1489721) (@lem1489720 x)). Qed.
Lemma lem1489723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489724 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1489723) (@lem1489722 x)). Qed.
Lemma lem1489725 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1489726 (x : real) : (term110 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1489725 x y)). Qed.
Lemma lem1489727 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489728 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1489727) (@lem1489726 x)). Qed.
Lemma lem1489729 (x : real) : (term95 x) = (term113 x).
Proof. exact (MK_COMB (@lem1489724 x) (@lem1489728 x)). Qed.
Lemma lem1489730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1489731 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1489730) (@lem1489729 x)). Qed.
Lemma lem1489732 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1489733 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489734 (x : real) (y : real) : (term99 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1489733) (@lem1489732 x y)). Qed.
Lemma lem1489735 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1489736 (x : real) (y : real) : (term101 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1489734 x y) (@lem1489735 x y)). Qed.
Lemma lem1489737 (x : real) : (term102 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1489736 x y)). Qed.
Lemma lem1489738 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489739 (x : real) : (term94 x) = (term87 x).
Proof. exact (MK_COMB (@lem1489738) (@lem1489737 x)). Qed.
Lemma lem1489740 (x : real) : ((term95 x) = (term94 x)) = ((term113 x) = (term87 x)).
Proof. exact (MK_COMB (@lem1489731 x) (@lem1489739 x)). Qed.
Lemma lem1489741 (x : real) : (term113 x) = (term87 x).
Proof. exact (EQ_MP (@lem1489740 x) (@lem1489718 x)). Qed.
Lemma lem1489742 : term114 = term88.
Proof. exact (fun_ext (fun x : real => @lem1489741 x)). Qed.
Lemma lem1489743 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489744 : term115 = term89.
Proof. exact (MK_COMB (@lem1489743) (@lem1489742)). Qed.
Lemma lem1489745 : term135 = term89.
Proof. exact (TRANS (@lem1489714) (@lem1489744)). Qed.
Lemma lem1489746 : term89 = term89.
Proof. exact (TRANS (@lem1489687) (@lem1489745)). Qed.
Lemma lem1489749 : term13 = term89.
Proof. exact (TRANS (@lem1489425) (@lem1489746)). Qed.
Lemma lem1489766 (x : real) (y : real) : (term82 x y) = (term140 x y).
Proof. exact (@lem19367 (term62 x y) (term58 x y) ((real_add x y) = term2)). Qed.
Lemma lem1489783 (x : real) (y : real) : (term68 x y) = (term141 x y).
Proof. exact (@lem19158 (term62 x y) ((real_add x y) = term2) (term58 x y)). Qed.
Lemma lem1489784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1489785 (x : real) (y : real) : (term84 x y) = (term142 x y).
Proof. exact (MK_COMB (@lem1489784) (@lem1489783 x y)). Qed.
Lemma lem1489786 (x : real) (y : real) : (term85 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1489785 x y) (@lem1489766 x y)). Qed.
Lemma lem1489787 (x : real) : (term86 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1489786 x y)). Qed.
Lemma lem1489788 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489789 (x : real) : (term87 x) = (term145 x).
Proof. exact (MK_COMB (@lem1489788) (@lem1489787 x)). Qed.
Lemma lem1489790 : term88 = term146.
Proof. exact (fun_ext (fun x : real => @lem1489789 x)). Qed.
Lemma lem1489791 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1489792 : term89 = term147.
Proof. exact (MK_COMB (@lem1489791) (@lem1489790)). Qed.
Lemma lem1489793 : term13 = term147.
Proof. exact (TRANS (@lem1489749) (@lem1489792)). Qed.
Lemma lem1489815 (x : real) (y : real) (h1 : term143 x y) : term143 x y.
Proof. exact (h1). Qed.
Lemma lem1489816 (x : real) (y : real) (h1 : term141 x y) : term141 x y.
Proof. exact (h1). Qed.
Lemma lem1489817 (x : real) (y : real) (h1 : term148 x y) : term148 x y.
Proof. exact (h1). Qed.
Lemma lem1489818 (x : real) (y : real) (h1 : term148 x y) : term62 x y.
Proof. exact (proj2 (@lem1489817 x y h1)). Qed.
Lemma lem1489819 (x : real) (y : real) (h1 : term148 x y) : (real_add x y) = term2.
Proof. exact (proj1 (@lem1489817 x y h1)). Qed.
Lemma lem1489821 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489822 : term150 = term151.
Proof. exact (@lem1489821 (NUMERAL 0) term26). Qed.
Lemma lem1489823 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1489824 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1489825 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1489824 h1) (fun h1 : term151 = True => @lem1489823)). Qed.
Lemma lem1489826 : term151 = True.
Proof. exact (EQ_MP (@lem1489825) (@lem1489823)). Qed.
Lemma lem1489827 : term150 = True.
Proof. exact (TRANS (@lem1489822) (@lem1489826)). Qed.
Lemma lem1489828 : True = term150.
Proof. exact (SYM (@lem1489827)). Qed.
Lemma lem1489829 : term150.
Proof. exact (EQ_MP (@lem1489828) (@lem0)). Qed.
Lemma lem1489830 (x : real) (y : real) (h1 : term148 x y) : term153 x y.
Proof. exact (conj (@lem1489829) (@lem1489818 x y h1)). Qed.
Lemma lem1489832 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1489833 (x : real) (y : real) : term155 x y.
Proof. exact (@lem1489832 term46 (real_add x y)). Qed.
Lemma lem1489834 (x : real) (y : real) (h1 : term148 x y) : term156 x y.
Proof. exact (@lem1489833 x y (@lem1489830 x y h1)). Qed.
Lemma lem1489835 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1489836 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489837 (x : real) (y : real) : (term158 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1489836) (@lem1489835 x y)). Qed.
Lemma lem1489838 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489839 (x : real) (y : real) : (term156 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1489837 x y) (@lem1489838)). Qed.
Lemma lem1489840 (x : real) (y : real) (h1 : term148 x y) : term62 x y.
Proof. exact (EQ_MP (@lem1489839 x y) (@lem1489834 x y h1)). Qed.
Lemma lem1489842 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1489843 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1489842 (real_add x y)). Qed.
Lemma lem1489844 (x : real) (y : real) (h1 : term148 x y) : term161 x y.
Proof. exact (@lem1489843 x y (@lem1489819 x y h1)). Qed.
Lemma lem1489845 (x : real) (y : real) (h1 : term148 x y) : term162 x y.
Proof. exact (@lem1489844 x y h1 term39). Qed.
Lemma lem1489846 (x : real) (y : real) : (term162 x y) = ((term52 x y) = term2).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem1489847 (x : real) (y : real) (h1 : term148 x y) : (term52 x y) = term2.
Proof. exact (EQ_MP (@lem1489846 x y) (@lem1489845 x y h1)). Qed.
Lemma lem1489854 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1489855 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1489856 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1489855) (@lem1489854 x y)). Qed.
Lemma lem1489857 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489858 (x : real) (y : real) : ((term52 x y) = term2) = ((term53 x y) = term2).
Proof. exact (MK_COMB (@lem1489856 x y) (@lem1489857)). Qed.
Lemma lem1489859 (x : real) (y : real) (h1 : term148 x y) : (term53 x y) = term2.
Proof. exact (EQ_MP (@lem1489858 x y) (@lem1489847 x y h1)). Qed.
Lemma lem1489860 (x : real) (y : real) (h1 : term148 x y) : term165 x y.
Proof. exact (conj (@lem1489859 x y h1) (@lem1489840 x y h1)). Qed.
Lemma lem1489862 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1489863 (x : real) (y : real) : term167 x y.
Proof. exact (@lem1489862 (term53 x y) (real_add x y)). Qed.
Lemma lem1489864 (x : real) (y : real) (h1 : term148 x y) : term168 x y.
Proof. exact (@lem1489863 x y (@lem1489860 x y h1)). Qed.
Lemma lem1489865 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (@lem1483480 (term33 x) x (term33 y) y). Qed.
Lemma lem1489866 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1489868 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1489869 : term174 = term2.
Proof. exact (@lem1489868 term26). Qed.
Lemma lem1489870 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489871 : term175 = term176.
Proof. exact (MK_COMB (@lem1489870) (@lem1489869)). Qed.
Lemma lem1489872 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1489873 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1489871) (@lem1489872 x)). Qed.
Lemma lem1489874 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1489866 x) (@lem1489873 x)). Qed.
Lemma lem1489875 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1489876 (x : real) : (term171 x) = term2.
Proof. exact (TRANS (@lem1489874 x) (@lem1489875 x)). Qed.
Lemma lem1489877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1489878 (x : real) : (term178 x) = term179.
Proof. exact (MK_COMB (@lem1489877) (@lem1489876 x)). Qed.
Lemma lem1489879 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1489881 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1489882 : term174 = term2.
Proof. exact (@lem1489881 term26). Qed.
Lemma lem1489883 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489884 : term175 = term176.
Proof. exact (MK_COMB (@lem1489883) (@lem1489882)). Qed.
Lemma lem1489885 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1489886 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1489884) (@lem1489885 y)). Qed.
Lemma lem1489887 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1489879 y) (@lem1489886 y)). Qed.
Lemma lem1489888 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1489889 (y : real) : (term171 y) = term2.
Proof. exact (TRANS (@lem1489887 y) (@lem1489888 y)). Qed.
Lemma lem1489890 (x : real) (y : real) : (term170 x y) = term180.
Proof. exact (MK_COMB (@lem1489878 x) (@lem1489889 y)). Qed.
Lemma lem1489891 (x : real) (y : real) : (term169 x y) = term180.
Proof. exact (TRANS (@lem1489865 x y) (@lem1489890 x y)). Qed.
Lemma lem1489892 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1489893 (x : real) (y : real) : (term169 x y) = term2.
Proof. exact (TRANS (@lem1489891 x y) (@lem1489892)). Qed.
Lemma lem1489894 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489895 (x : real) (y : real) : (term181 x y) = term182.
Proof. exact (MK_COMB (@lem1489894) (@lem1489893 x y)). Qed.
Lemma lem1489896 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489897 (x : real) (y : real) : (term168 x y) = term183.
Proof. exact (MK_COMB (@lem1489895 x y) (@lem1489896)). Qed.
Lemma lem1489898 (x : real) (y : real) (h1 : term148 x y) : term183.
Proof. exact (EQ_MP (@lem1489897 x y) (@lem1489864 x y h1)). Qed.
Lemma lem1489900 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489901 : term183 = term184.
Proof. exact (@lem1489900 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1489902 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1489903 : term183 = False.
Proof. exact (TRANS (@lem1489901) (@lem1489902)). Qed.
Lemma lem1489904 (x : real) (y : real) (h1 : term148 x y) : False.
Proof. exact (EQ_MP (@lem1489903) (@lem1489898 x y h1)). Qed.
Lemma lem1489905 (x : real) (y : real) (h1 : term185 x y) : term185 x y.
Proof. exact (h1). Qed.
Lemma lem1489906 (x : real) (y : real) (h1 : term185 x y) : term58 x y.
Proof. exact (proj2 (@lem1489905 x y h1)). Qed.
Lemma lem1489907 (x : real) (y : real) (h1 : term185 x y) : (real_add x y) = term2.
Proof. exact (proj1 (@lem1489905 x y h1)). Qed.
Lemma lem1489909 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489910 : term150 = term151.
Proof. exact (@lem1489909 (NUMERAL 0) term26). Qed.
Lemma lem1489911 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1489912 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1489913 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1489912 h1) (fun h1 : term151 = True => @lem1489911)). Qed.
Lemma lem1489914 : term151 = True.
Proof. exact (EQ_MP (@lem1489913) (@lem1489911)). Qed.
Lemma lem1489915 : term150 = True.
Proof. exact (TRANS (@lem1489910) (@lem1489914)). Qed.
Lemma lem1489916 : True = term150.
Proof. exact (SYM (@lem1489915)). Qed.
Lemma lem1489917 : term150.
Proof. exact (EQ_MP (@lem1489916) (@lem0)). Qed.
Lemma lem1489918 (x : real) (y : real) (h1 : term185 x y) : term186 x y.
Proof. exact (conj (@lem1489917) (@lem1489906 x y h1)). Qed.
Lemma lem1489920 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1489921 (x : real) (y : real) : term187 x y.
Proof. exact (@lem1489920 term46 (term53 x y)). Qed.
Lemma lem1489922 (x : real) (y : real) (h1 : term185 x y) : term188 x y.
Proof. exact (@lem1489921 x y (@lem1489918 x y h1)). Qed.
Lemma lem1489923 (x : real) (y : real) : (term189 x y) = (term53 x y).
Proof. exact (@lem1483460 (term53 x y)). Qed.
Lemma lem1489924 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489925 (x : real) (y : real) : (term190 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1489924) (@lem1489923 x y)). Qed.
Lemma lem1489926 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489927 (x : real) (y : real) : (term188 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1489925 x y) (@lem1489926)). Qed.
Lemma lem1489928 (x : real) (y : real) (h1 : term185 x y) : term58 x y.
Proof. exact (EQ_MP (@lem1489927 x y) (@lem1489922 x y h1)). Qed.
Lemma lem1489930 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1489931 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1489930 (real_add x y)). Qed.
Lemma lem1489932 (x : real) (y : real) (h1 : term185 x y) : term161 x y.
Proof. exact (@lem1489931 x y (@lem1489907 x y h1)). Qed.
Lemma lem1489933 (x : real) (y : real) (h1 : term185 x y) : term191 x y.
Proof. exact (@lem1489932 x y h1 term46). Qed.
Lemma lem1489934 (x : real) (y : real) : (term191 x y) = ((term157 x y) = term2).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1489935 (x : real) (y : real) (h1 : term185 x y) : (term157 x y) = term2.
Proof. exact (EQ_MP (@lem1489934 x y) (@lem1489933 x y h1)). Qed.
Lemma lem1489936 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1489937 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1489938 (x : real) (y : real) : (term192 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1489937) (@lem1489936 x y)). Qed.
Lemma lem1489939 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489940 (x : real) (y : real) : ((term157 x y) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1489938 x y) (@lem1489939)). Qed.
Lemma lem1489941 (x : real) (y : real) (h1 : term185 x y) : (real_add x y) = term2.
Proof. exact (EQ_MP (@lem1489940 x y) (@lem1489935 x y h1)). Qed.
Lemma lem1489942 (x : real) (y : real) (h1 : term185 x y) : term185 x y.
Proof. exact (conj (@lem1489941 x y h1) (@lem1489928 x y h1)). Qed.
Lemma lem1489944 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1489945 (x : real) (y : real) : term193 x y.
Proof. exact (@lem1489944 (real_add x y) (term53 x y)). Qed.
Lemma lem1489946 (x : real) (y : real) (h1 : term185 x y) : term194 x y.
Proof. exact (@lem1489945 x y (@lem1489942 x y h1)). Qed.
Lemma lem1489947 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483480 x (term33 x) y (term33 y)). Qed.
Lemma lem1489948 (x : real) : (term197 x) = (term172 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1489950 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1489951 : term174 = term2.
Proof. exact (@lem1489950 term26). Qed.
Lemma lem1489952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489953 : term175 = term176.
Proof. exact (MK_COMB (@lem1489952) (@lem1489951)). Qed.
Lemma lem1489954 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1489955 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1489953) (@lem1489954 x)). Qed.
Lemma lem1489956 (x : real) : (term197 x) = (term177 x).
Proof. exact (TRANS (@lem1489948 x) (@lem1489955 x)). Qed.
Lemma lem1489957 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1489958 (x : real) : (term197 x) = term2.
Proof. exact (TRANS (@lem1489956 x) (@lem1489957 x)). Qed.
Lemma lem1489959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1489960 (x : real) : (term198 x) = term179.
Proof. exact (MK_COMB (@lem1489959) (@lem1489958 x)). Qed.
Lemma lem1489961 (y : real) : (term197 y) = (term172 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1489963 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1489964 : term174 = term2.
Proof. exact (@lem1489963 term26). Qed.
Lemma lem1489965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489966 : term175 = term176.
Proof. exact (MK_COMB (@lem1489965) (@lem1489964)). Qed.
Lemma lem1489967 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1489968 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1489966) (@lem1489967 y)). Qed.
Lemma lem1489969 (y : real) : (term197 y) = (term177 y).
Proof. exact (TRANS (@lem1489961 y) (@lem1489968 y)). Qed.
Lemma lem1489970 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1489971 (y : real) : (term197 y) = term2.
Proof. exact (TRANS (@lem1489969 y) (@lem1489970 y)). Qed.
Lemma lem1489972 (x : real) (y : real) : (term196 x y) = term180.
Proof. exact (MK_COMB (@lem1489960 x) (@lem1489971 y)). Qed.
Lemma lem1489973 (x : real) (y : real) : (term195 x y) = term180.
Proof. exact (TRANS (@lem1489947 x y) (@lem1489972 x y)). Qed.
Lemma lem1489974 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1489975 (x : real) (y : real) : (term195 x y) = term2.
Proof. exact (TRANS (@lem1489973 x y) (@lem1489974)). Qed.
Lemma lem1489976 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489977 (x : real) (y : real) : (term199 x y) = term182.
Proof. exact (MK_COMB (@lem1489976) (@lem1489975 x y)). Qed.
Lemma lem1489978 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489979 (x : real) (y : real) : (term194 x y) = term183.
Proof. exact (MK_COMB (@lem1489977 x y) (@lem1489978)). Qed.
Lemma lem1489980 (x : real) (y : real) (h1 : term185 x y) : term183.
Proof. exact (EQ_MP (@lem1489979 x y) (@lem1489946 x y h1)). Qed.
Lemma lem1489982 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489983 : term183 = term184.
Proof. exact (@lem1489982 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1489984 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1489985 : term183 = False.
Proof. exact (TRANS (@lem1489983) (@lem1489984)). Qed.
Lemma lem1489986 (x : real) (y : real) (h1 : term185 x y) : False.
Proof. exact (EQ_MP (@lem1489985) (@lem1489980 x y h1)). Qed.
Lemma lem1489987 (x : real) (y : real) (h1 : term141 x y) : False.
Proof. exact (or_elim (@lem1489816 x y h1) (fun h0 : term148 x y => @lem1489904 x y h0) (fun h0 : term185 x y => @lem1489986 x y h0)). Qed.
Lemma lem1489988 (x : real) (y : real) (h1 : term140 x y) : term140 x y.
Proof. exact (h1). Qed.
Lemma lem1489989 (x : real) (y : real) (h1 : term200 x y) : term200 x y.
Proof. exact (h1). Qed.
Lemma lem1489990 (x : real) (y : real) (h1 : term200 x y) : (real_add x y) = term2.
Proof. exact (proj2 (@lem1489989 x y h1)). Qed.
Lemma lem1489991 (x : real) (y : real) (h1 : term200 x y) : term62 x y.
Proof. exact (proj1 (@lem1489989 x y h1)). Qed.
Lemma lem1489993 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489994 : term150 = term151.
Proof. exact (@lem1489993 (NUMERAL 0) term26). Qed.
Lemma lem1489995 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1489996 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1489997 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1489996 h1) (fun h1 : term151 = True => @lem1489995)). Qed.
Lemma lem1489998 : term151 = True.
Proof. exact (EQ_MP (@lem1489997) (@lem1489995)). Qed.
Lemma lem1489999 : term150 = True.
Proof. exact (TRANS (@lem1489994) (@lem1489998)). Qed.
Lemma lem1490000 : True = term150.
Proof. exact (SYM (@lem1489999)). Qed.
Lemma lem1490001 : term150.
Proof. exact (EQ_MP (@lem1490000) (@lem0)). Qed.
Lemma lem1490002 (x : real) (y : real) (h1 : term200 x y) : term153 x y.
Proof. exact (conj (@lem1490001) (@lem1489991 x y h1)). Qed.
Lemma lem1490004 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1490005 (x : real) (y : real) : term155 x y.
Proof. exact (@lem1490004 term46 (real_add x y)). Qed.
Lemma lem1490006 (x : real) (y : real) (h1 : term200 x y) : term156 x y.
Proof. exact (@lem1490005 x y (@lem1490002 x y h1)). Qed.
Lemma lem1490007 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1490008 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490009 (x : real) (y : real) : (term158 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1490008) (@lem1490007 x y)). Qed.
Lemma lem1490010 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490011 (x : real) (y : real) : (term156 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1490009 x y) (@lem1490010)). Qed.
Lemma lem1490012 (x : real) (y : real) (h1 : term200 x y) : term62 x y.
Proof. exact (EQ_MP (@lem1490011 x y) (@lem1490006 x y h1)). Qed.
Lemma lem1490014 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1490015 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1490014 (real_add x y)). Qed.
Lemma lem1490016 (x : real) (y : real) (h1 : term200 x y) : term161 x y.
Proof. exact (@lem1490015 x y (@lem1489990 x y h1)). Qed.
Lemma lem1490017 (x : real) (y : real) (h1 : term200 x y) : term162 x y.
Proof. exact (@lem1490016 x y h1 term39). Qed.
Lemma lem1490018 (x : real) (y : real) : (term162 x y) = ((term52 x y) = term2).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem1490019 (x : real) (y : real) (h1 : term200 x y) : (term52 x y) = term2.
Proof. exact (EQ_MP (@lem1490018 x y) (@lem1490017 x y h1)). Qed.
Lemma lem1490026 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1490027 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1490028 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1490027) (@lem1490026 x y)). Qed.
Lemma lem1490029 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490030 (x : real) (y : real) : ((term52 x y) = term2) = ((term53 x y) = term2).
Proof. exact (MK_COMB (@lem1490028 x y) (@lem1490029)). Qed.
Lemma lem1490031 (x : real) (y : real) (h1 : term200 x y) : (term53 x y) = term2.
Proof. exact (EQ_MP (@lem1490030 x y) (@lem1490019 x y h1)). Qed.
Lemma lem1490032 (x : real) (y : real) (h1 : term200 x y) : term165 x y.
Proof. exact (conj (@lem1490031 x y h1) (@lem1490012 x y h1)). Qed.
Lemma lem1490034 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1490035 (x : real) (y : real) : term167 x y.
Proof. exact (@lem1490034 (term53 x y) (real_add x y)). Qed.
Lemma lem1490036 (x : real) (y : real) (h1 : term200 x y) : term168 x y.
Proof. exact (@lem1490035 x y (@lem1490032 x y h1)). Qed.
Lemma lem1490037 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (@lem1483480 (term33 x) x (term33 y) y). Qed.
Lemma lem1490038 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1490040 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490041 : term174 = term2.
Proof. exact (@lem1490040 term26). Qed.
Lemma lem1490042 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490043 : term175 = term176.
Proof. exact (MK_COMB (@lem1490042) (@lem1490041)). Qed.
Lemma lem1490044 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1490045 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1490043) (@lem1490044 x)). Qed.
Lemma lem1490046 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1490038 x) (@lem1490045 x)). Qed.
Lemma lem1490047 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1490048 (x : real) : (term171 x) = term2.
Proof. exact (TRANS (@lem1490046 x) (@lem1490047 x)). Qed.
Lemma lem1490049 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1490050 (x : real) : (term178 x) = term179.
Proof. exact (MK_COMB (@lem1490049) (@lem1490048 x)). Qed.
Lemma lem1490051 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1490053 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490054 : term174 = term2.
Proof. exact (@lem1490053 term26). Qed.
Lemma lem1490055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490056 : term175 = term176.
Proof. exact (MK_COMB (@lem1490055) (@lem1490054)). Qed.
Lemma lem1490057 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1490058 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1490056) (@lem1490057 y)). Qed.
Lemma lem1490059 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1490051 y) (@lem1490058 y)). Qed.
Lemma lem1490060 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1490061 (y : real) : (term171 y) = term2.
Proof. exact (TRANS (@lem1490059 y) (@lem1490060 y)). Qed.
Lemma lem1490062 (x : real) (y : real) : (term170 x y) = term180.
Proof. exact (MK_COMB (@lem1490050 x) (@lem1490061 y)). Qed.
Lemma lem1490063 (x : real) (y : real) : (term169 x y) = term180.
Proof. exact (TRANS (@lem1490037 x y) (@lem1490062 x y)). Qed.
Lemma lem1490064 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1490065 (x : real) (y : real) : (term169 x y) = term2.
Proof. exact (TRANS (@lem1490063 x y) (@lem1490064)). Qed.
Lemma lem1490066 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490067 (x : real) (y : real) : (term181 x y) = term182.
Proof. exact (MK_COMB (@lem1490066) (@lem1490065 x y)). Qed.
Lemma lem1490068 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490069 (x : real) (y : real) : (term168 x y) = term183.
Proof. exact (MK_COMB (@lem1490067 x y) (@lem1490068)). Qed.
Lemma lem1490070 (x : real) (y : real) (h1 : term200 x y) : term183.
Proof. exact (EQ_MP (@lem1490069 x y) (@lem1490036 x y h1)). Qed.
Lemma lem1490072 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1490073 : term183 = term184.
Proof. exact (@lem1490072 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1490074 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1490075 : term183 = False.
Proof. exact (TRANS (@lem1490073) (@lem1490074)). Qed.
Lemma lem1490076 (x : real) (y : real) (h1 : term200 x y) : False.
Proof. exact (EQ_MP (@lem1490075) (@lem1490070 x y h1)). Qed.
Lemma lem1490077 (x : real) (y : real) (h1 : term201 x y) : term201 x y.
Proof. exact (h1). Qed.
Lemma lem1490078 (x : real) (y : real) (h1 : term201 x y) : (real_add x y) = term2.
Proof. exact (proj2 (@lem1490077 x y h1)). Qed.
Lemma lem1490079 (x : real) (y : real) (h1 : term201 x y) : term58 x y.
Proof. exact (proj1 (@lem1490077 x y h1)). Qed.
Lemma lem1490081 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1490082 : term150 = term151.
Proof. exact (@lem1490081 (NUMERAL 0) term26). Qed.
Lemma lem1490083 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1490084 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1490085 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1490084 h1) (fun h1 : term151 = True => @lem1490083)). Qed.
Lemma lem1490086 : term151 = True.
Proof. exact (EQ_MP (@lem1490085) (@lem1490083)). Qed.
Lemma lem1490087 : term150 = True.
Proof. exact (TRANS (@lem1490082) (@lem1490086)). Qed.
Lemma lem1490088 : True = term150.
Proof. exact (SYM (@lem1490087)). Qed.
Lemma lem1490089 : term150.
Proof. exact (EQ_MP (@lem1490088) (@lem0)). Qed.
Lemma lem1490090 (x : real) (y : real) (h1 : term201 x y) : term186 x y.
Proof. exact (conj (@lem1490089) (@lem1490079 x y h1)). Qed.
Lemma lem1490092 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1490093 (x : real) (y : real) : term187 x y.
Proof. exact (@lem1490092 term46 (term53 x y)). Qed.
Lemma lem1490094 (x : real) (y : real) (h1 : term201 x y) : term188 x y.
Proof. exact (@lem1490093 x y (@lem1490090 x y h1)). Qed.
Lemma lem1490095 (x : real) (y : real) : (term189 x y) = (term53 x y).
Proof. exact (@lem1483460 (term53 x y)). Qed.
Lemma lem1490096 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490097 (x : real) (y : real) : (term190 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1490096) (@lem1490095 x y)). Qed.
Lemma lem1490098 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490099 (x : real) (y : real) : (term188 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1490097 x y) (@lem1490098)). Qed.
Lemma lem1490100 (x : real) (y : real) (h1 : term201 x y) : term58 x y.
Proof. exact (EQ_MP (@lem1490099 x y) (@lem1490094 x y h1)). Qed.
Lemma lem1490102 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1490103 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1490102 (real_add x y)). Qed.
Lemma lem1490104 (x : real) (y : real) (h1 : term201 x y) : term161 x y.
Proof. exact (@lem1490103 x y (@lem1490078 x y h1)). Qed.
Lemma lem1490105 (x : real) (y : real) (h1 : term201 x y) : term191 x y.
Proof. exact (@lem1490104 x y h1 term46). Qed.
Lemma lem1490106 (x : real) (y : real) : (term191 x y) = ((term157 x y) = term2).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1490107 (x : real) (y : real) (h1 : term201 x y) : (term157 x y) = term2.
Proof. exact (EQ_MP (@lem1490106 x y) (@lem1490105 x y h1)). Qed.
Lemma lem1490108 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1490109 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1490110 (x : real) (y : real) : (term192 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1490109) (@lem1490108 x y)). Qed.
Lemma lem1490111 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490112 (x : real) (y : real) : ((term157 x y) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1490110 x y) (@lem1490111)). Qed.
Lemma lem1490113 (x : real) (y : real) (h1 : term201 x y) : (real_add x y) = term2.
Proof. exact (EQ_MP (@lem1490112 x y) (@lem1490107 x y h1)). Qed.
Lemma lem1490114 (x : real) (y : real) (h1 : term201 x y) : term185 x y.
Proof. exact (conj (@lem1490113 x y h1) (@lem1490100 x y h1)). Qed.
Lemma lem1490116 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1490117 (x : real) (y : real) : term193 x y.
Proof. exact (@lem1490116 (real_add x y) (term53 x y)). Qed.
Lemma lem1490118 (x : real) (y : real) (h1 : term201 x y) : term194 x y.
Proof. exact (@lem1490117 x y (@lem1490114 x y h1)). Qed.
Lemma lem1490119 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483480 x (term33 x) y (term33 y)). Qed.
Lemma lem1490120 (x : real) : (term197 x) = (term172 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1490122 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490123 : term174 = term2.
Proof. exact (@lem1490122 term26). Qed.
Lemma lem1490124 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490125 : term175 = term176.
Proof. exact (MK_COMB (@lem1490124) (@lem1490123)). Qed.
Lemma lem1490126 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1490127 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1490125) (@lem1490126 x)). Qed.
Lemma lem1490128 (x : real) : (term197 x) = (term177 x).
Proof. exact (TRANS (@lem1490120 x) (@lem1490127 x)). Qed.
Lemma lem1490129 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1490130 (x : real) : (term197 x) = term2.
Proof. exact (TRANS (@lem1490128 x) (@lem1490129 x)). Qed.
Lemma lem1490131 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1490132 (x : real) : (term198 x) = term179.
Proof. exact (MK_COMB (@lem1490131) (@lem1490130 x)). Qed.
Lemma lem1490133 (y : real) : (term197 y) = (term172 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1490135 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490136 : term174 = term2.
Proof. exact (@lem1490135 term26). Qed.
Lemma lem1490137 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490138 : term175 = term176.
Proof. exact (MK_COMB (@lem1490137) (@lem1490136)). Qed.
Lemma lem1490139 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1490140 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1490138) (@lem1490139 y)). Qed.
Lemma lem1490141 (y : real) : (term197 y) = (term177 y).
Proof. exact (TRANS (@lem1490133 y) (@lem1490140 y)). Qed.
Lemma lem1490142 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1490143 (y : real) : (term197 y) = term2.
Proof. exact (TRANS (@lem1490141 y) (@lem1490142 y)). Qed.
Lemma lem1490144 (x : real) (y : real) : (term196 x y) = term180.
Proof. exact (MK_COMB (@lem1490132 x) (@lem1490143 y)). Qed.
Lemma lem1490145 (x : real) (y : real) : (term195 x y) = term180.
Proof. exact (TRANS (@lem1490119 x y) (@lem1490144 x y)). Qed.
Lemma lem1490146 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1490147 (x : real) (y : real) : (term195 x y) = term2.
Proof. exact (TRANS (@lem1490145 x y) (@lem1490146)). Qed.
Lemma lem1490148 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490149 (x : real) (y : real) : (term199 x y) = term182.
Proof. exact (MK_COMB (@lem1490148) (@lem1490147 x y)). Qed.
Lemma lem1490150 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490151 (x : real) (y : real) : (term194 x y) = term183.
Proof. exact (MK_COMB (@lem1490149 x y) (@lem1490150)). Qed.
Lemma lem1490152 (x : real) (y : real) (h1 : term201 x y) : term183.
Proof. exact (EQ_MP (@lem1490151 x y) (@lem1490118 x y h1)). Qed.
Lemma lem1490154 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1490155 : term183 = term184.
Proof. exact (@lem1490154 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1490156 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1490157 : term183 = False.
Proof. exact (TRANS (@lem1490155) (@lem1490156)). Qed.
Lemma lem1490158 (x : real) (y : real) (h1 : term201 x y) : False.
Proof. exact (EQ_MP (@lem1490157) (@lem1490152 x y h1)). Qed.
Lemma lem1490159 (x : real) (y : real) (h1 : term140 x y) : False.
Proof. exact (or_elim (@lem1489988 x y h1) (fun h0 : term200 x y => @lem1490076 x y h0) (fun h0 : term201 x y => @lem1490158 x y h0)). Qed.
Lemma lem1490160 (x : real) (y : real) (h1 : term143 x y) : False.
Proof. exact (or_elim (@lem1489815 x y h1) (fun h0 : term141 x y => @lem1489987 x y h0) (fun h0 : term140 x y => @lem1490159 x y h0)). Qed.
Lemma lem1490162 (x : real) (y : real) (h1 : term143 x y) : term143 x y.
Proof. exact (h1). Qed.
Lemma lem1490163 (x : real) (y : real) (h1 : term143 x y) : (term143 x y) = False.
Proof. exact (prop_ext (fun h2 : term143 x y => @lem1490160 x y h1) (fun h2 : False => @lem1490162 x y h1)). Qed.
Lemma lem1490164 (x : real) (y : real) (h1 : term143 x y) : False.
Proof. exact (EQ_MP (@lem1490163 x y h1) (@lem1490162 x y h1)). Qed.
Lemma lem1490165 (x : real) (h1 : term145 x) : term145 x.
Proof. exact (h1). Qed.
Lemma lem1490166 (x : real) (h1 : term145 x) : False.
Proof. exact (ex_elim (@lem1490165 x h1) (fun y : real => fun h0 : term144 x y => @lem1490164 x y h0)). Qed.
Lemma lem1490167 (h1 : term147) : term147.
Proof. exact (h1). Qed.
Lemma lem1490168 (h1 : term147) : False.
Proof. exact (ex_elim (@lem1490167 h1) (fun x : real => fun h0 : term146 x => @lem1490166 x h0)). Qed.
Lemma lem1490169 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1490170 (h1 : term13) : term147.
Proof. exact (EQ_MP (@lem1489793) (@lem1490169 h1)). Qed.
Lemma lem1490171 (h1 : term13) : term147 = False.
Proof. exact (prop_ext (fun h2 : term147 => @lem1490168 h2) (fun h2 : False => @lem1490170 h1)). Qed.
Lemma lem1490172 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1490171 h1) (@lem1490170 h1)). Qed.
Lemma lem1490173 : term202.
Proof. exact (fun h0 : term13 => @lem1490172 h0). Qed.
Lemma lem1490174 : term203.
Proof. exact (@lem1386578 term204). Qed.
Lemma lem1490175 : term204.
Proof. exact (@lem1490174 (@lem1490173)). Qed.
