Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1978411_term_abbrevs.
Require Import REAL_MUL_LNEG_spec.
Require Import real_div_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm1978260_spec.
Lemma lem1978264 (x : real) (y : real) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem1978265 (x : real) (y : real) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem1978264 x y h1)). Qed.
Lemma lem1978266 (x : real) (y : real) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1978267 (x : real) (y : real) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem1978266 x y h1)). Qed.
Lemma lem1978268 (x : real) (y : real) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem1978265 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem1978267 x y h1)). Qed.
Lemma lem1978269 (x : real) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : real => @lem1978268 x y)). Qed.
Lemma lem1978270 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1978271 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1978270) (@lem1978269 x)). Qed.
Lemma lem1978272 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1978271 x)). Qed.
Lemma lem1978273 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1978274 : term8 = term9.
Proof. exact (MK_COMB (@lem1978273) (@lem1978272)). Qed.
Lemma lem1978275 : term9.
Proof. exact (EQ_MP (@lem1978274) (@lem1360913)). Qed.
Lemma lem1978276 (x : real) : term10 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1978277 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1978278 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1978277 x) (@lem1978276 x)). Qed.
Lemma lem1978279 (x : real) (y : real) : term12 x y.
Proof. exact (@lem1978278 x y). Qed.
Lemma lem1978280 (x : real) (y : real) : (term12 x y) = ((real_div x y) = (term13 x y)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1978282 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term14 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1978284 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term15 x1 x2 y1 y2.
Proof. exact (fun h0 : term14 y1 y2 => @lem1978260 x1 x2 y1 y2 h0). Qed.
Lemma lem1978285 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term16 x1 y1 x2 y2) = (term17 x1 x2 y1 y2).
Proof. exact (@lem1978284 x1 x2 y1 y2 (@lem1978282 y1 y2 h1)). Qed.
Lemma lem1978286 (x1 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term18 x1 y1 y2.
Proof. exact (fun x2 : real => @lem1978285 x1 x2 y1 y2 h1). Qed.
Lemma lem1978287 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term19 y1 y2.
Proof. exact (fun x1 : real => @lem1978286 x1 y1 y2 h1). Qed.
Lemma lem1978301 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1978280 x y) (@lem1978279 x y)). Qed.
Lemma lem1978302 (x1 : real) (y1 : real) : (real_div x1 y1) = (term13 x1 y1).
Proof. exact (@lem1978301 x1 y1). Qed.
Lemma lem1978303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1978304 (x1 : real) (y1 : real) : (term20 x1 y1) = (term21 x1 y1).
Proof. exact (MK_COMB (@lem1978303) (@lem1978302 x1 y1)). Qed.
Lemma lem1978306 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1978280 x y) (@lem1978279 x y)). Qed.
Lemma lem1978307 (x2 : real) (y2 : real) : (real_div x2 y2) = (term13 x2 y2).
Proof. exact (@lem1978306 x2 y2). Qed.
Lemma lem1978308 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term16 x1 y1 x2 y2) = (term22 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1978304 x1 y1) (@lem1978307 x2 y2)). Qed.
Lemma lem1978309 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1978310 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term23 x1 y1 x2 y2) = (term24 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1978309) (@lem1978308 x1 y1 x2 y2)). Qed.
Lemma lem1978311 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term17 x1 x2 y1 y2) = (term17 x1 x2 y1 y2).
Proof. exact (eq_refl (term17 x1 x2 y1 y2)). Qed.
Lemma lem1978312 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term16 x1 y1 x2 y2) = (term17 x1 x2 y1 y2)) = ((term22 x1 y1 x2 y2) = (term17 x1 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1978310 x1 y1 x2 y2) (@lem1978311 x1 x2 y1 y2)). Qed.
Lemma lem1978315 (x1 : real) (y1 : real) (y2 : real) : (term25 x1 y1 y2) = (term26 x1 y1 y2).
Proof. exact (fun_ext (fun x2 : real => @lem1978312 x1 x2 y1 y2)). Qed.
Lemma lem1978316 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1978317 (x1 : real) (y1 : real) (y2 : real) : (term18 x1 y1 y2) = (term27 x1 y1 y2).
Proof. exact (MK_COMB (@lem1978316) (@lem1978315 x1 y1 y2)). Qed.
Lemma lem1978322 (y1 : real) (y2 : real) : (term28 y1 y2) = (term29 y1 y2).
Proof. exact (fun_ext (fun x1 : real => @lem1978317 x1 y1 y2)). Qed.
Lemma lem1978323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1978324 (y1 : real) (y2 : real) : (term19 y1 y2) = (term30 y1 y2).
Proof. exact (MK_COMB (@lem1978323) (@lem1978322 y1 y2)). Qed.
Lemma lem1978329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1978330 (y1 : real) (y2 : real) : (term31 y1 y2) = (term32 y1 y2).
Proof. exact (MK_COMB (@lem1978329) (@lem1978324 y1 y2)). Qed.
Lemma lem1978334 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1978280 x y) (@lem1978279 x y)). Qed.
Lemma lem1978335 (x1 : real) (y1 : real) : (real_div x1 y1) = (term13 x1 y1).
Proof. exact (@lem1978334 x1 y1). Qed.
Lemma lem1978336 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1978337 (x1 : real) (y1 : real) : (term33 x1 y1) = (term34 x1 y1).
Proof. exact (MK_COMB (@lem1978336) (@lem1978335 x1 y1)). Qed.
Lemma lem1978339 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1978280 x y) (@lem1978279 x y)). Qed.
Lemma lem1978340 (x2 : real) (y2 : real) : (real_div x2 y2) = (term13 x2 y2).
Proof. exact (@lem1978339 x2 y2). Qed.
Lemma lem1978341 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term35 x1 y1 x2 y2) = (term36 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1978337 x1 y1) (@lem1978340 x2 y2)). Qed.
Lemma lem1978342 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1978343 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term37 x1 y1 x2 y2) = (term38 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1978342) (@lem1978341 x1 y1 x2 y2)). Qed.
Lemma lem1978344 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term39 x1 x2 y1 y2) = (term39 x1 x2 y1 y2).
Proof. exact (eq_refl (term39 x1 x2 y1 y2)). Qed.
Lemma lem1978345 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term35 x1 y1 x2 y2) = (term39 x1 x2 y1 y2)) = ((term36 x1 y1 x2 y2) = (term39 x1 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1978343 x1 y1 x2 y2) (@lem1978344 x1 x2 y1 y2)). Qed.
Lemma lem1978348 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term40 x1 x2 y1 y2) = (term41 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1978330 y1 y2) (@lem1978345 x1 x2 y1 y2)). Qed.
Lemma lem1978351 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term41 x1 x2 y1 y2) = (term40 x1 x2 y1 y2).
Proof. exact (SYM (@lem1978348 x1 x2 y1 y2)). Qed.
Lemma lem1978352 (y1 : real) (y2 : real) (h1 : term30 y1 y2) : term30 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1978353 (x : real) : term42 x.
Proof. exact (@lem1978275 x). Qed.
Lemma lem1978354 (x : real) : (term42 x) = (term5 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1978355 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1978354 x) (@lem1978353 x)). Qed.
Lemma lem1978356 (x : real) (y : real) : term43 x y.
Proof. exact (@lem1978355 x y). Qed.
Lemma lem1978357 (x : real) (y : real) : (term43 x y) = ((term1 x y) = (term0 x y)).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1978359 (x : real) : term44 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1978360 (x : real) : (term44 x) = (term45 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1978361 (x : real) : term45 x.
Proof. exact (EQ_MP (@lem1978360 x) (@lem1978359 x)). Qed.
Lemma lem1978362 (x : real) (y : real) : term46 x y.
Proof. exact (@lem1978361 x y). Qed.
Lemma lem1978363 (x : real) (y : real) : (term46 x y) = ((real_sub x y) = (term47 x y)).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1978365 (x1 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : term48 y1 y2 x1.
Proof. exact (@lem1978352 y1 y2 h1 x1). Qed.
Lemma lem1978366 (x1 : real) (y1 : real) (y2 : real) : (term48 y1 y2 x1) = (term27 x1 y1 y2).
Proof. exact (eq_refl (term48 y1 y2 x1)). Qed.
Lemma lem1978367 (x1 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : term27 x1 y1 y2.
Proof. exact (EQ_MP (@lem1978366 x1 y1 y2) (@lem1978365 x1 y1 y2 h1)). Qed.
Lemma lem1978368 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : term49 x1 y1 y2 x2.
Proof. exact (@lem1978367 x1 y1 y2 h1 x2). Qed.
Lemma lem1978369 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term49 x1 y1 y2 x2) = ((term22 x1 y1 x2 y2) = (term17 x1 x2 y1 y2)).
Proof. exact (eq_refl (term49 x1 y1 y2 x2)). Qed.
Lemma lem1978374 (x : real) (y : real) : (real_sub x y) = (term47 x y).
Proof. exact (EQ_MP (@lem1978363 x y) (@lem1978362 x y)). Qed.
Lemma lem1978375 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term36 x1 y1 x2 y2) = (term50 x1 y1 x2 y2).
Proof. exact (@lem1978374 (term13 x1 y1) (term13 x2 y2)). Qed.
Lemma lem1978377 (x : real) (y : real) : (term1 x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1978357 x y) (@lem1978356 x y)). Qed.
Lemma lem1978378 (x2 : real) (y2 : real) : (term51 x2 y2) = (term52 x2 y2).
Proof. exact (@lem1978377 x2 (real_inv y2)). Qed.
Lemma lem1978379 (x1 : real) (y1 : real) : (term21 x1 y1) = (term21 x1 y1).
Proof. exact (eq_refl (term21 x1 y1)). Qed.
Lemma lem1978380 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term50 x1 y1 x2 y2) = (term53 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1978379 x1 y1) (@lem1978378 x2 y2)). Qed.
Lemma lem1978382 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : (term22 x1 y1 x2 y2) = (term17 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1978369 x1 x2 y1 y2) (@lem1978368 x1 x2 y1 y2 h1)). Qed.
Lemma lem1978383 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : (term53 x1 y1 x2 y2) = (term54 x1 x2 y1 y2).
Proof. exact (@lem1978382 x1 (real_neg x2) y1 y2 h1). Qed.
Lemma lem1978384 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : (term50 x1 y1 x2 y2) = (term54 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1978380 x1 y1 x2 y2) (@lem1978383 x1 x2 y1 y2 h1)). Qed.
Lemma lem1978385 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : (term36 x1 y1 x2 y2) = (term54 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1978375 x1 y1 x2 y2) (@lem1978384 x1 x2 y1 y2 h1)). Qed.
Lemma lem1978386 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1978387 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : (term38 x1 y1 x2 y2) = (term55 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1978386) (@lem1978385 x1 x2 y1 y2 h1)). Qed.
Lemma lem1978389 (x : real) (y : real) : (real_sub x y) = (term47 x y).
Proof. exact (EQ_MP (@lem1978363 x y) (@lem1978362 x y)). Qed.
Lemma lem1978390 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term56 x1 y2 x2 y1) = (term57 x1 y2 x2 y1).
Proof. exact (@lem1978389 (real_mul x1 y2) (real_mul x2 y1)). Qed.
Lemma lem1978392 (x : real) (y : real) : (term1 x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1978357 x y) (@lem1978356 x y)). Qed.
Lemma lem1978393 (x2 : real) (y1 : real) : (term1 x2 y1) = (term0 x2 y1).
Proof. exact (@lem1978392 x2 y1). Qed.
Lemma lem1978394 (x1 : real) (y2 : real) : (term58 x1 y2) = (term58 x1 y2).
Proof. exact (eq_refl (term58 x1 y2)). Qed.
Lemma lem1978395 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term57 x1 y2 x2 y1) = (term59 x1 y2 x2 y1).
Proof. exact (MK_COMB (@lem1978394 x1 y2) (@lem1978393 x2 y1)). Qed.
Lemma lem1978396 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term56 x1 y2 x2 y1) = (term59 x1 y2 x2 y1).
Proof. exact (TRANS (@lem1978390 x1 y2 x2 y1) (@lem1978395 x1 y2 x2 y1)). Qed.
Lemma lem1978397 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1978398 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term60 x1 y2 x2 y1) = (term61 x1 y2 x2 y1).
Proof. exact (MK_COMB (@lem1978397) (@lem1978396 x1 y2 x2 y1)). Qed.
Lemma lem1978399 (y1 : real) (y2 : real) : (term62 y1 y2) = (term62 y1 y2).
Proof. exact (eq_refl (term62 y1 y2)). Qed.
Lemma lem1978400 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term39 x1 x2 y1 y2) = (term54 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1978398 x1 y2 x2 y1) (@lem1978399 y1 y2)). Qed.
Lemma lem1978401 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : ((term36 x1 y1 x2 y2) = (term39 x1 x2 y1 y2)) = ((term54 x1 x2 y1 y2) = (term54 x1 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1978387 x1 x2 y1 y2 h1) (@lem1978400 x1 x2 y1 y2)). Qed.
Lemma lem1978403 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1978404 (x : real) : (x = x) = True.
Proof. exact (@lem1978403 real x). Qed.
Lemma lem1978405 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term54 x1 x2 y1 y2) = (term54 x1 x2 y1 y2)) = True.
Proof. exact (@lem1978404 (term54 x1 x2 y1 y2)). Qed.
Lemma lem1978406 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : ((term36 x1 y1 x2 y2) = (term39 x1 x2 y1 y2)) = True.
Proof. exact (TRANS (@lem1978401 x1 x2 y1 y2 h1) (@lem1978405 x1 x2 y1 y2)). Qed.
Lemma lem1978407 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : True = ((term36 x1 y1 x2 y2) = (term39 x1 x2 y1 y2)).
Proof. exact (SYM (@lem1978406 x1 x2 y1 y2 h1)). Qed.
Lemma lem1978408 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term30 y1 y2) : (term36 x1 y1 x2 y2) = (term39 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1978407 x1 x2 y1 y2 h1) (@lem0)). Qed.
Lemma lem1978409 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term41 x1 x2 y1 y2.
Proof. exact (fun h0 : term30 y1 y2 => @lem1978408 x1 x2 y1 y2 h0). Qed.
Lemma lem1978410 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term40 x1 x2 y1 y2.
Proof. exact (EQ_MP (@lem1978351 x1 x2 y1 y2) (@lem1978409 x1 x2 y1 y2)). Qed.
Lemma lem1978411 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term35 x1 y1 x2 y2) = (term39 x1 x2 y1 y2).
Proof. exact (@lem1978410 x1 x2 y1 y2 (@lem1978287 y1 y2 h1)). Qed.
