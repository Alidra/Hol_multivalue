Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_INT_CLAUSES_term_abbrevs.
Require Import int_abs_th_spec.
Require Import int_add_th_spec.
Require Import int_eq_spec.
Require Import int_ge_spec.
Require Import int_gt_spec.
Require Import int_le_spec.
Require Import int_lt_spec.
Require Import int_max_th_spec.
Require Import int_min_th_spec.
Require Import int_mul_th_spec.
Require Import int_neg_th_spec.
Require Import int_of_num_th_spec.
Require Import int_pow_th_spec.
Require Import int_sgn_th_spec.
Require Import int_sub_th_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2294269 (x : int) : term0 x.
Proof. exact (@lem2294268 x). Qed.
Lemma lem2294270 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2294271 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2294270 x) (@lem2294269 x)). Qed.
Lemma lem2294272 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2294271 x n). Qed.
Lemma lem2294273 (x : int) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2294275 (x : int) : term5 x.
Proof. exact (@lem2287415 x). Qed.
Lemma lem2294276 (x : int) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2294277 (x : int) : term6 x.
Proof. exact (EQ_MP (@lem2294276 x) (@lem2294275 x)). Qed.
Lemma lem2294278 (x : int) (y : int) : term7 x y.
Proof. exact (@lem2294277 x y). Qed.
Lemma lem2294279 (x : int) (y : int) : (term7 x y) = ((term8 x y) = (term9 x y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem2294281 (x : int) : term10 x.
Proof. exact (@lem2285582 x). Qed.
Lemma lem2294282 (x : int) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem2294283 (x : int) : term11 x.
Proof. exact (EQ_MP (@lem2294282 x) (@lem2294281 x)). Qed.
Lemma lem2294284 (x : int) (y : int) : term12 x y.
Proof. exact (@lem2294283 x y). Qed.
Lemma lem2294285 (x : int) (y : int) : (term12 x y) = ((term13 x y) = (term14 x y)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem2294287 (x : int) : term15 x.
Proof. exact (@lem2284714 x). Qed.
Lemma lem2294288 (x : int) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem2294289 (x : int) : term16 x.
Proof. exact (EQ_MP (@lem2294288 x) (@lem2294287 x)). Qed.
Lemma lem2294290 (x : int) (y : int) : term17 x y.
Proof. exact (@lem2294289 x y). Qed.
Lemma lem2294291 (x : int) (y : int) : (term17 x y) = ((term18 x y) = (term19 x y)).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem2294293 (x : int) : term20 x.
Proof. exact (@lem2291527 x). Qed.
Lemma lem2294294 (x : int) : (term20 x) = ((term21 x) = (term22 x)).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2294296 (x : int) : term23 x.
Proof. exact (@lem2293297 x). Qed.
Lemma lem2294297 (x : int) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2294298 (x : int) : term24 x.
Proof. exact (EQ_MP (@lem2294297 x) (@lem2294296 x)). Qed.
Lemma lem2294299 (x : int) (y : int) : term25 x y.
Proof. exact (@lem2294298 x y). Qed.
Lemma lem2294300 (x : int) (y : int) : (term25 x y) = ((term26 x y) = (term27 x y)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2294302 (x : int) : term28 x.
Proof. exact (@lem2292408 x). Qed.
Lemma lem2294303 (x : int) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2294304 (x : int) : term29 x.
Proof. exact (EQ_MP (@lem2294303 x) (@lem2294302 x)). Qed.
Lemma lem2294305 (x : int) (y : int) : term30 x y.
Proof. exact (@lem2294304 x y). Qed.
Lemma lem2294306 (x : int) (y : int) : (term30 x y) = ((term31 x y) = (term32 x y)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem2294308 (x : int) : term33 x.
Proof. exact (@lem2288272 x). Qed.
Lemma lem2294309 (x : int) : (term33 x) = ((term34 x) = (term35 x)).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem2294311 (x : int) : term36 x.
Proof. exact (@lem2273074 x). Qed.
Lemma lem2294312 (x : int) : (term36 x) = ((term37 x) = (term38 x)).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2294314 (n : nat) : term39 n.
Proof. exact (@lem2271980 n). Qed.
Lemma lem2294315 (n : nat) : (term39 n) = ((term40 n) = (real_of_num n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem2294329 (x : int) : term41 x.
Proof. exact (@lem2269769 x). Qed.
Lemma lem2294330 (x : int) : (term41 x) = (term42 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem2294331 (x : int) : term42 x.
Proof. exact (EQ_MP (@lem2294330 x) (@lem2294329 x)). Qed.
Lemma lem2294332 (x : int) (y : int) : term43 x y.
Proof. exact (@lem2294331 x y). Qed.
Lemma lem2294333 (x : int) (y : int) : (term43 x y) = ((int_lt x y) = (term44 x y)).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem2294335 (x : int) : term45 x.
Proof. exact (@lem2269094 x). Qed.
Lemma lem2294336 (x : int) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2294337 (x : int) : term46 x.
Proof. exact (EQ_MP (@lem2294336 x) (@lem2294335 x)). Qed.
Lemma lem2294338 (x : int) (y : int) : term47 x y.
Proof. exact (@lem2294337 x y). Qed.
Lemma lem2294339 (x : int) (y : int) : (term47 x y) = ((int_le x y) = (term48 x y)).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem2294341 (x : int) : term49 x.
Proof. exact (@lem2271143 x). Qed.
Lemma lem2294342 (x : int) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem2294343 (x : int) : term50 x.
Proof. exact (EQ_MP (@lem2294342 x) (@lem2294341 x)). Qed.
Lemma lem2294344 (x : int) (y : int) : term51 x y.
Proof. exact (@lem2294343 x y). Qed.
Lemma lem2294345 (x : int) (y : int) : (term51 x y) = ((int_gt x y) = (term52 x y)).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem2294347 (x : int) : term53 x.
Proof. exact (@lem2270452 x). Qed.
Lemma lem2294348 (x : int) : (term53 x) = (term54 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2294349 (x : int) : term54 x.
Proof. exact (EQ_MP (@lem2294348 x) (@lem2294347 x)). Qed.
Lemma lem2294350 (x : int) (y : int) : term55 x y.
Proof. exact (@lem2294349 x y). Qed.
Lemma lem2294351 (x : int) (y : int) : (term55 x y) = ((int_ge x y) = (term56 x y)).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem2294353 (x : int) : term57 x.
Proof. exact (@lem2268427 x). Qed.
Lemma lem2294354 (x : int) : (term57 x) = (term58 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem2294355 (x : int) : term58 x.
Proof. exact (EQ_MP (@lem2294354 x) (@lem2294353 x)). Qed.
Lemma lem2294356 (x : int) (y : int) : term59 x y.
Proof. exact (@lem2294355 x y). Qed.
Lemma lem2294357 (x : int) (y : int) : (term59 x y) = ((x = y) = ((real_of_int x) = (real_of_int y))).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem2294380 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2294357 x y) (@lem2294356 x y)). Qed.
Lemma lem2294385 (x : int) (y : int) : (term60 x y) = (term60 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem2294386 (x : int) (y : int) : (((real_of_int x) = (real_of_int y)) = (x = y)) = (((real_of_int x) = (real_of_int y)) = ((real_of_int x) = (real_of_int y))).
Proof. exact (MK_COMB (@lem2294385 x y) (@lem2294380 x y)). Qed.
Lemma lem2294388 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294389 (x : Prop) : (x = x) = True.
Proof. exact (@lem2294388 Prop x). Qed.
Lemma lem2294390 (x : int) (y : int) : (((real_of_int x) = (real_of_int y)) = ((real_of_int x) = (real_of_int y))) = True.
Proof. exact (@lem2294389 ((real_of_int x) = (real_of_int y))). Qed.
Lemma lem2294391 (x : int) (y : int) : (((real_of_int x) = (real_of_int y)) = (x = y)) = True.
Proof. exact (TRANS (@lem2294386 x y) (@lem2294390 x y)). Qed.
Lemma lem2294392 (x : int) : (term61 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294391 x y)). Qed.
Lemma lem2294393 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294394 (x : int) : (term63 x) = term64.
Proof. exact (MK_COMB (@lem2294393) (@lem2294392 x)). Qed.
Lemma lem2294396 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294397 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294396 int t). Qed.
Lemma lem2294398 : term64 = True.
Proof. exact (@lem2294397 True). Qed.
Lemma lem2294399 (x : int) : (term63 x) = True.
Proof. exact (TRANS (@lem2294394 x) (@lem2294398)). Qed.
Lemma lem2294400 : term67 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294399 x)). Qed.
Lemma lem2294401 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294402 : term68 = term64.
Proof. exact (MK_COMB (@lem2294401) (@lem2294400)). Qed.
Lemma lem2294404 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294405 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294404 int t). Qed.
Lemma lem2294406 : term64 = True.
Proof. exact (@lem2294405 True). Qed.
Lemma lem2294407 : term68 = True.
Proof. exact (TRANS (@lem2294402) (@lem2294406)). Qed.
Lemma lem2294408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294409 : term69 = (and True).
Proof. exact (MK_COMB (@lem2294408) (@lem2294407)). Qed.
Lemma lem2294425 (x : int) (y : int) : (int_ge x y) = (term56 x y).
Proof. exact (EQ_MP (@lem2294351 x y) (@lem2294350 x y)). Qed.
Lemma lem2294426 (x : int) (y : int) : (term70 x y) = (term70 x y).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem2294427 (x : int) (y : int) : ((term56 x y) = (int_ge x y)) = ((term56 x y) = (term56 x y)).
Proof. exact (MK_COMB (@lem2294426 x y) (@lem2294425 x y)). Qed.
Lemma lem2294429 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294430 (x : Prop) : (x = x) = True.
Proof. exact (@lem2294429 Prop x). Qed.
Lemma lem2294431 (x : int) (y : int) : ((term56 x y) = (term56 x y)) = True.
Proof. exact (@lem2294430 (term56 x y)). Qed.
Lemma lem2294432 (x : int) (y : int) : ((term56 x y) = (int_ge x y)) = True.
Proof. exact (TRANS (@lem2294427 x y) (@lem2294431 x y)). Qed.
Lemma lem2294433 (x : int) : (term71 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294432 x y)). Qed.
Lemma lem2294434 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294435 (x : int) : (term72 x) = term64.
Proof. exact (MK_COMB (@lem2294434) (@lem2294433 x)). Qed.
Lemma lem2294437 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294438 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294437 int t). Qed.
Lemma lem2294439 : term64 = True.
Proof. exact (@lem2294438 True). Qed.
Lemma lem2294440 (x : int) : (term72 x) = True.
Proof. exact (TRANS (@lem2294435 x) (@lem2294439)). Qed.
Lemma lem2294441 : term73 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294440 x)). Qed.
Lemma lem2294442 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294443 : term74 = term64.
Proof. exact (MK_COMB (@lem2294442) (@lem2294441)). Qed.
Lemma lem2294445 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294446 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294445 int t). Qed.
Lemma lem2294447 : term64 = True.
Proof. exact (@lem2294446 True). Qed.
Lemma lem2294448 : term74 = True.
Proof. exact (TRANS (@lem2294443) (@lem2294447)). Qed.
Lemma lem2294449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294450 : term75 = (and True).
Proof. exact (MK_COMB (@lem2294449) (@lem2294448)). Qed.
Lemma lem2294466 (x : int) (y : int) : (int_gt x y) = (term52 x y).
Proof. exact (EQ_MP (@lem2294345 x y) (@lem2294344 x y)). Qed.
Lemma lem2294467 (x : int) (y : int) : (term76 x y) = (term76 x y).
Proof. exact (eq_refl (term76 x y)). Qed.
Lemma lem2294468 (x : int) (y : int) : ((term52 x y) = (int_gt x y)) = ((term52 x y) = (term52 x y)).
Proof. exact (MK_COMB (@lem2294467 x y) (@lem2294466 x y)). Qed.
Lemma lem2294470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294471 (x : Prop) : (x = x) = True.
Proof. exact (@lem2294470 Prop x). Qed.
Lemma lem2294472 (x : int) (y : int) : ((term52 x y) = (term52 x y)) = True.
Proof. exact (@lem2294471 (term52 x y)). Qed.
Lemma lem2294473 (x : int) (y : int) : ((term52 x y) = (int_gt x y)) = True.
Proof. exact (TRANS (@lem2294468 x y) (@lem2294472 x y)). Qed.
Lemma lem2294474 (x : int) : (term77 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294473 x y)). Qed.
Lemma lem2294475 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294476 (x : int) : (term78 x) = term64.
Proof. exact (MK_COMB (@lem2294475) (@lem2294474 x)). Qed.
Lemma lem2294478 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294479 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294478 int t). Qed.
Lemma lem2294480 : term64 = True.
Proof. exact (@lem2294479 True). Qed.
Lemma lem2294481 (x : int) : (term78 x) = True.
Proof. exact (TRANS (@lem2294476 x) (@lem2294480)). Qed.
Lemma lem2294482 : term79 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294481 x)). Qed.
Lemma lem2294483 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294484 : term80 = term64.
Proof. exact (MK_COMB (@lem2294483) (@lem2294482)). Qed.
Lemma lem2294486 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294487 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294486 int t). Qed.
Lemma lem2294488 : term64 = True.
Proof. exact (@lem2294487 True). Qed.
Lemma lem2294489 : term80 = True.
Proof. exact (TRANS (@lem2294484) (@lem2294488)). Qed.
Lemma lem2294490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294491 : term81 = (and True).
Proof. exact (MK_COMB (@lem2294490) (@lem2294489)). Qed.
Lemma lem2294507 (x : int) (y : int) : (int_le x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2294339 x y) (@lem2294338 x y)). Qed.
Lemma lem2294508 (x : int) (y : int) : (term82 x y) = (term82 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem2294509 (x : int) (y : int) : ((term48 x y) = (int_le x y)) = ((term48 x y) = (term48 x y)).
Proof. exact (MK_COMB (@lem2294508 x y) (@lem2294507 x y)). Qed.
Lemma lem2294511 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294512 (x : Prop) : (x = x) = True.
Proof. exact (@lem2294511 Prop x). Qed.
Lemma lem2294513 (x : int) (y : int) : ((term48 x y) = (term48 x y)) = True.
Proof. exact (@lem2294512 (term48 x y)). Qed.
Lemma lem2294514 (x : int) (y : int) : ((term48 x y) = (int_le x y)) = True.
Proof. exact (TRANS (@lem2294509 x y) (@lem2294513 x y)). Qed.
Lemma lem2294515 (x : int) : (term83 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294514 x y)). Qed.
Lemma lem2294516 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294517 (x : int) : (term84 x) = term64.
Proof. exact (MK_COMB (@lem2294516) (@lem2294515 x)). Qed.
Lemma lem2294519 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294520 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294519 int t). Qed.
Lemma lem2294521 : term64 = True.
Proof. exact (@lem2294520 True). Qed.
Lemma lem2294522 (x : int) : (term84 x) = True.
Proof. exact (TRANS (@lem2294517 x) (@lem2294521)). Qed.
Lemma lem2294523 : term85 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294522 x)). Qed.
Lemma lem2294524 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294525 : term86 = term64.
Proof. exact (MK_COMB (@lem2294524) (@lem2294523)). Qed.
Lemma lem2294527 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294528 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294527 int t). Qed.
Lemma lem2294529 : term64 = True.
Proof. exact (@lem2294528 True). Qed.
Lemma lem2294530 : term86 = True.
Proof. exact (TRANS (@lem2294525) (@lem2294529)). Qed.
Lemma lem2294531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294532 : term87 = (and True).
Proof. exact (MK_COMB (@lem2294531) (@lem2294530)). Qed.
Lemma lem2294548 (x : int) (y : int) : (int_lt x y) = (term44 x y).
Proof. exact (EQ_MP (@lem2294333 x y) (@lem2294332 x y)). Qed.
Lemma lem2294549 (x : int) (y : int) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem2294550 (x : int) (y : int) : ((term44 x y) = (int_lt x y)) = ((term44 x y) = (term44 x y)).
Proof. exact (MK_COMB (@lem2294549 x y) (@lem2294548 x y)). Qed.
Lemma lem2294552 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294553 (x : Prop) : (x = x) = True.
Proof. exact (@lem2294552 Prop x). Qed.
Lemma lem2294554 (x : int) (y : int) : ((term44 x y) = (term44 x y)) = True.
Proof. exact (@lem2294553 (term44 x y)). Qed.
Lemma lem2294555 (x : int) (y : int) : ((term44 x y) = (int_lt x y)) = True.
Proof. exact (TRANS (@lem2294550 x y) (@lem2294554 x y)). Qed.
Lemma lem2294556 (x : int) : (term89 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294555 x y)). Qed.
Lemma lem2294557 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294558 (x : int) : (term90 x) = term64.
Proof. exact (MK_COMB (@lem2294557) (@lem2294556 x)). Qed.
Lemma lem2294560 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294561 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294560 int t). Qed.
Lemma lem2294562 : term64 = True.
Proof. exact (@lem2294561 True). Qed.
Lemma lem2294563 (x : int) : (term90 x) = True.
Proof. exact (TRANS (@lem2294558 x) (@lem2294562)). Qed.
Lemma lem2294564 : term91 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294563 x)). Qed.
Lemma lem2294565 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294566 : term92 = term64.
Proof. exact (MK_COMB (@lem2294565) (@lem2294564)). Qed.
Lemma lem2294568 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294569 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294568 int t). Qed.
Lemma lem2294570 : term64 = True.
Proof. exact (@lem2294569 True). Qed.
Lemma lem2294571 : term92 = True.
Proof. exact (TRANS (@lem2294566) (@lem2294570)). Qed.
Lemma lem2294572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294573 : term93 = (and True).
Proof. exact (MK_COMB (@lem2294572) (@lem2294571)). Qed.
Lemma lem2294589 (x : int) (y : int) : (term31 x y) = (term32 x y).
Proof. exact (EQ_MP (@lem2294306 x y) (@lem2294305 x y)). Qed.
Lemma lem2294590 (x : int) (y : int) : (term94 x y) = (term94 x y).
Proof. exact (eq_refl (term94 x y)). Qed.
Lemma lem2294591 (x : int) (y : int) : ((term32 x y) = (term31 x y)) = ((term32 x y) = (term32 x y)).
Proof. exact (MK_COMB (@lem2294590 x y) (@lem2294589 x y)). Qed.
Lemma lem2294593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294594 (x : real) : (x = x) = True.
Proof. exact (@lem2294593 real x). Qed.
Lemma lem2294595 (x : int) (y : int) : ((term32 x y) = (term32 x y)) = True.
Proof. exact (@lem2294594 (term32 x y)). Qed.
Lemma lem2294596 (x : int) (y : int) : ((term32 x y) = (term31 x y)) = True.
Proof. exact (TRANS (@lem2294591 x y) (@lem2294595 x y)). Qed.
Lemma lem2294597 (x : int) : (term95 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294596 x y)). Qed.
Lemma lem2294598 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294599 (x : int) : (term96 x) = term64.
Proof. exact (MK_COMB (@lem2294598) (@lem2294597 x)). Qed.
Lemma lem2294601 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294602 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294601 int t). Qed.
Lemma lem2294603 : term64 = True.
Proof. exact (@lem2294602 True). Qed.
Lemma lem2294604 (x : int) : (term96 x) = True.
Proof. exact (TRANS (@lem2294599 x) (@lem2294603)). Qed.
Lemma lem2294605 : term97 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294604 x)). Qed.
Lemma lem2294606 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294607 : term98 = term64.
Proof. exact (MK_COMB (@lem2294606) (@lem2294605)). Qed.
Lemma lem2294609 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294610 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294609 int t). Qed.
Lemma lem2294611 : term64 = True.
Proof. exact (@lem2294610 True). Qed.
Lemma lem2294612 : term98 = True.
Proof. exact (TRANS (@lem2294607) (@lem2294611)). Qed.
Lemma lem2294613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294614 : term99 = (and True).
Proof. exact (MK_COMB (@lem2294613) (@lem2294612)). Qed.
Lemma lem2294630 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2294300 x y) (@lem2294299 x y)). Qed.
Lemma lem2294631 (x : int) (y : int) : (term100 x y) = (term100 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem2294632 (x : int) (y : int) : ((term27 x y) = (term26 x y)) = ((term27 x y) = (term27 x y)).
Proof. exact (MK_COMB (@lem2294631 x y) (@lem2294630 x y)). Qed.
Lemma lem2294634 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294635 (x : real) : (x = x) = True.
Proof. exact (@lem2294634 real x). Qed.
Lemma lem2294636 (x : int) (y : int) : ((term27 x y) = (term27 x y)) = True.
Proof. exact (@lem2294635 (term27 x y)). Qed.
Lemma lem2294637 (x : int) (y : int) : ((term27 x y) = (term26 x y)) = True.
Proof. exact (TRANS (@lem2294632 x y) (@lem2294636 x y)). Qed.
Lemma lem2294638 (x : int) : (term101 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294637 x y)). Qed.
Lemma lem2294639 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294640 (x : int) : (term102 x) = term64.
Proof. exact (MK_COMB (@lem2294639) (@lem2294638 x)). Qed.
Lemma lem2294642 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294643 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294642 int t). Qed.
Lemma lem2294644 : term64 = True.
Proof. exact (@lem2294643 True). Qed.
Lemma lem2294645 (x : int) : (term102 x) = True.
Proof. exact (TRANS (@lem2294640 x) (@lem2294644)). Qed.
Lemma lem2294646 : term103 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294645 x)). Qed.
Lemma lem2294647 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294648 : term104 = term64.
Proof. exact (MK_COMB (@lem2294647) (@lem2294646)). Qed.
Lemma lem2294650 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294651 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294650 int t). Qed.
Lemma lem2294652 : term64 = True.
Proof. exact (@lem2294651 True). Qed.
Lemma lem2294653 : term104 = True.
Proof. exact (TRANS (@lem2294648) (@lem2294652)). Qed.
Lemma lem2294654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294655 : term105 = (and True).
Proof. exact (MK_COMB (@lem2294654) (@lem2294653)). Qed.
Lemma lem2294667 (n : nat) : (term40 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2294315 n) (@lem2294314 n)). Qed.
Lemma lem2294668 (n : nat) : (term106 n) = (term106 n).
Proof. exact (eq_refl (term106 n)). Qed.
Lemma lem2294669 (n : nat) : ((real_of_num n) = (term40 n)) = ((real_of_num n) = (real_of_num n)).
Proof. exact (MK_COMB (@lem2294668 n) (@lem2294667 n)). Qed.
Lemma lem2294671 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294672 (x : real) : (x = x) = True.
Proof. exact (@lem2294671 real x). Qed.
Lemma lem2294673 (n : nat) : ((real_of_num n) = (real_of_num n)) = True.
Proof. exact (@lem2294672 (real_of_num n)). Qed.
Lemma lem2294674 (n : nat) : ((real_of_num n) = (term40 n)) = True.
Proof. exact (TRANS (@lem2294669 n) (@lem2294673 n)). Qed.
Lemma lem2294675 : term107 = term108.
Proof. exact (fun_ext (fun n : nat => @lem2294674 n)). Qed.
Lemma lem2294676 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2294677 : term109 = term110.
Proof. exact (MK_COMB (@lem2294676) (@lem2294675)). Qed.
Lemma lem2294679 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294680 (t : Prop) : (term111 t) = t.
Proof. exact (@lem2294679 nat t). Qed.
Lemma lem2294681 : term110 = True.
Proof. exact (@lem2294680 True). Qed.
Lemma lem2294682 : term109 = True.
Proof. exact (TRANS (@lem2294677) (@lem2294681)). Qed.
Lemma lem2294683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294684 : term112 = (and True).
Proof. exact (MK_COMB (@lem2294683) (@lem2294682)). Qed.
Lemma lem2294696 (x : int) : (term37 x) = (term38 x).
Proof. exact (EQ_MP (@lem2294312 x) (@lem2294311 x)). Qed.
Lemma lem2294697 (x : int) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem2294698 (x : int) : ((term38 x) = (term37 x)) = ((term38 x) = (term38 x)).
Proof. exact (MK_COMB (@lem2294697 x) (@lem2294696 x)). Qed.
Lemma lem2294700 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294701 (x : real) : (x = x) = True.
Proof. exact (@lem2294700 real x). Qed.
Lemma lem2294702 (x : int) : ((term38 x) = (term38 x)) = True.
Proof. exact (@lem2294701 (term38 x)). Qed.
Lemma lem2294703 (x : int) : ((term38 x) = (term37 x)) = True.
Proof. exact (TRANS (@lem2294698 x) (@lem2294702 x)). Qed.
Lemma lem2294704 : term114 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294703 x)). Qed.
Lemma lem2294705 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294706 : term115 = term64.
Proof. exact (MK_COMB (@lem2294705) (@lem2294704)). Qed.
Lemma lem2294708 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294709 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294708 int t). Qed.
Lemma lem2294710 : term64 = True.
Proof. exact (@lem2294709 True). Qed.
Lemma lem2294711 : term115 = True.
Proof. exact (TRANS (@lem2294706) (@lem2294710)). Qed.
Lemma lem2294712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294713 : term116 = (and True).
Proof. exact (MK_COMB (@lem2294712) (@lem2294711)). Qed.
Lemma lem2294725 (x : int) : (term34 x) = (term35 x).
Proof. exact (EQ_MP (@lem2294309 x) (@lem2294308 x)). Qed.
Lemma lem2294726 (x : int) : (term117 x) = (term117 x).
Proof. exact (eq_refl (term117 x)). Qed.
Lemma lem2294727 (x : int) : ((term35 x) = (term34 x)) = ((term35 x) = (term35 x)).
Proof. exact (MK_COMB (@lem2294726 x) (@lem2294725 x)). Qed.
Lemma lem2294729 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294730 (x : real) : (x = x) = True.
Proof. exact (@lem2294729 real x). Qed.
Lemma lem2294731 (x : int) : ((term35 x) = (term35 x)) = True.
Proof. exact (@lem2294730 (term35 x)). Qed.
Lemma lem2294732 (x : int) : ((term35 x) = (term34 x)) = True.
Proof. exact (TRANS (@lem2294727 x) (@lem2294731 x)). Qed.
Lemma lem2294733 : term118 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294732 x)). Qed.
Lemma lem2294734 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294735 : term119 = term64.
Proof. exact (MK_COMB (@lem2294734) (@lem2294733)). Qed.
Lemma lem2294737 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294738 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294737 int t). Qed.
Lemma lem2294739 : term64 = True.
Proof. exact (@lem2294738 True). Qed.
Lemma lem2294740 : term119 = True.
Proof. exact (TRANS (@lem2294735) (@lem2294739)). Qed.
Lemma lem2294741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294742 : term120 = (and True).
Proof. exact (MK_COMB (@lem2294741) (@lem2294740)). Qed.
Lemma lem2294758 (x : int) (y : int) : (term31 x y) = (term32 x y).
Proof. exact (EQ_MP (@lem2294306 x y) (@lem2294305 x y)). Qed.
Lemma lem2294759 (x : int) (y : int) : (term94 x y) = (term94 x y).
Proof. exact (eq_refl (term94 x y)). Qed.
Lemma lem2294760 (x : int) (y : int) : ((term32 x y) = (term31 x y)) = ((term32 x y) = (term32 x y)).
Proof. exact (MK_COMB (@lem2294759 x y) (@lem2294758 x y)). Qed.
Lemma lem2294762 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294763 (x : real) : (x = x) = True.
Proof. exact (@lem2294762 real x). Qed.
Lemma lem2294764 (x : int) (y : int) : ((term32 x y) = (term32 x y)) = True.
Proof. exact (@lem2294763 (term32 x y)). Qed.
Lemma lem2294765 (x : int) (y : int) : ((term32 x y) = (term31 x y)) = True.
Proof. exact (TRANS (@lem2294760 x y) (@lem2294764 x y)). Qed.
Lemma lem2294766 (x : int) : (term95 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294765 x y)). Qed.
Lemma lem2294767 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294768 (x : int) : (term96 x) = term64.
Proof. exact (MK_COMB (@lem2294767) (@lem2294766 x)). Qed.
Lemma lem2294770 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294771 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294770 int t). Qed.
Lemma lem2294772 : term64 = True.
Proof. exact (@lem2294771 True). Qed.
Lemma lem2294773 (x : int) : (term96 x) = True.
Proof. exact (TRANS (@lem2294768 x) (@lem2294772)). Qed.
Lemma lem2294774 : term97 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294773 x)). Qed.
Lemma lem2294775 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294776 : term98 = term64.
Proof. exact (MK_COMB (@lem2294775) (@lem2294774)). Qed.
Lemma lem2294778 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294779 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294778 int t). Qed.
Lemma lem2294780 : term64 = True.
Proof. exact (@lem2294779 True). Qed.
Lemma lem2294781 : term98 = True.
Proof. exact (TRANS (@lem2294776) (@lem2294780)). Qed.
Lemma lem2294782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294783 : term99 = (and True).
Proof. exact (MK_COMB (@lem2294782) (@lem2294781)). Qed.
Lemma lem2294799 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2294300 x y) (@lem2294299 x y)). Qed.
Lemma lem2294800 (x : int) (y : int) : (term100 x y) = (term100 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem2294801 (x : int) (y : int) : ((term27 x y) = (term26 x y)) = ((term27 x y) = (term27 x y)).
Proof. exact (MK_COMB (@lem2294800 x y) (@lem2294799 x y)). Qed.
Lemma lem2294803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294804 (x : real) : (x = x) = True.
Proof. exact (@lem2294803 real x). Qed.
Lemma lem2294805 (x : int) (y : int) : ((term27 x y) = (term27 x y)) = True.
Proof. exact (@lem2294804 (term27 x y)). Qed.
Lemma lem2294806 (x : int) (y : int) : ((term27 x y) = (term26 x y)) = True.
Proof. exact (TRANS (@lem2294801 x y) (@lem2294805 x y)). Qed.
Lemma lem2294807 (x : int) : (term101 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294806 x y)). Qed.
Lemma lem2294808 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294809 (x : int) : (term102 x) = term64.
Proof. exact (MK_COMB (@lem2294808) (@lem2294807 x)). Qed.
Lemma lem2294811 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294812 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294811 int t). Qed.
Lemma lem2294813 : term64 = True.
Proof. exact (@lem2294812 True). Qed.
Lemma lem2294814 (x : int) : (term102 x) = True.
Proof. exact (TRANS (@lem2294809 x) (@lem2294813)). Qed.
Lemma lem2294815 : term103 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294814 x)). Qed.
Lemma lem2294816 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294817 : term104 = term64.
Proof. exact (MK_COMB (@lem2294816) (@lem2294815)). Qed.
Lemma lem2294819 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294820 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294819 int t). Qed.
Lemma lem2294821 : term64 = True.
Proof. exact (@lem2294820 True). Qed.
Lemma lem2294822 : term104 = True.
Proof. exact (TRANS (@lem2294817) (@lem2294821)). Qed.
Lemma lem2294823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294824 : term105 = (and True).
Proof. exact (MK_COMB (@lem2294823) (@lem2294822)). Qed.
Lemma lem2294836 (x : int) : (term21 x) = (term22 x).
Proof. exact (EQ_MP (@lem2294294 x) (@lem2294293 x)). Qed.
Lemma lem2294837 (x : int) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem2294838 (x : int) : ((term22 x) = (term21 x)) = ((term22 x) = (term22 x)).
Proof. exact (MK_COMB (@lem2294837 x) (@lem2294836 x)). Qed.
Lemma lem2294840 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294841 (x : real) : (x = x) = True.
Proof. exact (@lem2294840 real x). Qed.
Lemma lem2294842 (x : int) : ((term22 x) = (term22 x)) = True.
Proof. exact (@lem2294841 (term22 x)). Qed.
Lemma lem2294843 (x : int) : ((term22 x) = (term21 x)) = True.
Proof. exact (TRANS (@lem2294838 x) (@lem2294842 x)). Qed.
Lemma lem2294844 : term122 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294843 x)). Qed.
Lemma lem2294845 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294846 : term123 = term64.
Proof. exact (MK_COMB (@lem2294845) (@lem2294844)). Qed.
Lemma lem2294848 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294849 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294848 int t). Qed.
Lemma lem2294850 : term64 = True.
Proof. exact (@lem2294849 True). Qed.
Lemma lem2294851 : term123 = True.
Proof. exact (TRANS (@lem2294846) (@lem2294850)). Qed.
Lemma lem2294852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294853 : term124 = (and True).
Proof. exact (MK_COMB (@lem2294852) (@lem2294851)). Qed.
Lemma lem2294869 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2294291 x y) (@lem2294290 x y)). Qed.
Lemma lem2294870 (x : int) (y : int) : (term125 x y) = (term125 x y).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem2294871 (x : int) (y : int) : ((term19 x y) = (term18 x y)) = ((term19 x y) = (term19 x y)).
Proof. exact (MK_COMB (@lem2294870 x y) (@lem2294869 x y)). Qed.
Lemma lem2294873 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294874 (x : real) : (x = x) = True.
Proof. exact (@lem2294873 real x). Qed.
Lemma lem2294875 (x : int) (y : int) : ((term19 x y) = (term19 x y)) = True.
Proof. exact (@lem2294874 (term19 x y)). Qed.
Lemma lem2294876 (x : int) (y : int) : ((term19 x y) = (term18 x y)) = True.
Proof. exact (TRANS (@lem2294871 x y) (@lem2294875 x y)). Qed.
Lemma lem2294877 (x : int) : (term126 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294876 x y)). Qed.
Lemma lem2294878 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294879 (x : int) : (term127 x) = term64.
Proof. exact (MK_COMB (@lem2294878) (@lem2294877 x)). Qed.
Lemma lem2294881 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294882 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294881 int t). Qed.
Lemma lem2294883 : term64 = True.
Proof. exact (@lem2294882 True). Qed.
Lemma lem2294884 (x : int) : (term127 x) = True.
Proof. exact (TRANS (@lem2294879 x) (@lem2294883)). Qed.
Lemma lem2294885 : term128 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294884 x)). Qed.
Lemma lem2294886 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294887 : term129 = term64.
Proof. exact (MK_COMB (@lem2294886) (@lem2294885)). Qed.
Lemma lem2294889 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294890 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294889 int t). Qed.
Lemma lem2294891 : term64 = True.
Proof. exact (@lem2294890 True). Qed.
Lemma lem2294892 : term129 = True.
Proof. exact (TRANS (@lem2294887) (@lem2294891)). Qed.
Lemma lem2294893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294894 : term130 = (and True).
Proof. exact (MK_COMB (@lem2294893) (@lem2294892)). Qed.
Lemma lem2294910 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2294285 x y) (@lem2294284 x y)). Qed.
Lemma lem2294911 (x : int) (y : int) : (term131 x y) = (term131 x y).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem2294912 (x : int) (y : int) : ((term14 x y) = (term13 x y)) = ((term14 x y) = (term14 x y)).
Proof. exact (MK_COMB (@lem2294911 x y) (@lem2294910 x y)). Qed.
Lemma lem2294914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294915 (x : real) : (x = x) = True.
Proof. exact (@lem2294914 real x). Qed.
Lemma lem2294916 (x : int) (y : int) : ((term14 x y) = (term14 x y)) = True.
Proof. exact (@lem2294915 (term14 x y)). Qed.
Lemma lem2294917 (x : int) (y : int) : ((term14 x y) = (term13 x y)) = True.
Proof. exact (TRANS (@lem2294912 x y) (@lem2294916 x y)). Qed.
Lemma lem2294918 (x : int) : (term132 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294917 x y)). Qed.
Lemma lem2294919 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294920 (x : int) : (term133 x) = term64.
Proof. exact (MK_COMB (@lem2294919) (@lem2294918 x)). Qed.
Lemma lem2294922 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294923 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294922 int t). Qed.
Lemma lem2294924 : term64 = True.
Proof. exact (@lem2294923 True). Qed.
Lemma lem2294925 (x : int) : (term133 x) = True.
Proof. exact (TRANS (@lem2294920 x) (@lem2294924)). Qed.
Lemma lem2294926 : term134 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294925 x)). Qed.
Lemma lem2294927 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294928 : term135 = term64.
Proof. exact (MK_COMB (@lem2294927) (@lem2294926)). Qed.
Lemma lem2294930 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294931 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294930 int t). Qed.
Lemma lem2294932 : term64 = True.
Proof. exact (@lem2294931 True). Qed.
Lemma lem2294933 : term135 = True.
Proof. exact (TRANS (@lem2294928) (@lem2294932)). Qed.
Lemma lem2294934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294935 : term136 = (and True).
Proof. exact (MK_COMB (@lem2294934) (@lem2294933)). Qed.
Lemma lem2294951 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2294279 x y) (@lem2294278 x y)). Qed.
Lemma lem2294952 (x : int) (y : int) : (term137 x y) = (term137 x y).
Proof. exact (eq_refl (term137 x y)). Qed.
Lemma lem2294953 (x : int) (y : int) : ((term9 x y) = (term8 x y)) = ((term9 x y) = (term9 x y)).
Proof. exact (MK_COMB (@lem2294952 x y) (@lem2294951 x y)). Qed.
Lemma lem2294955 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294956 (x : real) : (x = x) = True.
Proof. exact (@lem2294955 real x). Qed.
Lemma lem2294957 (x : int) (y : int) : ((term9 x y) = (term9 x y)) = True.
Proof. exact (@lem2294956 (term9 x y)). Qed.
Lemma lem2294958 (x : int) (y : int) : ((term9 x y) = (term8 x y)) = True.
Proof. exact (TRANS (@lem2294953 x y) (@lem2294957 x y)). Qed.
Lemma lem2294959 (x : int) : (term138 x) = term62.
Proof. exact (fun_ext (fun y : int => @lem2294958 x y)). Qed.
Lemma lem2294960 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294961 (x : int) : (term139 x) = term64.
Proof. exact (MK_COMB (@lem2294960) (@lem2294959 x)). Qed.
Lemma lem2294963 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294964 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294963 int t). Qed.
Lemma lem2294965 : term64 = True.
Proof. exact (@lem2294964 True). Qed.
Lemma lem2294966 (x : int) : (term139 x) = True.
Proof. exact (TRANS (@lem2294961 x) (@lem2294965)). Qed.
Lemma lem2294967 : term140 = term62.
Proof. exact (fun_ext (fun x : int => @lem2294966 x)). Qed.
Lemma lem2294968 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294969 : term141 = term64.
Proof. exact (MK_COMB (@lem2294968) (@lem2294967)). Qed.
Lemma lem2294971 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2294972 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2294971 int t). Qed.
Lemma lem2294973 : term64 = True.
Proof. exact (@lem2294972 True). Qed.
Lemma lem2294974 : term141 = True.
Proof. exact (TRANS (@lem2294969) (@lem2294973)). Qed.
Lemma lem2294975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294976 : term142 = (and True).
Proof. exact (MK_COMB (@lem2294975) (@lem2294974)). Qed.
Lemma lem2294990 (x : int) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem2294273 x n) (@lem2294272 x n)). Qed.
Lemma lem2294991 (x : int) (n : nat) : (term143 x n) = (term143 x n).
Proof. exact (eq_refl (term143 x n)). Qed.
Lemma lem2294992 (x : int) (n : nat) : ((term4 x n) = (term3 x n)) = ((term4 x n) = (term4 x n)).
Proof. exact (MK_COMB (@lem2294991 x n) (@lem2294990 x n)). Qed.
Lemma lem2294994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294995 (x : real) : (x = x) = True.
Proof. exact (@lem2294994 real x). Qed.
Lemma lem2294996 (x : int) (n : nat) : ((term4 x n) = (term4 x n)) = True.
Proof. exact (@lem2294995 (term4 x n)). Qed.
Lemma lem2294997 (x : int) (n : nat) : ((term4 x n) = (term3 x n)) = True.
Proof. exact (TRANS (@lem2294992 x n) (@lem2294996 x n)). Qed.
Lemma lem2294998 (x : int) : (term144 x) = term108.
Proof. exact (fun_ext (fun n : nat => @lem2294997 x n)). Qed.
Lemma lem2294999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2295000 (x : int) : (term145 x) = term110.
Proof. exact (MK_COMB (@lem2294999) (@lem2294998 x)). Qed.
Lemma lem2295002 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2295003 (t : Prop) : (term111 t) = t.
Proof. exact (@lem2295002 nat t). Qed.
Lemma lem2295004 : term110 = True.
Proof. exact (@lem2295003 True). Qed.
Lemma lem2295005 (x : int) : (term145 x) = True.
Proof. exact (TRANS (@lem2295000 x) (@lem2295004)). Qed.
Lemma lem2295006 : term146 = term62.
Proof. exact (fun_ext (fun x : int => @lem2295005 x)). Qed.
Lemma lem2295007 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2295008 : term147 = term64.
Proof. exact (MK_COMB (@lem2295007) (@lem2295006)). Qed.
Lemma lem2295010 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2295011 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2295010 int t). Qed.
Lemma lem2295012 : term64 = True.
Proof. exact (@lem2295011 True). Qed.
Lemma lem2295013 : term147 = True.
Proof. exact (TRANS (@lem2295008) (@lem2295012)). Qed.
Lemma lem2295014 : term148 = (True /\ True).
Proof. exact (MK_COMB (@lem2294976) (@lem2295013)). Qed.
Lemma lem2295016 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295017 : (True /\ True) = True.
Proof. exact (@lem2295016 True). Qed.
Lemma lem2295018 : term148 = True.
Proof. exact (TRANS (@lem2295014) (@lem2295017)). Qed.
Lemma lem2295019 : term149 = (True /\ True).
Proof. exact (MK_COMB (@lem2294935) (@lem2295018)). Qed.
Lemma lem2295021 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295022 : (True /\ True) = True.
Proof. exact (@lem2295021 True). Qed.
Lemma lem2295023 : term149 = True.
Proof. exact (TRANS (@lem2295019) (@lem2295022)). Qed.
Lemma lem2295024 : term150 = (True /\ True).
Proof. exact (MK_COMB (@lem2294894) (@lem2295023)). Qed.
Lemma lem2295026 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295027 : (True /\ True) = True.
Proof. exact (@lem2295026 True). Qed.
Lemma lem2295028 : term150 = True.
Proof. exact (TRANS (@lem2295024) (@lem2295027)). Qed.
Lemma lem2295029 : term151 = (True /\ True).
Proof. exact (MK_COMB (@lem2294853) (@lem2295028)). Qed.
Lemma lem2295031 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295032 : (True /\ True) = True.
Proof. exact (@lem2295031 True). Qed.
Lemma lem2295033 : term151 = True.
Proof. exact (TRANS (@lem2295029) (@lem2295032)). Qed.
Lemma lem2295034 : term152 = (True /\ True).
Proof. exact (MK_COMB (@lem2294824) (@lem2295033)). Qed.
Lemma lem2295036 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295037 : (True /\ True) = True.
Proof. exact (@lem2295036 True). Qed.
Lemma lem2295038 : term152 = True.
Proof. exact (TRANS (@lem2295034) (@lem2295037)). Qed.
Lemma lem2295039 : term153 = (True /\ True).
Proof. exact (MK_COMB (@lem2294783) (@lem2295038)). Qed.
Lemma lem2295041 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295042 : (True /\ True) = True.
Proof. exact (@lem2295041 True). Qed.
Lemma lem2295043 : term153 = True.
Proof. exact (TRANS (@lem2295039) (@lem2295042)). Qed.
Lemma lem2295044 : term154 = (True /\ True).
Proof. exact (MK_COMB (@lem2294742) (@lem2295043)). Qed.
Lemma lem2295046 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295047 : (True /\ True) = True.
Proof. exact (@lem2295046 True). Qed.
Lemma lem2295048 : term154 = True.
Proof. exact (TRANS (@lem2295044) (@lem2295047)). Qed.
Lemma lem2295049 : term155 = (True /\ True).
Proof. exact (MK_COMB (@lem2294713) (@lem2295048)). Qed.
Lemma lem2295051 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295052 : (True /\ True) = True.
Proof. exact (@lem2295051 True). Qed.
Lemma lem2295053 : term155 = True.
Proof. exact (TRANS (@lem2295049) (@lem2295052)). Qed.
Lemma lem2295054 : term156 = (True /\ True).
Proof. exact (MK_COMB (@lem2294684) (@lem2295053)). Qed.
Lemma lem2295056 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295057 : (True /\ True) = True.
Proof. exact (@lem2295056 True). Qed.
Lemma lem2295058 : term156 = True.
Proof. exact (TRANS (@lem2295054) (@lem2295057)). Qed.
Lemma lem2295059 : term157 = (True /\ True).
Proof. exact (MK_COMB (@lem2294655) (@lem2295058)). Qed.
Lemma lem2295061 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295062 : (True /\ True) = True.
Proof. exact (@lem2295061 True). Qed.
Lemma lem2295063 : term157 = True.
Proof. exact (TRANS (@lem2295059) (@lem2295062)). Qed.
Lemma lem2295064 : term158 = (True /\ True).
Proof. exact (MK_COMB (@lem2294614) (@lem2295063)). Qed.
Lemma lem2295066 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295067 : (True /\ True) = True.
Proof. exact (@lem2295066 True). Qed.
Lemma lem2295068 : term158 = True.
Proof. exact (TRANS (@lem2295064) (@lem2295067)). Qed.
Lemma lem2295069 : term159 = (True /\ True).
Proof. exact (MK_COMB (@lem2294573) (@lem2295068)). Qed.
Lemma lem2295071 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295072 : (True /\ True) = True.
Proof. exact (@lem2295071 True). Qed.
Lemma lem2295073 : term159 = True.
Proof. exact (TRANS (@lem2295069) (@lem2295072)). Qed.
Lemma lem2295074 : term160 = (True /\ True).
Proof. exact (MK_COMB (@lem2294532) (@lem2295073)). Qed.
Lemma lem2295076 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295077 : (True /\ True) = True.
Proof. exact (@lem2295076 True). Qed.
Lemma lem2295078 : term160 = True.
Proof. exact (TRANS (@lem2295074) (@lem2295077)). Qed.
Lemma lem2295079 : term161 = (True /\ True).
Proof. exact (MK_COMB (@lem2294491) (@lem2295078)). Qed.
Lemma lem2295081 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295082 : (True /\ True) = True.
Proof. exact (@lem2295081 True). Qed.
Lemma lem2295083 : term161 = True.
Proof. exact (TRANS (@lem2295079) (@lem2295082)). Qed.
Lemma lem2295084 : term162 = (True /\ True).
Proof. exact (MK_COMB (@lem2294450) (@lem2295083)). Qed.
Lemma lem2295086 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295087 : (True /\ True) = True.
Proof. exact (@lem2295086 True). Qed.
Lemma lem2295088 : term162 = True.
Proof. exact (TRANS (@lem2295084) (@lem2295087)). Qed.
Lemma lem2295089 : term163 = (True /\ True).
Proof. exact (MK_COMB (@lem2294409) (@lem2295088)). Qed.
Lemma lem2295091 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2295092 : (True /\ True) = True.
Proof. exact (@lem2295091 True). Qed.
Lemma lem2295093 : term163 = True.
Proof. exact (TRANS (@lem2295089) (@lem2295092)). Qed.
Lemma lem2295094 : True = term163.
Proof. exact (SYM (@lem2295093)). Qed.
Lemma lem2295095 : term163.
Proof. exact (EQ_MP (@lem2295094) (@lem0)). Qed.
