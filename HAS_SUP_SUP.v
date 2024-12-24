Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SUP_SUP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUP_spec.
Require Import SUP_UNIQUE_spec.
Require Import has_sup_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982759_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5295265 (s : real -> Prop) : term0 s.
Proof. exact (@lem5136700 s). Qed.
Lemma lem5295266 (s : real -> Prop) : (term0 s) = (term1 s).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5295267 (s : real -> Prop) : term1 s.
Proof. exact (EQ_MP (@lem5295266 s) (@lem5295265 s)). Qed.
Lemma lem5295268 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem5295269 (s : real -> Prop) (h1 : term2) : term3 s.
Proof. exact (@lem5295268 h1 s). Qed.
Lemma lem5295270 (s : real -> Prop) : (term3 s) = (term4 s).
Proof. exact (eq_refl (term3 s)). Qed.
Lemma lem5295271 (s : real -> Prop) (h1 : term2) : term4 s.
Proof. exact (EQ_MP (@lem5295270 s) (@lem5295269 s h1)). Qed.
Lemma lem5295272 (s : real -> Prop) (b : real) (h1 : term2) : term5 s b.
Proof. exact (@lem5295271 s h1 b). Qed.
Lemma lem5295273 (s : real -> Prop) (b : real) : (term5 s b) = (term6 s b).
Proof. exact (eq_refl (term5 s b)). Qed.
Lemma lem5295274 (s : real -> Prop) (b : real) (h1 : term2) : term6 s b.
Proof. exact (EQ_MP (@lem5295273 s b) (@lem5295272 s b h1)). Qed.
Lemma lem5295275 (s : real -> Prop) (b : real) (h1 : term7 s b) : term7 s b.
Proof. exact (h1). Qed.
Lemma lem5295276 (s : real -> Prop) (b : real) (h1 : term2) (h2 : term7 s b) : (sup s) = b.
Proof. exact (@lem5295274 s b h1 (@lem5295275 s b h2)). Qed.
Lemma lem5295277 (s : real -> Prop) (b : real) (h1 : term7 s b) : term8 s b.
Proof. exact (fun h0 : term2 => @lem5295276 s b h0 h1). Qed.
Lemma lem5295278 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem5295279 (s : real -> Prop) (b : real) (h1 : term2) (h2 : term7 s b) : (sup s) = b.
Proof. exact (@lem5295277 s b h2 (@lem5295278 h1)). Qed.
Lemma lem5295280 (s : real -> Prop) (b : real) (h1 : term2) : term6 s b.
Proof. exact (fun h0 : term7 s b => @lem5295279 s b h1 h0). Qed.
Lemma lem5295281 (s : real -> Prop) (h1 : term2) : term4 s.
Proof. exact (fun b : real => @lem5295280 s b h1). Qed.
Lemma lem5295282 (h1 : term2) : term2.
Proof. exact (fun s : real -> Prop => @lem5295281 s h1). Qed.
Lemma lem5295283 : term9.
Proof. exact (fun h0 : term2 => @lem5295282 h0). Qed.
Lemma lem5295284 : term2.
Proof. exact (@lem5295283 (@lem5190240)). Qed.
Lemma lem5295285 (s : real -> Prop) : term3 s.
Proof. exact (@lem5295284 s). Qed.
Lemma lem5295286 (s : real -> Prop) : (term3 s) = (term4 s).
Proof. exact (eq_refl (term3 s)). Qed.
Lemma lem5295287 (s : real -> Prop) : term4 s.
Proof. exact (EQ_MP (@lem5295286 s) (@lem5295285 s)). Qed.
Lemma lem5295288 (s : real -> Prop) (b : real) : term5 s b.
Proof. exact (@lem5295287 s b). Qed.
Lemma lem5295289 (s : real -> Prop) (b : real) : (term5 s b) = (term6 s b).
Proof. exact (eq_refl (term5 s b)). Qed.
Lemma lem5295301 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem5295302 {A : Type'} (P : A -> Prop) : (term10 A P) = ((term11 A P) = (term12 A P)).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem5295304 {A : Type'} (x : A) : term13 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5295305 {A : Type'} (x : A) : (term13 A x) = (term14 A x).
Proof. exact (eq_refl (term13 A x)). Qed.
Lemma lem5295306 {A : Type'} (x : A) : term14 A x.
Proof. exact (EQ_MP (@lem5295305 A x) (@lem5295304 A x)). Qed.
Lemma lem5295307 {A : Type'} (x : A) : term15 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5295309 (s : real -> Prop) : term16 s.
Proof. exact (@lem5291214 s). Qed.
Lemma lem5295310 (s : real -> Prop) : (term16 s) = (term17 s).
Proof. exact (eq_refl (term16 s)). Qed.
Lemma lem5295311 (s : real -> Prop) : term17 s.
Proof. exact (EQ_MP (@lem5295310 s) (@lem5295309 s)). Qed.
Lemma lem5295312 (s : real -> Prop) (b : real) : term18 s b.
Proof. exact (@lem5295311 s b). Qed.
Lemma lem5295313 (s : real -> Prop) (b : real) : (term18 s b) = ((has_sup s b) = (term7 s b)).
Proof. exact (eq_refl (term18 s b)). Qed.
Lemma lem5295318 (s : real -> Prop) (b : real) : (has_sup s b) = (term7 s b).
Proof. exact (EQ_MP (@lem5295313 s b) (@lem5295312 s b)). Qed.
Lemma lem5295319 (s : real -> Prop) (l : real) : (has_sup s l) = (term7 s l).
Proof. exact (@lem5295318 s l). Qed.
Lemma lem5295332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5295333 (s : real -> Prop) (l : real) : (term19 s l) = (term20 s l).
Proof. exact (MK_COMB (@lem5295332) (@lem5295319 s l)). Qed.
Lemma lem5295352 (s : real -> Prop) (l : real) : (term21 s l) = (term21 s l).
Proof. exact (eq_refl (term21 s l)). Qed.
Lemma lem5295353 (s : real -> Prop) (l : real) : ((has_sup s l) = (term21 s l)) = ((term7 s l) = (term21 s l)).
Proof. exact (MK_COMB (@lem5295333 s l) (@lem5295352 s l)). Qed.
Lemma lem5295356 (s : real -> Prop) (l : real) : ((term7 s l) = (term21 s l)) = ((has_sup s l) = (term21 s l)).
Proof. exact (SYM (@lem5295353 s l)). Qed.
Lemma lem5295357 (s : real -> Prop) (l : real) (h1 : term7 s l) : term7 s l.
Proof. exact (h1). Qed.
Lemma lem5295358 (s : real -> Prop) (l : real) (h1 : term21 s l) : term21 s l.
Proof. exact (h1). Qed.
Lemma lem5295359 (s : real -> Prop) (l : real) (h1 : term22 s l) : term22 s l.
Proof. exact (h1). Qed.
Lemma lem5295360 (s : real -> Prop) (h1 : term23 s) : term23 s.
Proof. exact (h1). Qed.
Lemma lem5295361 (s : real -> Prop) (l : real) (h1 : (sup s) = l) : (sup s) = l.
Proof. exact (h1). Qed.
Lemma lem5295362 (s : real -> Prop) (h1 : term24 s) : term24 s.
Proof. exact (h1). Qed.
Lemma lem5295363 (s : real -> Prop) (b : real) (h1 : term25 s b) : term25 s b.
Proof. exact (h1). Qed.
Lemma lem5295364 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5295379 (l : real) : (term26 l) = (term26 l).
Proof. exact (eq_refl (term26 l)). Qed.
Lemma lem5295380 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term27 l s) = (term28 l).
Proof. exact (MK_COMB (@lem5295379 l) (@lem5295364 s h1)). Qed.
Lemma lem5295381 (l : real) : (term28 l) = (term29 l).
Proof. exact (eq_refl (term28 l)). Qed.
Lemma lem5295382 (l : real) (s : real -> Prop) : (term30 l s) = (term30 l s).
Proof. exact (eq_refl (term30 l s)). Qed.
Lemma lem5295383 (s : real -> Prop) (l : real) : ((term27 l s) = (term28 l)) = ((term27 l s) = (term29 l)).
Proof. exact (MK_COMB (@lem5295382 l s) (@lem5295381 l)). Qed.
Lemma lem5295384 (s : real -> Prop) (l : real) : (term27 l s) = (term7 s l).
Proof. exact (eq_refl (term27 l s)). Qed.
Lemma lem5295385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5295386 (s : real -> Prop) (l : real) : (term30 l s) = (term20 s l).
Proof. exact (MK_COMB (@lem5295385) (@lem5295384 s l)). Qed.
Lemma lem5295387 (l : real) : (term29 l) = (term29 l).
Proof. exact (eq_refl (term29 l)). Qed.
Lemma lem5295388 (s : real -> Prop) (l : real) : ((term27 l s) = (term29 l)) = ((term7 s l) = (term29 l)).
Proof. exact (MK_COMB (@lem5295386 s l) (@lem5295387 l)). Qed.
Lemma lem5295389 (s : real -> Prop) (l : real) : ((term27 l s) = (term28 l)) = ((term7 s l) = (term29 l)).
Proof. exact (TRANS (@lem5295383 s l) (@lem5295388 s l)). Qed.
Lemma lem5295390 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term7 s l) = (term29 l).
Proof. exact (EQ_MP (@lem5295389 s l) (@lem5295380 l s h1)). Qed.
Lemma lem5295391 (l : real) (s : real -> Prop) (h1 : term7 s l) (h2 : s = (@EMPTY real)) : term29 l.
Proof. exact (EQ_MP (@lem5295390 l s h2) (@lem5295357 s l h1)). Qed.
Lemma lem5295393 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5295394 (l : real) : (term31 l) = (term32 l).
Proof. exact (@lem5295393 (term29 l)). Qed.
Lemma lem5295396 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem5295302 A P) (@lem5295301 A P)). Qed.
Lemma lem5295397 (P : real -> Prop) : (term33 P) = (term34 P).
Proof. exact (@lem5295396 real P). Qed.
Lemma lem5295398 (l : real) : (term35 l) = (term36 l).
Proof. exact (@lem5295397 (term37 l)). Qed.
Lemma lem5295399 (l : real) (c : real) : (term38 l c) = ((term39 c) = (real_le l c)).
Proof. exact (eq_refl (term38 l c)). Qed.
Lemma lem5295400 (l : real) : (term40 l) = (term37 l).
Proof. exact (fun_ext (fun c : real => @lem5295399 l c)). Qed.
Lemma lem5295401 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295402 (l : real) : (term41 l) = (term29 l).
Proof. exact (MK_COMB (@lem5295401) (@lem5295400 l)). Qed.
Lemma lem5295403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5295404 (l : real) : (term35 l) = (term32 l).
Proof. exact (MK_COMB (@lem5295403) (@lem5295402 l)). Qed.
Lemma lem5295405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5295406 (l : real) : (term42 l) = (term43 l).
Proof. exact (MK_COMB (@lem5295405) (@lem5295404 l)). Qed.
Lemma lem5295407 (l : real) (c : real) : (term38 l c) = ((term39 c) = (real_le l c)).
Proof. exact (eq_refl (term38 l c)). Qed.
Lemma lem5295408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5295409 (l : real) (c : real) : (term44 l c) = (term45 l c).
Proof. exact (MK_COMB (@lem5295408) (@lem5295407 l c)). Qed.
Lemma lem5295410 (l : real) : (term46 l) = (term47 l).
Proof. exact (fun_ext (fun c : real => @lem5295409 l c)). Qed.
Lemma lem5295411 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5295412 (l : real) : (term36 l) = (term48 l).
Proof. exact (MK_COMB (@lem5295411) (@lem5295410 l)). Qed.
Lemma lem5295413 (l : real) : ((term35 l) = (term36 l)) = ((term32 l) = (term48 l)).
Proof. exact (MK_COMB (@lem5295406 l) (@lem5295412 l)). Qed.
Lemma lem5295414 (l : real) : (term32 l) = (term48 l).
Proof. exact (EQ_MP (@lem5295413 l) (@lem5295398 l)). Qed.
Lemma lem5295419 (l : real) : (term31 l) = (term48 l).
Proof. exact (TRANS (@lem5295394 l) (@lem5295414 l)). Qed.
Lemma lem5295429 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5295307 A x (@lem5295306 A x)). Qed.
Lemma lem5295430 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5295429 real x). Qed.
Lemma lem5295431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5295432 (x : real) : (term49 x) = (imp False).
Proof. exact (MK_COMB (@lem5295431) (@lem5295430 x)). Qed.
Lemma lem5295433 (x : real) (c : real) : (real_le x c) = (real_le x c).
Proof. exact (eq_refl (real_le x c)). Qed.
Lemma lem5295434 (x : real) (c : real) : (term50 x c) = (term51 x c).
Proof. exact (MK_COMB (@lem5295432 x) (@lem5295433 x c)). Qed.
Lemma lem5295436 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5295437 (x : real) (c : real) : (term51 x c) = True.
Proof. exact (@lem5295436 (real_le x c)). Qed.
Lemma lem5295438 (x : real) (c : real) : (term50 x c) = True.
Proof. exact (TRANS (@lem5295434 x c) (@lem5295437 x c)). Qed.
Lemma lem5295439 (c : real) : (term52 c) = term53.
Proof. exact (fun_ext (fun x : real => @lem5295438 x c)). Qed.
Lemma lem5295440 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295441 (c : real) : (term39 c) = term54.
Proof. exact (MK_COMB (@lem5295440) (@lem5295439 c)). Qed.
Lemma lem5295443 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5295444 (t : Prop) : (term56 t) = t.
Proof. exact (@lem5295443 real t). Qed.
Lemma lem5295445 : term54 = True.
Proof. exact (@lem5295444 True). Qed.
Lemma lem5295446 (c : real) : (term39 c) = True.
Proof. exact (TRANS (@lem5295441 c) (@lem5295445)). Qed.
Lemma lem5295447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5295448 (c : real) : (term57 c) = (@eq Prop True).
Proof. exact (MK_COMB (@lem5295447) (@lem5295446 c)). Qed.
Lemma lem5295449 (l : real) (c : real) : (real_le l c) = (real_le l c).
Proof. exact (eq_refl (real_le l c)). Qed.
Lemma lem5295450 (l : real) (c : real) : ((term39 c) = (real_le l c)) = (True = (real_le l c)).
Proof. exact (MK_COMB (@lem5295448 c) (@lem5295449 l c)). Qed.
Lemma lem5295452 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem5295453 (l : real) (c : real) : (True = (real_le l c)) = (real_le l c).
Proof. exact (@lem5295452 (real_le l c)). Qed.
Lemma lem5295454 (l : real) (c : real) : ((term39 c) = (real_le l c)) = (real_le l c).
Proof. exact (TRANS (@lem5295450 l c) (@lem5295453 l c)). Qed.
Lemma lem5295455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5295456 (l : real) (c : real) : (term45 l c) = (term58 l c).
Proof. exact (MK_COMB (@lem5295455) (@lem5295454 l c)). Qed.
Lemma lem5295457 (l : real) : (term47 l) = (term59 l).
Proof. exact (fun_ext (fun c : real => @lem5295456 l c)). Qed.
Lemma lem5295458 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5295459 (l : real) : (term48 l) = (term60 l).
Proof. exact (MK_COMB (@lem5295458) (@lem5295457 l)). Qed.
Lemma lem5295464 (l : real) : (term31 l) = (term60 l).
Proof. exact (TRANS (@lem5295419 l) (@lem5295459 l)). Qed.
Lemma lem5295465 (l : real) : (term60 l) = (term31 l).
Proof. exact (SYM (@lem5295464 l)). Qed.
Lemma lem5295469 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5295475 (l : real) : (term62 l) = (term63 l).
Proof. exact (@lem5295469 (term63 l)). Qed.
Lemma lem5295476 (l : real) : (term63 l) = (term64 l).
Proof. exact (@lem1988287 (term65 l) l). Qed.
Lemma lem5295477 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5295483 (l : real) : (term65 l) = (term66 l).
Proof. exact (@lem1982792 l term67). Qed.
Lemma lem5295485 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5295486 : term67 = term69.
Proof. exact (@lem5295485 term70). Qed.
Lemma lem5295488 (x : nat) : (term71 x) = (term72 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5295489 : term73 = term74.
Proof. exact (@lem5295488 term70). Qed.
Lemma lem5295490 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5295491 : term75 = term76.
Proof. exact (MK_COMB (@lem5295490) (@lem5295489)). Qed.
Lemma lem5295492 : term77 = term78.
Proof. exact (MK_COMB (@lem5295491) (@lem5295486)). Qed.
Lemma lem5295493 : term78 = term79.
Proof. exact (@lem1981613 term73 term67 term67 term67). Qed.
Lemma lem5295495 (m : nat) (n : nat) : (term80 m n) = (term81 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5295496 : term82 = term83.
Proof. exact (@lem5295495 term70 term70). Qed.
Lemma lem5295497 : (term84 = (BIT1 0)) = (term85 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5295498 : term85 = term70.
Proof. exact (EQ_MP (@lem5295497) (@lem940073)). Qed.
Lemma lem5295499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5295500 : term83 = term67.
Proof. exact (MK_COMB (@lem5295499) (@lem5295498)). Qed.
Lemma lem5295501 : term82 = term67.
Proof. exact (TRANS (@lem5295496) (@lem5295500)). Qed.
Lemma lem5295503 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5295504 : term77 = term88.
Proof. exact (@lem5295503 term70 term70). Qed.
Lemma lem5295505 : (term84 = (BIT1 0)) = (term85 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5295506 : term85 = term70.
Proof. exact (EQ_MP (@lem5295505) (@lem940073)). Qed.
Lemma lem5295507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5295508 : term83 = term67.
Proof. exact (MK_COMB (@lem5295507) (@lem5295506)). Qed.
Lemma lem5295509 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5295510 : term88 = term73.
Proof. exact (MK_COMB (@lem5295509) (@lem5295508)). Qed.
Lemma lem5295511 : term77 = term73.
Proof. exact (TRANS (@lem5295504) (@lem5295510)). Qed.
Lemma lem5295512 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5295513 : term89 = term90.
Proof. exact (MK_COMB (@lem5295512) (@lem5295511)). Qed.
Lemma lem5295514 : term79 = term74.
Proof. exact (MK_COMB (@lem5295513) (@lem5295501)). Qed.
Lemma lem5295515 : term78 = term74.
Proof. exact (TRANS (@lem5295493) (@lem5295514)). Qed.
Lemma lem5295516 : term77 = term74.
Proof. exact (TRANS (@lem5295492) (@lem5295515)). Qed.
Lemma lem5295518 (x : real) : (term91 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5295519 : term74 = term73.
Proof. exact (@lem5295518 term73). Qed.
Lemma lem5295520 : term77 = term73.
Proof. exact (TRANS (@lem5295516) (@lem5295519)). Qed.
Lemma lem5295521 (l : real) : (real_add l) = (real_add l).
Proof. exact (eq_refl (real_add l)). Qed.
Lemma lem5295524 (l : real) : (term66 l) = (term92 l).
Proof. exact (MK_COMB (@lem5295521 l) (@lem5295520)). Qed.
Lemma lem5295526 (l : real) : (term65 l) = (term92 l).
Proof. exact (TRANS (@lem5295483 l) (@lem5295524 l)). Qed.
Lemma lem5295527 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5295528 (l : real) : (term93 l) = (term94 l).
Proof. exact (MK_COMB (@lem5295527) (@lem5295526 l)). Qed.
Lemma lem5295529 (l : real) : (term95 l) = (term96 l).
Proof. exact (MK_COMB (@lem5295528 l) (@lem5295477 l)). Qed.
Lemma lem5295530 (l : real) : (term96 l) = (term97 l).
Proof. exact (@lem1982792 (term92 l) l). Qed.
Lemma lem5295534 (l : real) : (term97 l) = (term98 l).
Proof. exact (@lem1982759 l (term99 l) term73). Qed.
Lemma lem5295535 (l : real) : (term100 l) = (term101 l).
Proof. exact (@lem1982715 term73 l). Qed.
Lemma lem5295537 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5295538 : term67 = term69.
Proof. exact (@lem5295537 term70). Qed.
Lemma lem5295540 (x : nat) : (term71 x) = (term72 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5295541 : term73 = term74.
Proof. exact (@lem5295540 term70). Qed.
Lemma lem5295542 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5295543 : term102 = term103.
Proof. exact (MK_COMB (@lem5295542) (@lem5295541)). Qed.
Lemma lem5295544 : term104 = term105.
Proof. exact (MK_COMB (@lem5295543) (@lem5295538)). Qed.
Lemma lem5295545 : term106.
Proof. exact (@lem1981473 term73 term67 term67 term67 term107 term67). Qed.
Lemma lem5295547 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5295548 : term109 = term110.
Proof. exact (@lem5295547 (NUMERAL 0) term70). Qed.
Lemma lem5295549 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5295550 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5295551 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5295550 h1) (fun h1 : term110 = True => @lem5295549)). Qed.
Lemma lem5295552 : term110 = True.
Proof. exact (EQ_MP (@lem5295551) (@lem5295549)). Qed.
Lemma lem5295553 : term109 = True.
Proof. exact (TRANS (@lem5295548) (@lem5295552)). Qed.
Lemma lem5295554 : True = term109.
Proof. exact (SYM (@lem5295553)). Qed.
Lemma lem5295555 : term109.
Proof. exact (EQ_MP (@lem5295554) (@lem0)). Qed.
Lemma lem5295556 : term112.
Proof. exact (@lem5295545 (@lem5295555)). Qed.
Lemma lem5295558 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5295559 : term109 = term110.
Proof. exact (@lem5295558 (NUMERAL 0) term70). Qed.
Lemma lem5295560 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5295561 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5295562 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5295561 h1) (fun h1 : term110 = True => @lem5295560)). Qed.
Lemma lem5295563 : term110 = True.
Proof. exact (EQ_MP (@lem5295562) (@lem5295560)). Qed.
Lemma lem5295564 : term109 = True.
Proof. exact (TRANS (@lem5295559) (@lem5295563)). Qed.
Lemma lem5295565 : True = term109.
Proof. exact (SYM (@lem5295564)). Qed.
Lemma lem5295566 : term109.
Proof. exact (EQ_MP (@lem5295565) (@lem0)). Qed.
Lemma lem5295567 : term113.
Proof. exact (@lem5295556 (@lem5295566)). Qed.
Lemma lem5295569 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5295570 : term109 = term110.
Proof. exact (@lem5295569 (NUMERAL 0) term70). Qed.
Lemma lem5295571 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5295572 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5295573 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5295572 h1) (fun h1 : term110 = True => @lem5295571)). Qed.
Lemma lem5295574 : term110 = True.
Proof. exact (EQ_MP (@lem5295573) (@lem5295571)). Qed.
Lemma lem5295575 : term109 = True.
Proof. exact (TRANS (@lem5295570) (@lem5295574)). Qed.
Lemma lem5295576 : True = term109.
Proof. exact (SYM (@lem5295575)). Qed.
Lemma lem5295577 : term109.
Proof. exact (EQ_MP (@lem5295576) (@lem0)). Qed.
Lemma lem5295578 : term114.
Proof. exact (@lem5295567 (@lem5295577)). Qed.
Lemma lem5295580 (m : nat) (n : nat) : (term80 m n) = (term81 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5295581 : term82 = term83.
Proof. exact (@lem5295580 term70 term70). Qed.
Lemma lem5295582 : (term84 = (BIT1 0)) = (term85 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5295583 : term85 = term70.
Proof. exact (EQ_MP (@lem5295582) (@lem940073)). Qed.
Lemma lem5295584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5295585 : term83 = term67.
Proof. exact (MK_COMB (@lem5295584) (@lem5295583)). Qed.
Lemma lem5295586 : term82 = term67.
Proof. exact (TRANS (@lem5295581) (@lem5295585)). Qed.
Lemma lem5295588 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5295589 : term77 = term88.
Proof. exact (@lem5295588 term70 term70). Qed.
Lemma lem5295590 : (term84 = (BIT1 0)) = (term85 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5295591 : term85 = term70.
Proof. exact (EQ_MP (@lem5295590) (@lem940073)). Qed.
Lemma lem5295592 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5295593 : term83 = term67.
Proof. exact (MK_COMB (@lem5295592) (@lem5295591)). Qed.
Lemma lem5295594 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5295595 : term88 = term73.
Proof. exact (MK_COMB (@lem5295594) (@lem5295593)). Qed.
Lemma lem5295596 : term77 = term73.
Proof. exact (TRANS (@lem5295589) (@lem5295595)). Qed.
Lemma lem5295597 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5295598 : term115 = term102.
Proof. exact (MK_COMB (@lem5295597) (@lem5295596)). Qed.
Lemma lem5295599 : term116 = term104.
Proof. exact (MK_COMB (@lem5295598) (@lem5295586)). Qed.
Lemma lem5295601 (m : nat) : (term117 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5295602 : term104 = term107.
Proof. exact (@lem5295601 term70). Qed.
Lemma lem5295603 : term116 = term107.
Proof. exact (TRANS (@lem5295599) (@lem5295602)). Qed.
Lemma lem5295604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5295605 : term118 = term119.
Proof. exact (MK_COMB (@lem5295604) (@lem5295603)). Qed.
Lemma lem5295606 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem5295607 : term120 = term121.
Proof. exact (MK_COMB (@lem5295605) (@lem5295606)). Qed.
Lemma lem5295609 (x : nat) : (term122 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5295610 : term121 = term107.
Proof. exact (@lem5295609 term70). Qed.
Lemma lem5295611 : term120 = term107.
Proof. exact (TRANS (@lem5295607) (@lem5295610)). Qed.
Lemma lem5295613 (m : nat) (n : nat) : (term80 m n) = (term81 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5295614 : term82 = term83.
Proof. exact (@lem5295613 term70 term70). Qed.
Lemma lem5295615 : (term84 = (BIT1 0)) = (term85 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5295616 : term85 = term70.
Proof. exact (EQ_MP (@lem5295615) (@lem940073)). Qed.
Lemma lem5295617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5295618 : term83 = term67.
Proof. exact (MK_COMB (@lem5295617) (@lem5295616)). Qed.
Lemma lem5295619 : term82 = term67.
Proof. exact (TRANS (@lem5295614) (@lem5295618)). Qed.
Lemma lem5295620 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem5295621 : term123 = term121.
Proof. exact (MK_COMB (@lem5295620) (@lem5295619)). Qed.
Lemma lem5295623 (x : nat) : (term122 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5295624 : term121 = term107.
Proof. exact (@lem5295623 term70). Qed.
Lemma lem5295625 : term123 = term107.
Proof. exact (TRANS (@lem5295621) (@lem5295624)). Qed.
Lemma lem5295626 : term107 = term123.
Proof. exact (SYM (@lem5295625)). Qed.
Lemma lem5295627 : term120 = term123.
Proof. exact (TRANS (@lem5295611) (@lem5295626)). Qed.
Lemma lem5295628 : term105 = term124.
Proof. exact (@lem5295578 (@lem5295627)). Qed.
Lemma lem5295629 : term104 = term124.
Proof. exact (TRANS (@lem5295544) (@lem5295628)). Qed.
Lemma lem5295631 (x : real) : (term91 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5295632 : term124 = term107.
Proof. exact (@lem5295631 term107). Qed.
Lemma lem5295633 : term104 = term107.
Proof. exact (TRANS (@lem5295629) (@lem5295632)). Qed.
Lemma lem5295634 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5295635 : term125 = term119.
Proof. exact (MK_COMB (@lem5295634) (@lem5295633)). Qed.
Lemma lem5295636 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5295637 (l : real) : (term101 l) = (term126 l).
Proof. exact (MK_COMB (@lem5295635) (@lem5295636 l)). Qed.
Lemma lem5295638 (l : real) : (term100 l) = (term126 l).
Proof. exact (TRANS (@lem5295535 l) (@lem5295637 l)). Qed.
Lemma lem5295639 (l : real) : (term126 l) = term107.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5295640 (l : real) : (term100 l) = term107.
Proof. exact (TRANS (@lem5295638 l) (@lem5295639 l)). Qed.
Lemma lem5295641 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5295642 (l : real) : (term127 l) = term128.
Proof. exact (MK_COMB (@lem5295641) (@lem5295640 l)). Qed.
Lemma lem5295643 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem5295644 (l : real) : (term98 l) = term129.
Proof. exact (MK_COMB (@lem5295642 l) (@lem5295643)). Qed.
Lemma lem5295645 (l : real) : (term97 l) = term129.
Proof. exact (TRANS (@lem5295534 l) (@lem5295644 l)). Qed.
Lemma lem5295646 : term129 = term73.
Proof. exact (@lem1982721 term73). Qed.
Lemma lem5295648 (l : real) : (term97 l) = term73.
Proof. exact (TRANS (@lem5295645 l) (@lem5295646)). Qed.
Lemma lem5295649 (l : real) : (term96 l) = term73.
Proof. exact (TRANS (@lem5295530 l) (@lem5295648 l)). Qed.
Lemma lem5295650 (l : real) : (term95 l) = term73.
Proof. exact (TRANS (@lem5295529 l) (@lem5295649 l)). Qed.
Lemma lem5295651 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5295652 (l : real) : (term130 l) = term131.
Proof. exact (MK_COMB (@lem5295651) (@lem5295650 l)). Qed.
Lemma lem5295653 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem5295654 (l : real) : (term64 l) = term132.
Proof. exact (MK_COMB (@lem5295652 l) (@lem5295653)). Qed.
Lemma lem5295655 (l : real) : (term63 l) = term132.
Proof. exact (TRANS (@lem5295476 l) (@lem5295654 l)). Qed.
Lemma lem5295664 (l : real) : (term62 l) = term132.
Proof. exact (TRANS (@lem5295475 l) (@lem5295655 l)). Qed.
Lemma lem5295668 (h1 : term132) : term132.
Proof. exact (h1). Qed.
Lemma lem5295670 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5295671 : term132 = term133.
Proof. exact (@lem5295670 term107 term73). Qed.
Lemma lem5295673 (x : nat) : (term71 x) = (term72 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5295674 : term73 = term74.
Proof. exact (@lem5295673 term70). Qed.
Lemma lem5295676 (x : nat) : (real_of_num x) = (term68 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5295677 : term107 = term124.
Proof. exact (@lem5295676 (NUMERAL 0)). Qed.
Lemma lem5295678 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5295679 : term134 = term135.
Proof. exact (MK_COMB (@lem5295678) (@lem5295677)). Qed.
Lemma lem5295680 : term133 = term136.
Proof. exact (MK_COMB (@lem5295679) (@lem5295674)). Qed.
Lemma lem5295681 : term137.
Proof. exact (@lem1980026 term107 term67 term73 term67). Qed.
Lemma lem5295683 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5295684 : term109 = term110.
Proof. exact (@lem5295683 (NUMERAL 0) term70). Qed.
Lemma lem5295685 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5295686 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5295687 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5295686 h1) (fun h1 : term110 = True => @lem5295685)). Qed.
Lemma lem5295688 : term110 = True.
Proof. exact (EQ_MP (@lem5295687) (@lem5295685)). Qed.
Lemma lem5295689 : term109 = True.
Proof. exact (TRANS (@lem5295684) (@lem5295688)). Qed.
Lemma lem5295690 : True = term109.
Proof. exact (SYM (@lem5295689)). Qed.
Lemma lem5295691 : term109.
Proof. exact (EQ_MP (@lem5295690) (@lem0)). Qed.
Lemma lem5295692 : term138.
Proof. exact (@lem5295681 (@lem5295691)). Qed.
Lemma lem5295694 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5295695 : term109 = term110.
Proof. exact (@lem5295694 (NUMERAL 0) term70). Qed.
Lemma lem5295696 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5295697 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5295698 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5295697 h1) (fun h1 : term110 = True => @lem5295696)). Qed.
Lemma lem5295699 : term110 = True.
Proof. exact (EQ_MP (@lem5295698) (@lem5295696)). Qed.
Lemma lem5295700 : term109 = True.
Proof. exact (TRANS (@lem5295695) (@lem5295699)). Qed.
Lemma lem5295701 : True = term109.
Proof. exact (SYM (@lem5295700)). Qed.
Lemma lem5295702 : term109.
Proof. exact (EQ_MP (@lem5295701) (@lem0)). Qed.
Lemma lem5295703 : term136 = term139.
Proof. exact (@lem5295692 (@lem5295702)). Qed.
Lemma lem5295705 (m : nat) (n : nat) : (term86 m n) = (term87 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5295706 : term77 = term88.
Proof. exact (@lem5295705 term70 term70). Qed.
Lemma lem5295707 : (term84 = (BIT1 0)) = (term85 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5295708 : term85 = term70.
Proof. exact (EQ_MP (@lem5295707) (@lem940073)). Qed.
Lemma lem5295709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5295710 : term83 = term67.
Proof. exact (MK_COMB (@lem5295709) (@lem5295708)). Qed.
Lemma lem5295711 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5295712 : term88 = term73.
Proof. exact (MK_COMB (@lem5295711) (@lem5295710)). Qed.
Lemma lem5295713 : term77 = term73.
Proof. exact (TRANS (@lem5295706) (@lem5295712)). Qed.
Lemma lem5295715 (x : nat) : (term122 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5295716 : term121 = term107.
Proof. exact (@lem5295715 term70). Qed.
Lemma lem5295717 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5295718 : term140 = term134.
Proof. exact (MK_COMB (@lem5295717) (@lem5295716)). Qed.
Lemma lem5295719 : term139 = term133.
Proof. exact (MK_COMB (@lem5295718) (@lem5295713)). Qed.
Lemma lem5295721 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5295722 : term133 = term143.
Proof. exact (@lem5295721 (NUMERAL 0) term70). Qed.
Lemma lem5295723 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5295724 (h1 : term111 = (BIT1 0)) : (term70 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5295725 : (term111 = (BIT1 0)) = ((term70 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5295724 h1) (fun h1 : (term70 = (NUMERAL 0)) = False => @lem5295723)). Qed.
Lemma lem5295726 : (term70 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5295725) (@lem5295723)). Qed.
Lemma lem5295727 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5295728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5295729 : term144 = (and True).
Proof. exact (MK_COMB (@lem5295728) (@lem5295727)). Qed.
Lemma lem5295730 : term143 = (True /\ False).
Proof. exact (MK_COMB (@lem5295729) (@lem5295726)). Qed.
Lemma lem5295732 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5295733 : term143 = False.
Proof. exact (TRANS (@lem5295730) (@lem5295732)). Qed.
Lemma lem5295734 : term133 = False.
Proof. exact (TRANS (@lem5295722) (@lem5295733)). Qed.
Lemma lem5295735 : term139 = False.
Proof. exact (TRANS (@lem5295719) (@lem5295734)). Qed.
Lemma lem5295736 : term136 = False.
Proof. exact (TRANS (@lem5295703) (@lem5295735)). Qed.
Lemma lem5295737 : term133 = False.
Proof. exact (TRANS (@lem5295680) (@lem5295736)). Qed.
Lemma lem5295738 : term132 = False.
Proof. exact (TRANS (@lem5295671) (@lem5295737)). Qed.
Lemma lem5295739 (h1 : term132) : False.
Proof. exact (EQ_MP (@lem5295738) (@lem5295668 h1)). Qed.
Lemma lem5295741 (h1 : term132) : term132.
Proof. exact (h1). Qed.
Lemma lem5295742 (h1 : term132) : term132 = False.
Proof. exact (prop_ext (fun h2 : term132 => @lem5295739 h1) (fun h2 : False => @lem5295741 h1)). Qed.
Lemma lem5295743 (h1 : term132) : False.
Proof. exact (EQ_MP (@lem5295742 h1) (@lem5295741 h1)). Qed.
Lemma lem5295744 (l : real) (h1 : term62 l) : term62 l.
Proof. exact (h1). Qed.
Lemma lem5295745 (l : real) (h1 : term62 l) : term132.
Proof. exact (EQ_MP (@lem5295664 l) (@lem5295744 l h1)). Qed.
Lemma lem5295746 (l : real) (h1 : term62 l) : term132 = False.
Proof. exact (prop_ext (fun h2 : term132 => @lem5295743 h2) (fun h2 : False => @lem5295745 l h1)). Qed.
Lemma lem5295747 (l : real) (h1 : term62 l) : False.
Proof. exact (EQ_MP (@lem5295746 l h1) (@lem5295745 l h1)). Qed.
Lemma lem5295748 (l : real) : term145 l.
Proof. exact (fun h0 : term62 l => @lem5295747 l h0). Qed.
Lemma lem5295749 (l : real) : term146 l.
Proof. exact (@lem1386578 (term147 l)). Qed.
Lemma lem5295752 (l : real) : term147 l.
Proof. exact (@lem5295749 l (@lem5295748 l)). Qed.
Lemma lem5295753 (l : real) : term60 l.
Proof. exact (ex_intro (term59 l) (term65 l) (@lem5295752 l)). Qed.
Lemma lem5295754 (l : real) : term31 l.
Proof. exact (EQ_MP (@lem5295465 l) (@lem5295753 l)). Qed.
Lemma lem5295756 (l : real) (s : real -> Prop) (h1 : term7 s l) (h2 : s = (@EMPTY real)) : False.
Proof. exact (@lem5295754 l (@lem5295391 l s h1 h2)). Qed.
Lemma lem5295757 (s : real -> Prop) (l : real) (h1 : term7 s l) : term148 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5295756 l s h1 h0). Qed.
Lemma lem5295758 (s : real -> Prop) : (term148 s) = (term23 s).
Proof. exact (@lem69 (s = (@EMPTY real))). Qed.
Lemma lem5295759 (s : real -> Prop) (l : real) (h1 : term7 s l) : term23 s.
Proof. exact (EQ_MP (@lem5295758 s) (@lem5295757 s l h1)). Qed.
Lemma lem5295760 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : term149 s l c.
Proof. exact (@lem5295357 s l h1 c). Qed.
Lemma lem5295761 (s : real -> Prop) (l : real) (c : real) : (term149 s l c) = ((term25 s c) = (real_le l c)).
Proof. exact (eq_refl (term149 s l c)). Qed.
Lemma lem5295768 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5295761 s l c) (@lem5295760 c s l h1)). Qed.
Lemma lem5295769 (b : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term25 s b) = (real_le l b).
Proof. exact (@lem5295768 b s l h1). Qed.
Lemma lem5295770 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term150 s) = (term151 l).
Proof. exact (fun_ext (fun b : real => @lem5295769 b s l h1)). Qed.
Lemma lem5295771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5295772 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term24 s) = (term152 l).
Proof. exact (MK_COMB (@lem5295771) (@lem5295770 s l h1)). Qed.
Lemma lem5295777 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term152 l) = (term24 s).
Proof. exact (SYM (@lem5295772 s l h1)). Qed.
Lemma lem5295779 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5295780 (l : real) : (term152 l) = (term154 l).
Proof. exact (@lem5295779 (term152 l)). Qed.
Lemma lem5295781 (l : real) : (term154 l) = (term152 l).
Proof. exact (SYM (@lem5295780 l)). Qed.
Lemma lem5295782 (l : real) (h1 : term155 l) : term155 l.
Proof. exact (h1). Qed.
Lemma lem5295785 (l : real) (h1 : term156 l) : term156 l.
Proof. exact (h1). Qed.
Lemma lem5295786 (l : real) : term157 l.
Proof. exact (fun h0 : term156 l => @lem5295785 l h0). Qed.
Lemma lem5295787 (l : real) (h1 : term157 l) : term157 l.
Proof. exact (h1). Qed.
Lemma lem5295788 (l : real) (h1 : term156 l) : term156 l.
Proof. exact (h1). Qed.
Lemma lem5295789 (l : real) (h1 : term156 l) (h2 : term157 l) : term156 l.
Proof. exact (@lem5295787 l h2 (@lem5295788 l h1)). Qed.
Lemma lem5295790 (l : real) (h1 : term156 l) : term158 l.
Proof. exact (fun h0 : term157 l => @lem5295789 l h1 h0). Qed.
Lemma lem5295791 (l : real) (h1 : term157 l) : term157 l.
Proof. exact (h1). Qed.
Lemma lem5295792 (l : real) (h1 : term156 l) (h2 : term157 l) : term156 l.
Proof. exact (@lem5295790 l h1 (@lem5295791 l h2)). Qed.
Lemma lem5295793 (l : real) (h1 : term157 l) : term157 l.
Proof. exact (fun h0 : term156 l => @lem5295792 l h0 h1). Qed.
Lemma lem5295794 (l : real) : term159 l.
Proof. exact (fun h0 : term157 l => @lem5295793 l h0). Qed.
Lemma lem5295797 (l : real) : term157 l.
Proof. exact (@lem5295794 l (@lem5295786 l)). Qed.
Lemma lem5295809 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5295810 : term160 = term161.
Proof. exact (@lem5295809 term162). Qed.
Lemma lem5295815 (l : real) : (term163 l) = (term163 l).
Proof. exact (eq_refl (term163 l)). Qed.
Lemma lem5295816 (l : real) : (term156 l) = (term164 l).
Proof. exact (MK_COMB (@lem5295815 l) (@lem5295810)). Qed.
Lemma lem5295819 : term165 = term166.
Proof. exact (fun_ext (fun l : real => @lem5295816 l)). Qed.
Lemma lem5295820 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295829 : term167 = term168.
Proof. exact (MK_COMB (@lem5295820) (@lem5295819)). Qed.
Lemma lem5295830 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5295831 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5295830 x)). Qed.
Lemma lem5295832 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295833 : term162 = term162.
Proof. exact (MK_COMB (@lem5295832) (@lem5295831)). Qed.
Lemma lem5295834 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5295835 : term161 = term161.
Proof. exact (MK_COMB (@lem5295834) (@lem5295833)). Qed.
Lemma lem5295836 (l : real) (b : real) : (real_le l b) = (real_le l b).
Proof. exact (eq_refl (real_le l b)). Qed.
Lemma lem5295837 (l : real) : (term151 l) = (term151 l).
Proof. exact (fun_ext (fun b : real => @lem5295836 l b)). Qed.
Lemma lem5295838 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5295839 (l : real) : (term152 l) = (term152 l).
Proof. exact (MK_COMB (@lem5295838) (@lem5295837 l)). Qed.
Lemma lem5295840 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5295841 (l : real) : (term155 l) = (term155 l).
Proof. exact (MK_COMB (@lem5295840) (@lem5295839 l)). Qed.
Lemma lem5295842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5295843 (l : real) : (term163 l) = (term163 l).
Proof. exact (MK_COMB (@lem5295842) (@lem5295841 l)). Qed.
Lemma lem5295844 (l : real) : (term164 l) = (term164 l).
Proof. exact (MK_COMB (@lem5295843 l) (@lem5295835)). Qed.
Lemma lem5295845 : term166 = term166.
Proof. exact (fun_ext (fun l : real => @lem5295844 l)). Qed.
Lemma lem5295846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295847 : term168 = term168.
Proof. exact (MK_COMB (@lem5295846) (@lem5295845)). Qed.
Lemma lem5295870 : term167 = term168.
Proof. exact (TRANS (@lem5295829) (@lem5295847)). Qed.
Lemma lem5295871 : term168 = term167.
Proof. exact (SYM (@lem5295870)). Qed.
Lemma lem5295872 (l : real) (h1 : term155 l) : term155 l.
Proof. exact (h1). Qed.
Lemma lem5295873 (h1 : term162) : term162.
Proof. exact (h1). Qed.
Lemma lem5295875 (P : real -> Prop) : (term170 P) = (term171 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5295876 (l : real) : (term155 l) = (term172 l).
Proof. exact (@lem5295875 (term151 l)). Qed.
Lemma lem5295877 (l : real) (b : real) : (term173 l b) = (real_le l b).
Proof. exact (eq_refl (term173 l b)). Qed.
Lemma lem5295878 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5295880 (l : real) (b : real) : (term174 l b) = (term58 l b).
Proof. exact (MK_COMB (@lem5295878) (@lem5295877 l b)). Qed.
Lemma lem5295881 (l : real) : (term175 l) = (term59 l).
Proof. exact (fun_ext (fun b : real => @lem5295880 l b)). Qed.
Lemma lem5295882 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295883 (l : real) : (term172 l) = (term176 l).
Proof. exact (MK_COMB (@lem5295882) (@lem5295881 l)). Qed.
Lemma lem5295892 (l : real) : (term155 l) = (term176 l).
Proof. exact (TRANS (@lem5295876 l) (@lem5295883 l)). Qed.
Lemma lem5295893 (l : real) (h1 : term155 l) : term176 l.
Proof. exact (EQ_MP (@lem5295892 l) (@lem5295872 l h1)). Qed.
Lemma lem5295894 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5295895 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5295894 x)). Qed.
Lemma lem5295896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295905 : term162 = term162.
Proof. exact (MK_COMB (@lem5295896) (@lem5295895)). Qed.
Lemma lem5295906 (h1 : term162) : term162.
Proof. exact (EQ_MP (@lem5295905) (@lem5295873 h1)). Qed.
Lemma lem5295913 (l : real) (b : real) : (term58 l b) = (term58 l b).
Proof. exact (eq_refl (term58 l b)). Qed.
Lemma lem5295914 (l : real) : (term59 l) = (term59 l).
Proof. exact (fun_ext (fun b : real => @lem5295913 l b)). Qed.
Lemma lem5295915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295916 (l : real) : (term176 l) = (term176 l).
Proof. exact (MK_COMB (@lem5295915) (@lem5295914 l)). Qed.
Lemma lem5295917 (l : real) (h1 : term155 l) : term176 l.
Proof. exact (EQ_MP (@lem5295916 l) (@lem5295893 l h1)). Qed.
Lemma lem5295922 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5295923 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5295922 x)). Qed.
Lemma lem5295924 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295925 : term162 = term162.
Proof. exact (MK_COMB (@lem5295924) (@lem5295923)). Qed.
Lemma lem5295926 (h1 : term162) : term162.
Proof. exact (EQ_MP (@lem5295925) (@lem5295906 h1)). Qed.
Lemma lem5295928 (l : real) (b : real) : (term58 l b) = (term58 l b).
Proof. exact (eq_refl (term58 l b)). Qed.
Lemma lem5295929 (l : real) : (term59 l) = (term59 l).
Proof. exact (fun_ext (fun b : real => @lem5295928 l b)). Qed.
Lemma lem5295930 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295932 (l : real) : (term176 l) = (term176 l).
Proof. exact (MK_COMB (@lem5295930) (@lem5295929 l)). Qed.
Lemma lem5295933 (l : real) (h1 : term155 l) : term176 l.
Proof. exact (EQ_MP (@lem5295932 l) (@lem5295917 l h1)). Qed.
Lemma lem5295935 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5295936 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5295935 x)). Qed.
Lemma lem5295937 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5295939 : term162 = term162.
Proof. exact (MK_COMB (@lem5295937) (@lem5295936)). Qed.
Lemma lem5295940 (h1 : term162) : term162.
Proof. exact (EQ_MP (@lem5295939) (@lem5295926 h1)). Qed.
Lemma lem5295941 (_69326 : real) (l : real) (h1 : term155 l) : term177 l _69326.
Proof. exact (@lem5295933 l h1 _69326). Qed.
Lemma lem5295942 (l : real) (_69326 : real) : (term177 l _69326) = (term58 l _69326).
Proof. exact (eq_refl (term177 l _69326)). Qed.
Lemma lem5295944 (_69327 : real) (h1 : term162) : term178 _69327.
Proof. exact (@lem5295940 h1 _69327). Qed.
Lemma lem5295945 (_69327 : real) : (term178 _69327) = (real_le _69327 _69327).
Proof. exact (eq_refl (term178 _69327)). Qed.
Lemma lem5295948 (_69326 : real) (l : real) (h1 : term155 l) : term58 l _69326.
Proof. exact (EQ_MP (@lem5295942 l _69326) (@lem5295941 _69326 l h1)). Qed.
Lemma lem5295952 (_69327 : real) (h1 : term162) : real_le _69327 _69327.
Proof. exact (EQ_MP (@lem5295945 _69327) (@lem5295944 _69327 h1)). Qed.
Lemma lem5295953 (l : real) (h1 : term162) : real_le l l.
Proof. exact (@lem5295952 l h1). Qed.
Lemma lem5295954 (l : real) (h1 : term162) : term179 l.
Proof. exact (fun h0 : term180 l => @lem5295953 l h1). Qed.
Lemma lem5295956 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5295957 (l : real) : (term179 l) = (real_le l l).
Proof. exact (@lem5295956 (real_le l l)). Qed.
Lemma lem5295958 (l : real) (h1 : term162) : real_le l l.
Proof. exact (EQ_MP (@lem5295957 l) (@lem5295954 l h1)). Qed.
Lemma lem5295961 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5295963 (l : real) (_69326 : real) : (term58 l _69326) = (term182 l _69326).
Proof. exact (@lem5295961 (real_le l _69326)). Qed.
Lemma lem5295966 (_69326 : real) (l : real) (h1 : term155 l) : term182 l _69326.
Proof. exact (EQ_MP (@lem5295963 l _69326) (@lem5295948 _69326 l h1)). Qed.
Lemma lem5295967 (l : real) (h1 : term155 l) : term183 l.
Proof. exact (@lem5295966 l l h1). Qed.
Lemma lem5295970 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (@lem5295967 l h2 (@lem5295958 l h1)). Qed.
Lemma lem5295971 (l : real) (h1 : term162) (h2 : term155 l) : term184.
Proof. exact (fun h0 : ~ False => @lem5295970 l h1 h2). Qed.
Lemma lem5295973 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5295974 : term184 = False.
Proof. exact (@lem5295973 False). Qed.
Lemma lem5295975 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5295974) (@lem5295971 l h1 h2)). Qed.
Lemma lem5295976 (l : real) (h1 : term162) (h2 : term155 l) : term162 = False.
Proof. exact (prop_ext (fun h3 : term162 => @lem5295975 l h1 h2) (fun h3 : False => @lem5295940 h1)). Qed.
Lemma lem5295977 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5295976 l h1 h2) (@lem5295940 h1)). Qed.
Lemma lem5295978 (l : real) (h1 : term162) (h2 : term155 l) : term162 = False.
Proof. exact (prop_ext (fun h3 : term162 => @lem5295977 l h1 h2) (fun h3 : False => @lem5295926 h1)). Qed.
Lemma lem5295979 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5295978 l h1 h2) (@lem5295926 h1)). Qed.
Lemma lem5295980 (l : real) (h1 : term162) (h2 : term155 l) : term162 = False.
Proof. exact (prop_ext (fun h3 : term162 => @lem5295979 l h1 h2) (fun h3 : False => @lem5295906 h1)). Qed.
Lemma lem5295981 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5295980 l h1 h2) (@lem5295906 h1)). Qed.
Lemma lem5295982 (l : real) (h1 : term155 l) : term160.
Proof. exact (fun h0 : term162 => @lem5295981 l h0 h1). Qed.
Lemma lem5295983 : term160 = term161.
Proof. exact (@lem69 term162). Qed.
Lemma lem5295984 (l : real) (h1 : term155 l) : term161.
Proof. exact (EQ_MP (@lem5295983) (@lem5295982 l h1)). Qed.
Lemma lem5295985 (l : real) : term164 l.
Proof. exact (fun h0 : term155 l => @lem5295984 l h0). Qed.
Lemma lem5295990 : term168.
Proof. exact (fun l : real => @lem5295985 l). Qed.
Lemma lem5295991 : term167.
Proof. exact (EQ_MP (@lem5295871) (@lem5295990)). Qed.
Lemma lem5295992 (l : real) : term185 l.
Proof. exact (@lem5295991 l). Qed.
Lemma lem5295993 (l : real) : (term185 l) = (term156 l).
Proof. exact (eq_refl (term185 l)). Qed.
Lemma lem5295994 (l : real) : term156 l.
Proof. exact (EQ_MP (@lem5295993 l) (@lem5295992 l)). Qed.
Lemma lem5295996 (l : real) : term156 l.
Proof. exact (@lem5295797 l (@lem5295994 l)). Qed.
Lemma lem5295997 (l : real) (h1 : term155 l) : term160.
Proof. exact (@lem5295996 l (@lem5295782 l h1)). Qed.
Lemma lem5295998 (l : real) (h1 : term155 l) : False.
Proof. exact (@lem5295997 l h1 (@lem1339240)). Qed.
Lemma lem5295999 (l : real) (h1 : term155 l) : (term155 l) = False.
Proof. exact (prop_ext (fun h2 : term155 l => @lem5295998 l h1) (fun h2 : False => @lem5295782 l h1)). Qed.
Lemma lem5296000 (l : real) (h1 : term155 l) : False.
Proof. exact (EQ_MP (@lem5295999 l h1) (@lem5295782 l h1)). Qed.
Lemma lem5296001 (l : real) : term154 l.
Proof. exact (fun h0 : term155 l => @lem5296000 l h0). Qed.
Lemma lem5296002 (l : real) : term152 l.
Proof. exact (EQ_MP (@lem5295781 l) (@lem5296001 l)). Qed.
Lemma lem5296003 (s : real -> Prop) (l : real) (h1 : term7 s l) : term24 s.
Proof. exact (EQ_MP (@lem5295777 s l h1) (@lem5296002 l)). Qed.
Lemma lem5296005 (s : real -> Prop) (b : real) : term6 s b.
Proof. exact (EQ_MP (@lem5295289 s b) (@lem5295288 s b)). Qed.
Lemma lem5296006 (s : real -> Prop) (l : real) : term6 s l.
Proof. exact (@lem5296005 s l). Qed.
Lemma lem5296007 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : term149 s l c.
Proof. exact (@lem5295357 s l h1 c). Qed.
Lemma lem5296008 (s : real -> Prop) (l : real) (c : real) : (term149 s l c) = ((term25 s c) = (real_le l c)).
Proof. exact (eq_refl (term149 s l c)). Qed.
Lemma lem5296017 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5296008 s l c) (@lem5296007 c s l h1)). Qed.
Lemma lem5296018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5296019 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term186 s c) = (term187 l c).
Proof. exact (MK_COMB (@lem5296018) (@lem5296017 c s l h1)). Qed.
Lemma lem5296020 (l : real) (c : real) : (real_le l c) = (real_le l c).
Proof. exact (eq_refl (real_le l c)). Qed.
Lemma lem5296021 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : ((term25 s c) = (real_le l c)) = ((real_le l c) = (real_le l c)).
Proof. exact (MK_COMB (@lem5296019 c s l h1) (@lem5296020 l c)). Qed.
Lemma lem5296023 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5296024 (x : Prop) : (x = x) = True.
Proof. exact (@lem5296023 Prop x). Qed.
Lemma lem5296025 (l : real) (c : real) : ((real_le l c) = (real_le l c)) = True.
Proof. exact (@lem5296024 (real_le l c)). Qed.
Lemma lem5296026 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : ((term25 s c) = (real_le l c)) = True.
Proof. exact (TRANS (@lem5296021 c s l h1) (@lem5296025 l c)). Qed.
Lemma lem5296027 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term188 s l) = term53.
Proof. exact (fun_ext (fun c : real => @lem5296026 c s l h1)). Qed.
Lemma lem5296028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296029 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term7 s l) = term54.
Proof. exact (MK_COMB (@lem5296028) (@lem5296027 s l h1)). Qed.
Lemma lem5296031 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5296032 (t : Prop) : (term56 t) = t.
Proof. exact (@lem5296031 real t). Qed.
Lemma lem5296033 : term54 = True.
Proof. exact (@lem5296032 True). Qed.
Lemma lem5296034 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term7 s l) = True.
Proof. exact (TRANS (@lem5296029 s l h1) (@lem5296033)). Qed.
Lemma lem5296035 (s : real -> Prop) (l : real) (h1 : term7 s l) : True = (term7 s l).
Proof. exact (SYM (@lem5296034 s l h1)). Qed.
Lemma lem5296036 (s : real -> Prop) (l : real) (h1 : term7 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5296035 s l h1) (@lem0)). Qed.
Lemma lem5296037 (s : real -> Prop) (l : real) (h1 : term7 s l) : (sup s) = l.
Proof. exact (@lem5296006 s l (@lem5296036 s l h1)). Qed.
Lemma lem5296038 (s : real -> Prop) (l : real) (h1 : term7 s l) : term22 s l.
Proof. exact (conj (@lem5296003 s l h1) (@lem5296037 s l h1)). Qed.
Lemma lem5296039 (s : real -> Prop) (l : real) (h1 : term7 s l) : term21 s l.
Proof. exact (conj (@lem5295759 s l h1) (@lem5296038 s l h1)). Qed.
Lemma lem5296041 (p : Prop) (q : Prop) (r : Prop) : term189 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5296042 (s : real -> Prop) (l : real) (c : real) : term190 s l c.
Proof. exact (@lem5296041 (term191 s) (term192 s) ((term25 s c) = (real_le l c))). Qed.
Lemma lem5296043 (s : real -> Prop) : term193 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5296064 (s : real -> Prop) (h1 : term23 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5296043 s (@lem5295360 s h1)). Qed.
Lemma lem5296065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5296066 (s : real -> Prop) (h1 : term23 s) : (term23 s) = (~ False).
Proof. exact (MK_COMB (@lem5296065) (@lem5296064 s h1)). Qed.
Lemma lem5296068 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5296069 (s : real -> Prop) (h1 : term23 s) : (term23 s) = True.
Proof. exact (TRANS (@lem5296066 s h1) (@lem5296068)). Qed.
Lemma lem5296070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5296071 (s : real -> Prop) (h1 : term23 s) : (term194 s) = (and True).
Proof. exact (MK_COMB (@lem5296070) (@lem5296069 s h1)). Qed.
Lemma lem5296096 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (eq_refl (term24 s)). Qed.
Lemma lem5296097 (s : real -> Prop) (h1 : term23 s) : (term191 s) = (term195 s).
Proof. exact (MK_COMB (@lem5296071 s h1) (@lem5296096 s)). Qed.
Lemma lem5296099 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5296100 (s : real -> Prop) : (term195 s) = (term24 s).
Proof. exact (@lem5296099 (term24 s)). Qed.
Lemma lem5296125 (s : real -> Prop) (h1 : term23 s) : (term191 s) = (term24 s).
Proof. exact (TRANS (@lem5296097 s h1) (@lem5296100 s)). Qed.
Lemma lem5296126 (s : real -> Prop) (h1 : term23 s) : (term24 s) = (term191 s).
Proof. exact (SYM (@lem5296125 s h1)). Qed.
Lemma lem5296128 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5296129 (s : real -> Prop) : (term24 s) = (term196 s).
Proof. exact (@lem5296128 (term24 s)). Qed.
Lemma lem5296130 (s : real -> Prop) : (term196 s) = (term24 s).
Proof. exact (SYM (@lem5296129 s)). Qed.
Lemma lem5296131 (s : real -> Prop) (h1 : term197 s) : term197 s.
Proof. exact (h1). Qed.
Lemma lem5296134 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) : term198 b l s.
Proof. exact (h1). Qed.
Lemma lem5296135 (b : real) (l : real) (s : real -> Prop) : term199 b l s.
Proof. exact (fun h0 : term198 b l s => @lem5296134 b l s h0). Qed.
Lemma lem5296136 (b : real) (l : real) (s : real -> Prop) (h1 : term199 b l s) : term199 b l s.
Proof. exact (h1). Qed.
Lemma lem5296137 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) : term198 b l s.
Proof. exact (h1). Qed.
Lemma lem5296138 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) (h2 : term199 b l s) : term198 b l s.
Proof. exact (@lem5296136 b l s h2 (@lem5296137 b l s h1)). Qed.
Lemma lem5296139 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) : term200 b l s.
Proof. exact (fun h0 : term199 b l s => @lem5296138 b l s h1 h0). Qed.
Lemma lem5296140 (b : real) (l : real) (s : real -> Prop) (h1 : term199 b l s) : term199 b l s.
Proof. exact (h1). Qed.
Lemma lem5296141 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) (h2 : term199 b l s) : term198 b l s.
Proof. exact (@lem5296139 b l s h1 (@lem5296140 b l s h2)). Qed.
Lemma lem5296142 (b : real) (l : real) (s : real -> Prop) (h1 : term199 b l s) : term199 b l s.
Proof. exact (fun h0 : term198 b l s => @lem5296141 b l s h0 h1). Qed.
Lemma lem5296143 (b : real) (l : real) (s : real -> Prop) : term201 b l s.
Proof. exact (fun h0 : term199 b l s => @lem5296142 b l s h0). Qed.
Lemma lem5296146 (b : real) (l : real) (s : real -> Prop) : term199 b l s.
Proof. exact (@lem5296143 b l s (@lem5296135 b l s)). Qed.
Lemma lem5296172 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5296173 (s : real -> Prop) : (term196 s) = (term202 s).
Proof. exact (@lem5296172 (term197 s)). Qed.
Lemma lem5296175 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5296176 (s : real -> Prop) : (term202 s) = (term24 s).
Proof. exact (@lem5296175 (term24 s)). Qed.
Lemma lem5296181 (s : real -> Prop) : (term196 s) = (term24 s).
Proof. exact (TRANS (@lem5296173 s) (@lem5296176 s)). Qed.
Lemma lem5296188 (s : real -> Prop) (l : real) : (term203 s l) = (term203 s l).
Proof. exact (eq_refl (term203 s l)). Qed.
Lemma lem5296189 (l : real) (s : real -> Prop) : (term204 l s) = (term205 l s).
Proof. exact (MK_COMB (@lem5296188 s l) (@lem5296181 s)). Qed.
Lemma lem5296192 (s : real -> Prop) (b : real) : (term206 s b) = (term206 s b).
Proof. exact (eq_refl (term206 s b)). Qed.
Lemma lem5296193 (b : real) (l : real) (s : real -> Prop) : (term207 b l s) = (term208 b l s).
Proof. exact (MK_COMB (@lem5296192 s b) (@lem5296189 l s)). Qed.
Lemma lem5296196 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (eq_refl (term209 s)). Qed.
Lemma lem5296197 (b : real) (l : real) (s : real -> Prop) : (term198 b l s) = (term210 b l s).
Proof. exact (MK_COMB (@lem5296196 s) (@lem5296193 b l s)). Qed.
Lemma lem5296200 (l : real) (s : real -> Prop) : (term211 l s) = (term212 l s).
Proof. exact (fun_ext (fun b : real => @lem5296197 b l s)). Qed.
Lemma lem5296201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296202 (l : real) (s : real -> Prop) : (term213 l s) = (term214 l s).
Proof. exact (MK_COMB (@lem5296201) (@lem5296200 l s)). Qed.
Lemma lem5296207 (s : real -> Prop) : (term215 s) = (term216 s).
Proof. exact (fun_ext (fun l : real => @lem5296202 l s)). Qed.
Lemma lem5296208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296209 (s : real -> Prop) : (term217 s) = (term218 s).
Proof. exact (MK_COMB (@lem5296208) (@lem5296207 s)). Qed.
Lemma lem5296214 : term219 = term220.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5296209 s)). Qed.
Lemma lem5296215 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5296224 : term221 = term222.
Proof. exact (MK_COMB (@lem5296215) (@lem5296214)). Qed.
Lemma lem5296229 (s : real -> Prop) (x : real) (b : real) : (term223 s x b) = (term223 s x b).
Proof. exact (eq_refl (term223 s x b)). Qed.
Lemma lem5296230 (s : real -> Prop) (b : real) : (term224 s b) = (term224 s b).
Proof. exact (fun_ext (fun x : real => @lem5296229 s x b)). Qed.
Lemma lem5296231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296232 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (MK_COMB (@lem5296231) (@lem5296230 s b)). Qed.
Lemma lem5296233 (s : real -> Prop) : (term150 s) = (term150 s).
Proof. exact (fun_ext (fun b : real => @lem5296232 s b)). Qed.
Lemma lem5296234 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5296235 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (MK_COMB (@lem5296234) (@lem5296233 s)). Qed.
Lemma lem5296238 (s : real -> Prop) (l : real) : (term203 s l) = (term203 s l).
Proof. exact (eq_refl (term203 s l)). Qed.
Lemma lem5296239 (l : real) (s : real -> Prop) : (term205 l s) = (term205 l s).
Proof. exact (MK_COMB (@lem5296238 s l) (@lem5296235 s)). Qed.
Lemma lem5296244 (s : real -> Prop) (x : real) (b : real) : (term223 s x b) = (term223 s x b).
Proof. exact (eq_refl (term223 s x b)). Qed.
Lemma lem5296245 (s : real -> Prop) (b : real) : (term224 s b) = (term224 s b).
Proof. exact (fun_ext (fun x : real => @lem5296244 s x b)). Qed.
Lemma lem5296246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296247 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (MK_COMB (@lem5296246) (@lem5296245 s b)). Qed.
Lemma lem5296248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5296249 (s : real -> Prop) (b : real) : (term206 s b) = (term206 s b).
Proof. exact (MK_COMB (@lem5296248) (@lem5296247 s b)). Qed.
Lemma lem5296250 (b : real) (l : real) (s : real -> Prop) : (term208 b l s) = (term208 b l s).
Proof. exact (MK_COMB (@lem5296249 s b) (@lem5296239 l s)). Qed.
Lemma lem5296255 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (eq_refl (term209 s)). Qed.
Lemma lem5296256 (b : real) (l : real) (s : real -> Prop) : (term210 b l s) = (term210 b l s).
Proof. exact (MK_COMB (@lem5296255 s) (@lem5296250 b l s)). Qed.
Lemma lem5296257 (l : real) (s : real -> Prop) : (term212 l s) = (term212 l s).
Proof. exact (fun_ext (fun b : real => @lem5296256 b l s)). Qed.
Lemma lem5296258 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296259 (l : real) (s : real -> Prop) : (term214 l s) = (term214 l s).
Proof. exact (MK_COMB (@lem5296258) (@lem5296257 l s)). Qed.
Lemma lem5296260 (s : real -> Prop) : (term216 s) = (term216 s).
Proof. exact (fun_ext (fun l : real => @lem5296259 l s)). Qed.
Lemma lem5296261 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296262 (s : real -> Prop) : (term218 s) = (term218 s).
Proof. exact (MK_COMB (@lem5296261) (@lem5296260 s)). Qed.
Lemma lem5296263 : term220 = term220.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5296262 s)). Qed.
Lemma lem5296264 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5296265 : term222 = term222.
Proof. exact (MK_COMB (@lem5296264) (@lem5296263)). Qed.
Lemma lem5296314 : term221 = term222.
Proof. exact (TRANS (@lem5296224) (@lem5296265)). Qed.
Lemma lem5296315 : term222 = term221.
Proof. exact (SYM (@lem5296314)). Qed.
Lemma lem5296317 (s : real -> Prop) (b : real) (h1 : term25 s b) : term25 s b.
Proof. exact (h1). Qed.
Lemma lem5296320 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5296321 (s : real -> Prop) : (term24 s) = (term196 s).
Proof. exact (@lem5296320 (term24 s)). Qed.
Lemma lem5296322 (s : real -> Prop) : (term196 s) = (term24 s).
Proof. exact (SYM (@lem5296321 s)). Qed.
Lemma lem5296323 (s : real -> Prop) (h1 : term197 s) : term197 s.
Proof. exact (h1). Qed.
Lemma lem5296336 (s : real -> Prop) (x : real) (b : real) : (term223 s x b) = (term225 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5296337 (s : real -> Prop) (b : real) : (term224 s b) = (term226 s b).
Proof. exact (fun_ext (fun x : real => @lem5296336 s x b)). Qed.
Lemma lem5296338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296391 (s : real -> Prop) (b : real) : (term25 s b) = (term227 s b).
Proof. exact (MK_COMB (@lem5296338) (@lem5296337 s b)). Qed.
Lemma lem5296392 (s : real -> Prop) (b : real) (h1 : term25 s b) : term227 s b.
Proof. exact (EQ_MP (@lem5296391 s b) (@lem5296317 s b h1)). Qed.
Lemma lem5296405 (s : real -> Prop) (x : real) (b : real) : (term228 s x b) = (term229 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5296406 (P : real -> Prop) : (term230 P) = (term34 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5296407 (s : real -> Prop) (b : real) : (term231 s b) = (term232 s b).
Proof. exact (@lem5296406 (term224 s b)). Qed.
Lemma lem5296408 (s : real -> Prop) (x : real) (b : real) : (term233 s b x) = (term223 s x b).
Proof. exact (eq_refl (term233 s b x)). Qed.
Lemma lem5296409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5296410 (s : real -> Prop) (x : real) (b : real) : (term234 s b x) = (term228 s x b).
Proof. exact (MK_COMB (@lem5296409) (@lem5296408 s x b)). Qed.
Lemma lem5296411 (s : real -> Prop) (x : real) (b : real) : (term234 s b x) = (term229 s x b).
Proof. exact (TRANS (@lem5296410 s x b) (@lem5296405 s x b)). Qed.
Lemma lem5296412 (s : real -> Prop) (b : real) : (term235 s b) = (term236 s b).
Proof. exact (fun_ext (fun x : real => @lem5296411 s x b)). Qed.
Lemma lem5296413 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5296414 (s : real -> Prop) (b : real) : (term232 s b) = (term237 s b).
Proof. exact (MK_COMB (@lem5296413) (@lem5296412 s b)). Qed.
Lemma lem5296415 (s : real -> Prop) (b : real) : (term231 s b) = (term237 s b).
Proof. exact (TRANS (@lem5296407 s b) (@lem5296414 s b)). Qed.
Lemma lem5296416 (P : real -> Prop) : (term170 P) = (term171 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5296417 (s : real -> Prop) : (term197 s) = (term238 s).
Proof. exact (@lem5296416 (term150 s)). Qed.
Lemma lem5296418 (s : real -> Prop) (b : real) : (term239 s b) = (term25 s b).
Proof. exact (eq_refl (term239 s b)). Qed.
Lemma lem5296419 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5296420 (s : real -> Prop) (b : real) : (term240 s b) = (term231 s b).
Proof. exact (MK_COMB (@lem5296419) (@lem5296418 s b)). Qed.
Lemma lem5296421 (s : real -> Prop) (b : real) : (term240 s b) = (term237 s b).
Proof. exact (TRANS (@lem5296420 s b) (@lem5296415 s b)). Qed.
Lemma lem5296422 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (fun_ext (fun b : real => @lem5296421 s b)). Qed.
Lemma lem5296423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296424 (s : real -> Prop) : (term238 s) = (term243 s).
Proof. exact (MK_COMB (@lem5296423) (@lem5296422 s)). Qed.
Lemma lem5296425 (s : real -> Prop) : (term197 s) = (term243 s).
Proof. exact (TRANS (@lem5296417 s) (@lem5296424 s)). Qed.
Lemma lem5296480 {A B : Type'} (P : type1413 A B) : (term244 A B P) = (term245 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5296481 (P : type1626) : (term246 P) = (term247 P).
Proof. exact (@lem5296480 real real P). Qed.
Lemma lem5296482 (s : real -> Prop) : (term248 s) = (term249 s).
Proof. exact (@lem5296481 (term250 s)). Qed.
Lemma lem5296483 (s : real -> Prop) (b : real) : (term251 s b) = (term236 s b).
Proof. exact (eq_refl (term251 s b)). Qed.
Lemma lem5296484 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5296485 (s : real -> Prop) (b : real) (x : real) : (term252 s b x) = (term253 s b x).
Proof. exact (MK_COMB (@lem5296483 s b) (@lem5296484 x)). Qed.
Lemma lem5296486 (s : real -> Prop) (x : real) (b : real) : (term253 s b x) = (term229 s x b).
Proof. exact (eq_refl (term253 s b x)). Qed.
Lemma lem5296487 (s : real -> Prop) (x : real) (b : real) : (term252 s b x) = (term229 s x b).
Proof. exact (TRANS (@lem5296485 s b x) (@lem5296486 s x b)). Qed.
Lemma lem5296488 (s : real -> Prop) (b : real) : (term254 s b) = (term236 s b).
Proof. exact (fun_ext (fun x : real => @lem5296487 s x b)). Qed.
Lemma lem5296489 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5296490 (s : real -> Prop) (b : real) : (term255 s b) = (term237 s b).
Proof. exact (MK_COMB (@lem5296489) (@lem5296488 s b)). Qed.
Lemma lem5296491 (s : real -> Prop) : (term256 s) = (term242 s).
Proof. exact (fun_ext (fun b : real => @lem5296490 s b)). Qed.
Lemma lem5296492 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296493 (s : real -> Prop) : (term248 s) = (term243 s).
Proof. exact (MK_COMB (@lem5296492) (@lem5296491 s)). Qed.
Lemma lem5296494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5296495 (s : real -> Prop) : (term257 s) = (term258 s).
Proof. exact (MK_COMB (@lem5296494) (@lem5296493 s)). Qed.
Lemma lem5296496 (s : real -> Prop) (b : real) : (term251 s b) = (term236 s b).
Proof. exact (eq_refl (term251 s b)). Qed.
Lemma lem5296497 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5296498 (s : real -> Prop) (x : real -> real) (b : real) : (term259 s x b) = (term260 s x b).
Proof. exact (MK_COMB (@lem5296496 s b) (@lem5296497 x b)). Qed.
Lemma lem5296499 (s : real -> Prop) (x : real -> real) (b : real) : (term260 s x b) = (term261 s x b).
Proof. exact (eq_refl (term260 s x b)). Qed.
Lemma lem5296500 (s : real -> Prop) (x : real -> real) (b : real) : (term259 s x b) = (term261 s x b).
Proof. exact (TRANS (@lem5296498 s x b) (@lem5296499 s x b)). Qed.
Lemma lem5296501 (s : real -> Prop) (x : real -> real) : (term262 s x) = (term263 s x).
Proof. exact (fun_ext (fun b : real => @lem5296500 s x b)). Qed.
Lemma lem5296502 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296503 (s : real -> Prop) (x : real -> real) : (term264 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5296502) (@lem5296501 s x)). Qed.
Lemma lem5296504 (s : real -> Prop) : (term266 s) = (term267 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5296503 s x)). Qed.
Lemma lem5296505 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5296506 (s : real -> Prop) : (term249 s) = (term268 s).
Proof. exact (MK_COMB (@lem5296505) (@lem5296504 s)). Qed.
Lemma lem5296507 (s : real -> Prop) : ((term248 s) = (term249 s)) = ((term243 s) = (term268 s)).
Proof. exact (MK_COMB (@lem5296495 s) (@lem5296506 s)). Qed.
Lemma lem5296509 (s : real -> Prop) : (term243 s) = (term268 s).
Proof. exact (EQ_MP (@lem5296507 s) (@lem5296482 s)). Qed.
Lemma lem5296510 (s : real -> Prop) : (term197 s) = (term268 s).
Proof. exact (TRANS (@lem5296425 s) (@lem5296509 s)). Qed.
Lemma lem5296511 (s : real -> Prop) (h1 : term197 s) : term268 s.
Proof. exact (EQ_MP (@lem5296510 s) (@lem5296323 s h1)). Qed.
Lemma lem5296512 (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term265 s x.
Proof. exact (h1). Qed.
Lemma lem5296535 (s : real -> Prop) (x : real) (b : real) : (term225 s x b) = (term225 s x b).
Proof. exact (eq_refl (term225 s x b)). Qed.
Lemma lem5296536 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (fun_ext (fun x : real => @lem5296535 s x b)). Qed.
Lemma lem5296537 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296538 (s : real -> Prop) (b : real) : (term227 s b) = (term227 s b).
Proof. exact (MK_COMB (@lem5296537) (@lem5296536 s b)). Qed.
Lemma lem5296539 (s : real -> Prop) (b : real) (h1 : term25 s b) : term227 s b.
Proof. exact (EQ_MP (@lem5296538 s b) (@lem5296392 s b h1)). Qed.
Lemma lem5296566 (s : real -> Prop) (x : real -> real) (b : real) : (term261 s x b) = (term261 s x b).
Proof. exact (eq_refl (term261 s x b)). Qed.
Lemma lem5296567 (s : real -> Prop) (x : real -> real) : (term263 s x) = (term263 s x).
Proof. exact (fun_ext (fun b : real => @lem5296566 s x b)). Qed.
Lemma lem5296568 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296569 (s : real -> Prop) (x : real -> real) : (term265 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5296568) (@lem5296567 s x)). Qed.
Lemma lem5296570 (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term265 s x.
Proof. exact (EQ_MP (@lem5296569 s x) (@lem5296512 s x h1)). Qed.
Lemma lem5296582 (s : real -> Prop) (x : real) (b : real) : (term225 s x b) = (term225 s x b).
Proof. exact (eq_refl (term225 s x b)). Qed.
Lemma lem5296583 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (fun_ext (fun x : real => @lem5296582 s x b)). Qed.
Lemma lem5296584 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296586 (s : real -> Prop) (b : real) : (term227 s b) = (term227 s b).
Proof. exact (MK_COMB (@lem5296584) (@lem5296583 s b)). Qed.
Lemma lem5296587 (s : real -> Prop) (b : real) (h1 : term25 s b) : term227 s b.
Proof. exact (EQ_MP (@lem5296586 s b) (@lem5296539 s b h1)). Qed.
Lemma lem5296597 (s : real -> Prop) (x : real -> real) (b : real) : (term261 s x b) = (term261 s x b).
Proof. exact (eq_refl (term261 s x b)). Qed.
Lemma lem5296598 (s : real -> Prop) (x : real -> real) : (term263 s x) = (term263 s x).
Proof. exact (fun_ext (fun b : real => @lem5296597 s x b)). Qed.
Lemma lem5296599 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5296601 (s : real -> Prop) (x : real -> real) : (term265 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5296599) (@lem5296598 s x)). Qed.
Lemma lem5296602 (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term265 s x.
Proof. exact (EQ_MP (@lem5296601 s x) (@lem5296570 s x h1)). Qed.
Lemma lem5296603 (_69330 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term269 s b _69330.
Proof. exact (@lem5296587 s b h1 _69330). Qed.
Lemma lem5296604 (s : real -> Prop) (_69330 : real) (b : real) : (term269 s b _69330) = (term225 s _69330 b).
Proof. exact (eq_refl (term269 s b _69330)). Qed.
Lemma lem5296606 (_69331 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term270 s x _69331.
Proof. exact (@lem5296602 s x h1 _69331). Qed.
Lemma lem5296607 (s : real -> Prop) (x : real -> real) (_69331 : real) : (term270 s x _69331) = (term261 s x _69331).
Proof. exact (eq_refl (term270 s x _69331)). Qed.
Lemma lem5296608 (_69331 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term261 s x _69331.
Proof. exact (EQ_MP (@lem5296607 s x _69331) (@lem5296606 _69331 s x h1)). Qed.
Lemma lem5296667 (_69330 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term225 s _69330 b.
Proof. exact (EQ_MP (@lem5296604 s _69330 b) (@lem5296603 _69330 s b h1)). Qed.
Lemma lem5296695 (_69331 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term271 x _69331.
Proof. exact (proj2 (@lem5296608 _69331 s x h1)). Qed.
Lemma lem5296747 (_69331 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term272 x _69331 s.
Proof. exact (proj1 (@lem5296608 _69331 s x h1)). Qed.
Lemma lem5296748 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term272 x b s.
Proof. exact (@lem5296747 b s x h1). Qed.
Lemma lem5296749 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term273 x b s.
Proof. exact (fun h0 : term274 x b s => @lem5296748 b s x h1). Qed.
Lemma lem5296751 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5296752 (x : real -> real) (b : real) (s : real -> Prop) : (term273 x b s) = (term272 x b s).
Proof. exact (@lem5296751 (term272 x b s)). Qed.
Lemma lem5296753 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term272 x b s.
Proof. exact (EQ_MP (@lem5296752 x b s) (@lem5296749 b s x h1)). Qed.
Lemma lem5296759 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5296760 (b : real) (_69330 : real) (s : real -> Prop) : (term225 s _69330 b) = (term275 b _69330 s).
Proof. exact (@lem5296759 (real_le _69330 b) (term276 _69330 s)). Qed.
Lemma lem5296766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5296767 (b : real) (_69330 : real) (s : real -> Prop) : (term277 s _69330 b) = (term278 b _69330 s).
Proof. exact (MK_COMB (@lem5296766) (@lem5296760 b _69330 s)). Qed.
Lemma lem5296773 (b : real) (_69330 : real) (s : real -> Prop) : (term275 b _69330 s) = (term275 b _69330 s).
Proof. exact (eq_refl (term275 b _69330 s)). Qed.
Lemma lem5296774 (b : real) (_69330 : real) (s : real -> Prop) : ((term225 s _69330 b) = (term275 b _69330 s)) = ((term275 b _69330 s) = (term275 b _69330 s)).
Proof. exact (MK_COMB (@lem5296767 b _69330 s) (@lem5296773 b _69330 s)). Qed.
Lemma lem5296776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5296777 (x : Prop) : (x = x) = True.
Proof. exact (@lem5296776 Prop x). Qed.
Lemma lem5296778 (b : real) (_69330 : real) (s : real -> Prop) : ((term275 b _69330 s) = (term275 b _69330 s)) = True.
Proof. exact (@lem5296777 (term275 b _69330 s)). Qed.
Lemma lem5296779 (b : real) (_69330 : real) (s : real -> Prop) : ((term225 s _69330 b) = (term275 b _69330 s)) = True.
Proof. exact (TRANS (@lem5296774 b _69330 s) (@lem5296778 b _69330 s)). Qed.
Lemma lem5296780 (b : real) (_69330 : real) (s : real -> Prop) : True = ((term225 s _69330 b) = (term275 b _69330 s)).
Proof. exact (SYM (@lem5296779 b _69330 s)). Qed.
Lemma lem5296781 (b : real) (_69330 : real) (s : real -> Prop) : (term225 s _69330 b) = (term275 b _69330 s).
Proof. exact (EQ_MP (@lem5296780 b _69330 s) (@lem0)). Qed.
Lemma lem5296782 (_69330 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term275 b _69330 s.
Proof. exact (EQ_MP (@lem5296781 b _69330 s) (@lem5296667 _69330 s b h1)). Qed.
Lemma lem5296784 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5296785 (s : real -> Prop) (_69330 : real) (b : real) : (term275 b _69330 s) = (term280 s _69330 b).
Proof. exact (@lem5296784 (term276 _69330 s) (real_le _69330 b)). Qed.
Lemma lem5296787 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5296788 (_69330 : real) (s : real -> Prop) : (term281 _69330 s) = (@IN real _69330 s).
Proof. exact (@lem5296787 (@IN real _69330 s)). Qed.
Lemma lem5296789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5296790 (_69330 : real) (s : real -> Prop) : (term282 _69330 s) = (term283 _69330 s).
Proof. exact (MK_COMB (@lem5296789) (@lem5296788 _69330 s)). Qed.
Lemma lem5296791 (_69330 : real) (b : real) : (real_le _69330 b) = (real_le _69330 b).
Proof. exact (eq_refl (real_le _69330 b)). Qed.
Lemma lem5296792 (s : real -> Prop) (_69330 : real) (b : real) : (term280 s _69330 b) = (term223 s _69330 b).
Proof. exact (MK_COMB (@lem5296790 _69330 s) (@lem5296791 _69330 b)). Qed.
Lemma lem5296793 (s : real -> Prop) (_69330 : real) (b : real) : (term275 b _69330 s) = (term223 s _69330 b).
Proof. exact (TRANS (@lem5296785 s _69330 b) (@lem5296792 s _69330 b)). Qed.
Lemma lem5296796 (_69330 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term223 s _69330 b.
Proof. exact (EQ_MP (@lem5296793 s _69330 b) (@lem5296782 _69330 s b h1)). Qed.
Lemma lem5296797 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term284 s x b.
Proof. exact (@lem5296796 (x b) s b h1). Qed.
Lemma lem5296800 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term285 x b.
Proof. exact (@lem5296797 x s b h2 (@lem5296753 b s x h1)). Qed.
Lemma lem5296801 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term286 x b.
Proof. exact (fun h0 : term271 x b => @lem5296800 x s b h1 h2). Qed.
Lemma lem5296803 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5296804 (x : real -> real) (b : real) : (term286 x b) = (term285 x b).
Proof. exact (@lem5296803 (term285 x b)). Qed.
Lemma lem5296805 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term285 x b.
Proof. exact (EQ_MP (@lem5296804 x b) (@lem5296801 x s b h1 h2)). Qed.
Lemma lem5296808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5296810 (x : real -> real) (_69331 : real) : (term271 x _69331) = (term287 x _69331).
Proof. exact (@lem5296808 (term285 x _69331)). Qed.
Lemma lem5296813 (_69331 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term287 x _69331.
Proof. exact (EQ_MP (@lem5296810 x _69331) (@lem5296695 _69331 s x h1)). Qed.
Lemma lem5296814 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term287 x b.
Proof. exact (@lem5296813 b s x h1). Qed.
Lemma lem5296817 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (@lem5296814 b s x h1 (@lem5296805 x s b h1 h2)). Qed.
Lemma lem5296818 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term184.
Proof. exact (fun h0 : ~ False => @lem5296817 x s b h1 h2). Qed.
Lemma lem5296820 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5296821 : term184 = False.
Proof. exact (@lem5296820 False). Qed.
Lemma lem5296823 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (EQ_MP (@lem5296821) (@lem5296818 x s b h1 h2)). Qed.
Lemma lem5296824 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : (term265 s x) = False.
Proof. exact (prop_ext (fun h3 : term265 s x => @lem5296823 x s b h1 h2) (fun h3 : False => @lem5296602 s x h1)). Qed.
Lemma lem5296825 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (EQ_MP (@lem5296824 x s b h1 h2) (@lem5296602 s x h1)). Qed.
Lemma lem5296826 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : (term265 s x) = False.
Proof. exact (prop_ext (fun h3 : term265 s x => @lem5296825 x s b h1 h2) (fun h3 : False => @lem5296570 s x h1)). Qed.
Lemma lem5296827 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (EQ_MP (@lem5296826 x s b h1 h2) (@lem5296570 s x h1)). Qed.
Lemma lem5296828 (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term197 s) : False.
Proof. exact (ex_elim (@lem5296511 s h2) (fun x : real -> real => fun h0 : term267 s x => @lem5296827 x s b h0 h1)). Qed.
Lemma lem5296829 (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term197 s) : (term197 s) = False.
Proof. exact (prop_ext (fun h3 : term197 s => @lem5296828 b s h1 h2) (fun h3 : False => @lem5296323 s h2)). Qed.
Lemma lem5296830 (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term197 s) : False.
Proof. exact (EQ_MP (@lem5296829 b s h1 h2) (@lem5296323 s h2)). Qed.
Lemma lem5296831 (s : real -> Prop) (b : real) (h1 : term25 s b) : term196 s.
Proof. exact (fun h0 : term197 s => @lem5296830 b s h1 h0). Qed.
Lemma lem5296832 (s : real -> Prop) (b : real) (h1 : term25 s b) : term24 s.
Proof. exact (EQ_MP (@lem5296322 s) (@lem5296831 s b h1)). Qed.
Lemma lem5296833 (l : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term205 l s.
Proof. exact (fun h0 : (sup s) = l => @lem5296832 s b h1). Qed.
Lemma lem5296834 (b : real) (l : real) (s : real -> Prop) : term208 b l s.
Proof. exact (fun h0 : term25 s b => @lem5296833 l s b h0). Qed.
Lemma lem5296835 (b : real) (l : real) (s : real -> Prop) : term210 b l s.
Proof. exact (fun h0 : term23 s => @lem5296834 b l s). Qed.
Lemma lem5296840 (l : real) (s : real -> Prop) : term214 l s.
Proof. exact (fun b : real => @lem5296835 b l s). Qed.
Lemma lem5296845 (s : real -> Prop) : term218 s.
Proof. exact (fun l : real => @lem5296840 l s). Qed.
Lemma lem5296850 : term222.
Proof. exact (fun s : real -> Prop => @lem5296845 s). Qed.
Lemma lem5296851 : term221.
Proof. exact (EQ_MP (@lem5296315) (@lem5296850)). Qed.
Lemma lem5296852 (s : real -> Prop) : term288 s.
Proof. exact (@lem5296851 s). Qed.
Lemma lem5296853 (s : real -> Prop) : (term288 s) = (term217 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5296854 (s : real -> Prop) : term217 s.
Proof. exact (EQ_MP (@lem5296853 s) (@lem5296852 s)). Qed.
Lemma lem5296855 (s : real -> Prop) (l : real) : term289 s l.
Proof. exact (@lem5296854 s l). Qed.
Lemma lem5296856 (l : real) (s : real -> Prop) : (term289 s l) = (term213 l s).
Proof. exact (eq_refl (term289 s l)). Qed.
Lemma lem5296857 (l : real) (s : real -> Prop) : term213 l s.
Proof. exact (EQ_MP (@lem5296856 l s) (@lem5296855 s l)). Qed.
Lemma lem5296858 (l : real) (s : real -> Prop) (b : real) : term290 l s b.
Proof. exact (@lem5296857 l s b). Qed.
Lemma lem5296859 (b : real) (l : real) (s : real -> Prop) : (term290 l s b) = (term198 b l s).
Proof. exact (eq_refl (term290 l s b)). Qed.
Lemma lem5296860 (b : real) (l : real) (s : real -> Prop) : term198 b l s.
Proof. exact (EQ_MP (@lem5296859 b l s) (@lem5296858 l s b)). Qed.
Lemma lem5296862 (b : real) (l : real) (s : real -> Prop) : term198 b l s.
Proof. exact (@lem5296146 b l s (@lem5296860 b l s)). Qed.
Lemma lem5296863 (b : real) (l : real) (s : real -> Prop) (h1 : term23 s) : term207 b l s.
Proof. exact (@lem5296862 b l s (@lem5295360 s h1)). Qed.
Lemma lem5296864 (l : real) (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term23 s) : term204 l s.
Proof. exact (@lem5296863 b l s h2 (@lem5295363 s b h1)). Qed.
Lemma lem5296865 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term196 s.
Proof. exact (@lem5296864 l b s h1 h2 (@lem5295361 s l h3)). Qed.
Lemma lem5296866 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term197 s) (h3 : term23 s) (h4 : (sup s) = l) : False.
Proof. exact (@lem5296865 b s l h1 h3 h4 (@lem5296131 s h2)). Qed.
Lemma lem5296867 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term197 s) (h3 : term23 s) (h4 : (sup s) = l) : (term197 s) = False.
Proof. exact (prop_ext (fun h5 : term197 s => @lem5296866 b s l h1 h2 h3 h4) (fun h5 : False => @lem5296131 s h2)). Qed.
Lemma lem5296868 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term197 s) (h3 : term23 s) (h4 : (sup s) = l) : False.
Proof. exact (EQ_MP (@lem5296867 b s l h1 h2 h3 h4) (@lem5296131 s h2)). Qed.
Lemma lem5296869 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term196 s.
Proof. exact (fun h0 : term197 s => @lem5296868 b s l h1 h0 h2 h3). Qed.
Lemma lem5296870 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term24 s.
Proof. exact (EQ_MP (@lem5296130 s) (@lem5296869 b s l h1 h2 h3)). Qed.
Lemma lem5296871 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term191 s.
Proof. exact (EQ_MP (@lem5296126 s h2) (@lem5296870 b s l h1 h2 h3)). Qed.
Lemma lem5296872 (s : real -> Prop) (l : real) (c : real) : (term291 s l c) = (term291 s l c).
Proof. exact (eq_refl (term291 s l c)). Qed.
Lemma lem5296873 (c : real) (s : real -> Prop) (l : real) (h1 : (sup s) = l) : (term292 l c s) = (term293 s c l).
Proof. exact (MK_COMB (@lem5296872 s l c) (@lem5295361 s l h1)). Qed.
Lemma lem5296874 (s : real -> Prop) (l : real) (c : real) : (term293 s c l) = (term294 s l c).
Proof. exact (eq_refl (term293 s c l)). Qed.
Lemma lem5296875 (l : real) (c : real) (s : real -> Prop) : (term295 l c s) = (term295 l c s).
Proof. exact (eq_refl (term295 l c s)). Qed.
Lemma lem5296876 (s : real -> Prop) (l : real) (c : real) : ((term292 l c s) = (term293 s c l)) = ((term292 l c s) = (term294 s l c)).
Proof. exact (MK_COMB (@lem5296875 l c s) (@lem5296874 s l c)). Qed.
Lemma lem5296877 (s : real -> Prop) (l : real) (c : real) : (term292 l c s) = (term296 s l c).
Proof. exact (eq_refl (term292 l c s)). Qed.
Lemma lem5296878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5296879 (s : real -> Prop) (l : real) (c : real) : (term295 l c s) = (term297 s l c).
Proof. exact (MK_COMB (@lem5296878) (@lem5296877 s l c)). Qed.
Lemma lem5296880 (s : real -> Prop) (l : real) (c : real) : (term294 s l c) = (term294 s l c).
Proof. exact (eq_refl (term294 s l c)). Qed.
Lemma lem5296881 (s : real -> Prop) (l : real) (c : real) : ((term292 l c s) = (term294 s l c)) = ((term296 s l c) = (term294 s l c)).
Proof. exact (MK_COMB (@lem5296879 s l c) (@lem5296880 s l c)). Qed.
Lemma lem5296882 (s : real -> Prop) (l : real) (c : real) : ((term292 l c s) = (term293 s c l)) = ((term296 s l c) = (term294 s l c)).
Proof. exact (TRANS (@lem5296876 s l c) (@lem5296881 s l c)). Qed.
Lemma lem5296883 (c : real) (s : real -> Prop) (l : real) (h1 : (sup s) = l) : (term296 s l c) = (term294 s l c).
Proof. exact (EQ_MP (@lem5296882 s l c) (@lem5296873 c s l h1)). Qed.
Lemma lem5296884 (c : real) (s : real -> Prop) (l : real) (h1 : (sup s) = l) : (term294 s l c) = (term296 s l c).
Proof. exact (SYM (@lem5296883 c s l h1)). Qed.
Lemma lem5296913 (s : real -> Prop) (l : real) (h1 : term298 s l) : term298 s l.
Proof. exact (h1). Qed.
Lemma lem5296914 (s : real -> Prop) (l : real) (h1 : term299 s l) : term299 s l.
Proof. exact (h1). Qed.
Lemma lem5296915 (s : real -> Prop) (l : real) (h1 : term25 s l) : term25 s l.
Proof. exact (h1). Qed.
Lemma lem5296939 (b : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : term300 s l b.
Proof. exact (@lem5296914 s l h1 b). Qed.
Lemma lem5296940 (s : real -> Prop) (l : real) (b : real) : (term300 s l b) = (term301 s l b).
Proof. exact (eq_refl (term300 s l b)). Qed.
Lemma lem5296941 (b : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : term301 s l b.
Proof. exact (EQ_MP (@lem5296940 s l b) (@lem5296939 b s l h1)). Qed.
Lemma lem5296942 (s : real -> Prop) (l : real) (b : real) : (term301 s l b) = ((term301 s l b) = True).
Proof. exact (@lem7 (term301 s l b)). Qed.
Lemma lem5296945 (b : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : (term301 s l b) = True.
Proof. exact (EQ_MP (@lem5296942 s l b) (@lem5296941 b s l h1)). Qed.
Lemma lem5296946 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : (term301 s l c) = True.
Proof. exact (@lem5296945 c s l h1). Qed.
Lemma lem5296947 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : True = (term301 s l c).
Proof. exact (SYM (@lem5296946 c s l h1)). Qed.
Lemma lem5296948 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : term301 s l c.
Proof. exact (EQ_MP (@lem5296947 c s l h1) (@lem0)). Qed.
Lemma lem5296987 (l : real) (c : real) (h1 : real_le l c) : real_le l c.
Proof. exact (h1). Qed.
Lemma lem5296988 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5296989 (h1 : term302) : term302.
Proof. exact (h1). Qed.
Lemma lem5296990 (x : real) (h1 : term302) : term303 x.
Proof. exact (@lem5296989 h1 x). Qed.
Lemma lem5296991 (x : real) : (term303 x) = (term304 x).
Proof. exact (eq_refl (term303 x)). Qed.
Lemma lem5296992 (x : real) (h1 : term302) : term304 x.
Proof. exact (EQ_MP (@lem5296991 x) (@lem5296990 x h1)). Qed.
Lemma lem5296993 (x : real) (y : real) (h1 : term302) : term305 x y.
Proof. exact (@lem5296992 x h1 y). Qed.
Lemma lem5296994 (y : real) (x : real) : (term305 x y) = (term306 y x).
Proof. exact (eq_refl (term305 x y)). Qed.
Lemma lem5296995 (y : real) (x : real) (h1 : term302) : term306 y x.
Proof. exact (EQ_MP (@lem5296994 y x) (@lem5296993 x y h1)). Qed.
Lemma lem5296996 (y : real) (x : real) (z : real) (h1 : term302) : term307 y x z.
Proof. exact (@lem5296995 y x h1 z). Qed.
Lemma lem5296997 (y : real) (x : real) (z : real) : (term307 y x z) = (term308 y x z).
Proof. exact (eq_refl (term307 y x z)). Qed.
Lemma lem5296998 (y : real) (x : real) (z : real) (h1 : term302) : term308 y x z.
Proof. exact (EQ_MP (@lem5296997 y x z) (@lem5296996 y x z h1)). Qed.
Lemma lem5296999 (x : real) (y : real) (z : real) (h1 : term309 x y z) : term309 x y z.
Proof. exact (h1). Qed.
Lemma lem5297000 (x : real) (y : real) (z : real) (h1 : term302) (h2 : term309 x y z) : real_le x z.
Proof. exact (@lem5296998 y x z h1 (@lem5296999 x y z h2)). Qed.
Lemma lem5297001 (x : real) (y : real) (z : real) (h1 : term309 x y z) : term310 x z.
Proof. exact (fun h0 : term302 => @lem5297000 x y z h0 h1). Qed.
Lemma lem5297002 (x : real) (z : real) (h1 : term311 x z) : term311 x z.
Proof. exact (h1). Qed.
Lemma lem5297003 (x : real) (z : real) (h1 : term311 x z) : term310 x z.
Proof. exact (ex_elim (@lem5297002 x z h1) (fun y : real => fun h0 : term312 x z y => @lem5297001 x y z h0)). Qed.
Lemma lem5297004 (h1 : term302) : term302.
Proof. exact (h1). Qed.
Lemma lem5297005 (x : real) (z : real) (h1 : term302) (h2 : term311 x z) : real_le x z.
Proof. exact (@lem5297003 x z h2 (@lem5297004 h1)). Qed.
Lemma lem5297006 (x : real) (z : real) (h1 : term302) : term313 x z.
Proof. exact (fun h0 : term311 x z => @lem5297005 x z h1 h0). Qed.
Lemma lem5297007 (x : real) (h1 : term302) : term314 x.
Proof. exact (fun z : real => @lem5297006 x z h1). Qed.
Lemma lem5297008 (h1 : term302) : term315.
Proof. exact (fun x : real => @lem5297007 x h1). Qed.
Lemma lem5297009 : term316.
Proof. exact (fun h0 : term302 => @lem5297008 h0). Qed.
Lemma lem5297010 : term315.
Proof. exact (@lem5297009 (@lem1339577)). Qed.
Lemma lem5297011 (x : real) : term317 x.
Proof. exact (@lem5297010 x). Qed.
Lemma lem5297012 (x : real) : (term317 x) = (term314 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem5297013 (x : real) : term314 x.
Proof. exact (EQ_MP (@lem5297012 x) (@lem5297011 x)). Qed.
Lemma lem5297014 (x : real) (z : real) : term318 x z.
Proof. exact (@lem5297013 x z). Qed.
Lemma lem5297015 (x : real) (z : real) : (term318 x z) = (term313 x z).
Proof. exact (eq_refl (term318 x z)). Qed.
Lemma lem5297018 (x : real) (z : real) : term313 x z.
Proof. exact (EQ_MP (@lem5297015 x z) (@lem5297014 x z)). Qed.
Lemma lem5297019 (x : real) (c : real) : term313 x c.
Proof. exact (@lem5297018 x c). Qed.
Lemma lem5297045 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term233 s l x.
Proof. exact (@lem5296915 s l h1 x). Qed.
Lemma lem5297046 (s : real -> Prop) (x : real) (l : real) : (term233 s l x) = (term223 s x l).
Proof. exact (eq_refl (term233 s l x)). Qed.
Lemma lem5297047 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term223 s x l.
Proof. exact (EQ_MP (@lem5297046 s x l) (@lem5297045 x s l h1)). Qed.
Lemma lem5297048 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5297049 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : real_le x l.
Proof. exact (@lem5297047 x s l h1 (@lem5297048 x s h2)). Qed.
Lemma lem5297050 (x : real) (l : real) : (real_le x l) = ((real_le x l) = True).
Proof. exact (@lem7 (real_le x l)). Qed.
Lemma lem5297051 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le x l) = True.
Proof. exact (EQ_MP (@lem5297050 x l) (@lem5297049 l x s h1 h2)). Qed.
Lemma lem5297069 (l : real) (c : real) : (real_le l c) = ((real_le l c) = True).
Proof. exact (@lem7 (real_le l c)). Qed.
Lemma lem5297071 (x : real) (s : real -> Prop) : (@IN real x s) = ((@IN real x s) = True).
Proof. exact (@lem7 (@IN real x s)). Qed.
Lemma lem5297076 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term319 s x l.
Proof. exact (fun h0 : @IN real x s => @lem5297051 l x s h1 h0). Qed.
Lemma lem5297078 (x : real) (s : real -> Prop) (h1 : @IN real x s) : (@IN real x s) = True.
Proof. exact (EQ_MP (@lem5297071 x s) (@lem5296988 x s h1)). Qed.
Lemma lem5297079 (x : real) (s : real -> Prop) (h1 : @IN real x s) : True = (@IN real x s).
Proof. exact (SYM (@lem5297078 x s h1)). Qed.
Lemma lem5297080 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (EQ_MP (@lem5297079 x s h1) (@lem0)). Qed.
Lemma lem5297081 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le x l) = True.
Proof. exact (@lem5297076 x s l h1 (@lem5297080 x s h2)). Qed.
Lemma lem5297082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5297083 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (term320 x l) = (and True).
Proof. exact (MK_COMB (@lem5297082) (@lem5297081 l x s h1 h2)). Qed.
Lemma lem5297085 (l : real) (c : real) (h1 : real_le l c) : (real_le l c) = True.
Proof. exact (EQ_MP (@lem5297069 l c) (@lem5296987 l c h1)). Qed.
Lemma lem5297086 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : (term309 x l c) = (True /\ True).
Proof. exact (MK_COMB (@lem5297083 l x s h1 h2) (@lem5297085 l c h3)). Qed.
Lemma lem5297088 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5297089 : (True /\ True) = True.
Proof. exact (@lem5297088 True). Qed.
Lemma lem5297090 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : (term309 x l c) = True.
Proof. exact (TRANS (@lem5297086 x s l c h1 h2 h3) (@lem5297089)). Qed.
Lemma lem5297091 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : True = (term309 x l c).
Proof. exact (SYM (@lem5297090 x s l c h1 h2 h3)). Qed.
Lemma lem5297092 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : term309 x l c.
Proof. exact (EQ_MP (@lem5297091 x s l c h1 h2 h3) (@lem0)). Qed.
Lemma lem5297093 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : term311 x c.
Proof. exact (ex_intro (term312 x c) l (@lem5297092 x s l c h1 h2 h3)). Qed.
Lemma lem5297094 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : real_le x c.
Proof. exact (@lem5297019 x c (@lem5297093 x s l c h1 h2 h3)). Qed.
Lemma lem5297095 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : (@IN real x s) = (real_le x c).
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5297094 x s l c h1 h2 h3) (fun h4 : real_le x c => @lem5296988 x s h2)). Qed.
Lemma lem5297096 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le l c) : real_le x c.
Proof. exact (EQ_MP (@lem5297095 x s l c h1 h2 h3) (@lem5296988 x s h2)). Qed.
Lemma lem5297097 (x : real) (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : term223 s x c.
Proof. exact (fun h0 : @IN real x s => @lem5297096 x s l c h1 h0 h2). Qed.
Lemma lem5297102 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : term25 s c.
Proof. exact (fun x : real => @lem5297097 x s l c h1 h2). Qed.
Lemma lem5297103 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : (real_le l c) = (term25 s c).
Proof. exact (prop_ext (fun h3 : real_le l c => @lem5297102 s l c h1 h2) (fun h3 : term25 s c => @lem5296987 l c h2)). Qed.
Lemma lem5297104 (s : real -> Prop) (l : real) (c : real) (h1 : term25 s l) (h2 : real_le l c) : term25 s c.
Proof. exact (EQ_MP (@lem5297103 s l c h1 h2) (@lem5296987 l c h2)). Qed.
Lemma lem5297106 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term321 l s c.
Proof. exact (fun h0 : real_le l c => @lem5297104 s l c h1 h0). Qed.
Lemma lem5297107 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : term322 l s c.
Proof. exact (conj (@lem5296948 c s l h1) (@lem5297106 c s l h2)). Qed.
Lemma lem5297108 (s : real -> Prop) (l : real) (c : real) : (term322 l s c) = ((term25 s c) = (real_le l c)).
Proof. exact (@lem32 (term25 s c) (real_le l c)). Qed.
Lemma lem5297109 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5297108 s l c) (@lem5297107 c s l h1 h2)). Qed.
Lemma lem5297110 (s : real -> Prop) (l : real) (h1 : term298 s l) : term299 s l.
Proof. exact (proj2 (@lem5296913 s l h1)). Qed.
Lemma lem5297111 (s : real -> Prop) (l : real) (h1 : term298 s l) : term25 s l.
Proof. exact (proj1 (@lem5296913 s l h1)). Qed.
Lemma lem5297112 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term299 s l) = ((term25 s c) = (real_le l c)).
Proof. exact (prop_ext (fun h3 : term299 s l => @lem5297109 c s l h1 h2) (fun h3 : (term25 s c) = (real_le l c) => @lem5296914 s l h1)). Qed.
Lemma lem5297113 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5297112 c s l h1 h2) (@lem5296914 s l h1)). Qed.
Lemma lem5297114 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s l) = ((term25 s c) = (real_le l c)).
Proof. exact (prop_ext (fun h3 : term25 s l => @lem5297113 c s l h1 h2) (fun h3 : (term25 s c) = (real_le l c) => @lem5296915 s l h2)). Qed.
Lemma lem5297115 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5297114 c s l h1 h2) (@lem5296915 s l h2)). Qed.
Lemma lem5297116 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) (h2 : term298 s l) : (term299 s l) = ((term25 s c) = (real_le l c)).
Proof. exact (prop_ext (fun h3 : term299 s l => @lem5297115 c s l h3 h1) (fun h3 : (term25 s c) = (real_le l c) => @lem5297110 s l h2)). Qed.
Lemma lem5297117 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) (h2 : term298 s l) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5297116 c s l h1 h2) (@lem5297110 s l h2)). Qed.
Lemma lem5297118 (c : real) (s : real -> Prop) (l : real) (h1 : term298 s l) : (term25 s l) = ((term25 s c) = (real_le l c)).
Proof. exact (prop_ext (fun h2 : term25 s l => @lem5297117 c s l h2 h1) (fun h2 : (term25 s c) = (real_le l c) => @lem5297111 s l h1)). Qed.
Lemma lem5297119 (c : real) (s : real -> Prop) (l : real) (h1 : term298 s l) : (term25 s c) = (real_le l c).
Proof. exact (EQ_MP (@lem5297118 c s l h1) (@lem5297111 s l h1)). Qed.
Lemma lem5297120 (s : real -> Prop) (l : real) (c : real) : term294 s l c.
Proof. exact (fun h0 : term298 s l => @lem5297119 c s l h0). Qed.
Lemma lem5297121 (c : real) (s : real -> Prop) (l : real) (h1 : (sup s) = l) : term296 s l c.
Proof. exact (EQ_MP (@lem5296884 c s l h1) (@lem5297120 s l c)). Qed.
Lemma lem5297122 (c : real) (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term323 s l c.
Proof. exact (conj (@lem5296871 b s l h1 h2 h3) (@lem5297121 c s l h3)). Qed.
Lemma lem5297123 (c : real) (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term324 s l c.
Proof. exact (@lem5296042 s l c (@lem5297122 c b s l h1 h2 h3)). Qed.
Lemma lem5297124 (c : real) (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : (term25 s c) = (real_le l c).
Proof. exact (@lem5297123 c b s l h1 h2 h3 (@lem5295267 s)). Qed.
Lemma lem5297129 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term7 s l.
Proof. exact (fun c : real => @lem5297124 c b s l h1 h2 h3). Qed.
Lemma lem5297130 (s : real -> Prop) (l : real) (h1 : term21 s l) : term22 s l.
Proof. exact (proj2 (@lem5295358 s l h1)). Qed.
Lemma lem5297131 (s : real -> Prop) (l : real) (h1 : term21 s l) : term23 s.
Proof. exact (proj1 (@lem5295358 s l h1)). Qed.
Lemma lem5297132 (s : real -> Prop) (l : real) (h1 : term22 s l) : (sup s) = l.
Proof. exact (proj2 (@lem5295359 s l h1)). Qed.
Lemma lem5297133 (s : real -> Prop) (l : real) (h1 : term22 s l) : term24 s.
Proof. exact (proj1 (@lem5295359 s l h1)). Qed.
Lemma lem5297134 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : ((sup s) = l) = (term7 s l).
Proof. exact (prop_ext (fun h4 : (sup s) = l => @lem5297129 b s l h1 h2 h3) (fun h4 : term7 s l => @lem5295361 s l h3)). Qed.
Lemma lem5297135 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term7 s l.
Proof. exact (EQ_MP (@lem5297134 b s l h1 h2 h3) (@lem5295361 s l h3)). Qed.
Lemma lem5297136 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : (term25 s b) = (term7 s l).
Proof. exact (prop_ext (fun h4 : term25 s b => @lem5297135 b s l h1 h2 h3) (fun h4 : term7 s l => @lem5295363 s b h1)). Qed.
Lemma lem5297137 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (sup s) = l) : term7 s l.
Proof. exact (EQ_MP (@lem5297136 b s l h1 h2 h3) (@lem5295363 s b h1)). Qed.
Lemma lem5297138 (s : real -> Prop) (l : real) (h1 : term24 s) (h2 : term23 s) (h3 : (sup s) = l) : term7 s l.
Proof. exact (ex_elim (@lem5295362 s h1) (fun b : real => fun h0 : term150 s b => @lem5297137 b s l h0 h2 h3)). Qed.
Lemma lem5297139 (s : real -> Prop) (l : real) (h1 : term24 s) (h2 : term23 s) (h3 : term22 s l) : ((sup s) = l) = (term7 s l).
Proof. exact (prop_ext (fun h4 : (sup s) = l => @lem5297138 s l h1 h2 h4) (fun h4 : term7 s l => @lem5297132 s l h3)). Qed.
Lemma lem5297140 (s : real -> Prop) (l : real) (h1 : term24 s) (h2 : term23 s) (h3 : term22 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5297139 s l h1 h2 h3) (@lem5297132 s l h3)). Qed.
Lemma lem5297141 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : (term24 s) = (term7 s l).
Proof. exact (prop_ext (fun h3 : term24 s => @lem5297140 s l h3 h1 h2) (fun h3 : term7 s l => @lem5297133 s l h2)). Qed.
Lemma lem5297142 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5297141 s l h1 h2) (@lem5297133 s l h2)). Qed.
Lemma lem5297143 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : (term23 s) = (term7 s l).
Proof. exact (prop_ext (fun h3 : term23 s => @lem5297142 s l h1 h2) (fun h3 : term7 s l => @lem5295360 s h1)). Qed.
Lemma lem5297144 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5297143 s l h1 h2) (@lem5295360 s h1)). Qed.
Lemma lem5297145 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term21 s l) : (term22 s l) = (term7 s l).
Proof. exact (prop_ext (fun h3 : term22 s l => @lem5297144 s l h1 h3) (fun h3 : term7 s l => @lem5297130 s l h2)). Qed.
Lemma lem5297146 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term21 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5297145 s l h1 h2) (@lem5297130 s l h2)). Qed.
Lemma lem5297147 (s : real -> Prop) (l : real) (h1 : term21 s l) : (term23 s) = (term7 s l).
Proof. exact (prop_ext (fun h2 : term23 s => @lem5297146 s l h2 h1) (fun h2 : term7 s l => @lem5297131 s l h1)). Qed.
Lemma lem5297148 (s : real -> Prop) (l : real) (h1 : term21 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5297147 s l h1) (@lem5297131 s l h1)). Qed.
Lemma lem5297149 (s : real -> Prop) (l : real) : term325 s l.
Proof. exact (fun h0 : term21 s l => @lem5297148 s l h0). Qed.
Lemma lem5297150 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term7 s l) = (term21 s l).
Proof. exact (prop_ext (fun h2 : term7 s l => @lem5296039 s l h1) (fun h2 : term21 s l => @lem5295357 s l h1)). Qed.
Lemma lem5297151 (s : real -> Prop) (l : real) (h1 : term7 s l) : term21 s l.
Proof. exact (EQ_MP (@lem5297150 s l h1) (@lem5295357 s l h1)). Qed.
Lemma lem5297152 (s : real -> Prop) (l : real) : term326 s l.
Proof. exact (fun h0 : term7 s l => @lem5297151 s l h0). Qed.
Lemma lem5297153 (s : real -> Prop) (l : real) : term327 s l.
Proof. exact (conj (@lem5297152 s l) (@lem5297149 s l)). Qed.
Lemma lem5297154 (s : real -> Prop) (l : real) : (term327 s l) = ((term7 s l) = (term21 s l)).
Proof. exact (@lem32 (term7 s l) (term21 s l)). Qed.
Lemma lem5297155 (s : real -> Prop) (l : real) : (term7 s l) = (term21 s l).
Proof. exact (EQ_MP (@lem5297154 s l) (@lem5297153 s l)). Qed.
Lemma lem5297156 (s : real -> Prop) (l : real) : (has_sup s l) = (term21 s l).
Proof. exact (EQ_MP (@lem5295356 s l) (@lem5297155 s l)). Qed.
Lemma lem5297161 (s : real -> Prop) : term328 s.
Proof. exact (fun l : real => @lem5297156 s l). Qed.
Lemma lem5297166 : term329.
Proof. exact (fun s : real -> Prop => @lem5297161 s). Qed.
