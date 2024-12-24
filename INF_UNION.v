Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_UNION_spec.
Require Import INF_spec.
Require Import INF_UNIQUE_spec.
Require Import REAL_LE_MIN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm69_spec.
Lemma lem5275335 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5275336 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5275337 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5275336 t1) (@lem5275335 t1)). Qed.
Lemma lem5275338 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5275337 t1 t2). Qed.
Lemma lem5275339 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5275340 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5275339 t1 t2) (@lem5275338 t1 t2)). Qed.
Lemma lem5275341 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5275340 t1 t2 t3). Qed.
Lemma lem5275342 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5275343 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5275342 t1 t2 t3) (@lem5275341 t1 t2 t3)). Qed.
Lemma lem5275344 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5275343 t1 t2 t3)). Qed.
Lemma lem5275345 (x : real) : term7 x.
Proof. exact (@lem1562409 x). Qed.
Lemma lem5275346 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem5275347 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem5275346 x) (@lem5275345 x)). Qed.
Lemma lem5275348 (x : real) (y : real) : term9 x y.
Proof. exact (@lem5275347 x y). Qed.
Lemma lem5275349 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem5275350 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem5275349 x y) (@lem5275348 x y)). Qed.
Lemma lem5275351 (x : real) (y : real) (z : real) : term11 x y z.
Proof. exact (@lem5275350 x y z). Qed.
Lemma lem5275352 (x : real) (z : real) (y : real) : (term11 x y z) = ((term12 z x y) = (term13 x z y)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem5275354 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (@lem3210122 A P). Qed.
Lemma lem5275355 {A : Type'} (P : A -> Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem5275356 {A : Type'} (P : A -> Prop) : term15 A P.
Proof. exact (EQ_MP (@lem5275355 A P) (@lem5275354 A P)). Qed.
Lemma lem5275357 {A : Type'} (P : A -> Prop) (s : A -> Prop) : term16 A P s.
Proof. exact (@lem5275356 A P s). Qed.
Lemma lem5275358 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term16 A P s) = (term17 A s P).
Proof. exact (eq_refl (term16 A P s)). Qed.
Lemma lem5275359 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term17 A s P.
Proof. exact (EQ_MP (@lem5275358 A s P) (@lem5275357 A P s)). Qed.
Lemma lem5275360 {A : Type'} (s : A -> Prop) (P : A -> Prop) (t : A -> Prop) : term18 A s P t.
Proof. exact (@lem5275359 A s P t). Qed.
Lemma lem5275361 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term18 A s P t) = ((term19 A s t P) = (term20 A s t P)).
Proof. exact (eq_refl (term18 A s P t)). Qed.
Lemma lem5275363 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem5275364 (s : real -> Prop) (h1 : term21) : term22 s.
Proof. exact (@lem5275363 h1 s). Qed.
Lemma lem5275365 (s : real -> Prop) : (term22 s) = (term23 s).
Proof. exact (eq_refl (term22 s)). Qed.
Lemma lem5275366 (s : real -> Prop) (h1 : term21) : term23 s.
Proof. exact (EQ_MP (@lem5275365 s) (@lem5275364 s h1)). Qed.
Lemma lem5275367 (s : real -> Prop) (b : real) (h1 : term21) : term24 s b.
Proof. exact (@lem5275366 s h1 b). Qed.
Lemma lem5275368 (s : real -> Prop) (b : real) : (term24 s b) = (term25 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5275369 (s : real -> Prop) (b : real) (h1 : term21) : term25 s b.
Proof. exact (EQ_MP (@lem5275368 s b) (@lem5275367 s b h1)). Qed.
Lemma lem5275370 (s : real -> Prop) (b : real) (h1 : term26 s b) : term26 s b.
Proof. exact (h1). Qed.
Lemma lem5275371 (s : real -> Prop) (b : real) (h1 : term21) (h2 : term26 s b) : (inf s) = b.
Proof. exact (@lem5275369 s b h1 (@lem5275370 s b h2)). Qed.
Lemma lem5275372 (s : real -> Prop) (b : real) (h1 : term26 s b) : term27 s b.
Proof. exact (fun h0 : term21 => @lem5275371 s b h0 h1). Qed.
Lemma lem5275373 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem5275374 (s : real -> Prop) (b : real) (h1 : term21) (h2 : term26 s b) : (inf s) = b.
Proof. exact (@lem5275372 s b h2 (@lem5275373 h1)). Qed.
Lemma lem5275375 (s : real -> Prop) (b : real) (h1 : term21) : term25 s b.
Proof. exact (fun h0 : term26 s b => @lem5275374 s b h1 h0). Qed.
Lemma lem5275376 (s : real -> Prop) (h1 : term21) : term23 s.
Proof. exact (fun b : real => @lem5275375 s b h1). Qed.
Lemma lem5275377 (h1 : term21) : term21.
Proof. exact (fun s : real -> Prop => @lem5275376 s h1). Qed.
Lemma lem5275378 : term28.
Proof. exact (fun h0 : term21 => @lem5275377 h0). Qed.
Lemma lem5275379 : term21.
Proof. exact (@lem5275378 (@lem5275334)). Qed.
Lemma lem5275380 (s : real -> Prop) : term22 s.
Proof. exact (@lem5275379 s). Qed.
Lemma lem5275381 (s : real -> Prop) : (term22 s) = (term23 s).
Proof. exact (eq_refl (term22 s)). Qed.
Lemma lem5275382 (s : real -> Prop) : term23 s.
Proof. exact (EQ_MP (@lem5275381 s) (@lem5275380 s)). Qed.
Lemma lem5275383 (s : real -> Prop) (b : real) : term24 s b.
Proof. exact (@lem5275382 s b). Qed.
Lemma lem5275384 (s : real -> Prop) (b : real) : (term24 s b) = (term25 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5275386 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : term29 s t.
Proof. exact (h1). Qed.
Lemma lem5275387 (s : real -> Prop) (t : real -> Prop) (h1 : term30 s t) : term30 s t.
Proof. exact (h1). Qed.
Lemma lem5275388 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5275389 (s : real -> Prop) (t : real -> Prop) (h1 : term32 s t) : term32 s t.
Proof. exact (h1). Qed.
Lemma lem5275390 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5275391 (t : real -> Prop) (h1 : term33 t) : term33 t.
Proof. exact (h1). Qed.
Lemma lem5275392 (s : real -> Prop) (h1 : term33 s) : term33 s.
Proof. exact (h1). Qed.
Lemma lem5275393 (s : real -> Prop) (b : real) (h1 : term34 s b) : term34 s b.
Proof. exact (h1). Qed.
Lemma lem5275394 (t : real -> Prop) (c : real) (h1 : term34 t c) : term34 t c.
Proof. exact (h1). Qed.
Lemma lem5275396 (s : real -> Prop) (b : real) : term25 s b.
Proof. exact (EQ_MP (@lem5275384 s b) (@lem5275383 s b)). Qed.
Lemma lem5275397 (s : real -> Prop) (t : real -> Prop) : term35 s t.
Proof. exact (@lem5275396 (@UNION real s t) (term36 s t)). Qed.
Lemma lem5275405 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term19 A s t P) = (term20 A s t P).
Proof. exact (EQ_MP (@lem5275361 A s t P) (@lem5275360 A s P t)). Qed.
Lemma lem5275406 (s : real -> Prop) (t : real -> Prop) (P : real -> Prop) : (term37 s t P) = (term38 s t P).
Proof. exact (@lem5275405 real s t P). Qed.
Lemma lem5275407 (s : real -> Prop) (t : real -> Prop) (c : real) : (term39 s t c) = (term40 s t c).
Proof. exact (@lem5275406 s t (term41 c)). Qed.
Lemma lem5275408 (c : real) (x : real) : (term42 c x) = (real_le c x).
Proof. exact (eq_refl (term42 c x)). Qed.
Lemma lem5275409 (x : real) (s : real -> Prop) (t : real -> Prop) : (term43 x s t) = (term43 x s t).
Proof. exact (eq_refl (term43 x s t)). Qed.
Lemma lem5275410 (s : real -> Prop) (t : real -> Prop) (c : real) (x : real) : (term44 s t c x) = (term45 s t c x).
Proof. exact (MK_COMB (@lem5275409 x s t) (@lem5275408 c x)). Qed.
Lemma lem5275411 (s : real -> Prop) (t : real -> Prop) (c : real) : (term46 s t c) = (term47 s t c).
Proof. exact (fun_ext (fun x : real => @lem5275410 s t c x)). Qed.
Lemma lem5275412 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275413 (s : real -> Prop) (t : real -> Prop) (c : real) : (term39 s t c) = (term48 s t c).
Proof. exact (MK_COMB (@lem5275412) (@lem5275411 s t c)). Qed.
Lemma lem5275414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5275415 (s : real -> Prop) (t : real -> Prop) (c : real) : (term49 s t c) = (term50 s t c).
Proof. exact (MK_COMB (@lem5275414) (@lem5275413 s t c)). Qed.
Lemma lem5275416 (c : real) (x : real) : (term42 c x) = (real_le c x).
Proof. exact (eq_refl (term42 c x)). Qed.
Lemma lem5275417 (x : real) (s : real -> Prop) : (term51 x s) = (term51 x s).
Proof. exact (eq_refl (term51 x s)). Qed.
Lemma lem5275418 (s : real -> Prop) (c : real) (x : real) : (term52 s c x) = (term53 s c x).
Proof. exact (MK_COMB (@lem5275417 x s) (@lem5275416 c x)). Qed.
Lemma lem5275419 (s : real -> Prop) (c : real) : (term54 s c) = (term55 s c).
Proof. exact (fun_ext (fun x : real => @lem5275418 s c x)). Qed.
Lemma lem5275420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275421 (s : real -> Prop) (c : real) : (term56 s c) = (term34 s c).
Proof. exact (MK_COMB (@lem5275420) (@lem5275419 s c)). Qed.
Lemma lem5275422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5275423 (s : real -> Prop) (c : real) : (term57 s c) = (term58 s c).
Proof. exact (MK_COMB (@lem5275422) (@lem5275421 s c)). Qed.
Lemma lem5275424 (c : real) (x : real) : (term42 c x) = (real_le c x).
Proof. exact (eq_refl (term42 c x)). Qed.
Lemma lem5275425 (x : real) (t : real -> Prop) : (term51 x t) = (term51 x t).
Proof. exact (eq_refl (term51 x t)). Qed.
Lemma lem5275426 (t : real -> Prop) (c : real) (x : real) : (term52 t c x) = (term53 t c x).
Proof. exact (MK_COMB (@lem5275425 x t) (@lem5275424 c x)). Qed.
Lemma lem5275427 (t : real -> Prop) (c : real) : (term54 t c) = (term55 t c).
Proof. exact (fun_ext (fun x : real => @lem5275426 t c x)). Qed.
Lemma lem5275428 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275429 (t : real -> Prop) (c : real) : (term56 t c) = (term34 t c).
Proof. exact (MK_COMB (@lem5275428) (@lem5275427 t c)). Qed.
Lemma lem5275430 (s : real -> Prop) (t : real -> Prop) (c : real) : (term40 s t c) = (term59 s t c).
Proof. exact (MK_COMB (@lem5275423 s c) (@lem5275429 t c)). Qed.
Lemma lem5275431 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term39 s t c) = (term40 s t c)) = ((term48 s t c) = (term59 s t c)).
Proof. exact (MK_COMB (@lem5275415 s t c) (@lem5275430 s t c)). Qed.
Lemma lem5275432 (s : real -> Prop) (t : real -> Prop) (c : real) : (term48 s t c) = (term59 s t c).
Proof. exact (EQ_MP (@lem5275431 s t c) (@lem5275407 s t c)). Qed.
Lemma lem5275447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5275448 (s : real -> Prop) (t : real -> Prop) (c : real) : (term50 s t c) = (term60 s t c).
Proof. exact (MK_COMB (@lem5275447) (@lem5275432 s t c)). Qed.
Lemma lem5275450 (x : real) (z : real) (y : real) : (term12 z x y) = (term13 x z y).
Proof. exact (EQ_MP (@lem5275352 x z y) (@lem5275351 x y z)). Qed.
Lemma lem5275451 (s : real -> Prop) (c : real) (t : real -> Prop) : (term61 c s t) = (term62 s c t).
Proof. exact (@lem5275450 (inf s) c (inf t)). Qed.
Lemma lem5275454 (s : real -> Prop) (c : real) (t : real -> Prop) : ((term48 s t c) = (term61 c s t)) = ((term59 s t c) = (term62 s c t)).
Proof. exact (MK_COMB (@lem5275448 s t c) (@lem5275451 s c t)). Qed.
Lemma lem5275457 (s : real -> Prop) (t : real -> Prop) : (term63 s t) = (term64 s t).
Proof. exact (fun_ext (fun c : real => @lem5275454 s c t)). Qed.
Lemma lem5275458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275459 (s : real -> Prop) (t : real -> Prop) : (term65 s t) = (term66 s t).
Proof. exact (MK_COMB (@lem5275458) (@lem5275457 s t)). Qed.
Lemma lem5275464 (s : real -> Prop) (t : real -> Prop) : (term66 s t) = (term65 s t).
Proof. exact (SYM (@lem5275459 s t)). Qed.
Lemma lem5275466 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5275467 (s : real -> Prop) (t : real -> Prop) : (term66 s t) = (term68 s t).
Proof. exact (@lem5275466 (term66 s t)). Qed.
Lemma lem5275468 (s : real -> Prop) (t : real -> Prop) : (term68 s t) = (term66 s t).
Proof. exact (SYM (@lem5275467 s t)). Qed.
Lemma lem5275469 (s : real -> Prop) (t : real -> Prop) (h1 : term69 s t) : term69 s t.
Proof. exact (h1). Qed.
Lemma lem5275472 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) : term70 b c s t.
Proof. exact (h1). Qed.
Lemma lem5275473 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term71 b c s t.
Proof. exact (fun h0 : term70 b c s t => @lem5275472 b c s t h0). Qed.
Lemma lem5275474 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term71 b c s t) : term71 b c s t.
Proof. exact (h1). Qed.
Lemma lem5275475 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) : term70 b c s t.
Proof. exact (h1). Qed.
Lemma lem5275476 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) (h2 : term71 b c s t) : term70 b c s t.
Proof. exact (@lem5275474 b c s t h2 (@lem5275475 b c s t h1)). Qed.
Lemma lem5275477 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) : term72 b c s t.
Proof. exact (fun h0 : term71 b c s t => @lem5275476 b c s t h1 h0). Qed.
Lemma lem5275478 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term71 b c s t) : term71 b c s t.
Proof. exact (h1). Qed.
Lemma lem5275479 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) (h2 : term71 b c s t) : term70 b c s t.
Proof. exact (@lem5275477 b c s t h1 (@lem5275478 b c s t h2)). Qed.
Lemma lem5275480 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term71 b c s t) : term71 b c s t.
Proof. exact (fun h0 : term70 b c s t => @lem5275479 b c s t h0 h1). Qed.
Lemma lem5275481 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term73 b c s t.
Proof. exact (fun h0 : term71 b c s t => @lem5275480 b c s t h0). Qed.
Lemma lem5275484 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term71 b c s t.
Proof. exact (@lem5275481 b c s t (@lem5275473 b c s t)). Qed.
Lemma lem5275562 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5275563 : term74 = term75.
Proof. exact (@lem5275562 term76). Qed.
Lemma lem5275602 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem5275603 : term78 = term79.
Proof. exact (MK_COMB (@lem5275602) (@lem5275563)). Qed.
Lemma lem5275606 (s : real -> Prop) (t : real -> Prop) : (term80 s t) = (term80 s t).
Proof. exact (eq_refl (term80 s t)). Qed.
Lemma lem5275607 (s : real -> Prop) (t : real -> Prop) : (term81 s t) = (term82 s t).
Proof. exact (MK_COMB (@lem5275606 s t) (@lem5275603)). Qed.
Lemma lem5275610 (t : real -> Prop) (c : real) : (term83 t c) = (term83 t c).
Proof. exact (eq_refl (term83 t c)). Qed.
Lemma lem5275611 (c : real) (s : real -> Prop) (t : real -> Prop) : (term84 c s t) = (term85 c s t).
Proof. exact (MK_COMB (@lem5275610 t c) (@lem5275607 s t)). Qed.
Lemma lem5275614 (s : real -> Prop) (b : real) : (term83 s b) = (term83 s b).
Proof. exact (eq_refl (term83 s b)). Qed.
Lemma lem5275615 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term86 b c s t) = (term87 b c s t).
Proof. exact (MK_COMB (@lem5275614 s b) (@lem5275611 c s t)). Qed.
Lemma lem5275618 (t : real -> Prop) : (term88 t) = (term88 t).
Proof. exact (eq_refl (term88 t)). Qed.
Lemma lem5275619 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term89 b c s t) = (term90 b c s t).
Proof. exact (MK_COMB (@lem5275618 t) (@lem5275615 b c s t)). Qed.
Lemma lem5275622 (s : real -> Prop) : (term88 s) = (term88 s).
Proof. exact (eq_refl (term88 s)). Qed.
Lemma lem5275623 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term70 b c s t) = (term91 b c s t).
Proof. exact (MK_COMB (@lem5275622 s) (@lem5275619 b c s t)). Qed.
Lemma lem5275626 (c : real) (s : real -> Prop) (t : real -> Prop) : (term92 c s t) = (term93 c s t).
Proof. exact (fun_ext (fun b : real => @lem5275623 b c s t)). Qed.
Lemma lem5275627 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275628 (c : real) (s : real -> Prop) (t : real -> Prop) : (term94 c s t) = (term95 c s t).
Proof. exact (MK_COMB (@lem5275627) (@lem5275626 c s t)). Qed.
Lemma lem5275633 (s : real -> Prop) (t : real -> Prop) : (term96 s t) = (term97 s t).
Proof. exact (fun_ext (fun c : real => @lem5275628 c s t)). Qed.
Lemma lem5275634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275635 (s : real -> Prop) (t : real -> Prop) : (term98 s t) = (term99 s t).
Proof. exact (MK_COMB (@lem5275634) (@lem5275633 s t)). Qed.
Lemma lem5275640 (t : real -> Prop) : (term100 t) = (term101 t).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5275635 s t)). Qed.
Lemma lem5275641 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5275642 (t : real -> Prop) : (term102 t) = (term103 t).
Proof. exact (MK_COMB (@lem5275641) (@lem5275640 t)). Qed.
Lemma lem5275647 : term104 = term105.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5275642 t)). Qed.
Lemma lem5275648 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5275657 : term106 = term107.
Proof. exact (MK_COMB (@lem5275648) (@lem5275647)). Qed.
Lemma lem5275658 (b : real) (s : real -> Prop) : (term108 b s) = (term108 b s).
Proof. exact (eq_refl (term108 b s)). Qed.
Lemma lem5275663 (s : real -> Prop) (b : real) (x : real) : (term53 s b x) = (term53 s b x).
Proof. exact (eq_refl (term53 s b x)). Qed.
Lemma lem5275664 (s : real -> Prop) (b : real) : (term55 s b) = (term55 s b).
Proof. exact (fun_ext (fun x : real => @lem5275663 s b x)). Qed.
Lemma lem5275665 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275666 (s : real -> Prop) (b : real) : (term34 s b) = (term34 s b).
Proof. exact (MK_COMB (@lem5275665) (@lem5275664 s b)). Qed.
Lemma lem5275667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275668 (s : real -> Prop) (b : real) : (term83 s b) = (term83 s b).
Proof. exact (MK_COMB (@lem5275667) (@lem5275666 s b)). Qed.
Lemma lem5275669 (b : real) (s : real -> Prop) : (term109 b s) = (term109 b s).
Proof. exact (MK_COMB (@lem5275668 s b) (@lem5275658 b s)). Qed.
Lemma lem5275670 (s : real -> Prop) : (term110 s) = (term110 s).
Proof. exact (fun_ext (fun b : real => @lem5275669 b s)). Qed.
Lemma lem5275671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275672 (s : real -> Prop) : (term111 s) = (term111 s).
Proof. exact (MK_COMB (@lem5275671) (@lem5275670 s)). Qed.
Lemma lem5275677 (s : real -> Prop) (x : real) : (term112 s x) = (term112 s x).
Proof. exact (eq_refl (term112 s x)). Qed.
Lemma lem5275678 (s : real -> Prop) : (term113 s) = (term113 s).
Proof. exact (fun_ext (fun x : real => @lem5275677 s x)). Qed.
Lemma lem5275679 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275680 (s : real -> Prop) : (term114 s) = (term114 s).
Proof. exact (MK_COMB (@lem5275679) (@lem5275678 s)). Qed.
Lemma lem5275681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5275682 (s : real -> Prop) : (term115 s) = (term115 s).
Proof. exact (MK_COMB (@lem5275681) (@lem5275680 s)). Qed.
Lemma lem5275683 (s : real -> Prop) : (term116 s) = (term116 s).
Proof. exact (MK_COMB (@lem5275682 s) (@lem5275672 s)). Qed.
Lemma lem5275688 (s : real -> Prop) (b : real) (x : real) : (term53 s b x) = (term53 s b x).
Proof. exact (eq_refl (term53 s b x)). Qed.
Lemma lem5275689 (s : real -> Prop) (b : real) : (term55 s b) = (term55 s b).
Proof. exact (fun_ext (fun x : real => @lem5275688 s b x)). Qed.
Lemma lem5275690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275691 (s : real -> Prop) (b : real) : (term34 s b) = (term34 s b).
Proof. exact (MK_COMB (@lem5275690) (@lem5275689 s b)). Qed.
Lemma lem5275692 (s : real -> Prop) : (term117 s) = (term117 s).
Proof. exact (fun_ext (fun b : real => @lem5275691 s b)). Qed.
Lemma lem5275693 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5275694 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (MK_COMB (@lem5275693) (@lem5275692 s)). Qed.
Lemma lem5275699 (s : real -> Prop) : (term118 s) = (term118 s).
Proof. exact (eq_refl (term118 s)). Qed.
Lemma lem5275700 (s : real -> Prop) : (term119 s) = (term119 s).
Proof. exact (MK_COMB (@lem5275699 s) (@lem5275694 s)). Qed.
Lemma lem5275701 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275702 (s : real -> Prop) : (term120 s) = (term120 s).
Proof. exact (MK_COMB (@lem5275701) (@lem5275700 s)). Qed.
Lemma lem5275703 (s : real -> Prop) : (term121 s) = (term121 s).
Proof. exact (MK_COMB (@lem5275702 s) (@lem5275683 s)). Qed.
Lemma lem5275704 : term122 = term122.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5275703 s)). Qed.
Lemma lem5275705 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5275706 : term76 = term76.
Proof. exact (MK_COMB (@lem5275705) (@lem5275704)). Qed.
Lemma lem5275707 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5275708 : term75 = term75.
Proof. exact (MK_COMB (@lem5275707) (@lem5275706)). Qed.
Lemma lem5275717 (y : real) (x : real) (z : real) : (term123 y x z) = (term123 y x z).
Proof. exact (eq_refl (term123 y x z)). Qed.
Lemma lem5275718 (y : real) (x : real) : (term124 y x) = (term124 y x).
Proof. exact (fun_ext (fun z : real => @lem5275717 y x z)). Qed.
Lemma lem5275719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275720 (y : real) (x : real) : (term125 y x) = (term125 y x).
Proof. exact (MK_COMB (@lem5275719) (@lem5275718 y x)). Qed.
Lemma lem5275721 (x : real) : (term126 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem5275720 y x)). Qed.
Lemma lem5275722 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275723 (x : real) : (term127 x) = (term127 x).
Proof. exact (MK_COMB (@lem5275722) (@lem5275721 x)). Qed.
Lemma lem5275724 : term128 = term128.
Proof. exact (fun_ext (fun x : real => @lem5275723 x)). Qed.
Lemma lem5275725 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275726 : term129 = term129.
Proof. exact (MK_COMB (@lem5275725) (@lem5275724)). Qed.
Lemma lem5275727 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275728 : term77 = term77.
Proof. exact (MK_COMB (@lem5275727) (@lem5275726)). Qed.
Lemma lem5275729 : term79 = term79.
Proof. exact (MK_COMB (@lem5275728) (@lem5275708)). Qed.
Lemma lem5275734 (s : real -> Prop) (c : real) (t : real -> Prop) : (term62 s c t) = (term62 s c t).
Proof. exact (eq_refl (term62 s c t)). Qed.
Lemma lem5275739 (t : real -> Prop) (c : real) (x : real) : (term53 t c x) = (term53 t c x).
Proof. exact (eq_refl (term53 t c x)). Qed.
Lemma lem5275740 (t : real -> Prop) (c : real) : (term55 t c) = (term55 t c).
Proof. exact (fun_ext (fun x : real => @lem5275739 t c x)). Qed.
Lemma lem5275741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275742 (t : real -> Prop) (c : real) : (term34 t c) = (term34 t c).
Proof. exact (MK_COMB (@lem5275741) (@lem5275740 t c)). Qed.
Lemma lem5275747 (s : real -> Prop) (c : real) (x : real) : (term53 s c x) = (term53 s c x).
Proof. exact (eq_refl (term53 s c x)). Qed.
Lemma lem5275748 (s : real -> Prop) (c : real) : (term55 s c) = (term55 s c).
Proof. exact (fun_ext (fun x : real => @lem5275747 s c x)). Qed.
Lemma lem5275749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275750 (s : real -> Prop) (c : real) : (term34 s c) = (term34 s c).
Proof. exact (MK_COMB (@lem5275749) (@lem5275748 s c)). Qed.
Lemma lem5275751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5275752 (s : real -> Prop) (c : real) : (term58 s c) = (term58 s c).
Proof. exact (MK_COMB (@lem5275751) (@lem5275750 s c)). Qed.
Lemma lem5275753 (s : real -> Prop) (t : real -> Prop) (c : real) : (term59 s t c) = (term59 s t c).
Proof. exact (MK_COMB (@lem5275752 s c) (@lem5275742 t c)). Qed.
Lemma lem5275754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5275755 (s : real -> Prop) (t : real -> Prop) (c : real) : (term60 s t c) = (term60 s t c).
Proof. exact (MK_COMB (@lem5275754) (@lem5275753 s t c)). Qed.
Lemma lem5275756 (s : real -> Prop) (c : real) (t : real -> Prop) : ((term59 s t c) = (term62 s c t)) = ((term59 s t c) = (term62 s c t)).
Proof. exact (MK_COMB (@lem5275755 s t c) (@lem5275734 s c t)). Qed.
Lemma lem5275757 (s : real -> Prop) (t : real -> Prop) : (term64 s t) = (term64 s t).
Proof. exact (fun_ext (fun c : real => @lem5275756 s c t)). Qed.
Lemma lem5275758 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275759 (s : real -> Prop) (t : real -> Prop) : (term66 s t) = (term66 s t).
Proof. exact (MK_COMB (@lem5275758) (@lem5275757 s t)). Qed.
Lemma lem5275760 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5275761 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term69 s t).
Proof. exact (MK_COMB (@lem5275760) (@lem5275759 s t)). Qed.
Lemma lem5275762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275763 (s : real -> Prop) (t : real -> Prop) : (term80 s t) = (term80 s t).
Proof. exact (MK_COMB (@lem5275762) (@lem5275761 s t)). Qed.
Lemma lem5275764 (s : real -> Prop) (t : real -> Prop) : (term82 s t) = (term82 s t).
Proof. exact (MK_COMB (@lem5275763 s t) (@lem5275729)). Qed.
Lemma lem5275769 (t : real -> Prop) (c : real) (x : real) : (term53 t c x) = (term53 t c x).
Proof. exact (eq_refl (term53 t c x)). Qed.
Lemma lem5275770 (t : real -> Prop) (c : real) : (term55 t c) = (term55 t c).
Proof. exact (fun_ext (fun x : real => @lem5275769 t c x)). Qed.
Lemma lem5275771 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275772 (t : real -> Prop) (c : real) : (term34 t c) = (term34 t c).
Proof. exact (MK_COMB (@lem5275771) (@lem5275770 t c)). Qed.
Lemma lem5275773 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275774 (t : real -> Prop) (c : real) : (term83 t c) = (term83 t c).
Proof. exact (MK_COMB (@lem5275773) (@lem5275772 t c)). Qed.
Lemma lem5275775 (c : real) (s : real -> Prop) (t : real -> Prop) : (term85 c s t) = (term85 c s t).
Proof. exact (MK_COMB (@lem5275774 t c) (@lem5275764 s t)). Qed.
Lemma lem5275780 (s : real -> Prop) (b : real) (x : real) : (term53 s b x) = (term53 s b x).
Proof. exact (eq_refl (term53 s b x)). Qed.
Lemma lem5275781 (s : real -> Prop) (b : real) : (term55 s b) = (term55 s b).
Proof. exact (fun_ext (fun x : real => @lem5275780 s b x)). Qed.
Lemma lem5275782 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275783 (s : real -> Prop) (b : real) : (term34 s b) = (term34 s b).
Proof. exact (MK_COMB (@lem5275782) (@lem5275781 s b)). Qed.
Lemma lem5275784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5275785 (s : real -> Prop) (b : real) : (term83 s b) = (term83 s b).
Proof. exact (MK_COMB (@lem5275784) (@lem5275783 s b)). Qed.
Lemma lem5275786 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term87 b c s t) = (term87 b c s t).
Proof. exact (MK_COMB (@lem5275785 s b) (@lem5275775 c s t)). Qed.
Lemma lem5275791 (t : real -> Prop) : (term88 t) = (term88 t).
Proof. exact (eq_refl (term88 t)). Qed.
Lemma lem5275792 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term90 b c s t) = (term90 b c s t).
Proof. exact (MK_COMB (@lem5275791 t) (@lem5275786 b c s t)). Qed.
Lemma lem5275797 (s : real -> Prop) : (term88 s) = (term88 s).
Proof. exact (eq_refl (term88 s)). Qed.
Lemma lem5275798 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term91 b c s t) = (term91 b c s t).
Proof. exact (MK_COMB (@lem5275797 s) (@lem5275792 b c s t)). Qed.
Lemma lem5275799 (c : real) (s : real -> Prop) (t : real -> Prop) : (term93 c s t) = (term93 c s t).
Proof. exact (fun_ext (fun b : real => @lem5275798 b c s t)). Qed.
Lemma lem5275800 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275801 (c : real) (s : real -> Prop) (t : real -> Prop) : (term95 c s t) = (term95 c s t).
Proof. exact (MK_COMB (@lem5275800) (@lem5275799 c s t)). Qed.
Lemma lem5275802 (s : real -> Prop) (t : real -> Prop) : (term97 s t) = (term97 s t).
Proof. exact (fun_ext (fun c : real => @lem5275801 c s t)). Qed.
Lemma lem5275803 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5275804 (s : real -> Prop) (t : real -> Prop) : (term99 s t) = (term99 s t).
Proof. exact (MK_COMB (@lem5275803) (@lem5275802 s t)). Qed.
Lemma lem5275805 (t : real -> Prop) : (term101 t) = (term101 t).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5275804 s t)). Qed.
Lemma lem5275806 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5275807 (t : real -> Prop) : (term103 t) = (term103 t).
Proof. exact (MK_COMB (@lem5275806) (@lem5275805 t)). Qed.
Lemma lem5275808 : term105 = term105.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5275807 t)). Qed.
Lemma lem5275809 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5275810 : term107 = term107.
Proof. exact (MK_COMB (@lem5275809) (@lem5275808)). Qed.
Lemma lem5275963 : term106 = term107.
Proof. exact (TRANS (@lem5275657) (@lem5275810)). Qed.
Lemma lem5275964 : term107 = term106.
Proof. exact (SYM (@lem5275963)). Qed.
Lemma lem5275967 (s : real -> Prop) (b : real) (h1 : term34 s b) : term34 s b.
Proof. exact (h1). Qed.
Lemma lem5275968 (t : real -> Prop) (c : real) (h1 : term34 t c) : term34 t c.
Proof. exact (h1). Qed.
Lemma lem5275969 (s : real -> Prop) (t : real -> Prop) (h1 : term69 s t) : term69 s t.
Proof. exact (h1). Qed.
Lemma lem5275970 (h1 : term129) : term129.
Proof. exact (h1). Qed.
Lemma lem5275971 (h1 : term76) : term76.
Proof. exact (h1). Qed.
Lemma lem5275977 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5275983 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5275990 (s : real -> Prop) (b : real) (x : real) : (term53 s b x) = (term130 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5275991 (s : real -> Prop) (b : real) : (term55 s b) = (term131 s b).
Proof. exact (fun_ext (fun x : real => @lem5275990 s b x)). Qed.
Lemma lem5275992 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276045 (s : real -> Prop) (b : real) : (term34 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5275992) (@lem5275991 s b)). Qed.
Lemma lem5276046 (s : real -> Prop) (b : real) (h1 : term34 s b) : term132 s b.
Proof. exact (EQ_MP (@lem5276045 s b) (@lem5275967 s b h1)). Qed.
Lemma lem5276053 (t : real -> Prop) (c : real) (x : real) : (term53 t c x) = (term130 t c x).
Proof. exact (@lem17265 (@IN real x t) (real_le c x)). Qed.
Lemma lem5276054 (t : real -> Prop) (c : real) : (term55 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5276053 t c x)). Qed.
Lemma lem5276055 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276108 (t : real -> Prop) (c : real) : (term34 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5276055) (@lem5276054 t c)). Qed.
Lemma lem5276109 (t : real -> Prop) (c : real) (h1 : term34 t c) : term132 t c.
Proof. exact (EQ_MP (@lem5276108 t c) (@lem5275968 t c h1)). Qed.
Lemma lem5276118 (s : real -> Prop) (c : real) (x : real) : (term133 s c x) = (term134 s c x).
Proof. exact (@lem17362 (@IN real x s) (real_le c x)). Qed.
Lemma lem5276123 (s : real -> Prop) (c : real) (x : real) : (term53 s c x) = (term130 s c x).
Proof. exact (@lem17265 (@IN real x s) (real_le c x)). Qed.
Lemma lem5276124 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5276125 (s : real -> Prop) (c : real) : (term137 s c) = (term138 s c).
Proof. exact (@lem5276124 (term55 s c)). Qed.
Lemma lem5276126 (s : real -> Prop) (c : real) (x : real) : (term139 s c x) = (term53 s c x).
Proof. exact (eq_refl (term139 s c x)). Qed.
Lemma lem5276127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5276128 (s : real -> Prop) (c : real) (x : real) : (term140 s c x) = (term133 s c x).
Proof. exact (MK_COMB (@lem5276127) (@lem5276126 s c x)). Qed.
Lemma lem5276129 (s : real -> Prop) (c : real) (x : real) : (term140 s c x) = (term134 s c x).
Proof. exact (TRANS (@lem5276128 s c x) (@lem5276118 s c x)). Qed.
Lemma lem5276130 (s : real -> Prop) (c : real) : (term141 s c) = (term142 s c).
Proof. exact (fun_ext (fun x : real => @lem5276129 s c x)). Qed.
Lemma lem5276131 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276132 (s : real -> Prop) (c : real) : (term138 s c) = (term143 s c).
Proof. exact (MK_COMB (@lem5276131) (@lem5276130 s c)). Qed.
Lemma lem5276133 (s : real -> Prop) (c : real) : (term137 s c) = (term143 s c).
Proof. exact (TRANS (@lem5276125 s c) (@lem5276132 s c)). Qed.
Lemma lem5276134 (s : real -> Prop) (c : real) : (term55 s c) = (term131 s c).
Proof. exact (fun_ext (fun x : real => @lem5276123 s c x)). Qed.
Lemma lem5276135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276136 (s : real -> Prop) (c : real) : (term34 s c) = (term132 s c).
Proof. exact (MK_COMB (@lem5276135) (@lem5276134 s c)). Qed.
Lemma lem5276145 (t : real -> Prop) (c : real) (x : real) : (term133 t c x) = (term134 t c x).
Proof. exact (@lem17362 (@IN real x t) (real_le c x)). Qed.
Lemma lem5276150 (t : real -> Prop) (c : real) (x : real) : (term53 t c x) = (term130 t c x).
Proof. exact (@lem17265 (@IN real x t) (real_le c x)). Qed.
Lemma lem5276151 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5276152 (t : real -> Prop) (c : real) : (term137 t c) = (term138 t c).
Proof. exact (@lem5276151 (term55 t c)). Qed.
Lemma lem5276153 (t : real -> Prop) (c : real) (x : real) : (term139 t c x) = (term53 t c x).
Proof. exact (eq_refl (term139 t c x)). Qed.
Lemma lem5276154 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5276155 (t : real -> Prop) (c : real) (x : real) : (term140 t c x) = (term133 t c x).
Proof. exact (MK_COMB (@lem5276154) (@lem5276153 t c x)). Qed.
Lemma lem5276156 (t : real -> Prop) (c : real) (x : real) : (term140 t c x) = (term134 t c x).
Proof. exact (TRANS (@lem5276155 t c x) (@lem5276145 t c x)). Qed.
Lemma lem5276157 (t : real -> Prop) (c : real) : (term141 t c) = (term142 t c).
Proof. exact (fun_ext (fun x : real => @lem5276156 t c x)). Qed.
Lemma lem5276158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276159 (t : real -> Prop) (c : real) : (term138 t c) = (term143 t c).
Proof. exact (MK_COMB (@lem5276158) (@lem5276157 t c)). Qed.
Lemma lem5276160 (t : real -> Prop) (c : real) : (term137 t c) = (term143 t c).
Proof. exact (TRANS (@lem5276152 t c) (@lem5276159 t c)). Qed.
Lemma lem5276161 (t : real -> Prop) (c : real) : (term55 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5276150 t c x)). Qed.
Lemma lem5276162 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276163 (t : real -> Prop) (c : real) : (term34 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5276162) (@lem5276161 t c)). Qed.
Lemma lem5276164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276165 (s : real -> Prop) (c : real) : (term144 s c) = (term145 s c).
Proof. exact (MK_COMB (@lem5276164) (@lem5276133 s c)). Qed.
Lemma lem5276166 (s : real -> Prop) (t : real -> Prop) (c : real) : (term146 s t c) = (term147 s t c).
Proof. exact (MK_COMB (@lem5276165 s c) (@lem5276160 t c)). Qed.
Lemma lem5276167 (s : real -> Prop) (t : real -> Prop) (c : real) : (term148 s t c) = (term146 s t c).
Proof. exact (@lem17045 (term34 s c) (term34 t c)). Qed.
Lemma lem5276168 (s : real -> Prop) (t : real -> Prop) (c : real) : (term148 s t c) = (term147 s t c).
Proof. exact (TRANS (@lem5276167 s t c) (@lem5276166 s t c)). Qed.
Lemma lem5276169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5276170 (s : real -> Prop) (c : real) : (term58 s c) = (term149 s c).
Proof. exact (MK_COMB (@lem5276169) (@lem5276136 s c)). Qed.
Lemma lem5276171 (s : real -> Prop) (t : real -> Prop) (c : real) : (term59 s t c) = (term150 s t c).
Proof. exact (MK_COMB (@lem5276170 s c) (@lem5276163 t c)). Qed.
Lemma lem5276180 (s : real -> Prop) (c : real) (t : real -> Prop) : (term151 s c t) = (term152 s c t).
Proof. exact (@lem17045 (term108 c s) (term108 c t)). Qed.
Lemma lem5276183 (s : real -> Prop) (c : real) (t : real -> Prop) : (term62 s c t) = (term62 s c t).
Proof. exact (eq_refl (term62 s c t)). Qed.
Lemma lem5276184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5276185 (s : real -> Prop) (t : real -> Prop) (c : real) : (term153 s t c) = (term154 s t c).
Proof. exact (MK_COMB (@lem5276184) (@lem5276168 s t c)). Qed.
Lemma lem5276186 (s : real -> Prop) (c : real) (t : real -> Prop) : (term155 s c t) = (term156 s c t).
Proof. exact (MK_COMB (@lem5276185 s t c) (@lem5276183 s c t)). Qed.
Lemma lem5276187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5276188 (s : real -> Prop) (t : real -> Prop) (c : real) : (term157 s t c) = (term158 s t c).
Proof. exact (MK_COMB (@lem5276187) (@lem5276171 s t c)). Qed.
Lemma lem5276189 (s : real -> Prop) (c : real) (t : real -> Prop) : (term159 s c t) = (term160 s c t).
Proof. exact (MK_COMB (@lem5276188 s t c) (@lem5276180 s c t)). Qed.
Lemma lem5276190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276191 (s : real -> Prop) (c : real) (t : real -> Prop) : (term161 s c t) = (term162 s c t).
Proof. exact (MK_COMB (@lem5276190) (@lem5276189 s c t)). Qed.
Lemma lem5276192 (s : real -> Prop) (c : real) (t : real -> Prop) : (term163 s c t) = (term164 s c t).
Proof. exact (MK_COMB (@lem5276191 s c t) (@lem5276186 s c t)). Qed.
Lemma lem5276193 (s : real -> Prop) (c : real) (t : real -> Prop) : (term165 s c t) = (term163 s c t).
Proof. exact (@lem17646 (term59 s t c) (term62 s c t)). Qed.
Lemma lem5276194 (s : real -> Prop) (c : real) (t : real -> Prop) : (term165 s c t) = (term164 s c t).
Proof. exact (TRANS (@lem5276193 s c t) (@lem5276192 s c t)). Qed.
Lemma lem5276195 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5276196 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term166 s t).
Proof. exact (@lem5276195 (term64 s t)). Qed.
Lemma lem5276197 (s : real -> Prop) (c : real) (t : real -> Prop) : (term167 s t c) = ((term59 s t c) = (term62 s c t)).
Proof. exact (eq_refl (term167 s t c)). Qed.
Lemma lem5276198 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5276199 (s : real -> Prop) (c : real) (t : real -> Prop) : (term168 s t c) = (term165 s c t).
Proof. exact (MK_COMB (@lem5276198) (@lem5276197 s c t)). Qed.
Lemma lem5276200 (s : real -> Prop) (c : real) (t : real -> Prop) : (term168 s t c) = (term164 s c t).
Proof. exact (TRANS (@lem5276199 s c t) (@lem5276194 s c t)). Qed.
Lemma lem5276201 (s : real -> Prop) (t : real -> Prop) : (term169 s t) = (term170 s t).
Proof. exact (fun_ext (fun c : real => @lem5276200 s c t)). Qed.
Lemma lem5276202 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276203 (s : real -> Prop) (t : real -> Prop) : (term166 s t) = (term171 s t).
Proof. exact (MK_COMB (@lem5276202) (@lem5276201 s t)). Qed.
Lemma lem5276204 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term171 s t).
Proof. exact (TRANS (@lem5276196 s t) (@lem5276203 s t)). Qed.
Lemma lem5276206 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5276207 (P : real -> Prop) (Q : real -> Prop) : (term174 P Q) = (term175 P Q).
Proof. exact (@lem5276206 real P Q). Qed.
Lemma lem5276208 (s : real -> Prop) (t : real -> Prop) : (term176 s t) = (term177 s t).
Proof. exact (@lem5276207 (term178 s t) (term179 s t)). Qed.
Lemma lem5276209 (s : real -> Prop) (c : real) (t : real -> Prop) : (term180 s t c) = (term160 s c t).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5276210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276211 (s : real -> Prop) (c : real) (t : real -> Prop) : (term181 s t c) = (term162 s c t).
Proof. exact (MK_COMB (@lem5276210) (@lem5276209 s c t)). Qed.
Lemma lem5276212 (s : real -> Prop) (c : real) (t : real -> Prop) : (term182 s t c) = (term156 s c t).
Proof. exact (eq_refl (term182 s t c)). Qed.
Lemma lem5276213 (s : real -> Prop) (c : real) (t : real -> Prop) : (term183 s t c) = (term164 s c t).
Proof. exact (MK_COMB (@lem5276211 s c t) (@lem5276212 s c t)). Qed.
Lemma lem5276214 (s : real -> Prop) (t : real -> Prop) : (term184 s t) = (term170 s t).
Proof. exact (fun_ext (fun c : real => @lem5276213 s c t)). Qed.
Lemma lem5276215 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276216 (s : real -> Prop) (t : real -> Prop) : (term176 s t) = (term171 s t).
Proof. exact (MK_COMB (@lem5276215) (@lem5276214 s t)). Qed.
Lemma lem5276217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5276218 (s : real -> Prop) (t : real -> Prop) : (term185 s t) = (term186 s t).
Proof. exact (MK_COMB (@lem5276217) (@lem5276216 s t)). Qed.
Lemma lem5276219 (s : real -> Prop) (c : real) (t : real -> Prop) : (term180 s t c) = (term160 s c t).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5276220 (s : real -> Prop) (t : real -> Prop) : (term187 s t) = (term178 s t).
Proof. exact (fun_ext (fun c : real => @lem5276219 s c t)). Qed.
Lemma lem5276221 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276222 (s : real -> Prop) (t : real -> Prop) : (term188 s t) = (term189 s t).
Proof. exact (MK_COMB (@lem5276221) (@lem5276220 s t)). Qed.
Lemma lem5276223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276224 (s : real -> Prop) (t : real -> Prop) : (term190 s t) = (term191 s t).
Proof. exact (MK_COMB (@lem5276223) (@lem5276222 s t)). Qed.
Lemma lem5276225 (s : real -> Prop) (c : real) (t : real -> Prop) : (term182 s t c) = (term156 s c t).
Proof. exact (eq_refl (term182 s t c)). Qed.
Lemma lem5276226 (s : real -> Prop) (t : real -> Prop) : (term192 s t) = (term179 s t).
Proof. exact (fun_ext (fun c : real => @lem5276225 s c t)). Qed.
Lemma lem5276227 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276228 (s : real -> Prop) (t : real -> Prop) : (term193 s t) = (term194 s t).
Proof. exact (MK_COMB (@lem5276227) (@lem5276226 s t)). Qed.
Lemma lem5276229 (s : real -> Prop) (t : real -> Prop) : (term177 s t) = (term195 s t).
Proof. exact (MK_COMB (@lem5276224 s t) (@lem5276228 s t)). Qed.
Lemma lem5276230 (s : real -> Prop) (t : real -> Prop) : ((term176 s t) = (term177 s t)) = ((term171 s t) = (term195 s t)).
Proof. exact (MK_COMB (@lem5276218 s t) (@lem5276229 s t)). Qed.
Lemma lem5276231 (s : real -> Prop) (t : real -> Prop) : (term171 s t) = (term195 s t).
Proof. exact (EQ_MP (@lem5276230 s t) (@lem5276208 s t)). Qed.
Lemma lem5276521 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term173 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5276522 (P : real -> Prop) (Q : real -> Prop) : (term175 P Q) = (term174 P Q).
Proof. exact (@lem5276521 real P Q). Qed.
Lemma lem5276523 (s : real -> Prop) (t : real -> Prop) (c : real) : (term196 s t c) = (term197 s t c).
Proof. exact (@lem5276522 (term142 s c) (term142 t c)). Qed.
Lemma lem5276524 (s : real -> Prop) (c : real) (x : real) : (term198 s c x) = (term134 s c x).
Proof. exact (eq_refl (term198 s c x)). Qed.
Lemma lem5276525 (s : real -> Prop) (c : real) : (term199 s c) = (term142 s c).
Proof. exact (fun_ext (fun x : real => @lem5276524 s c x)). Qed.
Lemma lem5276526 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276527 (s : real -> Prop) (c : real) : (term200 s c) = (term143 s c).
Proof. exact (MK_COMB (@lem5276526) (@lem5276525 s c)). Qed.
Lemma lem5276528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276529 (s : real -> Prop) (c : real) : (term201 s c) = (term145 s c).
Proof. exact (MK_COMB (@lem5276528) (@lem5276527 s c)). Qed.
Lemma lem5276530 (t : real -> Prop) (c : real) (x : real) : (term198 t c x) = (term134 t c x).
Proof. exact (eq_refl (term198 t c x)). Qed.
Lemma lem5276531 (t : real -> Prop) (c : real) : (term199 t c) = (term142 t c).
Proof. exact (fun_ext (fun x : real => @lem5276530 t c x)). Qed.
Lemma lem5276532 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276533 (t : real -> Prop) (c : real) : (term200 t c) = (term143 t c).
Proof. exact (MK_COMB (@lem5276532) (@lem5276531 t c)). Qed.
Lemma lem5276534 (s : real -> Prop) (t : real -> Prop) (c : real) : (term196 s t c) = (term147 s t c).
Proof. exact (MK_COMB (@lem5276529 s c) (@lem5276533 t c)). Qed.
Lemma lem5276535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5276536 (s : real -> Prop) (t : real -> Prop) (c : real) : (term202 s t c) = (term203 s t c).
Proof. exact (MK_COMB (@lem5276535) (@lem5276534 s t c)). Qed.
Lemma lem5276537 (s : real -> Prop) (c : real) (x : real) : (term198 s c x) = (term134 s c x).
Proof. exact (eq_refl (term198 s c x)). Qed.
Lemma lem5276538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276539 (s : real -> Prop) (c : real) (x : real) : (term204 s c x) = (term205 s c x).
Proof. exact (MK_COMB (@lem5276538) (@lem5276537 s c x)). Qed.
Lemma lem5276540 (t : real -> Prop) (c : real) (x : real) : (term198 t c x) = (term134 t c x).
Proof. exact (eq_refl (term198 t c x)). Qed.
Lemma lem5276541 (s : real -> Prop) (t : real -> Prop) (c : real) (x : real) : (term206 s t c x) = (term207 s t c x).
Proof. exact (MK_COMB (@lem5276539 s c x) (@lem5276540 t c x)). Qed.
Lemma lem5276542 (s : real -> Prop) (t : real -> Prop) (c : real) : (term208 s t c) = (term209 s t c).
Proof. exact (fun_ext (fun x : real => @lem5276541 s t c x)). Qed.
Lemma lem5276543 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276544 (s : real -> Prop) (t : real -> Prop) (c : real) : (term197 s t c) = (term210 s t c).
Proof. exact (MK_COMB (@lem5276543) (@lem5276542 s t c)). Qed.
Lemma lem5276545 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term196 s t c) = (term197 s t c)) = ((term147 s t c) = (term210 s t c)).
Proof. exact (MK_COMB (@lem5276536 s t c) (@lem5276544 s t c)). Qed.
Lemma lem5276546 (s : real -> Prop) (t : real -> Prop) (c : real) : (term147 s t c) = (term210 s t c).
Proof. exact (EQ_MP (@lem5276545 s t c) (@lem5276523 s t c)). Qed.
Lemma lem5276547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5276548 (s : real -> Prop) (t : real -> Prop) (c : real) : (term154 s t c) = (term211 s t c).
Proof. exact (MK_COMB (@lem5276547) (@lem5276546 s t c)). Qed.
Lemma lem5276549 (s : real -> Prop) (c : real) (t : real -> Prop) : (term62 s c t) = (term62 s c t).
Proof. exact (eq_refl (term62 s c t)). Qed.
Lemma lem5276550 (s : real -> Prop) (c : real) (t : real -> Prop) : (term156 s c t) = (term212 s c t).
Proof. exact (MK_COMB (@lem5276548 s t c) (@lem5276549 s c t)). Qed.
Lemma lem5276552 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5276553 (P : real -> Prop) (Q : Prop) : (term215 P Q) = (term216 P Q).
Proof. exact (@lem5276552 real P Q). Qed.
Lemma lem5276554 (s : real -> Prop) (c : real) (t : real -> Prop) : (term217 s c t) = (term218 s c t).
Proof. exact (@lem5276553 (term209 s t c) (term62 s c t)). Qed.
Lemma lem5276555 (s : real -> Prop) (t : real -> Prop) (c : real) (x : real) : (term219 s t c x) = (term207 s t c x).
Proof. exact (eq_refl (term219 s t c x)). Qed.
Lemma lem5276556 (s : real -> Prop) (t : real -> Prop) (c : real) : (term220 s t c) = (term209 s t c).
Proof. exact (fun_ext (fun x : real => @lem5276555 s t c x)). Qed.
Lemma lem5276557 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276558 (s : real -> Prop) (t : real -> Prop) (c : real) : (term221 s t c) = (term210 s t c).
Proof. exact (MK_COMB (@lem5276557) (@lem5276556 s t c)). Qed.
Lemma lem5276559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5276560 (s : real -> Prop) (t : real -> Prop) (c : real) : (term222 s t c) = (term211 s t c).
Proof. exact (MK_COMB (@lem5276559) (@lem5276558 s t c)). Qed.
Lemma lem5276561 (s : real -> Prop) (c : real) (t : real -> Prop) : (term62 s c t) = (term62 s c t).
Proof. exact (eq_refl (term62 s c t)). Qed.
Lemma lem5276562 (s : real -> Prop) (c : real) (t : real -> Prop) : (term217 s c t) = (term212 s c t).
Proof. exact (MK_COMB (@lem5276560 s t c) (@lem5276561 s c t)). Qed.
Lemma lem5276563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5276564 (s : real -> Prop) (c : real) (t : real -> Prop) : (term223 s c t) = (term224 s c t).
Proof. exact (MK_COMB (@lem5276563) (@lem5276562 s c t)). Qed.
Lemma lem5276565 (s : real -> Prop) (t : real -> Prop) (c : real) (x : real) : (term219 s t c x) = (term207 s t c x).
Proof. exact (eq_refl (term219 s t c x)). Qed.
Lemma lem5276566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5276567 (s : real -> Prop) (t : real -> Prop) (c : real) (x : real) : (term225 s t c x) = (term226 s t c x).
Proof. exact (MK_COMB (@lem5276566) (@lem5276565 s t c x)). Qed.
Lemma lem5276568 (s : real -> Prop) (c : real) (t : real -> Prop) : (term62 s c t) = (term62 s c t).
Proof. exact (eq_refl (term62 s c t)). Qed.
Lemma lem5276569 (x : real) (s : real -> Prop) (c : real) (t : real -> Prop) : (term227 x s c t) = (term228 x s c t).
Proof. exact (MK_COMB (@lem5276567 s t c x) (@lem5276568 s c t)). Qed.
Lemma lem5276570 (s : real -> Prop) (c : real) (t : real -> Prop) : (term229 s c t) = (term230 s c t).
Proof. exact (fun_ext (fun x : real => @lem5276569 x s c t)). Qed.
Lemma lem5276571 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276572 (s : real -> Prop) (c : real) (t : real -> Prop) : (term218 s c t) = (term231 s c t).
Proof. exact (MK_COMB (@lem5276571) (@lem5276570 s c t)). Qed.
Lemma lem5276573 (s : real -> Prop) (c : real) (t : real -> Prop) : ((term217 s c t) = (term218 s c t)) = ((term212 s c t) = (term231 s c t)).
Proof. exact (MK_COMB (@lem5276564 s c t) (@lem5276572 s c t)). Qed.
Lemma lem5276574 (s : real -> Prop) (c : real) (t : real -> Prop) : (term212 s c t) = (term231 s c t).
Proof. exact (EQ_MP (@lem5276573 s c t) (@lem5276554 s c t)). Qed.
Lemma lem5276575 (s : real -> Prop) (c : real) (t : real -> Prop) : (term156 s c t) = (term231 s c t).
Proof. exact (TRANS (@lem5276550 s c t) (@lem5276574 s c t)). Qed.
Lemma lem5276576 (s : real -> Prop) (t : real -> Prop) : (term179 s t) = (term232 s t).
Proof. exact (fun_ext (fun c : real => @lem5276575 s c t)). Qed.
Lemma lem5276577 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276578 (s : real -> Prop) (t : real -> Prop) : (term194 s t) = (term233 s t).
Proof. exact (MK_COMB (@lem5276577) (@lem5276576 s t)). Qed.
Lemma lem5276579 (s : real -> Prop) (t : real -> Prop) : (term191 s t) = (term191 s t).
Proof. exact (eq_refl (term191 s t)). Qed.
Lemma lem5276580 (s : real -> Prop) (t : real -> Prop) : (term195 s t) = (term234 s t).
Proof. exact (MK_COMB (@lem5276579 s t) (@lem5276578 s t)). Qed.
Lemma lem5276582 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term173 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5276583 (P : real -> Prop) (Q : real -> Prop) : (term175 P Q) = (term174 P Q).
Proof. exact (@lem5276582 real P Q). Qed.
Lemma lem5276584 (s : real -> Prop) (t : real -> Prop) : (term235 s t) = (term236 s t).
Proof. exact (@lem5276583 (term178 s t) (term232 s t)). Qed.
Lemma lem5276585 (s : real -> Prop) (c : real) (t : real -> Prop) : (term180 s t c) = (term160 s c t).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5276586 (s : real -> Prop) (t : real -> Prop) : (term187 s t) = (term178 s t).
Proof. exact (fun_ext (fun c : real => @lem5276585 s c t)). Qed.
Lemma lem5276587 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276588 (s : real -> Prop) (t : real -> Prop) : (term188 s t) = (term189 s t).
Proof. exact (MK_COMB (@lem5276587) (@lem5276586 s t)). Qed.
Lemma lem5276589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276590 (s : real -> Prop) (t : real -> Prop) : (term190 s t) = (term191 s t).
Proof. exact (MK_COMB (@lem5276589) (@lem5276588 s t)). Qed.
Lemma lem5276591 (s : real -> Prop) (c : real) (t : real -> Prop) : (term237 s t c) = (term231 s c t).
Proof. exact (eq_refl (term237 s t c)). Qed.
Lemma lem5276592 (s : real -> Prop) (t : real -> Prop) : (term238 s t) = (term232 s t).
Proof. exact (fun_ext (fun c : real => @lem5276591 s c t)). Qed.
Lemma lem5276593 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276594 (s : real -> Prop) (t : real -> Prop) : (term239 s t) = (term233 s t).
Proof. exact (MK_COMB (@lem5276593) (@lem5276592 s t)). Qed.
Lemma lem5276595 (s : real -> Prop) (t : real -> Prop) : (term235 s t) = (term234 s t).
Proof. exact (MK_COMB (@lem5276590 s t) (@lem5276594 s t)). Qed.
Lemma lem5276596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5276597 (s : real -> Prop) (t : real -> Prop) : (term240 s t) = (term241 s t).
Proof. exact (MK_COMB (@lem5276596) (@lem5276595 s t)). Qed.
Lemma lem5276598 (s : real -> Prop) (c : real) (t : real -> Prop) : (term180 s t c) = (term160 s c t).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5276599 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276600 (s : real -> Prop) (c : real) (t : real -> Prop) : (term181 s t c) = (term162 s c t).
Proof. exact (MK_COMB (@lem5276599) (@lem5276598 s c t)). Qed.
Lemma lem5276601 (s : real -> Prop) (c : real) (t : real -> Prop) : (term237 s t c) = (term231 s c t).
Proof. exact (eq_refl (term237 s t c)). Qed.
Lemma lem5276602 (s : real -> Prop) (c : real) (t : real -> Prop) : (term242 s t c) = (term243 s c t).
Proof. exact (MK_COMB (@lem5276600 s c t) (@lem5276601 s c t)). Qed.
Lemma lem5276603 (s : real -> Prop) (t : real -> Prop) : (term244 s t) = (term245 s t).
Proof. exact (fun_ext (fun c : real => @lem5276602 s c t)). Qed.
Lemma lem5276604 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276605 (s : real -> Prop) (t : real -> Prop) : (term236 s t) = (term246 s t).
Proof. exact (MK_COMB (@lem5276604) (@lem5276603 s t)). Qed.
Lemma lem5276606 (s : real -> Prop) (t : real -> Prop) : ((term235 s t) = (term236 s t)) = ((term234 s t) = (term246 s t)).
Proof. exact (MK_COMB (@lem5276597 s t) (@lem5276605 s t)). Qed.
Lemma lem5276607 (s : real -> Prop) (t : real -> Prop) : (term234 s t) = (term246 s t).
Proof. exact (EQ_MP (@lem5276606 s t) (@lem5276584 s t)). Qed.
Lemma lem5276609 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5276610 (P : Prop) (Q : real -> Prop) : (term249 P Q) = (term250 P Q).
Proof. exact (@lem5276609 real P Q). Qed.
Lemma lem5276611 (s : real -> Prop) (c : real) (t : real -> Prop) : (term251 s c t) = (term252 s c t).
Proof. exact (@lem5276610 (term160 s c t) (term230 s c t)). Qed.
Lemma lem5276612 (x : real) (s : real -> Prop) (c : real) (t : real -> Prop) : (term253 s c t x) = (term228 x s c t).
Proof. exact (eq_refl (term253 s c t x)). Qed.
Lemma lem5276613 (s : real -> Prop) (c : real) (t : real -> Prop) : (term254 s c t) = (term230 s c t).
Proof. exact (fun_ext (fun x : real => @lem5276612 x s c t)). Qed.
Lemma lem5276614 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276615 (s : real -> Prop) (c : real) (t : real -> Prop) : (term255 s c t) = (term231 s c t).
Proof. exact (MK_COMB (@lem5276614) (@lem5276613 s c t)). Qed.
Lemma lem5276616 (s : real -> Prop) (c : real) (t : real -> Prop) : (term162 s c t) = (term162 s c t).
Proof. exact (eq_refl (term162 s c t)). Qed.
Lemma lem5276617 (s : real -> Prop) (c : real) (t : real -> Prop) : (term251 s c t) = (term243 s c t).
Proof. exact (MK_COMB (@lem5276616 s c t) (@lem5276615 s c t)). Qed.
Lemma lem5276618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5276619 (s : real -> Prop) (c : real) (t : real -> Prop) : (term256 s c t) = (term257 s c t).
Proof. exact (MK_COMB (@lem5276618) (@lem5276617 s c t)). Qed.
Lemma lem5276620 (x : real) (s : real -> Prop) (c : real) (t : real -> Prop) : (term253 s c t x) = (term228 x s c t).
Proof. exact (eq_refl (term253 s c t x)). Qed.
Lemma lem5276621 (s : real -> Prop) (c : real) (t : real -> Prop) : (term162 s c t) = (term162 s c t).
Proof. exact (eq_refl (term162 s c t)). Qed.
Lemma lem5276622 (x : real) (s : real -> Prop) (c : real) (t : real -> Prop) : (term258 s c t x) = (term259 x s c t).
Proof. exact (MK_COMB (@lem5276621 s c t) (@lem5276620 x s c t)). Qed.
Lemma lem5276623 (s : real -> Prop) (c : real) (t : real -> Prop) : (term260 s c t) = (term261 s c t).
Proof. exact (fun_ext (fun x : real => @lem5276622 x s c t)). Qed.
Lemma lem5276624 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276625 (s : real -> Prop) (c : real) (t : real -> Prop) : (term252 s c t) = (term262 s c t).
Proof. exact (MK_COMB (@lem5276624) (@lem5276623 s c t)). Qed.
Lemma lem5276626 (s : real -> Prop) (c : real) (t : real -> Prop) : ((term251 s c t) = (term252 s c t)) = ((term243 s c t) = (term262 s c t)).
Proof. exact (MK_COMB (@lem5276619 s c t) (@lem5276625 s c t)). Qed.
Lemma lem5276627 (s : real -> Prop) (c : real) (t : real -> Prop) : (term243 s c t) = (term262 s c t).
Proof. exact (EQ_MP (@lem5276626 s c t) (@lem5276611 s c t)). Qed.
Lemma lem5276628 (s : real -> Prop) (t : real -> Prop) : (term245 s t) = (term263 s t).
Proof. exact (fun_ext (fun c : real => @lem5276627 s c t)). Qed.
Lemma lem5276629 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276630 (s : real -> Prop) (t : real -> Prop) : (term246 s t) = (term264 s t).
Proof. exact (MK_COMB (@lem5276629) (@lem5276628 s t)). Qed.
Lemma lem5276631 (s : real -> Prop) (t : real -> Prop) : (term234 s t) = (term264 s t).
Proof. exact (TRANS (@lem5276607 s t) (@lem5276630 s t)). Qed.
Lemma lem5276632 (s : real -> Prop) (t : real -> Prop) : (term195 s t) = (term264 s t).
Proof. exact (TRANS (@lem5276580 s t) (@lem5276631 s t)). Qed.
Lemma lem5276633 (s : real -> Prop) (t : real -> Prop) : (term171 s t) = (term264 s t).
Proof. exact (TRANS (@lem5276231 s t) (@lem5276632 s t)). Qed.
Lemma lem5276634 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term264 s t).
Proof. exact (TRANS (@lem5276204 s t) (@lem5276633 s t)). Qed.
Lemma lem5276635 (s : real -> Prop) (t : real -> Prop) (h1 : term69 s t) : term264 s t.
Proof. exact (EQ_MP (@lem5276634 s t) (@lem5275969 s t h1)). Qed.
Lemma lem5276642 (x : real) (y : real) (z : real) : (term265 x y z) = (term266 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5276643 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5276644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276645 (x : real) (y : real) (z : real) : (term267 x y z) = (term268 x y z).
Proof. exact (MK_COMB (@lem5276644) (@lem5276642 x y z)). Qed.
Lemma lem5276646 (y : real) (x : real) (z : real) : (term269 y x z) = (term270 y x z).
Proof. exact (MK_COMB (@lem5276645 x y z) (@lem5276643 x z)). Qed.
Lemma lem5276647 (y : real) (x : real) (z : real) : (term123 y x z) = (term269 y x z).
Proof. exact (@lem17265 (term271 x y z) (real_le x z)). Qed.
Lemma lem5276648 (y : real) (x : real) (z : real) : (term123 y x z) = (term270 y x z).
Proof. exact (TRANS (@lem5276647 y x z) (@lem5276646 y x z)). Qed.
Lemma lem5276649 (y : real) (x : real) : (term124 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5276648 y x z)). Qed.
Lemma lem5276650 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276651 (y : real) (x : real) : (term125 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5276650) (@lem5276649 y x)). Qed.
Lemma lem5276652 (x : real) : (term126 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5276651 y x)). Qed.
Lemma lem5276653 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276654 (x : real) : (term127 x) = (term275 x).
Proof. exact (MK_COMB (@lem5276653) (@lem5276652 x)). Qed.
Lemma lem5276655 : term128 = term276.
Proof. exact (fun_ext (fun x : real => @lem5276654 x)). Qed.
Lemma lem5276656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276717 : term129 = term277.
Proof. exact (MK_COMB (@lem5276656) (@lem5276655)). Qed.
Lemma lem5276718 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5276717) (@lem5275970 h1)). Qed.
Lemma lem5276721 (s : real -> Prop) : (term278 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5276728 (s : real -> Prop) (b : real) (x : real) : (term133 s b x) = (term134 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5276729 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5276730 (s : real -> Prop) (b : real) : (term137 s b) = (term138 s b).
Proof. exact (@lem5276729 (term55 s b)). Qed.
Lemma lem5276731 (s : real -> Prop) (b : real) (x : real) : (term139 s b x) = (term53 s b x).
Proof. exact (eq_refl (term139 s b x)). Qed.
Lemma lem5276732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5276733 (s : real -> Prop) (b : real) (x : real) : (term140 s b x) = (term133 s b x).
Proof. exact (MK_COMB (@lem5276732) (@lem5276731 s b x)). Qed.
Lemma lem5276734 (s : real -> Prop) (b : real) (x : real) : (term140 s b x) = (term134 s b x).
Proof. exact (TRANS (@lem5276733 s b x) (@lem5276728 s b x)). Qed.
Lemma lem5276735 (s : real -> Prop) (b : real) : (term141 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5276734 s b x)). Qed.
Lemma lem5276736 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276737 (s : real -> Prop) (b : real) : (term138 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5276736) (@lem5276735 s b)). Qed.
Lemma lem5276738 (s : real -> Prop) (b : real) : (term137 s b) = (term143 s b).
Proof. exact (TRANS (@lem5276730 s b) (@lem5276737 s b)). Qed.
Lemma lem5276739 (P : real -> Prop) : (term279 P) = (term280 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5276740 (s : real -> Prop) : (term281 s) = (term282 s).
Proof. exact (@lem5276739 (term117 s)). Qed.
Lemma lem5276741 (s : real -> Prop) (b : real) : (term283 s b) = (term34 s b).
Proof. exact (eq_refl (term283 s b)). Qed.
Lemma lem5276742 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5276743 (s : real -> Prop) (b : real) : (term284 s b) = (term137 s b).
Proof. exact (MK_COMB (@lem5276742) (@lem5276741 s b)). Qed.
Lemma lem5276744 (s : real -> Prop) (b : real) : (term284 s b) = (term143 s b).
Proof. exact (TRANS (@lem5276743 s b) (@lem5276738 s b)). Qed.
Lemma lem5276745 (s : real -> Prop) : (term285 s) = (term286 s).
Proof. exact (fun_ext (fun b : real => @lem5276744 s b)). Qed.
Lemma lem5276746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276747 (s : real -> Prop) : (term282 s) = (term287 s).
Proof. exact (MK_COMB (@lem5276746) (@lem5276745 s)). Qed.
Lemma lem5276748 (s : real -> Prop) : (term281 s) = (term287 s).
Proof. exact (TRANS (@lem5276740 s) (@lem5276747 s)). Qed.
Lemma lem5276749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276750 (s : real -> Prop) : (term288 s) = (term289 s).
Proof. exact (MK_COMB (@lem5276749) (@lem5276721 s)). Qed.
Lemma lem5276751 (s : real -> Prop) : (term290 s) = (term291 s).
Proof. exact (MK_COMB (@lem5276750 s) (@lem5276748 s)). Qed.
Lemma lem5276752 (s : real -> Prop) : (term292 s) = (term290 s).
Proof. exact (@lem17045 (term31 s) (term33 s)). Qed.
Lemma lem5276753 (s : real -> Prop) : (term292 s) = (term291 s).
Proof. exact (TRANS (@lem5276752 s) (@lem5276751 s)). Qed.
Lemma lem5276760 (s : real -> Prop) (x : real) : (term112 s x) = (term293 s x).
Proof. exact (@lem17265 (@IN real x s) (term294 s x)). Qed.
Lemma lem5276761 (s : real -> Prop) : (term113 s) = (term295 s).
Proof. exact (fun_ext (fun x : real => @lem5276760 s x)). Qed.
Lemma lem5276762 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276763 (s : real -> Prop) : (term114 s) = (term296 s).
Proof. exact (MK_COMB (@lem5276762) (@lem5276761 s)). Qed.
Lemma lem5276770 (s : real -> Prop) (b : real) (x : real) : (term133 s b x) = (term134 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5276771 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5276772 (s : real -> Prop) (b : real) : (term137 s b) = (term138 s b).
Proof. exact (@lem5276771 (term55 s b)). Qed.
Lemma lem5276773 (s : real -> Prop) (b : real) (x : real) : (term139 s b x) = (term53 s b x).
Proof. exact (eq_refl (term139 s b x)). Qed.
Lemma lem5276774 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5276775 (s : real -> Prop) (b : real) (x : real) : (term140 s b x) = (term133 s b x).
Proof. exact (MK_COMB (@lem5276774) (@lem5276773 s b x)). Qed.
Lemma lem5276776 (s : real -> Prop) (b : real) (x : real) : (term140 s b x) = (term134 s b x).
Proof. exact (TRANS (@lem5276775 s b x) (@lem5276770 s b x)). Qed.
Lemma lem5276777 (s : real -> Prop) (b : real) : (term141 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5276776 s b x)). Qed.
Lemma lem5276778 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5276779 (s : real -> Prop) (b : real) : (term138 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5276778) (@lem5276777 s b)). Qed.
Lemma lem5276780 (s : real -> Prop) (b : real) : (term137 s b) = (term143 s b).
Proof. exact (TRANS (@lem5276772 s b) (@lem5276779 s b)). Qed.
Lemma lem5276781 (b : real) (s : real -> Prop) : (term108 b s) = (term108 b s).
Proof. exact (eq_refl (term108 b s)). Qed.
Lemma lem5276782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276783 (s : real -> Prop) (b : real) : (term144 s b) = (term145 s b).
Proof. exact (MK_COMB (@lem5276782) (@lem5276780 s b)). Qed.
Lemma lem5276784 (b : real) (s : real -> Prop) : (term297 b s) = (term298 b s).
Proof. exact (MK_COMB (@lem5276783 s b) (@lem5276781 b s)). Qed.
Lemma lem5276785 (b : real) (s : real -> Prop) : (term109 b s) = (term297 b s).
Proof. exact (@lem17265 (term34 s b) (term108 b s)). Qed.
Lemma lem5276786 (b : real) (s : real -> Prop) : (term109 b s) = (term298 b s).
Proof. exact (TRANS (@lem5276785 b s) (@lem5276784 b s)). Qed.
Lemma lem5276787 (s : real -> Prop) : (term110 s) = (term299 s).
Proof. exact (fun_ext (fun b : real => @lem5276786 b s)). Qed.
Lemma lem5276788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5276789 (s : real -> Prop) : (term111 s) = (term300 s).
Proof. exact (MK_COMB (@lem5276788) (@lem5276787 s)). Qed.
Lemma lem5276790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5276791 (s : real -> Prop) : (term115 s) = (term301 s).
Proof. exact (MK_COMB (@lem5276790) (@lem5276763 s)). Qed.
Lemma lem5276792 (s : real -> Prop) : (term116 s) = (term302 s).
Proof. exact (MK_COMB (@lem5276791 s) (@lem5276789 s)). Qed.
Lemma lem5276793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5276794 (s : real -> Prop) : (term303 s) = (term304 s).
Proof. exact (MK_COMB (@lem5276793) (@lem5276753 s)). Qed.
Lemma lem5276795 (s : real -> Prop) : (term305 s) = (term306 s).
Proof. exact (MK_COMB (@lem5276794 s) (@lem5276792 s)). Qed.
Lemma lem5276796 (s : real -> Prop) : (term121 s) = (term305 s).
Proof. exact (@lem17265 (term119 s) (term116 s)). Qed.
Lemma lem5276797 (s : real -> Prop) : (term121 s) = (term306 s).
Proof. exact (TRANS (@lem5276796 s) (@lem5276795 s)). Qed.
Lemma lem5276798 : term122 = term307.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5276797 s)). Qed.
Lemma lem5276799 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5276800 : term76 = term308.
Proof. exact (MK_COMB (@lem5276799) (@lem5276798)). Qed.
Lemma lem5277047 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5277048 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5277047 real real P). Qed.
Lemma lem5277049 (s : real -> Prop) : (term313 s) = (term314 s).
Proof. exact (@lem5277048 (term315 s)). Qed.
Lemma lem5277050 (s : real -> Prop) (b : real) : (term316 s b) = (term142 s b).
Proof. exact (eq_refl (term316 s b)). Qed.
Lemma lem5277051 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5277052 (s : real -> Prop) (b : real) (x : real) : (term317 s b x) = (term198 s b x).
Proof. exact (MK_COMB (@lem5277050 s b) (@lem5277051 x)). Qed.
Lemma lem5277053 (s : real -> Prop) (b : real) (x : real) : (term198 s b x) = (term134 s b x).
Proof. exact (eq_refl (term198 s b x)). Qed.
Lemma lem5277054 (s : real -> Prop) (b : real) (x : real) : (term317 s b x) = (term134 s b x).
Proof. exact (TRANS (@lem5277052 s b x) (@lem5277053 s b x)). Qed.
Lemma lem5277055 (s : real -> Prop) (b : real) : (term318 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5277054 s b x)). Qed.
Lemma lem5277056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5277057 (s : real -> Prop) (b : real) : (term319 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5277056) (@lem5277055 s b)). Qed.
Lemma lem5277058 (s : real -> Prop) : (term320 s) = (term286 s).
Proof. exact (fun_ext (fun b : real => @lem5277057 s b)). Qed.
Lemma lem5277059 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277060 (s : real -> Prop) : (term313 s) = (term287 s).
Proof. exact (MK_COMB (@lem5277059) (@lem5277058 s)). Qed.
Lemma lem5277061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277062 (s : real -> Prop) : (term321 s) = (term322 s).
Proof. exact (MK_COMB (@lem5277061) (@lem5277060 s)). Qed.
Lemma lem5277063 (s : real -> Prop) (b : real) : (term316 s b) = (term142 s b).
Proof. exact (eq_refl (term316 s b)). Qed.
Lemma lem5277064 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5277065 (s : real -> Prop) (x : real -> real) (b : real) : (term323 s x b) = (term324 s x b).
Proof. exact (MK_COMB (@lem5277063 s b) (@lem5277064 x b)). Qed.
Lemma lem5277066 (s : real -> Prop) (x : real -> real) (b : real) : (term324 s x b) = (term325 s x b).
Proof. exact (eq_refl (term324 s x b)). Qed.
Lemma lem5277067 (s : real -> Prop) (x : real -> real) (b : real) : (term323 s x b) = (term325 s x b).
Proof. exact (TRANS (@lem5277065 s x b) (@lem5277066 s x b)). Qed.
Lemma lem5277068 (s : real -> Prop) (x : real -> real) : (term326 s x) = (term327 s x).
Proof. exact (fun_ext (fun b : real => @lem5277067 s x b)). Qed.
Lemma lem5277069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277070 (s : real -> Prop) (x : real -> real) : (term328 s x) = (term329 s x).
Proof. exact (MK_COMB (@lem5277069) (@lem5277068 s x)). Qed.
Lemma lem5277071 (s : real -> Prop) : (term330 s) = (term331 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277070 s x)). Qed.
Lemma lem5277072 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277073 (s : real -> Prop) : (term314 s) = (term332 s).
Proof. exact (MK_COMB (@lem5277072) (@lem5277071 s)). Qed.
Lemma lem5277074 (s : real -> Prop) : ((term313 s) = (term314 s)) = ((term287 s) = (term332 s)).
Proof. exact (MK_COMB (@lem5277062 s) (@lem5277073 s)). Qed.
Lemma lem5277075 (s : real -> Prop) : (term287 s) = (term332 s).
Proof. exact (EQ_MP (@lem5277074 s) (@lem5277049 s)). Qed.
Lemma lem5277076 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277077 (s : real -> Prop) : (term291 s) = (term333 s).
Proof. exact (MK_COMB (@lem5277076 s) (@lem5277075 s)). Qed.
Lemma lem5277079 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5277080 (P : Prop) (Q : type1028) : (term334 P Q) = (term335 P Q).
Proof. exact (@lem5277079 (real -> real) P Q). Qed.
Lemma lem5277081 (s : real -> Prop) : (term336 s) = (term337 s).
Proof. exact (@lem5277080 (s = (@EMPTY real)) (term331 s)). Qed.
Lemma lem5277082 (s : real -> Prop) (x : real -> real) : (term338 s x) = (term329 s x).
Proof. exact (eq_refl (term338 s x)). Qed.
Lemma lem5277083 (s : real -> Prop) : (term339 s) = (term331 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277082 s x)). Qed.
Lemma lem5277084 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277085 (s : real -> Prop) : (term340 s) = (term332 s).
Proof. exact (MK_COMB (@lem5277084) (@lem5277083 s)). Qed.
Lemma lem5277086 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277087 (s : real -> Prop) : (term336 s) = (term333 s).
Proof. exact (MK_COMB (@lem5277086 s) (@lem5277085 s)). Qed.
Lemma lem5277088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277089 (s : real -> Prop) : (term341 s) = (term342 s).
Proof. exact (MK_COMB (@lem5277088) (@lem5277087 s)). Qed.
Lemma lem5277090 (s : real -> Prop) (x : real -> real) : (term338 s x) = (term329 s x).
Proof. exact (eq_refl (term338 s x)). Qed.
Lemma lem5277091 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277092 (s : real -> Prop) (x : real -> real) : (term343 s x) = (term344 s x).
Proof. exact (MK_COMB (@lem5277091 s) (@lem5277090 s x)). Qed.
Lemma lem5277093 (s : real -> Prop) : (term345 s) = (term346 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277092 s x)). Qed.
Lemma lem5277094 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277095 (s : real -> Prop) : (term337 s) = (term347 s).
Proof. exact (MK_COMB (@lem5277094) (@lem5277093 s)). Qed.
Lemma lem5277096 (s : real -> Prop) : ((term336 s) = (term337 s)) = ((term333 s) = (term347 s)).
Proof. exact (MK_COMB (@lem5277089 s) (@lem5277095 s)). Qed.
Lemma lem5277097 (s : real -> Prop) : (term333 s) = (term347 s).
Proof. exact (EQ_MP (@lem5277096 s) (@lem5277081 s)). Qed.
Lemma lem5277098 (s : real -> Prop) : (term291 s) = (term347 s).
Proof. exact (TRANS (@lem5277077 s) (@lem5277097 s)). Qed.
Lemma lem5277099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277100 (s : real -> Prop) : (term304 s) = (term348 s).
Proof. exact (MK_COMB (@lem5277099) (@lem5277098 s)). Qed.
Lemma lem5277102 {A : Type'} (P : A -> Prop) (Q : Prop) : (term349 A P Q) = (term350 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5277103 (P : real -> Prop) (Q : Prop) : (term351 P Q) = (term352 P Q).
Proof. exact (@lem5277102 real P Q). Qed.
Lemma lem5277104 (b : real) (s : real -> Prop) : (term353 b s) = (term354 b s).
Proof. exact (@lem5277103 (term142 s b) (term108 b s)). Qed.
Lemma lem5277105 (s : real -> Prop) (b : real) (x : real) : (term198 s b x) = (term134 s b x).
Proof. exact (eq_refl (term198 s b x)). Qed.
Lemma lem5277106 (s : real -> Prop) (b : real) : (term199 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5277105 s b x)). Qed.
Lemma lem5277107 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5277108 (s : real -> Prop) (b : real) : (term200 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5277107) (@lem5277106 s b)). Qed.
Lemma lem5277109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277110 (s : real -> Prop) (b : real) : (term201 s b) = (term145 s b).
Proof. exact (MK_COMB (@lem5277109) (@lem5277108 s b)). Qed.
Lemma lem5277111 (b : real) (s : real -> Prop) : (term108 b s) = (term108 b s).
Proof. exact (eq_refl (term108 b s)). Qed.
Lemma lem5277112 (b : real) (s : real -> Prop) : (term353 b s) = (term298 b s).
Proof. exact (MK_COMB (@lem5277110 s b) (@lem5277111 b s)). Qed.
Lemma lem5277113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277114 (b : real) (s : real -> Prop) : (term355 b s) = (term356 b s).
Proof. exact (MK_COMB (@lem5277113) (@lem5277112 b s)). Qed.
Lemma lem5277115 (s : real -> Prop) (b : real) (x : real) : (term198 s b x) = (term134 s b x).
Proof. exact (eq_refl (term198 s b x)). Qed.
Lemma lem5277116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277117 (s : real -> Prop) (b : real) (x : real) : (term204 s b x) = (term205 s b x).
Proof. exact (MK_COMB (@lem5277116) (@lem5277115 s b x)). Qed.
Lemma lem5277118 (b : real) (s : real -> Prop) : (term108 b s) = (term108 b s).
Proof. exact (eq_refl (term108 b s)). Qed.
Lemma lem5277119 (x : real) (b : real) (s : real -> Prop) : (term357 x b s) = (term358 x b s).
Proof. exact (MK_COMB (@lem5277117 s b x) (@lem5277118 b s)). Qed.
Lemma lem5277120 (b : real) (s : real -> Prop) : (term359 b s) = (term360 b s).
Proof. exact (fun_ext (fun x : real => @lem5277119 x b s)). Qed.
Lemma lem5277121 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5277122 (b : real) (s : real -> Prop) : (term354 b s) = (term361 b s).
Proof. exact (MK_COMB (@lem5277121) (@lem5277120 b s)). Qed.
Lemma lem5277123 (b : real) (s : real -> Prop) : ((term353 b s) = (term354 b s)) = ((term298 b s) = (term361 b s)).
Proof. exact (MK_COMB (@lem5277114 b s) (@lem5277122 b s)). Qed.
Lemma lem5277124 (b : real) (s : real -> Prop) : (term298 b s) = (term361 b s).
Proof. exact (EQ_MP (@lem5277123 b s) (@lem5277104 b s)). Qed.
Lemma lem5277125 (s : real -> Prop) : (term299 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5277124 b s)). Qed.
Lemma lem5277126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277127 (s : real -> Prop) : (term300 s) = (term363 s).
Proof. exact (MK_COMB (@lem5277126) (@lem5277125 s)). Qed.
Lemma lem5277129 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5277130 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5277129 real real P). Qed.
Lemma lem5277131 (s : real -> Prop) : (term364 s) = (term365 s).
Proof. exact (@lem5277130 (term366 s)). Qed.
Lemma lem5277132 (b : real) (s : real -> Prop) : (term367 s b) = (term360 b s).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5277133 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5277134 (b : real) (s : real -> Prop) (x : real) : (term368 s b x) = (term369 b s x).
Proof. exact (MK_COMB (@lem5277132 b s) (@lem5277133 x)). Qed.
Lemma lem5277135 (x : real) (b : real) (s : real -> Prop) : (term369 b s x) = (term358 x b s).
Proof. exact (eq_refl (term369 b s x)). Qed.
Lemma lem5277136 (x : real) (b : real) (s : real -> Prop) : (term368 s b x) = (term358 x b s).
Proof. exact (TRANS (@lem5277134 b s x) (@lem5277135 x b s)). Qed.
Lemma lem5277137 (b : real) (s : real -> Prop) : (term370 s b) = (term360 b s).
Proof. exact (fun_ext (fun x : real => @lem5277136 x b s)). Qed.
Lemma lem5277138 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5277139 (b : real) (s : real -> Prop) : (term371 s b) = (term361 b s).
Proof. exact (MK_COMB (@lem5277138) (@lem5277137 b s)). Qed.
Lemma lem5277140 (s : real -> Prop) : (term372 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5277139 b s)). Qed.
Lemma lem5277141 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277142 (s : real -> Prop) : (term364 s) = (term363 s).
Proof. exact (MK_COMB (@lem5277141) (@lem5277140 s)). Qed.
Lemma lem5277143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277144 (s : real -> Prop) : (term373 s) = (term374 s).
Proof. exact (MK_COMB (@lem5277143) (@lem5277142 s)). Qed.
Lemma lem5277145 (b : real) (s : real -> Prop) : (term367 s b) = (term360 b s).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5277146 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5277147 (s : real -> Prop) (x : real -> real) (b : real) : (term375 s x b) = (term376 s x b).
Proof. exact (MK_COMB (@lem5277145 b s) (@lem5277146 x b)). Qed.
Lemma lem5277148 (x : real -> real) (b : real) (s : real -> Prop) : (term376 s x b) = (term377 x b s).
Proof. exact (eq_refl (term376 s x b)). Qed.
Lemma lem5277149 (x : real -> real) (b : real) (s : real -> Prop) : (term375 s x b) = (term377 x b s).
Proof. exact (TRANS (@lem5277147 s x b) (@lem5277148 x b s)). Qed.
Lemma lem5277150 (x : real -> real) (s : real -> Prop) : (term378 s x) = (term379 x s).
Proof. exact (fun_ext (fun b : real => @lem5277149 x b s)). Qed.
Lemma lem5277151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277152 (x : real -> real) (s : real -> Prop) : (term380 s x) = (term381 x s).
Proof. exact (MK_COMB (@lem5277151) (@lem5277150 x s)). Qed.
Lemma lem5277153 (s : real -> Prop) : (term382 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277152 x s)). Qed.
Lemma lem5277154 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277155 (s : real -> Prop) : (term365 s) = (term384 s).
Proof. exact (MK_COMB (@lem5277154) (@lem5277153 s)). Qed.
Lemma lem5277156 (s : real -> Prop) : ((term364 s) = (term365 s)) = ((term363 s) = (term384 s)).
Proof. exact (MK_COMB (@lem5277144 s) (@lem5277155 s)). Qed.
Lemma lem5277157 (s : real -> Prop) : (term363 s) = (term384 s).
Proof. exact (EQ_MP (@lem5277156 s) (@lem5277131 s)). Qed.
Lemma lem5277158 (s : real -> Prop) : (term300 s) = (term384 s).
Proof. exact (TRANS (@lem5277127 s) (@lem5277157 s)). Qed.
Lemma lem5277159 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5277160 (s : real -> Prop) : (term302 s) = (term385 s).
Proof. exact (MK_COMB (@lem5277159 s) (@lem5277158 s)). Qed.
Lemma lem5277162 {A : Type'} (P : Prop) (Q : A -> Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5277163 (P : Prop) (Q : type1028) : (term388 P Q) = (term389 P Q).
Proof. exact (@lem5277162 (real -> real) P Q). Qed.
Lemma lem5277164 (s : real -> Prop) : (term390 s) = (term391 s).
Proof. exact (@lem5277163 (term296 s) (term383 s)). Qed.
Lemma lem5277165 (x : real -> real) (s : real -> Prop) : (term392 s x) = (term381 x s).
Proof. exact (eq_refl (term392 s x)). Qed.
Lemma lem5277166 (s : real -> Prop) : (term393 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277165 x s)). Qed.
Lemma lem5277167 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277168 (s : real -> Prop) : (term394 s) = (term384 s).
Proof. exact (MK_COMB (@lem5277167) (@lem5277166 s)). Qed.
Lemma lem5277169 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5277170 (s : real -> Prop) : (term390 s) = (term385 s).
Proof. exact (MK_COMB (@lem5277169 s) (@lem5277168 s)). Qed.
Lemma lem5277171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277172 (s : real -> Prop) : (term395 s) = (term396 s).
Proof. exact (MK_COMB (@lem5277171) (@lem5277170 s)). Qed.
Lemma lem5277173 (x : real -> real) (s : real -> Prop) : (term392 s x) = (term381 x s).
Proof. exact (eq_refl (term392 s x)). Qed.
Lemma lem5277174 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5277175 (x : real -> real) (s : real -> Prop) : (term397 s x) = (term398 x s).
Proof. exact (MK_COMB (@lem5277174 s) (@lem5277173 x s)). Qed.
Lemma lem5277176 (s : real -> Prop) : (term399 s) = (term400 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277175 x s)). Qed.
Lemma lem5277177 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277178 (s : real -> Prop) : (term391 s) = (term401 s).
Proof. exact (MK_COMB (@lem5277177) (@lem5277176 s)). Qed.
Lemma lem5277179 (s : real -> Prop) : ((term390 s) = (term391 s)) = ((term385 s) = (term401 s)).
Proof. exact (MK_COMB (@lem5277172 s) (@lem5277178 s)). Qed.
Lemma lem5277180 (s : real -> Prop) : (term385 s) = (term401 s).
Proof. exact (EQ_MP (@lem5277179 s) (@lem5277164 s)). Qed.
Lemma lem5277181 (s : real -> Prop) : (term302 s) = (term401 s).
Proof. exact (TRANS (@lem5277160 s) (@lem5277180 s)). Qed.
Lemma lem5277182 (s : real -> Prop) : (term306 s) = (term402 s).
Proof. exact (MK_COMB (@lem5277100 s) (@lem5277181 s)). Qed.
Lemma lem5277184 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term173 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5277185 (P : type1028) (Q : type1028) : (term403 P Q) = (term404 P Q).
Proof. exact (@lem5277184 (real -> real) P Q). Qed.
Lemma lem5277186 (s : real -> Prop) : (term405 s) = (term406 s).
Proof. exact (@lem5277185 (term346 s) (term400 s)). Qed.
Lemma lem5277187 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term344 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5277188 (s : real -> Prop) : (term408 s) = (term346 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277187 s x)). Qed.
Lemma lem5277189 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277190 (s : real -> Prop) : (term409 s) = (term347 s).
Proof. exact (MK_COMB (@lem5277189) (@lem5277188 s)). Qed.
Lemma lem5277191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277192 (s : real -> Prop) : (term410 s) = (term348 s).
Proof. exact (MK_COMB (@lem5277191) (@lem5277190 s)). Qed.
Lemma lem5277193 (x : real -> real) (s : real -> Prop) : (term411 s x) = (term398 x s).
Proof. exact (eq_refl (term411 s x)). Qed.
Lemma lem5277194 (s : real -> Prop) : (term412 s) = (term400 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277193 x s)). Qed.
Lemma lem5277195 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277196 (s : real -> Prop) : (term413 s) = (term401 s).
Proof. exact (MK_COMB (@lem5277195) (@lem5277194 s)). Qed.
Lemma lem5277197 (s : real -> Prop) : (term405 s) = (term402 s).
Proof. exact (MK_COMB (@lem5277192 s) (@lem5277196 s)). Qed.
Lemma lem5277198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277199 (s : real -> Prop) : (term414 s) = (term415 s).
Proof. exact (MK_COMB (@lem5277198) (@lem5277197 s)). Qed.
Lemma lem5277200 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term344 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5277201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277202 (s : real -> Prop) (x : real -> real) : (term416 s x) = (term417 s x).
Proof. exact (MK_COMB (@lem5277201) (@lem5277200 s x)). Qed.
Lemma lem5277203 (x : real -> real) (s : real -> Prop) : (term411 s x) = (term398 x s).
Proof. exact (eq_refl (term411 s x)). Qed.
Lemma lem5277204 (x : real -> real) (s : real -> Prop) : (term418 s x) = (term419 x s).
Proof. exact (MK_COMB (@lem5277202 s x) (@lem5277203 x s)). Qed.
Lemma lem5277205 (s : real -> Prop) : (term420 s) = (term421 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277204 x s)). Qed.
Lemma lem5277206 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277207 (s : real -> Prop) : (term406 s) = (term422 s).
Proof. exact (MK_COMB (@lem5277206) (@lem5277205 s)). Qed.
Lemma lem5277208 (s : real -> Prop) : ((term405 s) = (term406 s)) = ((term402 s) = (term422 s)).
Proof. exact (MK_COMB (@lem5277199 s) (@lem5277207 s)). Qed.
Lemma lem5277209 (s : real -> Prop) : (term402 s) = (term422 s).
Proof. exact (EQ_MP (@lem5277208 s) (@lem5277186 s)). Qed.
Lemma lem5277210 (s : real -> Prop) : (term306 s) = (term422 s).
Proof. exact (TRANS (@lem5277182 s) (@lem5277209 s)). Qed.
Lemma lem5277211 : term307 = term423.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5277210 s)). Qed.
Lemma lem5277212 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5277213 : term308 = term424.
Proof. exact (MK_COMB (@lem5277212) (@lem5277211)). Qed.
Lemma lem5277215 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5277216 (P : type1017) : (term425 P) = (term426 P).
Proof. exact (@lem5277215 (real -> Prop) (real -> real) P). Qed.
Lemma lem5277217 : term427 = term428.
Proof. exact (@lem5277216 term429). Qed.
Lemma lem5277218 (s : real -> Prop) : (term430 s) = (term421 s).
Proof. exact (eq_refl (term430 s)). Qed.
Lemma lem5277219 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5277220 (s : real -> Prop) (x : real -> real) : (term431 s x) = (term432 s x).
Proof. exact (MK_COMB (@lem5277218 s) (@lem5277219 x)). Qed.
Lemma lem5277221 (x : real -> real) (s : real -> Prop) : (term432 s x) = (term419 x s).
Proof. exact (eq_refl (term432 s x)). Qed.
Lemma lem5277222 (x : real -> real) (s : real -> Prop) : (term431 s x) = (term419 x s).
Proof. exact (TRANS (@lem5277220 s x) (@lem5277221 x s)). Qed.
Lemma lem5277223 (s : real -> Prop) : (term433 s) = (term421 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5277222 x s)). Qed.
Lemma lem5277224 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5277225 (s : real -> Prop) : (term434 s) = (term422 s).
Proof. exact (MK_COMB (@lem5277224) (@lem5277223 s)). Qed.
Lemma lem5277226 : term435 = term423.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5277225 s)). Qed.
Lemma lem5277227 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5277228 : term427 = term424.
Proof. exact (MK_COMB (@lem5277227) (@lem5277226)). Qed.
Lemma lem5277229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277230 : term436 = term437.
Proof. exact (MK_COMB (@lem5277229) (@lem5277228)). Qed.
Lemma lem5277231 (s : real -> Prop) : (term430 s) = (term421 s).
Proof. exact (eq_refl (term430 s)). Qed.
Lemma lem5277232 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5277233 (x : type1021) (s : real -> Prop) : (term438 x s) = (term439 x s).
Proof. exact (MK_COMB (@lem5277231 s) (@lem5277232 x s)). Qed.
Lemma lem5277234 (x : type1021) (s : real -> Prop) : (term439 x s) = (term440 x s).
Proof. exact (eq_refl (term439 x s)). Qed.
Lemma lem5277235 (x : type1021) (s : real -> Prop) : (term438 x s) = (term440 x s).
Proof. exact (TRANS (@lem5277233 x s) (@lem5277234 x s)). Qed.
Lemma lem5277236 (x : type1021) : (term441 x) = (term442 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5277235 x s)). Qed.
Lemma lem5277237 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5277238 (x : type1021) : (term443 x) = (term444 x).
Proof. exact (MK_COMB (@lem5277237) (@lem5277236 x)). Qed.
Lemma lem5277239 : term445 = term446.
Proof. exact (fun_ext (fun x : type1021 => @lem5277238 x)). Qed.
Lemma lem5277240 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5277241 : term428 = term447.
Proof. exact (MK_COMB (@lem5277240) (@lem5277239)). Qed.
Lemma lem5277242 : (term427 = term428) = (term424 = term447).
Proof. exact (MK_COMB (@lem5277230) (@lem5277241)). Qed.
Lemma lem5277243 : term424 = term447.
Proof. exact (EQ_MP (@lem5277242) (@lem5277217)). Qed.
Lemma lem5277245 : term308 = term447.
Proof. exact (TRANS (@lem5277213) (@lem5277243)). Qed.
Lemma lem5277246 : term76 = term447.
Proof. exact (TRANS (@lem5276800) (@lem5277245)). Qed.
Lemma lem5277247 (h1 : term76) : term447.
Proof. exact (EQ_MP (@lem5277246) (@lem5275971 h1)). Qed.
Lemma lem5277248 (x : type1021) (h1 : term444 x) : term444 x.
Proof. exact (h1). Qed.
Lemma lem5277249 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term262 s c' t) : term262 s c' t.
Proof. exact (h1). Qed.
Lemma lem5277250 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term259 x' s c' t) : term259 x' s c' t.
Proof. exact (h1). Qed.
Lemma lem5277258 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5277266 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5277281 (s : real -> Prop) (b : real) (x : real) : (term130 s b x) = (term130 s b x).
Proof. exact (eq_refl (term130 s b x)). Qed.
Lemma lem5277282 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (fun_ext (fun x : real => @lem5277281 s b x)). Qed.
Lemma lem5277283 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277284 (s : real -> Prop) (b : real) : (term132 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5277283) (@lem5277282 s b)). Qed.
Lemma lem5277285 (s : real -> Prop) (b : real) (h1 : term34 s b) : term132 s b.
Proof. exact (EQ_MP (@lem5277284 s b) (@lem5276046 s b h1)). Qed.
Lemma lem5277300 (t : real -> Prop) (c : real) (x : real) : (term130 t c x) = (term130 t c x).
Proof. exact (eq_refl (term130 t c x)). Qed.
Lemma lem5277301 (t : real -> Prop) (c : real) : (term131 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5277300 t c x)). Qed.
Lemma lem5277302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277303 (t : real -> Prop) (c : real) : (term132 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5277302) (@lem5277301 t c)). Qed.
Lemma lem5277304 (t : real -> Prop) (c : real) (h1 : term34 t c) : term132 t c.
Proof. exact (EQ_MP (@lem5277303 t c) (@lem5276109 t c h1)). Qed.
Lemma lem5277329 (y : real) (x : real) (z : real) : (term270 y x z) = (term270 y x z).
Proof. exact (eq_refl (term270 y x z)). Qed.
Lemma lem5277330 (y : real) (x : real) : (term272 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5277329 y x z)). Qed.
Lemma lem5277331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277332 (y : real) (x : real) : (term273 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5277331) (@lem5277330 y x)). Qed.
Lemma lem5277333 (x : real) : (term274 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5277332 y x)). Qed.
Lemma lem5277334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277335 (x : real) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5277334) (@lem5277333 x)). Qed.
Lemma lem5277336 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem5277335 x)). Qed.
Lemma lem5277337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277338 : term277 = term277.
Proof. exact (MK_COMB (@lem5277337) (@lem5277336)). Qed.
Lemma lem5277339 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5277338) (@lem5276718 h1)). Qed.
Lemma lem5277372 (x : type1021) (b : real) (s : real -> Prop) : (term448 x b s) = (term448 x b s).
Proof. exact (eq_refl (term448 x b s)). Qed.
Lemma lem5277373 (x : type1021) (s : real -> Prop) : (term449 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5277372 x b s)). Qed.
Lemma lem5277374 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277375 (x : type1021) (s : real -> Prop) : (term450 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5277374) (@lem5277373 x s)). Qed.
Lemma lem5277392 (s : real -> Prop) (x : real) : (term293 s x) = (term293 s x).
Proof. exact (eq_refl (term293 s x)). Qed.
Lemma lem5277393 (s : real -> Prop) : (term295 s) = (term295 s).
Proof. exact (fun_ext (fun x : real => @lem5277392 s x)). Qed.
Lemma lem5277394 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277395 (s : real -> Prop) : (term296 s) = (term296 s).
Proof. exact (MK_COMB (@lem5277394) (@lem5277393 s)). Qed.
Lemma lem5277396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277397 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (MK_COMB (@lem5277396) (@lem5277395 s)). Qed.
Lemma lem5277398 (x : type1021) (s : real -> Prop) : (term451 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5277397 s) (@lem5277375 x s)). Qed.
Lemma lem5277421 (x : type1021) (s : real -> Prop) (b : real) : (term452 x s b) = (term452 x s b).
Proof. exact (eq_refl (term452 x s b)). Qed.
Lemma lem5277422 (x : type1021) (s : real -> Prop) : (term453 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5277421 x s b)). Qed.
Lemma lem5277423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277424 (x : type1021) (s : real -> Prop) : (term454 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5277423) (@lem5277422 x s)). Qed.
Lemma lem5277431 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277432 (x : type1021) (s : real -> Prop) : (term455 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5277431 s) (@lem5277424 x s)). Qed.
Lemma lem5277433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277434 (x : type1021) (s : real -> Prop) : (term456 x s) = (term456 x s).
Proof. exact (MK_COMB (@lem5277433) (@lem5277432 x s)). Qed.
Lemma lem5277435 (x : type1021) (s : real -> Prop) : (term440 x s) = (term440 x s).
Proof. exact (MK_COMB (@lem5277434 x s) (@lem5277398 x s)). Qed.
Lemma lem5277436 (x : type1021) : (term442 x) = (term442 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5277435 x s)). Qed.
Lemma lem5277437 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5277438 (x : type1021) : (term444 x) = (term444 x).
Proof. exact (MK_COMB (@lem5277437) (@lem5277436 x)). Qed.
Lemma lem5277439 (x : type1021) (h1 : term444 x) : term444 x.
Proof. exact (EQ_MP (@lem5277438 x) (@lem5277248 x h1)). Qed.
Lemma lem5277492 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) : (term228 x' s c' t) = (term228 x' s c' t).
Proof. exact (eq_refl (term228 x' s c' t)). Qed.
Lemma lem5277513 (s : real -> Prop) (c' : real) (t : real -> Prop) : (term152 s c' t) = (term152 s c' t).
Proof. exact (eq_refl (term152 s c' t)). Qed.
Lemma lem5277528 (t : real -> Prop) (c' : real) (x : real) : (term130 t c' x) = (term130 t c' x).
Proof. exact (eq_refl (term130 t c' x)). Qed.
Lemma lem5277529 (t : real -> Prop) (c' : real) : (term131 t c') = (term131 t c').
Proof. exact (fun_ext (fun x : real => @lem5277528 t c' x)). Qed.
Lemma lem5277530 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277531 (t : real -> Prop) (c' : real) : (term132 t c') = (term132 t c').
Proof. exact (MK_COMB (@lem5277530) (@lem5277529 t c')). Qed.
Lemma lem5277546 (s : real -> Prop) (c' : real) (x : real) : (term130 s c' x) = (term130 s c' x).
Proof. exact (eq_refl (term130 s c' x)). Qed.
Lemma lem5277547 (s : real -> Prop) (c' : real) : (term131 s c') = (term131 s c').
Proof. exact (fun_ext (fun x : real => @lem5277546 s c' x)). Qed.
Lemma lem5277548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277549 (s : real -> Prop) (c' : real) : (term132 s c') = (term132 s c').
Proof. exact (MK_COMB (@lem5277548) (@lem5277547 s c')). Qed.
Lemma lem5277550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277551 (s : real -> Prop) (c' : real) : (term149 s c') = (term149 s c').
Proof. exact (MK_COMB (@lem5277550) (@lem5277549 s c')). Qed.
Lemma lem5277552 (s : real -> Prop) (t : real -> Prop) (c' : real) : (term150 s t c') = (term150 s t c').
Proof. exact (MK_COMB (@lem5277551 s c') (@lem5277531 t c')). Qed.
Lemma lem5277553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277554 (s : real -> Prop) (t : real -> Prop) (c' : real) : (term158 s t c') = (term158 s t c').
Proof. exact (MK_COMB (@lem5277553) (@lem5277552 s t c')). Qed.
Lemma lem5277555 (s : real -> Prop) (c' : real) (t : real -> Prop) : (term160 s c' t) = (term160 s c' t).
Proof. exact (MK_COMB (@lem5277554 s t c') (@lem5277513 s c' t)). Qed.
Lemma lem5277556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277557 (s : real -> Prop) (c' : real) (t : real -> Prop) : (term162 s c' t) = (term162 s c' t).
Proof. exact (MK_COMB (@lem5277556) (@lem5277555 s c' t)). Qed.
Lemma lem5277558 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) : (term259 x' s c' t) = (term259 x' s c' t).
Proof. exact (MK_COMB (@lem5277557 s c' t) (@lem5277492 x' s c' t)). Qed.
Lemma lem5277559 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term259 x' s c' t) : term259 x' s c' t.
Proof. exact (EQ_MP (@lem5277558 x' s c' t) (@lem5277250 x' s c' t h1)). Qed.
Lemma lem5277560 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term160 s c' t.
Proof. exact (h1). Qed.
Lemma lem5277561 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term228 x' s c' t.
Proof. exact (h1). Qed.
Lemma lem5277562 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term152 s c' t.
Proof. exact (proj2 (@lem5277560 s c' t h1)). Qed.
Lemma lem5277563 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term150 s t c'.
Proof. exact (proj1 (@lem5277560 s c' t h1)). Qed.
Lemma lem5277564 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term132 t c'.
Proof. exact (proj2 (@lem5277563 s c' t h1)). Qed.
Lemma lem5277565 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term132 s c'.
Proof. exact (proj1 (@lem5277563 s c' t h1)). Qed.
Lemma lem5277568 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term62 s c' t.
Proof. exact (proj2 (@lem5277561 x' s c' t h1)). Qed.
Lemma lem5277569 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term207 s t c' x'.
Proof. exact (proj1 (@lem5277561 x' s c' t h1)). Qed.
Lemma lem5277572 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : term134 s c' x'.
Proof. exact (h1). Qed.
Lemma lem5277573 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : term134 t c' x'.
Proof. exact (h1). Qed.
Lemma lem5277581 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5277638 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5277639 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5277638 real P Q). Qed.
Lemma lem5277640 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5277639 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5277641 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5277642 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5277641 x s b)). Qed.
Lemma lem5277643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277644 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5277643) (@lem5277642 x s)). Qed.
Lemma lem5277645 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277646 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5277645 s) (@lem5277644 x s)). Qed.
Lemma lem5277647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277648 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5277647) (@lem5277646 x s)). Qed.
Lemma lem5277649 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5277650 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277651 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5277650 s) (@lem5277649 x s b)). Qed.
Lemma lem5277652 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5277651 x s b)). Qed.
Lemma lem5277653 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277654 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5277653) (@lem5277652 x s)). Qed.
Lemma lem5277655 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5277648 x s) (@lem5277654 x s)). Qed.
Lemma lem5277656 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5277655 x s) (@lem5277640 x s)). Qed.
Lemma lem5277657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277658 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5277657) (@lem5277656 x s)). Qed.
Lemma lem5277660 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5277661 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5277660 real P Q). Qed.
Lemma lem5277662 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5277661 (term295 s) (term449 x s)). Qed.
Lemma lem5277663 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5277664 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5277663 s b)). Qed.
Lemma lem5277665 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277666 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5277665) (@lem5277664 s)). Qed.
Lemma lem5277667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277668 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5277667) (@lem5277666 s)). Qed.
Lemma lem5277669 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5277670 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5277669 x b s)). Qed.
Lemma lem5277671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277672 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5277671) (@lem5277670 x s)). Qed.
Lemma lem5277673 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5277668 s) (@lem5277672 x s)). Qed.
Lemma lem5277674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277675 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5277674) (@lem5277673 x s)). Qed.
Lemma lem5277676 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5277677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277678 (s : real -> Prop) (b : real) : (term489 s b) = (term490 s b).
Proof. exact (MK_COMB (@lem5277677) (@lem5277676 s b)). Qed.
Lemma lem5277679 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5277680 (x : type1021) (b : real) (s : real -> Prop) : (term491 x s b) = (term492 x b s).
Proof. exact (MK_COMB (@lem5277678 s b) (@lem5277679 x b s)). Qed.
Lemma lem5277681 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5277680 x b s)). Qed.
Lemma lem5277682 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277683 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5277682) (@lem5277681 x s)). Qed.
Lemma lem5277684 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5277675 x s) (@lem5277683 x s)). Qed.
Lemma lem5277685 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5277684 x s) (@lem5277662 x s)). Qed.
Lemma lem5277688 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5277689 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5277690 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5277691 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5277690 x s) (@lem5277689 x s)). Qed.
Lemma lem5277692 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5277693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277694 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5277693) (@lem5277692 x s)). Qed.
Lemma lem5277695 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5277696 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5277694 x s) (@lem5277695 x s)). Qed.
Lemma lem5277697 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5277691 x s) (@lem5277696 x s)). Qed.
Lemma lem5277698 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5277697 x s) (@lem5277688 x s)). Qed.
Lemma lem5277699 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5277698 x s) (@lem5277685 x s)). Qed.
Lemma lem5277700 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5277658 x s) (@lem5277699 x s)). Qed.
Lemma lem5277702 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5277703 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5277702 real P Q). Qed.
Lemma lem5277704 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5277703 (term471 x s) (term495 x s)). Qed.
Lemma lem5277705 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5277706 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5277705 x s b)). Qed.
Lemma lem5277707 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277708 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5277707) (@lem5277706 x s)). Qed.
Lemma lem5277709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277710 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5277709) (@lem5277708 x s)). Qed.
Lemma lem5277711 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5277712 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5277710 x s) (@lem5277711 x s)). Qed.
Lemma lem5277713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277714 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5277713) (@lem5277712 x s)). Qed.
Lemma lem5277715 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5277716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277717 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5277716) (@lem5277715 x s b)). Qed.
Lemma lem5277718 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5277719 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5277717 x s b) (@lem5277718 x s)). Qed.
Lemma lem5277720 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5277719 b x s)). Qed.
Lemma lem5277721 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277722 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5277721) (@lem5277720 x s)). Qed.
Lemma lem5277723 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5277714 x s) (@lem5277722 x s)). Qed.
Lemma lem5277724 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5277723 x s) (@lem5277704 x s)). Qed.
Lemma lem5277726 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5277727 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5277726 real P Q). Qed.
Lemma lem5277728 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5277727 (term469 x s b) (term494 x s)). Qed.
Lemma lem5277729 (x : type1021) (b : real) (s : real -> Prop) : (term521 x s b) = (term492 x b s).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5277730 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5277729 x b s)). Qed.
Lemma lem5277731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277732 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5277731) (@lem5277730 x s)). Qed.
Lemma lem5277733 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5277734 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5277733 x s b) (@lem5277732 x s)). Qed.
Lemma lem5277735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277736 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5277735) (@lem5277734 b x s)). Qed.
Lemma lem5277737 (x : type1021) (b' : real) (s : real -> Prop) : (term521 x s b') = (term492 x b' s).
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5277738 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5277739 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term526 b x s b') = (term527 b x b' s).
Proof. exact (MK_COMB (@lem5277738 x s b) (@lem5277737 x b' s)). Qed.
Lemma lem5277740 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5277739 b x b' s)). Qed.
Lemma lem5277741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277742 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5277741) (@lem5277740 b x s)). Qed.
Lemma lem5277743 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5277736 b x s) (@lem5277742 b x s)). Qed.
Lemma lem5277744 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5277743 b x s) (@lem5277728 b x s)). Qed.
Lemma lem5277745 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5277744 b x s)). Qed.
Lemma lem5277746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277747 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5277746) (@lem5277745 x s)). Qed.
Lemma lem5277748 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5277724 x s) (@lem5277747 x s)). Qed.
Lemma lem5277749 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5277700 x s) (@lem5277748 x s)). Qed.
Lemma lem5277750 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5277749 x s)). Qed.
Lemma lem5277751 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5277752 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5277751) (@lem5277750 x)). Qed.
Lemma lem5277769 (x : type1021) (b' : real) (s : real -> Prop) : (term448 x b' s) = (term535 x b' s).
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 b' s)). Qed.
Lemma lem5277778 (s : real -> Prop) (b' : real) : (term490 s b') = (term490 s b').
Proof. exact (eq_refl (term490 s b')). Qed.
Lemma lem5277779 (x : type1021) (b' : real) (s : real -> Prop) : (term492 x b' s) = (term538 x b' s).
Proof. exact (MK_COMB (@lem5277778 s b') (@lem5277769 x b' s)). Qed.
Lemma lem5277796 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5277797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277798 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5277797) (@lem5277796 x s b)). Qed.
Lemma lem5277799 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term541 b x b' s).
Proof. exact (MK_COMB (@lem5277798 x s b) (@lem5277779 x b' s)). Qed.
Lemma lem5277800 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term542 b x b' s).
Proof. exact (@lem19490 (term293 s b') (term539 x s b) (term535 x b' s)). Qed.
Lemma lem5277801 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term544 b x b' s).
Proof. exact (@lem19490 (term545 x b' s) (term539 x s b) (term546 x b' s)). Qed.
Lemma lem5277808 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term547 b x b' s) = (term548 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x b' s)). Qed.
Lemma lem5277815 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term551 b x b' s) = (term552 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x b' s)). Qed.
Lemma lem5277816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277817 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term553 b x b' s) = (term554 b x b' s).
Proof. exact (MK_COMB (@lem5277816) (@lem5277815 b x b' s)). Qed.
Lemma lem5277818 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term544 b x b' s) = (term555 b x b' s).
Proof. exact (MK_COMB (@lem5277817 b x b' s) (@lem5277808 b x b' s)). Qed.
Lemma lem5277819 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term555 b x b' s).
Proof. exact (TRANS (@lem5277801 b x b' s) (@lem5277818 b x b' s)). Qed.
Lemma lem5277826 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term556 x b s b') = (term557 x b s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 s b')). Qed.
Lemma lem5277827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277828 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term558 x b s b') = (term559 x b s b').
Proof. exact (MK_COMB (@lem5277827) (@lem5277826 x b s b')). Qed.
Lemma lem5277829 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term542 b x b' s) = (term560 b x b' s).
Proof. exact (MK_COMB (@lem5277828 x b s b') (@lem5277819 b x b' s)). Qed.
Lemma lem5277830 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5277800 b x b' s) (@lem5277829 b x b' s)). Qed.
Lemma lem5277831 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5277799 b x b' s) (@lem5277830 b x b' s)). Qed.
Lemma lem5277832 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5277831 b x b' s)). Qed.
Lemma lem5277833 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277834 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5277833) (@lem5277832 b x s)). Qed.
Lemma lem5277835 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5277834 b x s)). Qed.
Lemma lem5277836 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277837 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5277836) (@lem5277835 x s)). Qed.
Lemma lem5277838 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5277837 x s)). Qed.
Lemma lem5277839 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5277840 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5277839) (@lem5277838 x)). Qed.
Lemma lem5277841 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5277752 x) (@lem5277840 x)). Qed.
Lemma lem5277842 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5277841 x) (@lem5277439 x h1)). Qed.
Lemma lem5277850 (s : real -> Prop) (c' : real) (x : real) : (term130 s c' x) = (term130 s c' x).
Proof. exact (eq_refl (term130 s c' x)). Qed.
Lemma lem5277851 (s : real -> Prop) (c' : real) : (term131 s c') = (term131 s c').
Proof. exact (fun_ext (fun x : real => @lem5277850 s c' x)). Qed.
Lemma lem5277852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277854 (s : real -> Prop) (c' : real) : (term132 s c') = (term132 s c').
Proof. exact (MK_COMB (@lem5277852) (@lem5277851 s c')). Qed.
Lemma lem5277855 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term132 s c'.
Proof. exact (EQ_MP (@lem5277854 s c') (@lem5277565 s c' t h1)). Qed.
Lemma lem5277872 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (h1). Qed.
Lemma lem5277880 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5277933 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5277934 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5277933 real P Q). Qed.
Lemma lem5277935 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5277934 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5277936 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5277937 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5277936 x s b)). Qed.
Lemma lem5277938 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277939 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5277938) (@lem5277937 x s)). Qed.
Lemma lem5277940 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277941 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5277940 s) (@lem5277939 x s)). Qed.
Lemma lem5277942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277943 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5277942) (@lem5277941 x s)). Qed.
Lemma lem5277944 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5277945 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5277946 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5277945 s) (@lem5277944 x s b)). Qed.
Lemma lem5277947 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5277946 x s b)). Qed.
Lemma lem5277948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277949 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5277948) (@lem5277947 x s)). Qed.
Lemma lem5277950 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5277943 x s) (@lem5277949 x s)). Qed.
Lemma lem5277951 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5277950 x s) (@lem5277935 x s)). Qed.
Lemma lem5277952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5277953 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5277952) (@lem5277951 x s)). Qed.
Lemma lem5277955 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5277956 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5277955 real P Q). Qed.
Lemma lem5277957 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5277956 (term295 s) (term449 x s)). Qed.
Lemma lem5277958 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5277959 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5277958 s b)). Qed.
Lemma lem5277960 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277961 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5277960) (@lem5277959 s)). Qed.
Lemma lem5277962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277963 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5277962) (@lem5277961 s)). Qed.
Lemma lem5277964 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5277965 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5277964 x b s)). Qed.
Lemma lem5277966 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277967 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5277966) (@lem5277965 x s)). Qed.
Lemma lem5277968 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5277963 s) (@lem5277967 x s)). Qed.
Lemma lem5277969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277970 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5277969) (@lem5277968 x s)). Qed.
Lemma lem5277971 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5277972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5277973 (s : real -> Prop) (b : real) : (term489 s b) = (term490 s b).
Proof. exact (MK_COMB (@lem5277972) (@lem5277971 s b)). Qed.
Lemma lem5277974 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5277975 (x : type1021) (b : real) (s : real -> Prop) : (term491 x s b) = (term492 x b s).
Proof. exact (MK_COMB (@lem5277973 s b) (@lem5277974 x b s)). Qed.
Lemma lem5277976 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5277975 x b s)). Qed.
Lemma lem5277977 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5277978 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5277977) (@lem5277976 x s)). Qed.
Lemma lem5277979 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5277970 x s) (@lem5277978 x s)). Qed.
Lemma lem5277980 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5277979 x s) (@lem5277957 x s)). Qed.
Lemma lem5277983 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5277984 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5277985 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5277986 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5277985 x s) (@lem5277984 x s)). Qed.
Lemma lem5277987 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5277988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5277989 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5277988) (@lem5277987 x s)). Qed.
Lemma lem5277990 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5277991 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5277989 x s) (@lem5277990 x s)). Qed.
Lemma lem5277992 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5277986 x s) (@lem5277991 x s)). Qed.
Lemma lem5277993 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5277992 x s) (@lem5277983 x s)). Qed.
Lemma lem5277994 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5277993 x s) (@lem5277980 x s)). Qed.
Lemma lem5277995 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5277953 x s) (@lem5277994 x s)). Qed.
Lemma lem5277997 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5277998 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5277997 real P Q). Qed.
Lemma lem5277999 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5277998 (term471 x s) (term495 x s)). Qed.
Lemma lem5278000 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5278001 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5278000 x s b)). Qed.
Lemma lem5278002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278003 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5278002) (@lem5278001 x s)). Qed.
Lemma lem5278004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278005 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5278004) (@lem5278003 x s)). Qed.
Lemma lem5278006 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5278007 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5278005 x s) (@lem5278006 x s)). Qed.
Lemma lem5278008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278009 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5278008) (@lem5278007 x s)). Qed.
Lemma lem5278010 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5278011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278012 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5278011) (@lem5278010 x s b)). Qed.
Lemma lem5278013 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5278014 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5278012 x s b) (@lem5278013 x s)). Qed.
Lemma lem5278015 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5278014 b x s)). Qed.
Lemma lem5278016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278017 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5278016) (@lem5278015 x s)). Qed.
Lemma lem5278018 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5278009 x s) (@lem5278017 x s)). Qed.
Lemma lem5278019 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5278018 x s) (@lem5277999 x s)). Qed.
Lemma lem5278021 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5278022 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5278021 real P Q). Qed.
Lemma lem5278023 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5278022 (term469 x s b) (term494 x s)). Qed.
Lemma lem5278024 (x : type1021) (b : real) (s : real -> Prop) : (term521 x s b) = (term492 x b s).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5278025 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5278024 x b s)). Qed.
Lemma lem5278026 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278027 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5278026) (@lem5278025 x s)). Qed.
Lemma lem5278028 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5278029 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5278028 x s b) (@lem5278027 x s)). Qed.
Lemma lem5278030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278031 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5278030) (@lem5278029 b x s)). Qed.
Lemma lem5278032 (x : type1021) (b' : real) (s : real -> Prop) : (term521 x s b') = (term492 x b' s).
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5278033 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5278034 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term526 b x s b') = (term527 b x b' s).
Proof. exact (MK_COMB (@lem5278033 x s b) (@lem5278032 x b' s)). Qed.
Lemma lem5278035 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5278034 b x b' s)). Qed.
Lemma lem5278036 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278037 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5278036) (@lem5278035 b x s)). Qed.
Lemma lem5278038 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5278031 b x s) (@lem5278037 b x s)). Qed.
Lemma lem5278039 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5278038 b x s) (@lem5278023 b x s)). Qed.
Lemma lem5278040 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5278039 b x s)). Qed.
Lemma lem5278041 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278042 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5278041) (@lem5278040 x s)). Qed.
Lemma lem5278043 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5278019 x s) (@lem5278042 x s)). Qed.
Lemma lem5278044 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5277995 x s) (@lem5278043 x s)). Qed.
Lemma lem5278045 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5278044 x s)). Qed.
Lemma lem5278046 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5278047 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5278046) (@lem5278045 x)). Qed.
Lemma lem5278064 (x : type1021) (b' : real) (s : real -> Prop) : (term448 x b' s) = (term535 x b' s).
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 b' s)). Qed.
Lemma lem5278073 (s : real -> Prop) (b' : real) : (term490 s b') = (term490 s b').
Proof. exact (eq_refl (term490 s b')). Qed.
Lemma lem5278074 (x : type1021) (b' : real) (s : real -> Prop) : (term492 x b' s) = (term538 x b' s).
Proof. exact (MK_COMB (@lem5278073 s b') (@lem5278064 x b' s)). Qed.
Lemma lem5278091 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5278092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278093 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5278092) (@lem5278091 x s b)). Qed.
Lemma lem5278094 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term541 b x b' s).
Proof. exact (MK_COMB (@lem5278093 x s b) (@lem5278074 x b' s)). Qed.
Lemma lem5278095 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term542 b x b' s).
Proof. exact (@lem19490 (term293 s b') (term539 x s b) (term535 x b' s)). Qed.
Lemma lem5278096 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term544 b x b' s).
Proof. exact (@lem19490 (term545 x b' s) (term539 x s b) (term546 x b' s)). Qed.
Lemma lem5278103 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term547 b x b' s) = (term548 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x b' s)). Qed.
Lemma lem5278110 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term551 b x b' s) = (term552 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x b' s)). Qed.
Lemma lem5278111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278112 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term553 b x b' s) = (term554 b x b' s).
Proof. exact (MK_COMB (@lem5278111) (@lem5278110 b x b' s)). Qed.
Lemma lem5278113 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term544 b x b' s) = (term555 b x b' s).
Proof. exact (MK_COMB (@lem5278112 b x b' s) (@lem5278103 b x b' s)). Qed.
Lemma lem5278114 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term555 b x b' s).
Proof. exact (TRANS (@lem5278096 b x b' s) (@lem5278113 b x b' s)). Qed.
Lemma lem5278121 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term556 x b s b') = (term557 x b s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 s b')). Qed.
Lemma lem5278122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278123 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term558 x b s b') = (term559 x b s b').
Proof. exact (MK_COMB (@lem5278122) (@lem5278121 x b s b')). Qed.
Lemma lem5278124 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term542 b x b' s) = (term560 b x b' s).
Proof. exact (MK_COMB (@lem5278123 x b s b') (@lem5278114 b x b' s)). Qed.
Lemma lem5278125 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5278095 b x b' s) (@lem5278124 b x b' s)). Qed.
Lemma lem5278126 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5278094 b x b' s) (@lem5278125 b x b' s)). Qed.
Lemma lem5278127 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5278126 b x b' s)). Qed.
Lemma lem5278128 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278129 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5278128) (@lem5278127 b x s)). Qed.
Lemma lem5278130 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5278129 b x s)). Qed.
Lemma lem5278131 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278132 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5278131) (@lem5278130 x s)). Qed.
Lemma lem5278133 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5278132 x s)). Qed.
Lemma lem5278134 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5278135 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5278134) (@lem5278133 x)). Qed.
Lemma lem5278136 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5278047 x) (@lem5278135 x)). Qed.
Lemma lem5278137 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5278136 x) (@lem5277439 x h1)). Qed.
Lemma lem5278158 (t : real -> Prop) (c' : real) (x : real) : (term130 t c' x) = (term130 t c' x).
Proof. exact (eq_refl (term130 t c' x)). Qed.
Lemma lem5278159 (t : real -> Prop) (c' : real) : (term131 t c') = (term131 t c').
Proof. exact (fun_ext (fun x : real => @lem5278158 t c' x)). Qed.
Lemma lem5278160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278162 (t : real -> Prop) (c' : real) : (term132 t c') = (term132 t c').
Proof. exact (MK_COMB (@lem5278160) (@lem5278159 t c')). Qed.
Lemma lem5278163 (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term132 t c'.
Proof. exact (EQ_MP (@lem5278162 t c') (@lem5277564 s c' t h1)). Qed.
Lemma lem5278167 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (h1). Qed.
Lemma lem5278171 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5278183 (s : real -> Prop) (b : real) (x : real) : (term130 s b x) = (term130 s b x).
Proof. exact (eq_refl (term130 s b x)). Qed.
Lemma lem5278184 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (fun_ext (fun x : real => @lem5278183 s b x)). Qed.
Lemma lem5278185 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278187 (s : real -> Prop) (b : real) : (term132 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5278185) (@lem5278184 s b)). Qed.
Lemma lem5278188 (s : real -> Prop) (b : real) (h1 : term34 s b) : term132 s b.
Proof. exact (EQ_MP (@lem5278187 s b) (@lem5277285 s b h1)). Qed.
Lemma lem5278215 (y : real) (x : real) (z : real) : (term270 y x z) = (term270 y x z).
Proof. exact (eq_refl (term270 y x z)). Qed.
Lemma lem5278216 (y : real) (x : real) : (term272 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5278215 y x z)). Qed.
Lemma lem5278217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278218 (y : real) (x : real) : (term273 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5278217) (@lem5278216 y x)). Qed.
Lemma lem5278219 (x : real) : (term274 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5278218 y x)). Qed.
Lemma lem5278220 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278221 (x : real) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5278220) (@lem5278219 x)). Qed.
Lemma lem5278222 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem5278221 x)). Qed.
Lemma lem5278223 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278225 : term277 = term277.
Proof. exact (MK_COMB (@lem5278223) (@lem5278222)). Qed.
Lemma lem5278226 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5278225) (@lem5277339 h1)). Qed.
Lemma lem5278228 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5278229 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5278228 real P Q). Qed.
Lemma lem5278230 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5278229 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5278231 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5278232 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5278231 x s b)). Qed.
Lemma lem5278233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278234 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5278233) (@lem5278232 x s)). Qed.
Lemma lem5278235 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5278236 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5278235 s) (@lem5278234 x s)). Qed.
Lemma lem5278237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278238 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5278237) (@lem5278236 x s)). Qed.
Lemma lem5278239 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5278240 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5278241 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5278240 s) (@lem5278239 x s b)). Qed.
Lemma lem5278242 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5278241 x s b)). Qed.
Lemma lem5278243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278244 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5278243) (@lem5278242 x s)). Qed.
Lemma lem5278245 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5278238 x s) (@lem5278244 x s)). Qed.
Lemma lem5278246 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5278245 x s) (@lem5278230 x s)). Qed.
Lemma lem5278247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278248 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5278247) (@lem5278246 x s)). Qed.
Lemma lem5278250 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5278251 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5278250 real P Q). Qed.
Lemma lem5278252 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5278251 (term295 s) (term449 x s)). Qed.
Lemma lem5278253 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5278254 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5278253 s b)). Qed.
Lemma lem5278255 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278256 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5278255) (@lem5278254 s)). Qed.
Lemma lem5278257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278258 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5278257) (@lem5278256 s)). Qed.
Lemma lem5278259 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5278260 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5278259 x b s)). Qed.
Lemma lem5278261 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278262 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5278261) (@lem5278260 x s)). Qed.
Lemma lem5278263 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5278258 s) (@lem5278262 x s)). Qed.
Lemma lem5278264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278265 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5278264) (@lem5278263 x s)). Qed.
Lemma lem5278266 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5278267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278268 (s : real -> Prop) (b : real) : (term489 s b) = (term490 s b).
Proof. exact (MK_COMB (@lem5278267) (@lem5278266 s b)). Qed.
Lemma lem5278269 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5278270 (x : type1021) (b : real) (s : real -> Prop) : (term491 x s b) = (term492 x b s).
Proof. exact (MK_COMB (@lem5278268 s b) (@lem5278269 x b s)). Qed.
Lemma lem5278271 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5278270 x b s)). Qed.
Lemma lem5278272 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278273 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5278272) (@lem5278271 x s)). Qed.
Lemma lem5278274 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5278265 x s) (@lem5278273 x s)). Qed.
Lemma lem5278275 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5278274 x s) (@lem5278252 x s)). Qed.
Lemma lem5278278 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5278279 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5278280 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5278281 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5278280 x s) (@lem5278279 x s)). Qed.
Lemma lem5278282 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5278283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278284 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5278283) (@lem5278282 x s)). Qed.
Lemma lem5278285 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5278286 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5278284 x s) (@lem5278285 x s)). Qed.
Lemma lem5278287 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5278281 x s) (@lem5278286 x s)). Qed.
Lemma lem5278288 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5278287 x s) (@lem5278278 x s)). Qed.
Lemma lem5278289 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5278288 x s) (@lem5278275 x s)). Qed.
Lemma lem5278290 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5278248 x s) (@lem5278289 x s)). Qed.
Lemma lem5278292 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5278293 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5278292 real P Q). Qed.
Lemma lem5278294 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5278293 (term471 x s) (term495 x s)). Qed.
Lemma lem5278295 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5278296 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5278295 x s b)). Qed.
Lemma lem5278297 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278298 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5278297) (@lem5278296 x s)). Qed.
Lemma lem5278299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278300 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5278299) (@lem5278298 x s)). Qed.
Lemma lem5278301 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5278302 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5278300 x s) (@lem5278301 x s)). Qed.
Lemma lem5278303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278304 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5278303) (@lem5278302 x s)). Qed.
Lemma lem5278305 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5278306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278307 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5278306) (@lem5278305 x s b)). Qed.
Lemma lem5278308 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5278309 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5278307 x s b) (@lem5278308 x s)). Qed.
Lemma lem5278310 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5278309 b x s)). Qed.
Lemma lem5278311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278312 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5278311) (@lem5278310 x s)). Qed.
Lemma lem5278313 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5278304 x s) (@lem5278312 x s)). Qed.
Lemma lem5278314 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5278313 x s) (@lem5278294 x s)). Qed.
Lemma lem5278316 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5278317 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5278316 real P Q). Qed.
Lemma lem5278318 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5278317 (term469 x s b) (term494 x s)). Qed.
Lemma lem5278319 (x : type1021) (b : real) (s : real -> Prop) : (term521 x s b) = (term492 x b s).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5278320 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5278319 x b s)). Qed.
Lemma lem5278321 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278322 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5278321) (@lem5278320 x s)). Qed.
Lemma lem5278323 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5278324 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5278323 x s b) (@lem5278322 x s)). Qed.
Lemma lem5278325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278326 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5278325) (@lem5278324 b x s)). Qed.
Lemma lem5278327 (x : type1021) (b' : real) (s : real -> Prop) : (term521 x s b') = (term492 x b' s).
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5278328 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5278329 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term526 b x s b') = (term527 b x b' s).
Proof. exact (MK_COMB (@lem5278328 x s b) (@lem5278327 x b' s)). Qed.
Lemma lem5278330 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5278329 b x b' s)). Qed.
Lemma lem5278331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278332 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5278331) (@lem5278330 b x s)). Qed.
Lemma lem5278333 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5278326 b x s) (@lem5278332 b x s)). Qed.
Lemma lem5278334 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5278333 b x s) (@lem5278318 b x s)). Qed.
Lemma lem5278335 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5278334 b x s)). Qed.
Lemma lem5278336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278337 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5278336) (@lem5278335 x s)). Qed.
Lemma lem5278338 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5278314 x s) (@lem5278337 x s)). Qed.
Lemma lem5278339 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5278290 x s) (@lem5278338 x s)). Qed.
Lemma lem5278340 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5278339 x s)). Qed.
Lemma lem5278341 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5278342 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5278341) (@lem5278340 x)). Qed.
Lemma lem5278359 (x : type1021) (b' : real) (s : real -> Prop) : (term448 x b' s) = (term535 x b' s).
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 b' s)). Qed.
Lemma lem5278368 (s : real -> Prop) (b' : real) : (term490 s b') = (term490 s b').
Proof. exact (eq_refl (term490 s b')). Qed.
Lemma lem5278369 (x : type1021) (b' : real) (s : real -> Prop) : (term492 x b' s) = (term538 x b' s).
Proof. exact (MK_COMB (@lem5278368 s b') (@lem5278359 x b' s)). Qed.
Lemma lem5278386 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5278387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278388 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5278387) (@lem5278386 x s b)). Qed.
Lemma lem5278389 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term541 b x b' s).
Proof. exact (MK_COMB (@lem5278388 x s b) (@lem5278369 x b' s)). Qed.
Lemma lem5278390 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term542 b x b' s).
Proof. exact (@lem19490 (term293 s b') (term539 x s b) (term535 x b' s)). Qed.
Lemma lem5278391 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term544 b x b' s).
Proof. exact (@lem19490 (term545 x b' s) (term539 x s b) (term546 x b' s)). Qed.
Lemma lem5278398 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term547 b x b' s) = (term548 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x b' s)). Qed.
Lemma lem5278405 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term551 b x b' s) = (term552 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x b' s)). Qed.
Lemma lem5278406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278407 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term553 b x b' s) = (term554 b x b' s).
Proof. exact (MK_COMB (@lem5278406) (@lem5278405 b x b' s)). Qed.
Lemma lem5278408 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term544 b x b' s) = (term555 b x b' s).
Proof. exact (MK_COMB (@lem5278407 b x b' s) (@lem5278398 b x b' s)). Qed.
Lemma lem5278409 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term555 b x b' s).
Proof. exact (TRANS (@lem5278391 b x b' s) (@lem5278408 b x b' s)). Qed.
Lemma lem5278416 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term556 x b s b') = (term557 x b s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 s b')). Qed.
Lemma lem5278417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278418 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term558 x b s b') = (term559 x b s b').
Proof. exact (MK_COMB (@lem5278417) (@lem5278416 x b s b')). Qed.
Lemma lem5278419 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term542 b x b' s) = (term560 b x b' s).
Proof. exact (MK_COMB (@lem5278418 x b s b') (@lem5278409 b x b' s)). Qed.
Lemma lem5278420 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5278390 b x b' s) (@lem5278419 b x b' s)). Qed.
Lemma lem5278421 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5278389 b x b' s) (@lem5278420 b x b' s)). Qed.
Lemma lem5278422 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5278421 b x b' s)). Qed.
Lemma lem5278423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278424 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5278423) (@lem5278422 b x s)). Qed.
Lemma lem5278425 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5278424 b x s)). Qed.
Lemma lem5278426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278427 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5278426) (@lem5278425 x s)). Qed.
Lemma lem5278428 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5278427 x s)). Qed.
Lemma lem5278429 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5278430 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5278429) (@lem5278428 x)). Qed.
Lemma lem5278431 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5278342 x) (@lem5278430 x)). Qed.
Lemma lem5278432 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5278431 x) (@lem5277439 x h1)). Qed.
Lemma lem5278456 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5278477 (t : real -> Prop) (c : real) (x : real) : (term130 t c x) = (term130 t c x).
Proof. exact (eq_refl (term130 t c x)). Qed.
Lemma lem5278478 (t : real -> Prop) (c : real) : (term131 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5278477 t c x)). Qed.
Lemma lem5278479 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278481 (t : real -> Prop) (c : real) : (term132 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5278479) (@lem5278478 t c)). Qed.
Lemma lem5278482 (t : real -> Prop) (c : real) (h1 : term34 t c) : term132 t c.
Proof. exact (EQ_MP (@lem5278481 t c) (@lem5277304 t c h1)). Qed.
Lemma lem5278496 (y : real) (x : real) (z : real) : (term270 y x z) = (term270 y x z).
Proof. exact (eq_refl (term270 y x z)). Qed.
Lemma lem5278497 (y : real) (x : real) : (term272 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5278496 y x z)). Qed.
Lemma lem5278498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278499 (y : real) (x : real) : (term273 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5278498) (@lem5278497 y x)). Qed.
Lemma lem5278500 (x : real) : (term274 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5278499 y x)). Qed.
Lemma lem5278501 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278502 (x : real) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5278501) (@lem5278500 x)). Qed.
Lemma lem5278503 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem5278502 x)). Qed.
Lemma lem5278504 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278506 : term277 = term277.
Proof. exact (MK_COMB (@lem5278504) (@lem5278503)). Qed.
Lemma lem5278507 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5278506) (@lem5277339 h1)). Qed.
Lemma lem5278509 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5278510 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5278509 real P Q). Qed.
Lemma lem5278511 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5278510 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5278512 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5278513 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5278512 x s b)). Qed.
Lemma lem5278514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278515 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5278514) (@lem5278513 x s)). Qed.
Lemma lem5278516 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5278517 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5278516 s) (@lem5278515 x s)). Qed.
Lemma lem5278518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278519 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5278518) (@lem5278517 x s)). Qed.
Lemma lem5278520 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5278521 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5278522 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5278521 s) (@lem5278520 x s b)). Qed.
Lemma lem5278523 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5278522 x s b)). Qed.
Lemma lem5278524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278525 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5278524) (@lem5278523 x s)). Qed.
Lemma lem5278526 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5278519 x s) (@lem5278525 x s)). Qed.
Lemma lem5278527 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5278526 x s) (@lem5278511 x s)). Qed.
Lemma lem5278528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278529 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5278528) (@lem5278527 x s)). Qed.
Lemma lem5278531 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5278532 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5278531 real P Q). Qed.
Lemma lem5278533 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5278532 (term295 s) (term449 x s)). Qed.
Lemma lem5278534 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5278535 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5278534 s b)). Qed.
Lemma lem5278536 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278537 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5278536) (@lem5278535 s)). Qed.
Lemma lem5278538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278539 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5278538) (@lem5278537 s)). Qed.
Lemma lem5278540 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5278541 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5278540 x b s)). Qed.
Lemma lem5278542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278543 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5278542) (@lem5278541 x s)). Qed.
Lemma lem5278544 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5278539 s) (@lem5278543 x s)). Qed.
Lemma lem5278545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278546 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5278545) (@lem5278544 x s)). Qed.
Lemma lem5278547 (s : real -> Prop) (b : real) : (term480 s b) = (term293 s b).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5278548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278549 (s : real -> Prop) (b : real) : (term489 s b) = (term490 s b).
Proof. exact (MK_COMB (@lem5278548) (@lem5278547 s b)). Qed.
Lemma lem5278550 (x : type1021) (b : real) (s : real -> Prop) : (term484 x s b) = (term448 x b s).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5278551 (x : type1021) (b : real) (s : real -> Prop) : (term491 x s b) = (term492 x b s).
Proof. exact (MK_COMB (@lem5278549 s b) (@lem5278550 x b s)). Qed.
Lemma lem5278552 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5278551 x b s)). Qed.
Lemma lem5278553 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278554 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5278553) (@lem5278552 x s)). Qed.
Lemma lem5278555 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5278546 x s) (@lem5278554 x s)). Qed.
Lemma lem5278556 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5278555 x s) (@lem5278533 x s)). Qed.
Lemma lem5278559 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5278560 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5278561 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5278562 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5278561 x s) (@lem5278560 x s)). Qed.
Lemma lem5278563 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5278564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278565 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5278564) (@lem5278563 x s)). Qed.
Lemma lem5278566 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5278567 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5278565 x s) (@lem5278566 x s)). Qed.
Lemma lem5278568 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5278562 x s) (@lem5278567 x s)). Qed.
Lemma lem5278569 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5278568 x s) (@lem5278559 x s)). Qed.
Lemma lem5278570 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5278569 x s) (@lem5278556 x s)). Qed.
Lemma lem5278571 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5278529 x s) (@lem5278570 x s)). Qed.
Lemma lem5278573 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5278574 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5278573 real P Q). Qed.
Lemma lem5278575 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5278574 (term471 x s) (term495 x s)). Qed.
Lemma lem5278576 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5278577 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5278576 x s b)). Qed.
Lemma lem5278578 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278579 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5278578) (@lem5278577 x s)). Qed.
Lemma lem5278580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278581 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5278580) (@lem5278579 x s)). Qed.
Lemma lem5278582 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5278583 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5278581 x s) (@lem5278582 x s)). Qed.
Lemma lem5278584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278585 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5278584) (@lem5278583 x s)). Qed.
Lemma lem5278586 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5278587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278588 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5278587) (@lem5278586 x s b)). Qed.
Lemma lem5278589 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5278590 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5278588 x s b) (@lem5278589 x s)). Qed.
Lemma lem5278591 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5278590 b x s)). Qed.
Lemma lem5278592 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278593 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5278592) (@lem5278591 x s)). Qed.
Lemma lem5278594 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5278585 x s) (@lem5278593 x s)). Qed.
Lemma lem5278595 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5278594 x s) (@lem5278575 x s)). Qed.
Lemma lem5278597 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5278598 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5278597 real P Q). Qed.
Lemma lem5278599 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5278598 (term469 x s b) (term494 x s)). Qed.
Lemma lem5278600 (x : type1021) (b : real) (s : real -> Prop) : (term521 x s b) = (term492 x b s).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5278601 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5278600 x b s)). Qed.
Lemma lem5278602 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278603 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5278602) (@lem5278601 x s)). Qed.
Lemma lem5278604 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5278605 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5278604 x s b) (@lem5278603 x s)). Qed.
Lemma lem5278606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5278607 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5278606) (@lem5278605 b x s)). Qed.
Lemma lem5278608 (x : type1021) (b' : real) (s : real -> Prop) : (term521 x s b') = (term492 x b' s).
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5278609 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5278610 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term526 b x s b') = (term527 b x b' s).
Proof. exact (MK_COMB (@lem5278609 x s b) (@lem5278608 x b' s)). Qed.
Lemma lem5278611 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5278610 b x b' s)). Qed.
Lemma lem5278612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278613 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5278612) (@lem5278611 b x s)). Qed.
Lemma lem5278614 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5278607 b x s) (@lem5278613 b x s)). Qed.
Lemma lem5278615 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5278614 b x s) (@lem5278599 b x s)). Qed.
Lemma lem5278616 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5278615 b x s)). Qed.
Lemma lem5278617 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278618 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5278617) (@lem5278616 x s)). Qed.
Lemma lem5278619 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5278595 x s) (@lem5278618 x s)). Qed.
Lemma lem5278620 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5278571 x s) (@lem5278619 x s)). Qed.
Lemma lem5278621 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5278620 x s)). Qed.
Lemma lem5278622 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5278623 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5278622) (@lem5278621 x)). Qed.
Lemma lem5278640 (x : type1021) (b' : real) (s : real -> Prop) : (term448 x b' s) = (term535 x b' s).
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 b' s)). Qed.
Lemma lem5278649 (s : real -> Prop) (b' : real) : (term490 s b') = (term490 s b').
Proof. exact (eq_refl (term490 s b')). Qed.
Lemma lem5278650 (x : type1021) (b' : real) (s : real -> Prop) : (term492 x b' s) = (term538 x b' s).
Proof. exact (MK_COMB (@lem5278649 s b') (@lem5278640 x b' s)). Qed.
Lemma lem5278667 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5278668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5278669 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5278668) (@lem5278667 x s b)). Qed.
Lemma lem5278670 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term541 b x b' s).
Proof. exact (MK_COMB (@lem5278669 x s b) (@lem5278650 x b' s)). Qed.
Lemma lem5278671 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term542 b x b' s).
Proof. exact (@lem19490 (term293 s b') (term539 x s b) (term535 x b' s)). Qed.
Lemma lem5278672 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term544 b x b' s).
Proof. exact (@lem19490 (term545 x b' s) (term539 x s b) (term546 x b' s)). Qed.
Lemma lem5278679 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term547 b x b' s) = (term548 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x b' s)). Qed.
Lemma lem5278686 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term551 b x b' s) = (term552 b x b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x b' s)). Qed.
Lemma lem5278687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278688 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term553 b x b' s) = (term554 b x b' s).
Proof. exact (MK_COMB (@lem5278687) (@lem5278686 b x b' s)). Qed.
Lemma lem5278689 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term544 b x b' s) = (term555 b x b' s).
Proof. exact (MK_COMB (@lem5278688 b x b' s) (@lem5278679 b x b' s)). Qed.
Lemma lem5278690 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term543 b x b' s) = (term555 b x b' s).
Proof. exact (TRANS (@lem5278672 b x b' s) (@lem5278689 b x b' s)). Qed.
Lemma lem5278697 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term556 x b s b') = (term557 x b s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 s b')). Qed.
Lemma lem5278698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5278699 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term558 x b s b') = (term559 x b s b').
Proof. exact (MK_COMB (@lem5278698) (@lem5278697 x b s b')). Qed.
Lemma lem5278700 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term542 b x b' s) = (term560 b x b' s).
Proof. exact (MK_COMB (@lem5278699 x b s b') (@lem5278690 b x b' s)). Qed.
Lemma lem5278701 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5278671 b x b' s) (@lem5278700 b x b' s)). Qed.
Lemma lem5278702 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term527 b x b' s) = (term560 b x b' s).
Proof. exact (TRANS (@lem5278670 b x b' s) (@lem5278701 b x b' s)). Qed.
Lemma lem5278703 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5278702 b x b' s)). Qed.
Lemma lem5278704 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278705 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5278704) (@lem5278703 b x s)). Qed.
Lemma lem5278706 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5278705 b x s)). Qed.
Lemma lem5278707 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5278708 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5278707) (@lem5278706 x s)). Qed.
Lemma lem5278709 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5278708 x s)). Qed.
Lemma lem5278710 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5278711 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5278710) (@lem5278709 x)). Qed.
Lemma lem5278712 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5278623 x) (@lem5278711 x)). Qed.
Lemma lem5278713 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5278712 x) (@lem5277439 x h1)). Qed.
Lemma lem5278745 (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _69064.
Proof. exact (@lem5277842 x h1 _69064). Qed.
Lemma lem5278746 (x : type1021) (_69064 : real -> Prop) : (term568 x _69064) = (term564 x _69064).
Proof. exact (eq_refl (term568 x _69064)). Qed.
Lemma lem5278747 (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _69064.
Proof. exact (EQ_MP (@lem5278746 x _69064) (@lem5278745 _69064 x h1)). Qed.
Lemma lem5278748 (_69064 : real -> Prop) (_69065 : real) (x : type1021) (h1 : term444 x) : term569 x _69064 _69065.
Proof. exact (@lem5278747 _69064 x h1 _69065). Qed.
Lemma lem5278749 (_69065 : real) (x : type1021) (_69064 : real -> Prop) : (term569 x _69064 _69065) = (term562 _69065 x _69064).
Proof. exact (eq_refl (term569 x _69064 _69065)). Qed.
Lemma lem5278750 (_69065 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _69065 x _69064.
Proof. exact (EQ_MP (@lem5278749 _69065 x _69064) (@lem5278748 _69064 _69065 x h1)). Qed.
Lemma lem5278751 (_69065 : real) (_69064 : real -> Prop) (_69066 : real) (x : type1021) (h1 : term444 x) : term570 _69065 x _69064 _69066.
Proof. exact (@lem5278750 _69065 _69064 x h1 _69066). Qed.
Lemma lem5278752 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term570 _69065 x _69064 _69066) = (term560 _69065 x _69066 _69064).
Proof. exact (eq_refl (term570 _69065 x _69064 _69066)). Qed.
Lemma lem5278753 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term560 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5278752 _69065 x _69066 _69064) (@lem5278751 _69065 _69064 _69066 x h1)). Qed.
Lemma lem5278754 (_69067 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term571 s c' _69067.
Proof. exact (@lem5277855 s c' t h1 _69067). Qed.
Lemma lem5278755 (s : real -> Prop) (c' : real) (_69067 : real) : (term571 s c' _69067) = (term130 s c' _69067).
Proof. exact (eq_refl (term571 s c' _69067)). Qed.
Lemma lem5278775 (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _69074.
Proof. exact (@lem5278137 x h1 _69074). Qed.
Lemma lem5278776 (x : type1021) (_69074 : real -> Prop) : (term568 x _69074) = (term564 x _69074).
Proof. exact (eq_refl (term568 x _69074)). Qed.
Lemma lem5278777 (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _69074.
Proof. exact (EQ_MP (@lem5278776 x _69074) (@lem5278775 _69074 x h1)). Qed.
Lemma lem5278778 (_69074 : real -> Prop) (_69075 : real) (x : type1021) (h1 : term444 x) : term569 x _69074 _69075.
Proof. exact (@lem5278777 _69074 x h1 _69075). Qed.
Lemma lem5278779 (_69075 : real) (x : type1021) (_69074 : real -> Prop) : (term569 x _69074 _69075) = (term562 _69075 x _69074).
Proof. exact (eq_refl (term569 x _69074 _69075)). Qed.
Lemma lem5278780 (_69075 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _69075 x _69074.
Proof. exact (EQ_MP (@lem5278779 _69075 x _69074) (@lem5278778 _69074 _69075 x h1)). Qed.
Lemma lem5278781 (_69075 : real) (_69074 : real -> Prop) (_69076 : real) (x : type1021) (h1 : term444 x) : term570 _69075 x _69074 _69076.
Proof. exact (@lem5278780 _69075 _69074 x h1 _69076). Qed.
Lemma lem5278782 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term570 _69075 x _69074 _69076) = (term560 _69075 x _69076 _69074).
Proof. exact (eq_refl (term570 _69075 x _69074 _69076)). Qed.
Lemma lem5278783 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term560 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5278782 _69075 x _69076 _69074) (@lem5278781 _69075 _69074 _69076 x h1)). Qed.
Lemma lem5278787 (_69078 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term571 t c' _69078.
Proof. exact (@lem5278163 s c' t h1 _69078). Qed.
Lemma lem5278788 (t : real -> Prop) (c' : real) (_69078 : real) : (term571 t c' _69078) = (term130 t c' _69078).
Proof. exact (eq_refl (term571 t c' _69078)). Qed.
Lemma lem5278790 (_69079 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term571 s b _69079.
Proof. exact (@lem5278188 s b h1 _69079). Qed.
Lemma lem5278791 (s : real -> Prop) (b : real) (_69079 : real) : (term571 s b _69079) = (term130 s b _69079).
Proof. exact (eq_refl (term571 s b _69079)). Qed.
Lemma lem5278796 (_69081 : real) (h1 : term129) : term572 _69081.
Proof. exact (@lem5278226 h1 _69081). Qed.
Lemma lem5278797 (_69081 : real) : (term572 _69081) = (term275 _69081).
Proof. exact (eq_refl (term572 _69081)). Qed.
Lemma lem5278798 (_69081 : real) (h1 : term129) : term275 _69081.
Proof. exact (EQ_MP (@lem5278797 _69081) (@lem5278796 _69081 h1)). Qed.
Lemma lem5278799 (_69081 : real) (_69082 : real) (h1 : term129) : term573 _69081 _69082.
Proof. exact (@lem5278798 _69081 h1 _69082). Qed.
Lemma lem5278800 (_69082 : real) (_69081 : real) : (term573 _69081 _69082) = (term273 _69082 _69081).
Proof. exact (eq_refl (term573 _69081 _69082)). Qed.
Lemma lem5278801 (_69082 : real) (_69081 : real) (h1 : term129) : term273 _69082 _69081.
Proof. exact (EQ_MP (@lem5278800 _69082 _69081) (@lem5278799 _69081 _69082 h1)). Qed.
Lemma lem5278802 (_69082 : real) (_69081 : real) (_69083 : real) (h1 : term129) : term574 _69082 _69081 _69083.
Proof. exact (@lem5278801 _69082 _69081 h1 _69083). Qed.
Lemma lem5278803 (_69082 : real) (_69081 : real) (_69083 : real) : (term574 _69082 _69081 _69083) = (term270 _69082 _69081 _69083).
Proof. exact (eq_refl (term574 _69082 _69081 _69083)). Qed.
Lemma lem5278804 (_69082 : real) (_69081 : real) (_69083 : real) (h1 : term129) : term270 _69082 _69081 _69083.
Proof. exact (EQ_MP (@lem5278803 _69082 _69081 _69083) (@lem5278802 _69082 _69081 _69083 h1)). Qed.
Lemma lem5278805 (_69084 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _69084.
Proof. exact (@lem5278432 x h1 _69084). Qed.
Lemma lem5278806 (x : type1021) (_69084 : real -> Prop) : (term568 x _69084) = (term564 x _69084).
Proof. exact (eq_refl (term568 x _69084)). Qed.
Lemma lem5278807 (_69084 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _69084.
Proof. exact (EQ_MP (@lem5278806 x _69084) (@lem5278805 _69084 x h1)). Qed.
Lemma lem5278808 (_69084 : real -> Prop) (_69085 : real) (x : type1021) (h1 : term444 x) : term569 x _69084 _69085.
Proof. exact (@lem5278807 _69084 x h1 _69085). Qed.
Lemma lem5278809 (_69085 : real) (x : type1021) (_69084 : real -> Prop) : (term569 x _69084 _69085) = (term562 _69085 x _69084).
Proof. exact (eq_refl (term569 x _69084 _69085)). Qed.
Lemma lem5278810 (_69085 : real) (_69084 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _69085 x _69084.
Proof. exact (EQ_MP (@lem5278809 _69085 x _69084) (@lem5278808 _69084 _69085 x h1)). Qed.
Lemma lem5278811 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term570 _69085 x _69084 _69086.
Proof. exact (@lem5278810 _69085 _69084 x h1 _69086). Qed.
Lemma lem5278812 (_69085 : real) (x : type1021) (_69086 : real) (_69084 : real -> Prop) : (term570 _69085 x _69084 _69086) = (term560 _69085 x _69086 _69084).
Proof. exact (eq_refl (term570 _69085 x _69084 _69086)). Qed.
Lemma lem5278813 (_69085 : real) (_69086 : real) (_69084 : real -> Prop) (x : type1021) (h1 : term444 x) : term560 _69085 x _69086 _69084.
Proof. exact (EQ_MP (@lem5278812 _69085 x _69086 _69084) (@lem5278811 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5278817 (_69088 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term571 t c _69088.
Proof. exact (@lem5278482 t c h1 _69088). Qed.
Lemma lem5278818 (t : real -> Prop) (c : real) (_69088 : real) : (term571 t c _69088) = (term130 t c _69088).
Proof. exact (eq_refl (term571 t c _69088)). Qed.
Lemma lem5278820 (_69089 : real) (h1 : term129) : term572 _69089.
Proof. exact (@lem5278507 h1 _69089). Qed.
Lemma lem5278821 (_69089 : real) : (term572 _69089) = (term275 _69089).
Proof. exact (eq_refl (term572 _69089)). Qed.
Lemma lem5278822 (_69089 : real) (h1 : term129) : term275 _69089.
Proof. exact (EQ_MP (@lem5278821 _69089) (@lem5278820 _69089 h1)). Qed.
Lemma lem5278823 (_69089 : real) (_69090 : real) (h1 : term129) : term573 _69089 _69090.
Proof. exact (@lem5278822 _69089 h1 _69090). Qed.
Lemma lem5278824 (_69090 : real) (_69089 : real) : (term573 _69089 _69090) = (term273 _69090 _69089).
Proof. exact (eq_refl (term573 _69089 _69090)). Qed.
Lemma lem5278825 (_69090 : real) (_69089 : real) (h1 : term129) : term273 _69090 _69089.
Proof. exact (EQ_MP (@lem5278824 _69090 _69089) (@lem5278823 _69089 _69090 h1)). Qed.
Lemma lem5278826 (_69090 : real) (_69089 : real) (_69091 : real) (h1 : term129) : term574 _69090 _69089 _69091.
Proof. exact (@lem5278825 _69090 _69089 h1 _69091). Qed.
Lemma lem5278827 (_69090 : real) (_69089 : real) (_69091 : real) : (term574 _69090 _69089 _69091) = (term270 _69090 _69089 _69091).
Proof. exact (eq_refl (term574 _69090 _69089 _69091)). Qed.
Lemma lem5278828 (_69090 : real) (_69089 : real) (_69091 : real) (h1 : term129) : term270 _69090 _69089 _69091.
Proof. exact (EQ_MP (@lem5278827 _69090 _69089 _69091) (@lem5278826 _69090 _69089 _69091 h1)). Qed.
Lemma lem5278829 (_69092 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _69092.
Proof. exact (@lem5278713 x h1 _69092). Qed.
Lemma lem5278830 (x : type1021) (_69092 : real -> Prop) : (term568 x _69092) = (term564 x _69092).
Proof. exact (eq_refl (term568 x _69092)). Qed.
Lemma lem5278831 (_69092 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _69092.
Proof. exact (EQ_MP (@lem5278830 x _69092) (@lem5278829 _69092 x h1)). Qed.
Lemma lem5278832 (_69092 : real -> Prop) (_69093 : real) (x : type1021) (h1 : term444 x) : term569 x _69092 _69093.
Proof. exact (@lem5278831 _69092 x h1 _69093). Qed.
Lemma lem5278833 (_69093 : real) (x : type1021) (_69092 : real -> Prop) : (term569 x _69092 _69093) = (term562 _69093 x _69092).
Proof. exact (eq_refl (term569 x _69092 _69093)). Qed.
Lemma lem5278834 (_69093 : real) (_69092 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _69093 x _69092.
Proof. exact (EQ_MP (@lem5278833 _69093 x _69092) (@lem5278832 _69092 _69093 x h1)). Qed.
Lemma lem5278835 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term570 _69093 x _69092 _69094.
Proof. exact (@lem5278834 _69093 _69092 x h1 _69094). Qed.
Lemma lem5278836 (_69093 : real) (x : type1021) (_69094 : real) (_69092 : real -> Prop) : (term570 _69093 x _69092 _69094) = (term560 _69093 x _69094 _69092).
Proof. exact (eq_refl (term570 _69093 x _69092 _69094)). Qed.
Lemma lem5278837 (_69093 : real) (_69094 : real) (_69092 : real -> Prop) (x : type1021) (h1 : term444 x) : term560 _69093 x _69094 _69092.
Proof. exact (EQ_MP (@lem5278836 _69093 x _69094 _69092) (@lem5278835 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5278838 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term555 _69065 x _69066 _69064.
Proof. exact (proj2 (@lem5278753 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278840 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term548 _69065 x _69066 _69064.
Proof. exact (proj2 (@lem5278838 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278841 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term552 _69065 x _69066 _69064.
Proof. exact (proj1 (@lem5278838 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278842 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term575 _69065 x _69066 _69064.
Proof. exact (proj2 (@lem5278840 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278844 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term576 _69065 x _69066 _69064.
Proof. exact (proj2 (@lem5278841 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278845 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term577 _69065 x _69066 _69064.
Proof. exact (proj1 (@lem5278841 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278848 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term555 _69075 x _69076 _69074.
Proof. exact (proj2 (@lem5278783 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5278850 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term548 _69075 x _69076 _69074.
Proof. exact (proj2 (@lem5278848 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5278851 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term552 _69075 x _69076 _69074.
Proof. exact (proj1 (@lem5278848 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5278852 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term575 _69075 x _69076 _69074.
Proof. exact (proj2 (@lem5278850 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5278854 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term576 _69075 x _69076 _69074.
Proof. exact (proj2 (@lem5278851 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5278855 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term577 _69075 x _69076 _69074.
Proof. exact (proj1 (@lem5278851 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5278859 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term557 x _69085 _69084 _69086.
Proof. exact (proj1 (@lem5278813 _69085 _69086 _69084 x h1)). Qed.
Lemma lem5278866 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term578 x _69085 _69084 _69086.
Proof. exact (proj2 (@lem5278859 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5278867 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term579 x _69085 _69084 _69086.
Proof. exact (proj1 (@lem5278859 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5278869 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term557 x _69093 _69092 _69094.
Proof. exact (proj1 (@lem5278837 _69093 _69094 _69092 x h1)). Qed.
Lemma lem5278876 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term578 x _69093 _69092 _69094.
Proof. exact (proj2 (@lem5278869 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5278877 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term579 x _69093 _69092 _69094.
Proof. exact (proj1 (@lem5278869 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5278879 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5278911 (_69067 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term130 s c' _69067.
Proof. exact (EQ_MP (@lem5278755 s c' _69067) (@lem5278754 _69067 s c' t h1)). Qed.
Lemma lem5278919 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (h1). Qed.
Lemma lem5278950 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term575 _69065 x _69066 _69064) = (term580 _69065 x _69066 _69064).
Proof. exact (@lem5275344 (_69064 = (@EMPTY real)) (term537 x _69064 _69065) (term546 x _69066 _69064)). Qed.
Lemma lem5278951 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term580 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5278950 _69065 x _69066 _69064) (@lem5278842 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278966 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term577 _69065 x _69066 _69064) = (term581 _69065 x _69066 _69064).
Proof. exact (@lem5275344 (_69064 = (@EMPTY real)) (term536 x _69065 _69064) (term545 x _69066 _69064)). Qed.
Lemma lem5278967 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term581 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5278966 _69065 x _69066 _69064) (@lem5278845 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5278982 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term576 _69065 x _69066 _69064) = (term582 _69065 x _69066 _69064).
Proof. exact (@lem5275344 (_69064 = (@EMPTY real)) (term537 x _69064 _69065) (term545 x _69066 _69064)). Qed.
Lemma lem5278983 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term582 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5278982 _69065 x _69066 _69064) (@lem5278844 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5279019 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5279055 (_69078 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term130 t c' _69078.
Proof. exact (EQ_MP (@lem5278788 t c' _69078) (@lem5278787 _69078 s c' t h1)). Qed.
Lemma lem5279057 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (h1). Qed.
Lemma lem5279088 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term575 _69075 x _69076 _69074) = (term580 _69075 x _69076 _69074).
Proof. exact (@lem5275344 (_69074 = (@EMPTY real)) (term537 x _69074 _69075) (term546 x _69076 _69074)). Qed.
Lemma lem5279089 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term580 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5279088 _69075 x _69076 _69074) (@lem5278852 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5279104 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term577 _69075 x _69076 _69074) = (term581 _69075 x _69076 _69074).
Proof. exact (@lem5275344 (_69074 = (@EMPTY real)) (term536 x _69075 _69074) (term545 x _69076 _69074)). Qed.
Lemma lem5279105 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term581 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5279104 _69075 x _69076 _69074) (@lem5278855 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5279120 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term576 _69075 x _69076 _69074) = (term582 _69075 x _69076 _69074).
Proof. exact (@lem5275344 (_69074 = (@EMPTY real)) (term537 x _69074 _69075) (term545 x _69076 _69074)). Qed.
Lemma lem5279121 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term582 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5279120 _69075 x _69076 _69074) (@lem5278854 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5279155 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5279163 (_69079 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term130 s b _69079.
Proof. exact (EQ_MP (@lem5278791 s b _69079) (@lem5278790 _69079 s b h1)). Qed.
Lemma lem5279180 (_69082 : real) (_69081 : real) (_69083 : real) : (term270 _69082 _69081 _69083) = (term583 _69082 _69081 _69083).
Proof. exact (@lem5275344 (term584 _69081 _69082) (term584 _69082 _69083) (real_le _69081 _69083)). Qed.
Lemma lem5279181 (_69082 : real) (_69081 : real) (_69083 : real) (h1 : term129) : term583 _69082 _69081 _69083.
Proof. exact (EQ_MP (@lem5279180 _69082 _69081 _69083) (@lem5278804 _69082 _69081 _69083 h1)). Qed.
Lemma lem5279189 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : term584 c' x'.
Proof. exact (proj2 (@lem5277572 s c' x' h1)). Qed.
Lemma lem5279268 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term579 x _69085 _69084 _69086) = (term585 x _69085 _69084 _69086).
Proof. exact (@lem5275344 (_69084 = (@EMPTY real)) (term536 x _69085 _69084) (term293 _69084 _69086)). Qed.
Lemma lem5279269 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term585 x _69085 _69084 _69086.
Proof. exact (EQ_MP (@lem5279268 x _69085 _69084 _69086) (@lem5278867 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5279284 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term578 x _69085 _69084 _69086) = (term586 x _69085 _69084 _69086).
Proof. exact (@lem5275344 (_69084 = (@EMPTY real)) (term537 x _69084 _69085) (term293 _69084 _69086)). Qed.
Lemma lem5279285 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term586 x _69085 _69084 _69086.
Proof. exact (EQ_MP (@lem5279284 x _69085 _69084 _69086) (@lem5278866 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5279289 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5279301 (_69088 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term130 t c _69088.
Proof. exact (EQ_MP (@lem5278818 t c _69088) (@lem5278817 _69088 t c h1)). Qed.
Lemma lem5279312 (_69090 : real) (_69089 : real) (_69091 : real) : (term270 _69090 _69089 _69091) = (term583 _69090 _69089 _69091).
Proof. exact (@lem5275344 (term584 _69089 _69090) (term584 _69090 _69091) (real_le _69089 _69091)). Qed.
Lemma lem5279313 (_69090 : real) (_69089 : real) (_69091 : real) (h1 : term129) : term583 _69090 _69089 _69091.
Proof. exact (EQ_MP (@lem5279312 _69090 _69089 _69091) (@lem5278828 _69090 _69089 _69091 h1)). Qed.
Lemma lem5279321 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : term584 c' x'.
Proof. exact (proj2 (@lem5277573 t c' x' h1)). Qed.
Lemma lem5279400 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term579 x _69093 _69092 _69094) = (term585 x _69093 _69092 _69094).
Proof. exact (@lem5275344 (_69092 = (@EMPTY real)) (term536 x _69093 _69092) (term293 _69092 _69094)). Qed.
Lemma lem5279401 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term585 x _69093 _69092 _69094.
Proof. exact (EQ_MP (@lem5279400 x _69093 _69092 _69094) (@lem5278877 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5279416 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term578 x _69093 _69092 _69094) = (term586 x _69093 _69092 _69094).
Proof. exact (@lem5275344 (_69092 = (@EMPTY real)) (term537 x _69092 _69093) (term293 _69092 _69094)). Qed.
Lemma lem5279417 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term586 x _69093 _69092 _69094.
Proof. exact (EQ_MP (@lem5279416 x _69093 _69092 _69094) (@lem5278876 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5279484 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5279485 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5279484 s h1). Qed.
Lemma lem5279487 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279488 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5279487 (s = (@EMPTY real))). Qed.
Lemma lem5279489 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5279488 s) (@lem5279485 s h1)). Qed.
Lemma lem5279491 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5279492 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5279491 s h1). Qed.
Lemma lem5279494 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279495 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5279494 (s = (@EMPTY real))). Qed.
Lemma lem5279496 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5279495 s) (@lem5279492 s h1)). Qed.
Lemma lem5279499 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (h1). Qed.
Lemma lem5279500 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term590 x c' s.
Proof. exact (fun h0 : term536 x c' s => @lem5279499 x c' s h1). Qed.
Lemma lem5279502 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279503 (x : type1021) (c' : real) (s : real -> Prop) : (term590 x c' s) = (term589 x c' s).
Proof. exact (@lem5279502 (term536 x c' s)). Qed.
Lemma lem5279504 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (EQ_MP (@lem5279503 x c' s) (@lem5279500 x c' s h1)). Qed.
Lemma lem5279507 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (h1). Qed.
Lemma lem5279508 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term591 c' s.
Proof. exact (fun h0 : term108 c' s => @lem5279507 c' s h1). Qed.
Lemma lem5279510 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279511 (c' : real) (s : real -> Prop) : (term591 c' s) = (term567 c' s).
Proof. exact (@lem5279510 (term108 c' s)). Qed.
Lemma lem5279512 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (EQ_MP (@lem5279511 c' s) (@lem5279508 c' s h1)). Qed.
Lemma lem5279545 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5279546 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term592 x _69065 _69066 _69064) = (term593 x _69065 _69066 _69064).
Proof. exact (@lem5279545 (_69064 = (@EMPTY real)) (term536 x _69066 _69064) (term594 x _69065 _69066 _69064)). Qed.
Lemma lem5279562 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5279563 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term595 x _69065 _69066 _69064) = (term596 _69065 x _69066 _69064).
Proof. exact (@lem5279562 (term536 x _69065 _69064) (term536 x _69066 _69064) (term108 _69066 _69064)). Qed.
Lemma lem5279579 (_69064 : real -> Prop) : (term289 _69064) = (term289 _69064).
Proof. exact (eq_refl (term289 _69064)). Qed.
Lemma lem5279580 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term593 x _69065 _69066 _69064) = (term581 _69065 x _69066 _69064).
Proof. exact (MK_COMB (@lem5279579 _69064) (@lem5279563 _69065 x _69066 _69064)). Qed.
Lemma lem5279591 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term592 x _69065 _69066 _69064) = (term581 _69065 x _69066 _69064).
Proof. exact (TRANS (@lem5279546 x _69065 _69066 _69064) (@lem5279580 _69065 x _69066 _69064)). Qed.
Lemma lem5279592 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term597 _69065 x _69066 _69064) = (term597 _69065 x _69066 _69064).
Proof. exact (eq_refl (term597 _69065 x _69066 _69064)). Qed.
Lemma lem5279593 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : ((term581 _69065 x _69066 _69064) = (term592 x _69065 _69066 _69064)) = ((term581 _69065 x _69066 _69064) = (term581 _69065 x _69066 _69064)).
Proof. exact (MK_COMB (@lem5279592 _69065 x _69066 _69064) (@lem5279591 _69065 x _69066 _69064)). Qed.
Lemma lem5279595 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5279596 (x : Prop) : (x = x) = True.
Proof. exact (@lem5279595 Prop x). Qed.
Lemma lem5279597 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : ((term581 _69065 x _69066 _69064) = (term581 _69065 x _69066 _69064)) = True.
Proof. exact (@lem5279596 (term581 _69065 x _69066 _69064)). Qed.
Lemma lem5279598 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : ((term581 _69065 x _69066 _69064) = (term592 x _69065 _69066 _69064)) = True.
Proof. exact (TRANS (@lem5279593 _69065 x _69066 _69064) (@lem5279597 _69065 x _69066 _69064)). Qed.
Lemma lem5279599 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : True = ((term581 _69065 x _69066 _69064) = (term592 x _69065 _69066 _69064)).
Proof. exact (SYM (@lem5279598 x _69065 _69066 _69064)). Qed.
Lemma lem5279600 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term581 _69065 x _69066 _69064) = (term592 x _69065 _69066 _69064).
Proof. exact (EQ_MP (@lem5279599 x _69065 _69066 _69064) (@lem0)). Qed.
Lemma lem5279601 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term592 x _69065 _69066 _69064.
Proof. exact (EQ_MP (@lem5279600 x _69065 _69066 _69064) (@lem5278967 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5279603 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5279604 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term592 x _69065 _69066 _69064) = (term599 _69065 x _69066 _69064).
Proof. exact (@lem5279603 (term600 x _69065 _69066 _69064) (term536 x _69066 _69064)). Qed.
Lemma lem5279606 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5279607 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term603 x _69065 _69066 _69064) = (term604 x _69065 _69066 _69064).
Proof. exact (@lem5279606 (_69064 = (@EMPTY real)) (term594 x _69065 _69066 _69064)). Qed.
Lemma lem5279609 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5279610 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term605 x _69065 _69066 _69064) = (term606 x _69065 _69066 _69064).
Proof. exact (@lem5279609 (term536 x _69065 _69064) (term108 _69066 _69064)). Qed.
Lemma lem5279611 (_69064 : real -> Prop) : (term118 _69064) = (term118 _69064).
Proof. exact (eq_refl (term118 _69064)). Qed.
Lemma lem5279612 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term604 x _69065 _69066 _69064) = (term607 x _69065 _69066 _69064).
Proof. exact (MK_COMB (@lem5279611 _69064) (@lem5279610 x _69065 _69066 _69064)). Qed.
Lemma lem5279613 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term603 x _69065 _69066 _69064) = (term607 x _69065 _69066 _69064).
Proof. exact (TRANS (@lem5279607 x _69065 _69066 _69064) (@lem5279612 x _69065 _69066 _69064)). Qed.
Lemma lem5279614 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5279615 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term608 x _69065 _69066 _69064) = (term609 x _69065 _69066 _69064).
Proof. exact (MK_COMB (@lem5279614) (@lem5279613 x _69065 _69066 _69064)). Qed.
Lemma lem5279616 (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term536 x _69066 _69064) = (term536 x _69066 _69064).
Proof. exact (eq_refl (term536 x _69066 _69064)). Qed.
Lemma lem5279617 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term599 _69065 x _69066 _69064) = (term610 _69065 x _69066 _69064).
Proof. exact (MK_COMB (@lem5279615 x _69065 _69066 _69064) (@lem5279616 x _69066 _69064)). Qed.
Lemma lem5279618 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term592 x _69065 _69066 _69064) = (term610 _69065 x _69066 _69064).
Proof. exact (TRANS (@lem5279604 _69065 x _69066 _69064) (@lem5279617 _69065 x _69066 _69064)). Qed.
Lemma lem5279620 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) (h2 : term567 c' s) : term611 x c' s.
Proof. exact (conj (@lem5279504 x c' s h1) (@lem5279512 c' s h2)). Qed.
Lemma lem5279621 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term31 s) (h2 : term589 x c' s) (h3 : term567 c' s) : term612 x c' s.
Proof. exact (conj (@lem5279496 s h1) (@lem5279620 x c' s h2 h3)). Qed.
Lemma lem5279623 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5279618 _69065 x _69066 _69064) (@lem5279601 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5279624 (c' : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' s.
Proof. exact (@lem5279623 c' c' s x h1). Qed.
Lemma lem5279627 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term589 x c' s) (h4 : term567 c' s) : term536 x c' s.
Proof. exact (@lem5279624 c' s x h1 (@lem5279621 x c' s h2 h3 h4)). Qed.
Lemma lem5279628 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) : term614 x c' s.
Proof. exact (fun h0 : term589 x c' s => @lem5279627 x c' s h1 h2 h0 h3). Qed.
Lemma lem5279630 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5279631 (x : type1021) (c' : real) (s : real -> Prop) : (term614 x c' s) = (term536 x c' s).
Proof. exact (@lem5279630 (term536 x c' s)). Qed.
Lemma lem5279632 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) : term536 x c' s.
Proof. exact (EQ_MP (@lem5279631 x c' s) (@lem5279628 x c' s h1 h2 h3)). Qed.
Lemma lem5279638 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5279639 (c' : real) (_69067 : real) (s : real -> Prop) : (term130 s c' _69067) = (term616 c' _69067 s).
Proof. exact (@lem5279638 (real_le c' _69067) (term617 _69067 s)). Qed.
Lemma lem5279645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5279646 (c' : real) (_69067 : real) (s : real -> Prop) : (term618 s c' _69067) = (term619 c' _69067 s).
Proof. exact (MK_COMB (@lem5279645) (@lem5279639 c' _69067 s)). Qed.
Lemma lem5279652 (c' : real) (_69067 : real) (s : real -> Prop) : (term616 c' _69067 s) = (term616 c' _69067 s).
Proof. exact (eq_refl (term616 c' _69067 s)). Qed.
Lemma lem5279653 (c' : real) (_69067 : real) (s : real -> Prop) : ((term130 s c' _69067) = (term616 c' _69067 s)) = ((term616 c' _69067 s) = (term616 c' _69067 s)).
Proof. exact (MK_COMB (@lem5279646 c' _69067 s) (@lem5279652 c' _69067 s)). Qed.
Lemma lem5279655 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5279656 (x : Prop) : (x = x) = True.
Proof. exact (@lem5279655 Prop x). Qed.
Lemma lem5279657 (c' : real) (_69067 : real) (s : real -> Prop) : ((term616 c' _69067 s) = (term616 c' _69067 s)) = True.
Proof. exact (@lem5279656 (term616 c' _69067 s)). Qed.
Lemma lem5279658 (c' : real) (_69067 : real) (s : real -> Prop) : ((term130 s c' _69067) = (term616 c' _69067 s)) = True.
Proof. exact (TRANS (@lem5279653 c' _69067 s) (@lem5279657 c' _69067 s)). Qed.
Lemma lem5279659 (c' : real) (_69067 : real) (s : real -> Prop) : True = ((term130 s c' _69067) = (term616 c' _69067 s)).
Proof. exact (SYM (@lem5279658 c' _69067 s)). Qed.
Lemma lem5279660 (c' : real) (_69067 : real) (s : real -> Prop) : (term130 s c' _69067) = (term616 c' _69067 s).
Proof. exact (EQ_MP (@lem5279659 c' _69067 s) (@lem0)). Qed.
Lemma lem5279661 (_69067 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term616 c' _69067 s.
Proof. exact (EQ_MP (@lem5279660 c' _69067 s) (@lem5278911 _69067 s c' t h1)). Qed.
Lemma lem5279663 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5279664 (s : real -> Prop) (c' : real) (_69067 : real) : (term616 c' _69067 s) = (term620 s c' _69067).
Proof. exact (@lem5279663 (term617 _69067 s) (real_le c' _69067)). Qed.
Lemma lem5279666 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5279667 (_69067 : real) (s : real -> Prop) : (term622 _69067 s) = (@IN real _69067 s).
Proof. exact (@lem5279666 (@IN real _69067 s)). Qed.
Lemma lem5279668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5279669 (_69067 : real) (s : real -> Prop) : (term623 _69067 s) = (term51 _69067 s).
Proof. exact (MK_COMB (@lem5279668) (@lem5279667 _69067 s)). Qed.
Lemma lem5279670 (c' : real) (_69067 : real) : (real_le c' _69067) = (real_le c' _69067).
Proof. exact (eq_refl (real_le c' _69067)). Qed.
Lemma lem5279671 (s : real -> Prop) (c' : real) (_69067 : real) : (term620 s c' _69067) = (term53 s c' _69067).
Proof. exact (MK_COMB (@lem5279669 _69067 s) (@lem5279670 c' _69067)). Qed.
Lemma lem5279672 (s : real -> Prop) (c' : real) (_69067 : real) : (term616 c' _69067 s) = (term53 s c' _69067).
Proof. exact (TRANS (@lem5279664 s c' _69067) (@lem5279671 s c' _69067)). Qed.
Lemma lem5279675 (_69067 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term53 s c' _69067.
Proof. exact (EQ_MP (@lem5279672 s c' _69067) (@lem5279661 _69067 s c' t h1)). Qed.
Lemma lem5279676 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term624 x s c'.
Proof. exact (@lem5279675 (x s c') s c' t h1). Qed.
Lemma lem5279679 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term625 x s c'.
Proof. exact (@lem5279676 x s c' t h4 (@lem5279632 x c' s h1 h2 h3)). Qed.
Lemma lem5279680 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term626 x s c'.
Proof. exact (fun h0 : term537 x s c' => @lem5279679 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5279682 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5279683 (x : type1021) (s : real -> Prop) (c' : real) : (term626 x s c') = (term625 x s c').
Proof. exact (@lem5279682 (term625 x s c')). Qed.
Lemma lem5279684 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term625 x s c'.
Proof. exact (EQ_MP (@lem5279683 x s c') (@lem5279680 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5279686 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5279687 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5279686 s h1). Qed.
Lemma lem5279689 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279690 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5279689 (s = (@EMPTY real))). Qed.
Lemma lem5279691 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5279690 s) (@lem5279687 s h1)). Qed.
Lemma lem5279693 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5279694 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5279693 s h1). Qed.
Lemma lem5279696 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279697 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5279696 (s = (@EMPTY real))). Qed.
Lemma lem5279698 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5279697 s) (@lem5279694 s h1)). Qed.
Lemma lem5279701 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (h1). Qed.
Lemma lem5279702 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term590 x c' s.
Proof. exact (fun h0 : term536 x c' s => @lem5279701 x c' s h1). Qed.
Lemma lem5279704 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279705 (x : type1021) (c' : real) (s : real -> Prop) : (term590 x c' s) = (term589 x c' s).
Proof. exact (@lem5279704 (term536 x c' s)). Qed.
Lemma lem5279706 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (EQ_MP (@lem5279705 x c' s) (@lem5279702 x c' s h1)). Qed.
Lemma lem5279709 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (h1). Qed.
Lemma lem5279710 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term591 c' s.
Proof. exact (fun h0 : term108 c' s => @lem5279709 c' s h1). Qed.
Lemma lem5279712 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279713 (c' : real) (s : real -> Prop) : (term591 c' s) = (term567 c' s).
Proof. exact (@lem5279712 (term108 c' s)). Qed.
Lemma lem5279714 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (EQ_MP (@lem5279713 c' s) (@lem5279710 c' s h1)). Qed.
Lemma lem5279715 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) (h2 : term567 c' s) : term611 x c' s.
Proof. exact (conj (@lem5279706 x c' s h1) (@lem5279714 c' s h2)). Qed.
Lemma lem5279716 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term31 s) (h2 : term589 x c' s) (h3 : term567 c' s) : term612 x c' s.
Proof. exact (conj (@lem5279698 s h1) (@lem5279715 x c' s h2 h3)). Qed.
Lemma lem5279718 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5279618 _69065 x _69066 _69064) (@lem5279601 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5279719 (c' : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' s.
Proof. exact (@lem5279718 c' c' s x h1). Qed.
Lemma lem5279722 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term589 x c' s) (h4 : term567 c' s) : term536 x c' s.
Proof. exact (@lem5279719 c' s x h1 (@lem5279716 x c' s h2 h3 h4)). Qed.
Lemma lem5279723 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) : term614 x c' s.
Proof. exact (fun h0 : term589 x c' s => @lem5279722 x c' s h1 h2 h0 h3). Qed.
Lemma lem5279725 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5279726 (x : type1021) (c' : real) (s : real -> Prop) : (term614 x c' s) = (term536 x c' s).
Proof. exact (@lem5279725 (term536 x c' s)). Qed.
Lemma lem5279727 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) : term536 x c' s.
Proof. exact (EQ_MP (@lem5279726 x c' s) (@lem5279723 x c' s h1 h2 h3)). Qed.
Lemma lem5279729 (_69067 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term53 s c' _69067.
Proof. exact (EQ_MP (@lem5279672 s c' _69067) (@lem5279661 _69067 s c' t h1)). Qed.
Lemma lem5279730 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term624 x s c'.
Proof. exact (@lem5279729 (x s c') s c' t h1). Qed.
Lemma lem5279733 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term625 x s c'.
Proof. exact (@lem5279730 x s c' t h4 (@lem5279727 x c' s h1 h2 h3)). Qed.
Lemma lem5279734 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term626 x s c'.
Proof. exact (fun h0 : term537 x s c' => @lem5279733 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5279736 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5279737 (x : type1021) (s : real -> Prop) (c' : real) : (term626 x s c') = (term625 x s c').
Proof. exact (@lem5279736 (term625 x s c')). Qed.
Lemma lem5279738 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term625 x s c'.
Proof. exact (EQ_MP (@lem5279737 x s c') (@lem5279734 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5279741 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (h1). Qed.
Lemma lem5279742 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term591 c' s.
Proof. exact (fun h0 : term108 c' s => @lem5279741 c' s h1). Qed.
Lemma lem5279744 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279745 (c' : real) (s : real -> Prop) : (term591 c' s) = (term567 c' s).
Proof. exact (@lem5279744 (term108 c' s)). Qed.
Lemma lem5279746 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term567 c' s.
Proof. exact (EQ_MP (@lem5279745 c' s) (@lem5279742 c' s h1)). Qed.
Lemma lem5279774 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5279775 (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term546 x _69066 _69064) = (term627 x _69064 _69066).
Proof. exact (@lem5279774 (term108 _69066 _69064) (term537 x _69064 _69066)). Qed.
Lemma lem5279781 (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term628 x _69064 _69065) = (term628 x _69064 _69065).
Proof. exact (eq_refl (term628 x _69064 _69065)). Qed.
Lemma lem5279782 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term629 _69065 x _69066 _69064) = (term630 _69065 x _69064 _69066).
Proof. exact (MK_COMB (@lem5279781 x _69064 _69065) (@lem5279775 x _69064 _69066)). Qed.
Lemma lem5279786 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5279787 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term630 _69065 x _69064 _69066) = (term631 _69065 x _69064 _69066).
Proof. exact (@lem5279786 (term108 _69066 _69064) (term537 x _69064 _69065) (term537 x _69064 _69066)). Qed.
Lemma lem5279803 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term629 _69065 x _69066 _69064) = (term631 _69065 x _69064 _69066).
Proof. exact (TRANS (@lem5279782 _69065 x _69064 _69066) (@lem5279787 _69065 x _69064 _69066)). Qed.
Lemma lem5279804 (_69064 : real -> Prop) : (term289 _69064) = (term289 _69064).
Proof. exact (eq_refl (term289 _69064)). Qed.
Lemma lem5279805 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term580 _69065 x _69066 _69064) = (term632 _69065 x _69064 _69066).
Proof. exact (MK_COMB (@lem5279804 _69064) (@lem5279803 _69065 x _69064 _69066)). Qed.
Lemma lem5279816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5279817 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term633 _69065 x _69066 _69064) = (term634 _69065 x _69064 _69066).
Proof. exact (MK_COMB (@lem5279816) (@lem5279805 _69065 x _69064 _69066)). Qed.
Lemma lem5279821 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5279822 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term635 x _69065 _69066 _69064) = (term636 x _69065 _69066 _69064).
Proof. exact (@lem5279821 (_69064 = (@EMPTY real)) (term537 x _69064 _69066) (term637 x _69065 _69066 _69064)). Qed.
Lemma lem5279838 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5279839 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term638 x _69065 _69066 _69064) = (term629 _69065 x _69066 _69064).
Proof. exact (@lem5279838 (term537 x _69064 _69065) (term537 x _69064 _69066) (term108 _69066 _69064)). Qed.
Lemma lem5279853 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5279854 (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term546 x _69066 _69064) = (term627 x _69064 _69066).
Proof. exact (@lem5279853 (term108 _69066 _69064) (term537 x _69064 _69066)). Qed.
Lemma lem5279860 (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term628 x _69064 _69065) = (term628 x _69064 _69065).
Proof. exact (eq_refl (term628 x _69064 _69065)). Qed.
Lemma lem5279861 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term629 _69065 x _69066 _69064) = (term630 _69065 x _69064 _69066).
Proof. exact (MK_COMB (@lem5279860 x _69064 _69065) (@lem5279854 x _69064 _69066)). Qed.
Lemma lem5279865 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5279866 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term630 _69065 x _69064 _69066) = (term631 _69065 x _69064 _69066).
Proof. exact (@lem5279865 (term108 _69066 _69064) (term537 x _69064 _69065) (term537 x _69064 _69066)). Qed.
Lemma lem5279882 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term629 _69065 x _69066 _69064) = (term631 _69065 x _69064 _69066).
Proof. exact (TRANS (@lem5279861 _69065 x _69064 _69066) (@lem5279866 _69065 x _69064 _69066)). Qed.
Lemma lem5279883 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term638 x _69065 _69066 _69064) = (term631 _69065 x _69064 _69066).
Proof. exact (TRANS (@lem5279839 _69065 x _69066 _69064) (@lem5279882 _69065 x _69064 _69066)). Qed.
Lemma lem5279884 (_69064 : real -> Prop) : (term289 _69064) = (term289 _69064).
Proof. exact (eq_refl (term289 _69064)). Qed.
Lemma lem5279885 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term636 x _69065 _69066 _69064) = (term632 _69065 x _69064 _69066).
Proof. exact (MK_COMB (@lem5279884 _69064) (@lem5279883 _69065 x _69064 _69066)). Qed.
Lemma lem5279896 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term635 x _69065 _69066 _69064) = (term632 _69065 x _69064 _69066).
Proof. exact (TRANS (@lem5279822 x _69065 _69066 _69064) (@lem5279885 _69065 x _69064 _69066)). Qed.
Lemma lem5279897 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : ((term580 _69065 x _69066 _69064) = (term635 x _69065 _69066 _69064)) = ((term632 _69065 x _69064 _69066) = (term632 _69065 x _69064 _69066)).
Proof. exact (MK_COMB (@lem5279817 _69065 x _69064 _69066) (@lem5279896 _69065 x _69064 _69066)). Qed.
Lemma lem5279899 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5279900 (x : Prop) : (x = x) = True.
Proof. exact (@lem5279899 Prop x). Qed.
Lemma lem5279901 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : ((term632 _69065 x _69064 _69066) = (term632 _69065 x _69064 _69066)) = True.
Proof. exact (@lem5279900 (term632 _69065 x _69064 _69066)). Qed.
Lemma lem5279902 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : ((term580 _69065 x _69066 _69064) = (term635 x _69065 _69066 _69064)) = True.
Proof. exact (TRANS (@lem5279897 _69065 x _69064 _69066) (@lem5279901 _69065 x _69064 _69066)). Qed.
Lemma lem5279903 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : True = ((term580 _69065 x _69066 _69064) = (term635 x _69065 _69066 _69064)).
Proof. exact (SYM (@lem5279902 x _69065 _69066 _69064)). Qed.
Lemma lem5279904 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term580 _69065 x _69066 _69064) = (term635 x _69065 _69066 _69064).
Proof. exact (EQ_MP (@lem5279903 x _69065 _69066 _69064) (@lem0)). Qed.
Lemma lem5279905 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term635 x _69065 _69066 _69064.
Proof. exact (EQ_MP (@lem5279904 x _69065 _69066 _69064) (@lem5278951 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5279907 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5279908 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term635 x _69065 _69066 _69064) = (term639 _69065 x _69064 _69066).
Proof. exact (@lem5279907 (term640 x _69065 _69066 _69064) (term537 x _69064 _69066)). Qed.
Lemma lem5279910 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5279911 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term641 x _69065 _69066 _69064) = (term642 x _69065 _69066 _69064).
Proof. exact (@lem5279910 (_69064 = (@EMPTY real)) (term637 x _69065 _69066 _69064)). Qed.
Lemma lem5279913 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5279914 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term643 x _69065 _69066 _69064) = (term644 x _69065 _69066 _69064).
Proof. exact (@lem5279913 (term537 x _69064 _69065) (term108 _69066 _69064)). Qed.
Lemma lem5279916 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5279917 (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term645 x _69064 _69065) = (term625 x _69064 _69065).
Proof. exact (@lem5279916 (term625 x _69064 _69065)). Qed.
Lemma lem5279918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5279919 (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term646 x _69064 _69065) = (term647 x _69064 _69065).
Proof. exact (MK_COMB (@lem5279918) (@lem5279917 x _69064 _69065)). Qed.
Lemma lem5279920 (_69066 : real) (_69064 : real -> Prop) : (term567 _69066 _69064) = (term567 _69066 _69064).
Proof. exact (eq_refl (term567 _69066 _69064)). Qed.
Lemma lem5279921 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term644 x _69065 _69066 _69064) = (term648 x _69065 _69066 _69064).
Proof. exact (MK_COMB (@lem5279919 x _69064 _69065) (@lem5279920 _69066 _69064)). Qed.
Lemma lem5279922 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term643 x _69065 _69066 _69064) = (term648 x _69065 _69066 _69064).
Proof. exact (TRANS (@lem5279914 x _69065 _69066 _69064) (@lem5279921 x _69065 _69066 _69064)). Qed.
Lemma lem5279923 (_69064 : real -> Prop) : (term118 _69064) = (term118 _69064).
Proof. exact (eq_refl (term118 _69064)). Qed.
Lemma lem5279924 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term642 x _69065 _69066 _69064) = (term649 x _69065 _69066 _69064).
Proof. exact (MK_COMB (@lem5279923 _69064) (@lem5279922 x _69065 _69066 _69064)). Qed.
Lemma lem5279925 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term641 x _69065 _69066 _69064) = (term649 x _69065 _69066 _69064).
Proof. exact (TRANS (@lem5279911 x _69065 _69066 _69064) (@lem5279924 x _69065 _69066 _69064)). Qed.
Lemma lem5279926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5279927 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term650 x _69065 _69066 _69064) = (term651 x _69065 _69066 _69064).
Proof. exact (MK_COMB (@lem5279926) (@lem5279925 x _69065 _69066 _69064)). Qed.
Lemma lem5279928 (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term537 x _69064 _69066) = (term537 x _69064 _69066).
Proof. exact (eq_refl (term537 x _69064 _69066)). Qed.
Lemma lem5279929 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term639 _69065 x _69064 _69066) = (term652 _69065 x _69064 _69066).
Proof. exact (MK_COMB (@lem5279927 x _69065 _69066 _69064) (@lem5279928 x _69064 _69066)). Qed.
Lemma lem5279930 (_69065 : real) (x : type1021) (_69064 : real -> Prop) (_69066 : real) : (term635 x _69065 _69066 _69064) = (term652 _69065 x _69064 _69066).
Proof. exact (TRANS (@lem5279908 _69065 x _69064 _69066) (@lem5279929 _69065 x _69064 _69066)). Qed.
Lemma lem5279932 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term653 x c' s.
Proof. exact (conj (@lem5279738 x s c' t h1 h2 h3 h4) (@lem5279746 c' s h3)). Qed.
Lemma lem5279933 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term654 x c' s.
Proof. exact (conj (@lem5279691 s h2) (@lem5279932 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5279935 (_69065 : real) (_69064 : real -> Prop) (_69066 : real) (x : type1021) (h1 : term444 x) : term652 _69065 x _69064 _69066.
Proof. exact (EQ_MP (@lem5279930 _69065 x _69064 _69066) (@lem5279905 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5279936 (s : real -> Prop) (c' : real) (x : type1021) (h1 : term444 x) : term655 x s c'.
Proof. exact (@lem5279935 c' s c' x h1). Qed.
Lemma lem5279939 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term537 x s c'.
Proof. exact (@lem5279936 s c' x h1 (@lem5279933 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5279940 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term656 x s c'.
Proof. exact (fun h0 : term625 x s c' => @lem5279939 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5279942 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279943 (x : type1021) (s : real -> Prop) (c' : real) : (term656 x s c') = (term537 x s c').
Proof. exact (@lem5279942 (term625 x s c')). Qed.
Lemma lem5279944 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term537 x s c'.
Proof. exact (EQ_MP (@lem5279943 x s c') (@lem5279940 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5279946 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5279949 (c' : real) (_69067 : real) (s : real -> Prop) : (term130 s c' _69067) = (term657 c' _69067 s).
Proof. exact (@lem5279946 (real_le c' _69067) (term617 _69067 s)). Qed.
Lemma lem5279952 (_69067 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term657 c' _69067 s.
Proof. exact (EQ_MP (@lem5279949 c' _69067 s) (@lem5278911 _69067 s c' t h1)). Qed.
Lemma lem5279953 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term658 x c' s.
Proof. exact (@lem5279952 (x s c') s c' t h1). Qed.
Lemma lem5279956 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term589 x c' s.
Proof. exact (@lem5279953 x s c' t h4 (@lem5279944 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5279957 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term590 x c' s.
Proof. exact (fun h0 : term536 x c' s => @lem5279956 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5279959 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5279960 (x : type1021) (c' : real) (s : real -> Prop) : (term590 x c' s) = (term589 x c' s).
Proof. exact (@lem5279959 (term536 x c' s)). Qed.
Lemma lem5279961 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term589 x c' s.
Proof. exact (EQ_MP (@lem5279960 x c' s) (@lem5279957 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5279979 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5279980 (x : type1021) (_69065 : real) (_69066 : real) (_69064 : real -> Prop) : (term659 _69065 x _69066 _69064) = (term660 x _69065 _69066 _69064).
Proof. exact (@lem5279979 (term536 x _69066 _69064) (term537 x _69064 _69065) (term108 _69066 _69064)). Qed.
Lemma lem5279994 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5279995 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term637 x _69065 _69066 _69064) = (term661 _69066 x _69064 _69065).
Proof. exact (@lem5279994 (term108 _69066 _69064) (term537 x _69064 _69065)). Qed.
Lemma lem5280001 (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term662 x _69066 _69064) = (term662 x _69066 _69064).
Proof. exact (eq_refl (term662 x _69066 _69064)). Qed.
Lemma lem5280002 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term660 x _69065 _69066 _69064) = (term663 _69066 x _69064 _69065).
Proof. exact (MK_COMB (@lem5280001 x _69066 _69064) (@lem5279995 _69066 x _69064 _69065)). Qed.
Lemma lem5280013 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term659 _69065 x _69066 _69064) = (term663 _69066 x _69064 _69065).
Proof. exact (TRANS (@lem5279980 x _69065 _69066 _69064) (@lem5280002 _69066 x _69064 _69065)). Qed.
Lemma lem5280014 (_69064 : real -> Prop) : (term289 _69064) = (term289 _69064).
Proof. exact (eq_refl (term289 _69064)). Qed.
Lemma lem5280015 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term582 _69065 x _69066 _69064) = (term664 _69066 x _69064 _69065).
Proof. exact (MK_COMB (@lem5280014 _69064) (@lem5280013 _69066 x _69064 _69065)). Qed.
Lemma lem5280026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5280027 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term665 _69065 x _69066 _69064) = (term666 _69066 x _69064 _69065).
Proof. exact (MK_COMB (@lem5280026) (@lem5280015 _69066 x _69064 _69065)). Qed.
Lemma lem5280031 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280032 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term667 _69065 x _69066 _69064) = (term668 _69065 x _69066 _69064).
Proof. exact (@lem5280031 (_69064 = (@EMPTY real)) (term108 _69066 _69064) (term669 _69065 x _69066 _69064)). Qed.
Lemma lem5280058 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5280059 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term669 _69065 x _69066 _69064) = (term670 _69066 x _69064 _69065).
Proof. exact (@lem5280058 (term536 x _69066 _69064) (term537 x _69064 _69065)). Qed.
Lemma lem5280065 (_69066 : real) (_69064 : real -> Prop) : (term671 _69066 _69064) = (term671 _69066 _69064).
Proof. exact (eq_refl (term671 _69066 _69064)). Qed.
Lemma lem5280066 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term672 _69065 x _69066 _69064) = (term673 _69066 x _69064 _69065).
Proof. exact (MK_COMB (@lem5280065 _69066 _69064) (@lem5280059 _69066 x _69064 _69065)). Qed.
Lemma lem5280070 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280071 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term673 _69066 x _69064 _69065) = (term663 _69066 x _69064 _69065).
Proof. exact (@lem5280070 (term536 x _69066 _69064) (term108 _69066 _69064) (term537 x _69064 _69065)). Qed.
Lemma lem5280087 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term672 _69065 x _69066 _69064) = (term663 _69066 x _69064 _69065).
Proof. exact (TRANS (@lem5280066 _69066 x _69064 _69065) (@lem5280071 _69066 x _69064 _69065)). Qed.
Lemma lem5280088 (_69064 : real -> Prop) : (term289 _69064) = (term289 _69064).
Proof. exact (eq_refl (term289 _69064)). Qed.
Lemma lem5280089 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term668 _69065 x _69066 _69064) = (term664 _69066 x _69064 _69065).
Proof. exact (MK_COMB (@lem5280088 _69064) (@lem5280087 _69066 x _69064 _69065)). Qed.
Lemma lem5280100 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term667 _69065 x _69066 _69064) = (term664 _69066 x _69064 _69065).
Proof. exact (TRANS (@lem5280032 _69065 x _69066 _69064) (@lem5280089 _69066 x _69064 _69065)). Qed.
Lemma lem5280101 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : ((term582 _69065 x _69066 _69064) = (term667 _69065 x _69066 _69064)) = ((term664 _69066 x _69064 _69065) = (term664 _69066 x _69064 _69065)).
Proof. exact (MK_COMB (@lem5280027 _69066 x _69064 _69065) (@lem5280100 _69066 x _69064 _69065)). Qed.
Lemma lem5280103 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5280104 (x : Prop) : (x = x) = True.
Proof. exact (@lem5280103 Prop x). Qed.
Lemma lem5280105 (_69066 : real) (x : type1021) (_69064 : real -> Prop) (_69065 : real) : ((term664 _69066 x _69064 _69065) = (term664 _69066 x _69064 _69065)) = True.
Proof. exact (@lem5280104 (term664 _69066 x _69064 _69065)). Qed.
Lemma lem5280106 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : ((term582 _69065 x _69066 _69064) = (term667 _69065 x _69066 _69064)) = True.
Proof. exact (TRANS (@lem5280101 _69066 x _69064 _69065) (@lem5280105 _69066 x _69064 _69065)). Qed.
Lemma lem5280107 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : True = ((term582 _69065 x _69066 _69064) = (term667 _69065 x _69066 _69064)).
Proof. exact (SYM (@lem5280106 _69065 x _69066 _69064)). Qed.
Lemma lem5280108 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term582 _69065 x _69066 _69064) = (term667 _69065 x _69066 _69064).
Proof. exact (EQ_MP (@lem5280107 _69065 x _69066 _69064) (@lem0)). Qed.
Lemma lem5280109 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term667 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5280108 _69065 x _69066 _69064) (@lem5278983 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5280111 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5280112 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term667 _69065 x _69066 _69064) = (term674 _69065 x _69066 _69064).
Proof. exact (@lem5280111 (term675 _69065 x _69066 _69064) (term108 _69066 _69064)). Qed.
Lemma lem5280114 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280115 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term676 _69065 x _69066 _69064) = (term677 _69065 x _69066 _69064).
Proof. exact (@lem5280114 (_69064 = (@EMPTY real)) (term669 _69065 x _69066 _69064)). Qed.
Lemma lem5280117 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280118 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term678 _69065 x _69066 _69064) = (term679 _69065 x _69066 _69064).
Proof. exact (@lem5280117 (term537 x _69064 _69065) (term536 x _69066 _69064)). Qed.
Lemma lem5280120 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5280121 (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term645 x _69064 _69065) = (term625 x _69064 _69065).
Proof. exact (@lem5280120 (term625 x _69064 _69065)). Qed.
Lemma lem5280122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5280123 (x : type1021) (_69064 : real -> Prop) (_69065 : real) : (term646 x _69064 _69065) = (term647 x _69064 _69065).
Proof. exact (MK_COMB (@lem5280122) (@lem5280121 x _69064 _69065)). Qed.
Lemma lem5280124 (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term589 x _69066 _69064) = (term589 x _69066 _69064).
Proof. exact (eq_refl (term589 x _69066 _69064)). Qed.
Lemma lem5280125 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term679 _69065 x _69066 _69064) = (term680 _69065 x _69066 _69064).
Proof. exact (MK_COMB (@lem5280123 x _69064 _69065) (@lem5280124 x _69066 _69064)). Qed.
Lemma lem5280126 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term678 _69065 x _69066 _69064) = (term680 _69065 x _69066 _69064).
Proof. exact (TRANS (@lem5280118 _69065 x _69066 _69064) (@lem5280125 _69065 x _69066 _69064)). Qed.
Lemma lem5280127 (_69064 : real -> Prop) : (term118 _69064) = (term118 _69064).
Proof. exact (eq_refl (term118 _69064)). Qed.
Lemma lem5280128 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term677 _69065 x _69066 _69064) = (term681 _69065 x _69066 _69064).
Proof. exact (MK_COMB (@lem5280127 _69064) (@lem5280126 _69065 x _69066 _69064)). Qed.
Lemma lem5280129 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term676 _69065 x _69066 _69064) = (term681 _69065 x _69066 _69064).
Proof. exact (TRANS (@lem5280115 _69065 x _69066 _69064) (@lem5280128 _69065 x _69066 _69064)). Qed.
Lemma lem5280130 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5280131 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term682 _69065 x _69066 _69064) = (term683 _69065 x _69066 _69064).
Proof. exact (MK_COMB (@lem5280130) (@lem5280129 _69065 x _69066 _69064)). Qed.
Lemma lem5280132 (_69066 : real) (_69064 : real -> Prop) : (term108 _69066 _69064) = (term108 _69066 _69064).
Proof. exact (eq_refl (term108 _69066 _69064)). Qed.
Lemma lem5280133 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term674 _69065 x _69066 _69064) = (term684 _69065 x _69066 _69064).
Proof. exact (MK_COMB (@lem5280131 _69065 x _69066 _69064) (@lem5280132 _69066 _69064)). Qed.
Lemma lem5280134 (_69065 : real) (x : type1021) (_69066 : real) (_69064 : real -> Prop) : (term667 _69065 x _69066 _69064) = (term684 _69065 x _69066 _69064).
Proof. exact (TRANS (@lem5280112 _69065 x _69066 _69064) (@lem5280133 _69065 x _69066 _69064)). Qed.
Lemma lem5280136 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term685 x c' s.
Proof. exact (conj (@lem5279684 x s c' t h1 h2 h3 h4) (@lem5279961 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280137 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term686 x c' s.
Proof. exact (conj (@lem5279489 s h2) (@lem5280136 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280139 (_69065 : real) (_69066 : real) (_69064 : real -> Prop) (x : type1021) (h1 : term444 x) : term684 _69065 x _69066 _69064.
Proof. exact (EQ_MP (@lem5280134 _69065 x _69066 _69064) (@lem5280109 _69065 _69066 _69064 x h1)). Qed.
Lemma lem5280140 (c' : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term687 x c' s.
Proof. exact (@lem5280139 c' c' s x h1). Qed.
Lemma lem5280143 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term108 c' s.
Proof. exact (@lem5280140 c' s x h1 (@lem5280137 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280144 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term160 s c' t) : term688 c' s.
Proof. exact (fun h0 : term567 c' s => @lem5280143 x s c' t h1 h2 h0 h3). Qed.
Lemma lem5280146 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280147 (c' : real) (s : real -> Prop) : (term688 c' s) = (term108 c' s).
Proof. exact (@lem5280146 (term108 c' s)). Qed.
Lemma lem5280148 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term160 s c' t) : term108 c' s.
Proof. exact (EQ_MP (@lem5280147 c' s) (@lem5280144 x s c' t h1 h2 h3)). Qed.
Lemma lem5280151 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5280153 (c' : real) (s : real -> Prop) : (term567 c' s) = (term689 c' s).
Proof. exact (@lem5280151 (term108 c' s)). Qed.
Lemma lem5280156 (c' : real) (s : real -> Prop) (h1 : term567 c' s) : term689 c' s.
Proof. exact (EQ_MP (@lem5280153 c' s) (@lem5278919 c' s h1)). Qed.
Lemma lem5280159 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (@lem5280156 c' s h3 (@lem5280148 x s c' t h1 h2 h4)). Qed.
Lemma lem5280160 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : term690.
Proof. exact (fun h0 : ~ False => @lem5280159 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5280162 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280163 : term690 = False.
Proof. exact (@lem5280162 False). Qed.
Lemma lem5280164 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5280163) (@lem5280160 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280231 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5280232 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5280231 t h1). Qed.
Lemma lem5280234 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280235 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5280234 (t = (@EMPTY real))). Qed.
Lemma lem5280236 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5280235 t) (@lem5280232 t h1)). Qed.
Lemma lem5280238 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5280239 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5280238 t h1). Qed.
Lemma lem5280241 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280242 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5280241 (t = (@EMPTY real))). Qed.
Lemma lem5280243 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5280242 t) (@lem5280239 t h1)). Qed.
Lemma lem5280246 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (h1). Qed.
Lemma lem5280247 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term590 x c' t.
Proof. exact (fun h0 : term536 x c' t => @lem5280246 x c' t h1). Qed.
Lemma lem5280249 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280250 (x : type1021) (c' : real) (t : real -> Prop) : (term590 x c' t) = (term589 x c' t).
Proof. exact (@lem5280249 (term536 x c' t)). Qed.
Lemma lem5280251 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (EQ_MP (@lem5280250 x c' t) (@lem5280247 x c' t h1)). Qed.
Lemma lem5280254 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (h1). Qed.
Lemma lem5280255 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term591 c' t.
Proof. exact (fun h0 : term108 c' t => @lem5280254 c' t h1). Qed.
Lemma lem5280257 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280258 (c' : real) (t : real -> Prop) : (term591 c' t) = (term567 c' t).
Proof. exact (@lem5280257 (term108 c' t)). Qed.
Lemma lem5280259 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (EQ_MP (@lem5280258 c' t) (@lem5280255 c' t h1)). Qed.
Lemma lem5280292 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280293 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term592 x _69075 _69076 _69074) = (term593 x _69075 _69076 _69074).
Proof. exact (@lem5280292 (_69074 = (@EMPTY real)) (term536 x _69076 _69074) (term594 x _69075 _69076 _69074)). Qed.
Lemma lem5280309 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280310 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term595 x _69075 _69076 _69074) = (term596 _69075 x _69076 _69074).
Proof. exact (@lem5280309 (term536 x _69075 _69074) (term536 x _69076 _69074) (term108 _69076 _69074)). Qed.
Lemma lem5280326 (_69074 : real -> Prop) : (term289 _69074) = (term289 _69074).
Proof. exact (eq_refl (term289 _69074)). Qed.
Lemma lem5280327 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term593 x _69075 _69076 _69074) = (term581 _69075 x _69076 _69074).
Proof. exact (MK_COMB (@lem5280326 _69074) (@lem5280310 _69075 x _69076 _69074)). Qed.
Lemma lem5280338 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term592 x _69075 _69076 _69074) = (term581 _69075 x _69076 _69074).
Proof. exact (TRANS (@lem5280293 x _69075 _69076 _69074) (@lem5280327 _69075 x _69076 _69074)). Qed.
Lemma lem5280339 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term597 _69075 x _69076 _69074) = (term597 _69075 x _69076 _69074).
Proof. exact (eq_refl (term597 _69075 x _69076 _69074)). Qed.
Lemma lem5280340 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : ((term581 _69075 x _69076 _69074) = (term592 x _69075 _69076 _69074)) = ((term581 _69075 x _69076 _69074) = (term581 _69075 x _69076 _69074)).
Proof. exact (MK_COMB (@lem5280339 _69075 x _69076 _69074) (@lem5280338 _69075 x _69076 _69074)). Qed.
Lemma lem5280342 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5280343 (x : Prop) : (x = x) = True.
Proof. exact (@lem5280342 Prop x). Qed.
Lemma lem5280344 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : ((term581 _69075 x _69076 _69074) = (term581 _69075 x _69076 _69074)) = True.
Proof. exact (@lem5280343 (term581 _69075 x _69076 _69074)). Qed.
Lemma lem5280345 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : ((term581 _69075 x _69076 _69074) = (term592 x _69075 _69076 _69074)) = True.
Proof. exact (TRANS (@lem5280340 _69075 x _69076 _69074) (@lem5280344 _69075 x _69076 _69074)). Qed.
Lemma lem5280346 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : True = ((term581 _69075 x _69076 _69074) = (term592 x _69075 _69076 _69074)).
Proof. exact (SYM (@lem5280345 x _69075 _69076 _69074)). Qed.
Lemma lem5280347 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term581 _69075 x _69076 _69074) = (term592 x _69075 _69076 _69074).
Proof. exact (EQ_MP (@lem5280346 x _69075 _69076 _69074) (@lem0)). Qed.
Lemma lem5280348 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term592 x _69075 _69076 _69074.
Proof. exact (EQ_MP (@lem5280347 x _69075 _69076 _69074) (@lem5279105 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5280350 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5280351 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term592 x _69075 _69076 _69074) = (term599 _69075 x _69076 _69074).
Proof. exact (@lem5280350 (term600 x _69075 _69076 _69074) (term536 x _69076 _69074)). Qed.
Lemma lem5280353 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280354 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term603 x _69075 _69076 _69074) = (term604 x _69075 _69076 _69074).
Proof. exact (@lem5280353 (_69074 = (@EMPTY real)) (term594 x _69075 _69076 _69074)). Qed.
Lemma lem5280356 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280357 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term605 x _69075 _69076 _69074) = (term606 x _69075 _69076 _69074).
Proof. exact (@lem5280356 (term536 x _69075 _69074) (term108 _69076 _69074)). Qed.
Lemma lem5280358 (_69074 : real -> Prop) : (term118 _69074) = (term118 _69074).
Proof. exact (eq_refl (term118 _69074)). Qed.
Lemma lem5280359 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term604 x _69075 _69076 _69074) = (term607 x _69075 _69076 _69074).
Proof. exact (MK_COMB (@lem5280358 _69074) (@lem5280357 x _69075 _69076 _69074)). Qed.
Lemma lem5280360 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term603 x _69075 _69076 _69074) = (term607 x _69075 _69076 _69074).
Proof. exact (TRANS (@lem5280354 x _69075 _69076 _69074) (@lem5280359 x _69075 _69076 _69074)). Qed.
Lemma lem5280361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5280362 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term608 x _69075 _69076 _69074) = (term609 x _69075 _69076 _69074).
Proof. exact (MK_COMB (@lem5280361) (@lem5280360 x _69075 _69076 _69074)). Qed.
Lemma lem5280363 (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term536 x _69076 _69074) = (term536 x _69076 _69074).
Proof. exact (eq_refl (term536 x _69076 _69074)). Qed.
Lemma lem5280364 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term599 _69075 x _69076 _69074) = (term610 _69075 x _69076 _69074).
Proof. exact (MK_COMB (@lem5280362 x _69075 _69076 _69074) (@lem5280363 x _69076 _69074)). Qed.
Lemma lem5280365 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term592 x _69075 _69076 _69074) = (term610 _69075 x _69076 _69074).
Proof. exact (TRANS (@lem5280351 _69075 x _69076 _69074) (@lem5280364 _69075 x _69076 _69074)). Qed.
Lemma lem5280367 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) (h2 : term567 c' t) : term611 x c' t.
Proof. exact (conj (@lem5280251 x c' t h1) (@lem5280259 c' t h2)). Qed.
Lemma lem5280368 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term31 t) (h2 : term589 x c' t) (h3 : term567 c' t) : term612 x c' t.
Proof. exact (conj (@lem5280243 t h1) (@lem5280367 x c' t h2 h3)). Qed.
Lemma lem5280370 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5280365 _69075 x _69076 _69074) (@lem5280348 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5280371 (c' : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' t.
Proof. exact (@lem5280370 c' c' t x h1). Qed.
Lemma lem5280374 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term589 x c' t) (h4 : term567 c' t) : term536 x c' t.
Proof. exact (@lem5280371 c' t x h1 (@lem5280368 x c' t h2 h3 h4)). Qed.
Lemma lem5280375 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) : term614 x c' t.
Proof. exact (fun h0 : term589 x c' t => @lem5280374 x c' t h1 h2 h0 h3). Qed.
Lemma lem5280377 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280378 (x : type1021) (c' : real) (t : real -> Prop) : (term614 x c' t) = (term536 x c' t).
Proof. exact (@lem5280377 (term536 x c' t)). Qed.
Lemma lem5280379 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) : term536 x c' t.
Proof. exact (EQ_MP (@lem5280378 x c' t) (@lem5280375 x c' t h1 h2 h3)). Qed.
Lemma lem5280385 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5280386 (c' : real) (_69078 : real) (t : real -> Prop) : (term130 t c' _69078) = (term616 c' _69078 t).
Proof. exact (@lem5280385 (real_le c' _69078) (term617 _69078 t)). Qed.
Lemma lem5280392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5280393 (c' : real) (_69078 : real) (t : real -> Prop) : (term618 t c' _69078) = (term619 c' _69078 t).
Proof. exact (MK_COMB (@lem5280392) (@lem5280386 c' _69078 t)). Qed.
Lemma lem5280399 (c' : real) (_69078 : real) (t : real -> Prop) : (term616 c' _69078 t) = (term616 c' _69078 t).
Proof. exact (eq_refl (term616 c' _69078 t)). Qed.
Lemma lem5280400 (c' : real) (_69078 : real) (t : real -> Prop) : ((term130 t c' _69078) = (term616 c' _69078 t)) = ((term616 c' _69078 t) = (term616 c' _69078 t)).
Proof. exact (MK_COMB (@lem5280393 c' _69078 t) (@lem5280399 c' _69078 t)). Qed.
Lemma lem5280402 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5280403 (x : Prop) : (x = x) = True.
Proof. exact (@lem5280402 Prop x). Qed.
Lemma lem5280404 (c' : real) (_69078 : real) (t : real -> Prop) : ((term616 c' _69078 t) = (term616 c' _69078 t)) = True.
Proof. exact (@lem5280403 (term616 c' _69078 t)). Qed.
Lemma lem5280405 (c' : real) (_69078 : real) (t : real -> Prop) : ((term130 t c' _69078) = (term616 c' _69078 t)) = True.
Proof. exact (TRANS (@lem5280400 c' _69078 t) (@lem5280404 c' _69078 t)). Qed.
Lemma lem5280406 (c' : real) (_69078 : real) (t : real -> Prop) : True = ((term130 t c' _69078) = (term616 c' _69078 t)).
Proof. exact (SYM (@lem5280405 c' _69078 t)). Qed.
Lemma lem5280407 (c' : real) (_69078 : real) (t : real -> Prop) : (term130 t c' _69078) = (term616 c' _69078 t).
Proof. exact (EQ_MP (@lem5280406 c' _69078 t) (@lem0)). Qed.
Lemma lem5280408 (_69078 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term616 c' _69078 t.
Proof. exact (EQ_MP (@lem5280407 c' _69078 t) (@lem5279055 _69078 s c' t h1)). Qed.
Lemma lem5280410 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5280411 (t : real -> Prop) (c' : real) (_69078 : real) : (term616 c' _69078 t) = (term620 t c' _69078).
Proof. exact (@lem5280410 (term617 _69078 t) (real_le c' _69078)). Qed.
Lemma lem5280413 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5280414 (_69078 : real) (t : real -> Prop) : (term622 _69078 t) = (@IN real _69078 t).
Proof. exact (@lem5280413 (@IN real _69078 t)). Qed.
Lemma lem5280415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5280416 (_69078 : real) (t : real -> Prop) : (term623 _69078 t) = (term51 _69078 t).
Proof. exact (MK_COMB (@lem5280415) (@lem5280414 _69078 t)). Qed.
Lemma lem5280417 (c' : real) (_69078 : real) : (real_le c' _69078) = (real_le c' _69078).
Proof. exact (eq_refl (real_le c' _69078)). Qed.
Lemma lem5280418 (t : real -> Prop) (c' : real) (_69078 : real) : (term620 t c' _69078) = (term53 t c' _69078).
Proof. exact (MK_COMB (@lem5280416 _69078 t) (@lem5280417 c' _69078)). Qed.
Lemma lem5280419 (t : real -> Prop) (c' : real) (_69078 : real) : (term616 c' _69078 t) = (term53 t c' _69078).
Proof. exact (TRANS (@lem5280411 t c' _69078) (@lem5280418 t c' _69078)). Qed.
Lemma lem5280422 (_69078 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term53 t c' _69078.
Proof. exact (EQ_MP (@lem5280419 t c' _69078) (@lem5280408 _69078 s c' t h1)). Qed.
Lemma lem5280423 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term624 x t c'.
Proof. exact (@lem5280422 (x t c') s c' t h1). Qed.
Lemma lem5280426 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term625 x t c'.
Proof. exact (@lem5280423 x s c' t h4 (@lem5280379 x c' t h1 h2 h3)). Qed.
Lemma lem5280427 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term626 x t c'.
Proof. exact (fun h0 : term537 x t c' => @lem5280426 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5280429 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280430 (x : type1021) (t : real -> Prop) (c' : real) : (term626 x t c') = (term625 x t c').
Proof. exact (@lem5280429 (term625 x t c')). Qed.
Lemma lem5280431 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term625 x t c'.
Proof. exact (EQ_MP (@lem5280430 x t c') (@lem5280427 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280433 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5280434 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5280433 t h1). Qed.
Lemma lem5280436 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280437 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5280436 (t = (@EMPTY real))). Qed.
Lemma lem5280438 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5280437 t) (@lem5280434 t h1)). Qed.
Lemma lem5280440 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5280441 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5280440 t h1). Qed.
Lemma lem5280443 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280444 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5280443 (t = (@EMPTY real))). Qed.
Lemma lem5280445 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5280444 t) (@lem5280441 t h1)). Qed.
Lemma lem5280448 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (h1). Qed.
Lemma lem5280449 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term590 x c' t.
Proof. exact (fun h0 : term536 x c' t => @lem5280448 x c' t h1). Qed.
Lemma lem5280451 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280452 (x : type1021) (c' : real) (t : real -> Prop) : (term590 x c' t) = (term589 x c' t).
Proof. exact (@lem5280451 (term536 x c' t)). Qed.
Lemma lem5280453 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (EQ_MP (@lem5280452 x c' t) (@lem5280449 x c' t h1)). Qed.
Lemma lem5280456 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (h1). Qed.
Lemma lem5280457 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term591 c' t.
Proof. exact (fun h0 : term108 c' t => @lem5280456 c' t h1). Qed.
Lemma lem5280459 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280460 (c' : real) (t : real -> Prop) : (term591 c' t) = (term567 c' t).
Proof. exact (@lem5280459 (term108 c' t)). Qed.
Lemma lem5280461 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (EQ_MP (@lem5280460 c' t) (@lem5280457 c' t h1)). Qed.
Lemma lem5280462 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) (h2 : term567 c' t) : term611 x c' t.
Proof. exact (conj (@lem5280453 x c' t h1) (@lem5280461 c' t h2)). Qed.
Lemma lem5280463 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term31 t) (h2 : term589 x c' t) (h3 : term567 c' t) : term612 x c' t.
Proof. exact (conj (@lem5280445 t h1) (@lem5280462 x c' t h2 h3)). Qed.
Lemma lem5280465 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5280365 _69075 x _69076 _69074) (@lem5280348 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5280466 (c' : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' t.
Proof. exact (@lem5280465 c' c' t x h1). Qed.
Lemma lem5280469 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term589 x c' t) (h4 : term567 c' t) : term536 x c' t.
Proof. exact (@lem5280466 c' t x h1 (@lem5280463 x c' t h2 h3 h4)). Qed.
Lemma lem5280470 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) : term614 x c' t.
Proof. exact (fun h0 : term589 x c' t => @lem5280469 x c' t h1 h2 h0 h3). Qed.
Lemma lem5280472 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280473 (x : type1021) (c' : real) (t : real -> Prop) : (term614 x c' t) = (term536 x c' t).
Proof. exact (@lem5280472 (term536 x c' t)). Qed.
Lemma lem5280474 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) : term536 x c' t.
Proof. exact (EQ_MP (@lem5280473 x c' t) (@lem5280470 x c' t h1 h2 h3)). Qed.
Lemma lem5280476 (_69078 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term53 t c' _69078.
Proof. exact (EQ_MP (@lem5280419 t c' _69078) (@lem5280408 _69078 s c' t h1)). Qed.
Lemma lem5280477 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term624 x t c'.
Proof. exact (@lem5280476 (x t c') s c' t h1). Qed.
Lemma lem5280480 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term625 x t c'.
Proof. exact (@lem5280477 x s c' t h4 (@lem5280474 x c' t h1 h2 h3)). Qed.
Lemma lem5280481 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term626 x t c'.
Proof. exact (fun h0 : term537 x t c' => @lem5280480 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5280483 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280484 (x : type1021) (t : real -> Prop) (c' : real) : (term626 x t c') = (term625 x t c').
Proof. exact (@lem5280483 (term625 x t c')). Qed.
Lemma lem5280485 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term625 x t c'.
Proof. exact (EQ_MP (@lem5280484 x t c') (@lem5280481 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280488 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (h1). Qed.
Lemma lem5280489 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term591 c' t.
Proof. exact (fun h0 : term108 c' t => @lem5280488 c' t h1). Qed.
Lemma lem5280491 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280492 (c' : real) (t : real -> Prop) : (term591 c' t) = (term567 c' t).
Proof. exact (@lem5280491 (term108 c' t)). Qed.
Lemma lem5280493 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term567 c' t.
Proof. exact (EQ_MP (@lem5280492 c' t) (@lem5280489 c' t h1)). Qed.
Lemma lem5280521 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5280522 (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term546 x _69076 _69074) = (term627 x _69074 _69076).
Proof. exact (@lem5280521 (term108 _69076 _69074) (term537 x _69074 _69076)). Qed.
Lemma lem5280528 (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term628 x _69074 _69075) = (term628 x _69074 _69075).
Proof. exact (eq_refl (term628 x _69074 _69075)). Qed.
Lemma lem5280529 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term629 _69075 x _69076 _69074) = (term630 _69075 x _69074 _69076).
Proof. exact (MK_COMB (@lem5280528 x _69074 _69075) (@lem5280522 x _69074 _69076)). Qed.
Lemma lem5280533 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280534 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term630 _69075 x _69074 _69076) = (term631 _69075 x _69074 _69076).
Proof. exact (@lem5280533 (term108 _69076 _69074) (term537 x _69074 _69075) (term537 x _69074 _69076)). Qed.
Lemma lem5280550 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term629 _69075 x _69076 _69074) = (term631 _69075 x _69074 _69076).
Proof. exact (TRANS (@lem5280529 _69075 x _69074 _69076) (@lem5280534 _69075 x _69074 _69076)). Qed.
Lemma lem5280551 (_69074 : real -> Prop) : (term289 _69074) = (term289 _69074).
Proof. exact (eq_refl (term289 _69074)). Qed.
Lemma lem5280552 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term580 _69075 x _69076 _69074) = (term632 _69075 x _69074 _69076).
Proof. exact (MK_COMB (@lem5280551 _69074) (@lem5280550 _69075 x _69074 _69076)). Qed.
Lemma lem5280563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5280564 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term633 _69075 x _69076 _69074) = (term634 _69075 x _69074 _69076).
Proof. exact (MK_COMB (@lem5280563) (@lem5280552 _69075 x _69074 _69076)). Qed.
Lemma lem5280568 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280569 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term635 x _69075 _69076 _69074) = (term636 x _69075 _69076 _69074).
Proof. exact (@lem5280568 (_69074 = (@EMPTY real)) (term537 x _69074 _69076) (term637 x _69075 _69076 _69074)). Qed.
Lemma lem5280585 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280586 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term638 x _69075 _69076 _69074) = (term629 _69075 x _69076 _69074).
Proof. exact (@lem5280585 (term537 x _69074 _69075) (term537 x _69074 _69076) (term108 _69076 _69074)). Qed.
Lemma lem5280600 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5280601 (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term546 x _69076 _69074) = (term627 x _69074 _69076).
Proof. exact (@lem5280600 (term108 _69076 _69074) (term537 x _69074 _69076)). Qed.
Lemma lem5280607 (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term628 x _69074 _69075) = (term628 x _69074 _69075).
Proof. exact (eq_refl (term628 x _69074 _69075)). Qed.
Lemma lem5280608 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term629 _69075 x _69076 _69074) = (term630 _69075 x _69074 _69076).
Proof. exact (MK_COMB (@lem5280607 x _69074 _69075) (@lem5280601 x _69074 _69076)). Qed.
Lemma lem5280612 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280613 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term630 _69075 x _69074 _69076) = (term631 _69075 x _69074 _69076).
Proof. exact (@lem5280612 (term108 _69076 _69074) (term537 x _69074 _69075) (term537 x _69074 _69076)). Qed.
Lemma lem5280629 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term629 _69075 x _69076 _69074) = (term631 _69075 x _69074 _69076).
Proof. exact (TRANS (@lem5280608 _69075 x _69074 _69076) (@lem5280613 _69075 x _69074 _69076)). Qed.
Lemma lem5280630 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term638 x _69075 _69076 _69074) = (term631 _69075 x _69074 _69076).
Proof. exact (TRANS (@lem5280586 _69075 x _69076 _69074) (@lem5280629 _69075 x _69074 _69076)). Qed.
Lemma lem5280631 (_69074 : real -> Prop) : (term289 _69074) = (term289 _69074).
Proof. exact (eq_refl (term289 _69074)). Qed.
Lemma lem5280632 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term636 x _69075 _69076 _69074) = (term632 _69075 x _69074 _69076).
Proof. exact (MK_COMB (@lem5280631 _69074) (@lem5280630 _69075 x _69074 _69076)). Qed.
Lemma lem5280643 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term635 x _69075 _69076 _69074) = (term632 _69075 x _69074 _69076).
Proof. exact (TRANS (@lem5280569 x _69075 _69076 _69074) (@lem5280632 _69075 x _69074 _69076)). Qed.
Lemma lem5280644 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : ((term580 _69075 x _69076 _69074) = (term635 x _69075 _69076 _69074)) = ((term632 _69075 x _69074 _69076) = (term632 _69075 x _69074 _69076)).
Proof. exact (MK_COMB (@lem5280564 _69075 x _69074 _69076) (@lem5280643 _69075 x _69074 _69076)). Qed.
Lemma lem5280646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5280647 (x : Prop) : (x = x) = True.
Proof. exact (@lem5280646 Prop x). Qed.
Lemma lem5280648 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : ((term632 _69075 x _69074 _69076) = (term632 _69075 x _69074 _69076)) = True.
Proof. exact (@lem5280647 (term632 _69075 x _69074 _69076)). Qed.
Lemma lem5280649 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : ((term580 _69075 x _69076 _69074) = (term635 x _69075 _69076 _69074)) = True.
Proof. exact (TRANS (@lem5280644 _69075 x _69074 _69076) (@lem5280648 _69075 x _69074 _69076)). Qed.
Lemma lem5280650 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : True = ((term580 _69075 x _69076 _69074) = (term635 x _69075 _69076 _69074)).
Proof. exact (SYM (@lem5280649 x _69075 _69076 _69074)). Qed.
Lemma lem5280651 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term580 _69075 x _69076 _69074) = (term635 x _69075 _69076 _69074).
Proof. exact (EQ_MP (@lem5280650 x _69075 _69076 _69074) (@lem0)). Qed.
Lemma lem5280652 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term635 x _69075 _69076 _69074.
Proof. exact (EQ_MP (@lem5280651 x _69075 _69076 _69074) (@lem5279089 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5280654 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5280655 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term635 x _69075 _69076 _69074) = (term639 _69075 x _69074 _69076).
Proof. exact (@lem5280654 (term640 x _69075 _69076 _69074) (term537 x _69074 _69076)). Qed.
Lemma lem5280657 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280658 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term641 x _69075 _69076 _69074) = (term642 x _69075 _69076 _69074).
Proof. exact (@lem5280657 (_69074 = (@EMPTY real)) (term637 x _69075 _69076 _69074)). Qed.
Lemma lem5280660 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280661 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term643 x _69075 _69076 _69074) = (term644 x _69075 _69076 _69074).
Proof. exact (@lem5280660 (term537 x _69074 _69075) (term108 _69076 _69074)). Qed.
Lemma lem5280663 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5280664 (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term645 x _69074 _69075) = (term625 x _69074 _69075).
Proof. exact (@lem5280663 (term625 x _69074 _69075)). Qed.
Lemma lem5280665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5280666 (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term646 x _69074 _69075) = (term647 x _69074 _69075).
Proof. exact (MK_COMB (@lem5280665) (@lem5280664 x _69074 _69075)). Qed.
Lemma lem5280667 (_69076 : real) (_69074 : real -> Prop) : (term567 _69076 _69074) = (term567 _69076 _69074).
Proof. exact (eq_refl (term567 _69076 _69074)). Qed.
Lemma lem5280668 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term644 x _69075 _69076 _69074) = (term648 x _69075 _69076 _69074).
Proof. exact (MK_COMB (@lem5280666 x _69074 _69075) (@lem5280667 _69076 _69074)). Qed.
Lemma lem5280669 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term643 x _69075 _69076 _69074) = (term648 x _69075 _69076 _69074).
Proof. exact (TRANS (@lem5280661 x _69075 _69076 _69074) (@lem5280668 x _69075 _69076 _69074)). Qed.
Lemma lem5280670 (_69074 : real -> Prop) : (term118 _69074) = (term118 _69074).
Proof. exact (eq_refl (term118 _69074)). Qed.
Lemma lem5280671 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term642 x _69075 _69076 _69074) = (term649 x _69075 _69076 _69074).
Proof. exact (MK_COMB (@lem5280670 _69074) (@lem5280669 x _69075 _69076 _69074)). Qed.
Lemma lem5280672 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term641 x _69075 _69076 _69074) = (term649 x _69075 _69076 _69074).
Proof. exact (TRANS (@lem5280658 x _69075 _69076 _69074) (@lem5280671 x _69075 _69076 _69074)). Qed.
Lemma lem5280673 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5280674 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term650 x _69075 _69076 _69074) = (term651 x _69075 _69076 _69074).
Proof. exact (MK_COMB (@lem5280673) (@lem5280672 x _69075 _69076 _69074)). Qed.
Lemma lem5280675 (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term537 x _69074 _69076) = (term537 x _69074 _69076).
Proof. exact (eq_refl (term537 x _69074 _69076)). Qed.
Lemma lem5280676 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term639 _69075 x _69074 _69076) = (term652 _69075 x _69074 _69076).
Proof. exact (MK_COMB (@lem5280674 x _69075 _69076 _69074) (@lem5280675 x _69074 _69076)). Qed.
Lemma lem5280677 (_69075 : real) (x : type1021) (_69074 : real -> Prop) (_69076 : real) : (term635 x _69075 _69076 _69074) = (term652 _69075 x _69074 _69076).
Proof. exact (TRANS (@lem5280655 _69075 x _69074 _69076) (@lem5280676 _69075 x _69074 _69076)). Qed.
Lemma lem5280679 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term653 x c' t.
Proof. exact (conj (@lem5280485 x s c' t h1 h2 h3 h4) (@lem5280493 c' t h3)). Qed.
Lemma lem5280680 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term654 x c' t.
Proof. exact (conj (@lem5280438 t h2) (@lem5280679 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280682 (_69075 : real) (_69074 : real -> Prop) (_69076 : real) (x : type1021) (h1 : term444 x) : term652 _69075 x _69074 _69076.
Proof. exact (EQ_MP (@lem5280677 _69075 x _69074 _69076) (@lem5280652 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5280683 (t : real -> Prop) (c' : real) (x : type1021) (h1 : term444 x) : term655 x t c'.
Proof. exact (@lem5280682 c' t c' x h1). Qed.
Lemma lem5280686 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term537 x t c'.
Proof. exact (@lem5280683 t c' x h1 (@lem5280680 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280687 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term656 x t c'.
Proof. exact (fun h0 : term625 x t c' => @lem5280686 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5280689 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280690 (x : type1021) (t : real -> Prop) (c' : real) : (term656 x t c') = (term537 x t c').
Proof. exact (@lem5280689 (term625 x t c')). Qed.
Lemma lem5280691 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term537 x t c'.
Proof. exact (EQ_MP (@lem5280690 x t c') (@lem5280687 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280693 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5280696 (c' : real) (_69078 : real) (t : real -> Prop) : (term130 t c' _69078) = (term657 c' _69078 t).
Proof. exact (@lem5280693 (real_le c' _69078) (term617 _69078 t)). Qed.
Lemma lem5280699 (_69078 : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term657 c' _69078 t.
Proof. exact (EQ_MP (@lem5280696 c' _69078 t) (@lem5279055 _69078 s c' t h1)). Qed.
Lemma lem5280700 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term160 s c' t) : term658 x c' t.
Proof. exact (@lem5280699 (x t c') s c' t h1). Qed.
Lemma lem5280703 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term589 x c' t.
Proof. exact (@lem5280700 x s c' t h4 (@lem5280691 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280704 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term590 x c' t.
Proof. exact (fun h0 : term536 x c' t => @lem5280703 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5280706 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280707 (x : type1021) (c' : real) (t : real -> Prop) : (term590 x c' t) = (term589 x c' t).
Proof. exact (@lem5280706 (term536 x c' t)). Qed.
Lemma lem5280708 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term589 x c' t.
Proof. exact (EQ_MP (@lem5280707 x c' t) (@lem5280704 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280726 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280727 (x : type1021) (_69075 : real) (_69076 : real) (_69074 : real -> Prop) : (term659 _69075 x _69076 _69074) = (term660 x _69075 _69076 _69074).
Proof. exact (@lem5280726 (term536 x _69076 _69074) (term537 x _69074 _69075) (term108 _69076 _69074)). Qed.
Lemma lem5280741 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5280742 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term637 x _69075 _69076 _69074) = (term661 _69076 x _69074 _69075).
Proof. exact (@lem5280741 (term108 _69076 _69074) (term537 x _69074 _69075)). Qed.
Lemma lem5280748 (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term662 x _69076 _69074) = (term662 x _69076 _69074).
Proof. exact (eq_refl (term662 x _69076 _69074)). Qed.
Lemma lem5280749 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term660 x _69075 _69076 _69074) = (term663 _69076 x _69074 _69075).
Proof. exact (MK_COMB (@lem5280748 x _69076 _69074) (@lem5280742 _69076 x _69074 _69075)). Qed.
Lemma lem5280760 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term659 _69075 x _69076 _69074) = (term663 _69076 x _69074 _69075).
Proof. exact (TRANS (@lem5280727 x _69075 _69076 _69074) (@lem5280749 _69076 x _69074 _69075)). Qed.
Lemma lem5280761 (_69074 : real -> Prop) : (term289 _69074) = (term289 _69074).
Proof. exact (eq_refl (term289 _69074)). Qed.
Lemma lem5280762 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term582 _69075 x _69076 _69074) = (term664 _69076 x _69074 _69075).
Proof. exact (MK_COMB (@lem5280761 _69074) (@lem5280760 _69076 x _69074 _69075)). Qed.
Lemma lem5280773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5280774 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term665 _69075 x _69076 _69074) = (term666 _69076 x _69074 _69075).
Proof. exact (MK_COMB (@lem5280773) (@lem5280762 _69076 x _69074 _69075)). Qed.
Lemma lem5280778 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280779 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term667 _69075 x _69076 _69074) = (term668 _69075 x _69076 _69074).
Proof. exact (@lem5280778 (_69074 = (@EMPTY real)) (term108 _69076 _69074) (term669 _69075 x _69076 _69074)). Qed.
Lemma lem5280805 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5280806 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term669 _69075 x _69076 _69074) = (term670 _69076 x _69074 _69075).
Proof. exact (@lem5280805 (term536 x _69076 _69074) (term537 x _69074 _69075)). Qed.
Lemma lem5280812 (_69076 : real) (_69074 : real -> Prop) : (term671 _69076 _69074) = (term671 _69076 _69074).
Proof. exact (eq_refl (term671 _69076 _69074)). Qed.
Lemma lem5280813 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term672 _69075 x _69076 _69074) = (term673 _69076 x _69074 _69075).
Proof. exact (MK_COMB (@lem5280812 _69076 _69074) (@lem5280806 _69076 x _69074 _69075)). Qed.
Lemma lem5280817 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5280818 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term673 _69076 x _69074 _69075) = (term663 _69076 x _69074 _69075).
Proof. exact (@lem5280817 (term536 x _69076 _69074) (term108 _69076 _69074) (term537 x _69074 _69075)). Qed.
Lemma lem5280834 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term672 _69075 x _69076 _69074) = (term663 _69076 x _69074 _69075).
Proof. exact (TRANS (@lem5280813 _69076 x _69074 _69075) (@lem5280818 _69076 x _69074 _69075)). Qed.
Lemma lem5280835 (_69074 : real -> Prop) : (term289 _69074) = (term289 _69074).
Proof. exact (eq_refl (term289 _69074)). Qed.
Lemma lem5280836 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term668 _69075 x _69076 _69074) = (term664 _69076 x _69074 _69075).
Proof. exact (MK_COMB (@lem5280835 _69074) (@lem5280834 _69076 x _69074 _69075)). Qed.
Lemma lem5280847 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term667 _69075 x _69076 _69074) = (term664 _69076 x _69074 _69075).
Proof. exact (TRANS (@lem5280779 _69075 x _69076 _69074) (@lem5280836 _69076 x _69074 _69075)). Qed.
Lemma lem5280848 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : ((term582 _69075 x _69076 _69074) = (term667 _69075 x _69076 _69074)) = ((term664 _69076 x _69074 _69075) = (term664 _69076 x _69074 _69075)).
Proof. exact (MK_COMB (@lem5280774 _69076 x _69074 _69075) (@lem5280847 _69076 x _69074 _69075)). Qed.
Lemma lem5280850 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5280851 (x : Prop) : (x = x) = True.
Proof. exact (@lem5280850 Prop x). Qed.
Lemma lem5280852 (_69076 : real) (x : type1021) (_69074 : real -> Prop) (_69075 : real) : ((term664 _69076 x _69074 _69075) = (term664 _69076 x _69074 _69075)) = True.
Proof. exact (@lem5280851 (term664 _69076 x _69074 _69075)). Qed.
Lemma lem5280853 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : ((term582 _69075 x _69076 _69074) = (term667 _69075 x _69076 _69074)) = True.
Proof. exact (TRANS (@lem5280848 _69076 x _69074 _69075) (@lem5280852 _69076 x _69074 _69075)). Qed.
Lemma lem5280854 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : True = ((term582 _69075 x _69076 _69074) = (term667 _69075 x _69076 _69074)).
Proof. exact (SYM (@lem5280853 _69075 x _69076 _69074)). Qed.
Lemma lem5280855 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term582 _69075 x _69076 _69074) = (term667 _69075 x _69076 _69074).
Proof. exact (EQ_MP (@lem5280854 _69075 x _69076 _69074) (@lem0)). Qed.
Lemma lem5280856 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term667 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5280855 _69075 x _69076 _69074) (@lem5279121 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5280858 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5280859 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term667 _69075 x _69076 _69074) = (term674 _69075 x _69076 _69074).
Proof. exact (@lem5280858 (term675 _69075 x _69076 _69074) (term108 _69076 _69074)). Qed.
Lemma lem5280861 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280862 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term676 _69075 x _69076 _69074) = (term677 _69075 x _69076 _69074).
Proof. exact (@lem5280861 (_69074 = (@EMPTY real)) (term669 _69075 x _69076 _69074)). Qed.
Lemma lem5280864 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5280865 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term678 _69075 x _69076 _69074) = (term679 _69075 x _69076 _69074).
Proof. exact (@lem5280864 (term537 x _69074 _69075) (term536 x _69076 _69074)). Qed.
Lemma lem5280867 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5280868 (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term645 x _69074 _69075) = (term625 x _69074 _69075).
Proof. exact (@lem5280867 (term625 x _69074 _69075)). Qed.
Lemma lem5280869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5280870 (x : type1021) (_69074 : real -> Prop) (_69075 : real) : (term646 x _69074 _69075) = (term647 x _69074 _69075).
Proof. exact (MK_COMB (@lem5280869) (@lem5280868 x _69074 _69075)). Qed.
Lemma lem5280871 (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term589 x _69076 _69074) = (term589 x _69076 _69074).
Proof. exact (eq_refl (term589 x _69076 _69074)). Qed.
Lemma lem5280872 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term679 _69075 x _69076 _69074) = (term680 _69075 x _69076 _69074).
Proof. exact (MK_COMB (@lem5280870 x _69074 _69075) (@lem5280871 x _69076 _69074)). Qed.
Lemma lem5280873 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term678 _69075 x _69076 _69074) = (term680 _69075 x _69076 _69074).
Proof. exact (TRANS (@lem5280865 _69075 x _69076 _69074) (@lem5280872 _69075 x _69076 _69074)). Qed.
Lemma lem5280874 (_69074 : real -> Prop) : (term118 _69074) = (term118 _69074).
Proof. exact (eq_refl (term118 _69074)). Qed.
Lemma lem5280875 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term677 _69075 x _69076 _69074) = (term681 _69075 x _69076 _69074).
Proof. exact (MK_COMB (@lem5280874 _69074) (@lem5280873 _69075 x _69076 _69074)). Qed.
Lemma lem5280876 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term676 _69075 x _69076 _69074) = (term681 _69075 x _69076 _69074).
Proof. exact (TRANS (@lem5280862 _69075 x _69076 _69074) (@lem5280875 _69075 x _69076 _69074)). Qed.
Lemma lem5280877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5280878 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term682 _69075 x _69076 _69074) = (term683 _69075 x _69076 _69074).
Proof. exact (MK_COMB (@lem5280877) (@lem5280876 _69075 x _69076 _69074)). Qed.
Lemma lem5280879 (_69076 : real) (_69074 : real -> Prop) : (term108 _69076 _69074) = (term108 _69076 _69074).
Proof. exact (eq_refl (term108 _69076 _69074)). Qed.
Lemma lem5280880 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term674 _69075 x _69076 _69074) = (term684 _69075 x _69076 _69074).
Proof. exact (MK_COMB (@lem5280878 _69075 x _69076 _69074) (@lem5280879 _69076 _69074)). Qed.
Lemma lem5280881 (_69075 : real) (x : type1021) (_69076 : real) (_69074 : real -> Prop) : (term667 _69075 x _69076 _69074) = (term684 _69075 x _69076 _69074).
Proof. exact (TRANS (@lem5280859 _69075 x _69076 _69074) (@lem5280880 _69075 x _69076 _69074)). Qed.
Lemma lem5280883 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term685 x c' t.
Proof. exact (conj (@lem5280431 x s c' t h1 h2 h3 h4) (@lem5280708 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280884 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term686 x c' t.
Proof. exact (conj (@lem5280236 t h2) (@lem5280883 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280886 (_69075 : real) (_69076 : real) (_69074 : real -> Prop) (x : type1021) (h1 : term444 x) : term684 _69075 x _69076 _69074.
Proof. exact (EQ_MP (@lem5280881 _69075 x _69076 _69074) (@lem5280856 _69075 _69076 _69074 x h1)). Qed.
Lemma lem5280887 (c' : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term687 x c' t.
Proof. exact (@lem5280886 c' c' t x h1). Qed.
Lemma lem5280890 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term108 c' t.
Proof. exact (@lem5280887 c' t x h1 (@lem5280884 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280891 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term160 s c' t) : term688 c' t.
Proof. exact (fun h0 : term567 c' t => @lem5280890 x s c' t h1 h2 h0 h3). Qed.
Lemma lem5280893 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280894 (c' : real) (t : real -> Prop) : (term688 c' t) = (term108 c' t).
Proof. exact (@lem5280893 (term108 c' t)). Qed.
Lemma lem5280895 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term160 s c' t) : term108 c' t.
Proof. exact (EQ_MP (@lem5280894 c' t) (@lem5280891 x s c' t h1 h2 h3)). Qed.
Lemma lem5280898 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5280900 (c' : real) (t : real -> Prop) : (term567 c' t) = (term689 c' t).
Proof. exact (@lem5280898 (term108 c' t)). Qed.
Lemma lem5280903 (c' : real) (t : real -> Prop) (h1 : term567 c' t) : term689 c' t.
Proof. exact (EQ_MP (@lem5280900 c' t) (@lem5279057 c' t h1)). Qed.
Lemma lem5280906 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (@lem5280903 c' t h3 (@lem5280895 x s c' t h1 h2 h4)). Qed.
Lemma lem5280907 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : term690.
Proof. exact (fun h0 : ~ False => @lem5280906 x s c' t h1 h2 h3 h4). Qed.
Lemma lem5280909 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280910 : term690 = False.
Proof. exact (@lem5280909 False). Qed.
Lemma lem5280911 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5280910) (@lem5280907 x s c' t h1 h2 h3 h4)). Qed.
Lemma lem5280978 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term108 c' s.
Proof. exact (proj1 (@lem5277568 x' s c' t h1)). Qed.
Lemma lem5280979 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term688 c' s.
Proof. exact (fun h0 : term567 c' s => @lem5280978 x' s c' t h1). Qed.
Lemma lem5280981 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5280982 (c' : real) (s : real -> Prop) : (term688 c' s) = (term108 c' s).
Proof. exact (@lem5280981 (term108 c' s)). Qed.
Lemma lem5280983 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term108 c' s.
Proof. exact (EQ_MP (@lem5280982 c' s) (@lem5280979 x' s c' t h1)). Qed.
Lemma lem5280985 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5280986 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5280985 s h1). Qed.
Lemma lem5280988 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280989 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5280988 (s = (@EMPTY real))). Qed.
Lemma lem5280990 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5280989 s) (@lem5280986 s h1)). Qed.
Lemma lem5280992 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5280993 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5280992 s h1). Qed.
Lemma lem5280995 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5280996 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5280995 (s = (@EMPTY real))). Qed.
Lemma lem5280997 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5280996 s) (@lem5280993 s h1)). Qed.
Lemma lem5280999 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : @IN real x' s.
Proof. exact (proj1 (@lem5277572 s c' x' h1)). Qed.
Lemma lem5281000 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : term691 x' s.
Proof. exact (fun h0 : term617 x' s => @lem5280999 s c' x' h1). Qed.
Lemma lem5281002 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281003 (x' : real) (s : real -> Prop) : (term691 x' s) = (@IN real x' s).
Proof. exact (@lem5281002 (@IN real x' s)). Qed.
Lemma lem5281004 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : @IN real x' s.
Proof. exact (EQ_MP (@lem5281003 x' s) (@lem5281000 s c' x' h1)). Qed.
Lemma lem5281007 (s : real -> Prop) (x' : real) (h1 : term692 s x') : term692 s x'.
Proof. exact (h1). Qed.
Lemma lem5281008 (s : real -> Prop) (x' : real) (h1 : term692 s x') : term693 s x'.
Proof. exact (fun h0 : term294 s x' => @lem5281007 s x' h1). Qed.
Lemma lem5281010 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5281011 (s : real -> Prop) (x' : real) : (term693 s x') = (term692 s x').
Proof. exact (@lem5281010 (term294 s x')). Qed.
Lemma lem5281012 (s : real -> Prop) (x' : real) (h1 : term692 s x') : term692 s x'.
Proof. exact (EQ_MP (@lem5281011 s x') (@lem5281008 s x' h1)). Qed.
Lemma lem5281040 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281041 (_69086 : real) (_69084 : real -> Prop) : (term293 _69084 _69086) = (term694 _69086 _69084).
Proof. exact (@lem5281040 (term294 _69084 _69086) (term617 _69086 _69084)). Qed.
Lemma lem5281047 (x : type1021) (_69085 : real) (_69084 : real -> Prop) : (term662 x _69085 _69084) = (term662 x _69085 _69084).
Proof. exact (eq_refl (term662 x _69085 _69084)). Qed.
Lemma lem5281048 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term695 x _69085 _69084 _69086) = (term696 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281047 x _69085 _69084) (@lem5281041 _69086 _69084)). Qed.
Lemma lem5281059 (_69084 : real -> Prop) : (term289 _69084) = (term289 _69084).
Proof. exact (eq_refl (term289 _69084)). Qed.
Lemma lem5281060 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term585 x _69085 _69084 _69086) = (term697 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281059 _69084) (@lem5281048 x _69085 _69086 _69084)). Qed.
Lemma lem5281071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5281072 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term698 x _69085 _69084 _69086) = (term699 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281071) (@lem5281060 x _69085 _69086 _69084)). Qed.
Lemma lem5281076 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281077 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term700 x _69085 _69084 _69086) = (term585 x _69085 _69084 _69086).
Proof. exact (@lem5281076 (_69084 = (@EMPTY real)) (term536 x _69085 _69084) (term293 _69084 _69086)). Qed.
Lemma lem5281103 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281104 (_69086 : real) (_69084 : real -> Prop) : (term293 _69084 _69086) = (term694 _69086 _69084).
Proof. exact (@lem5281103 (term294 _69084 _69086) (term617 _69086 _69084)). Qed.
Lemma lem5281110 (x : type1021) (_69085 : real) (_69084 : real -> Prop) : (term662 x _69085 _69084) = (term662 x _69085 _69084).
Proof. exact (eq_refl (term662 x _69085 _69084)). Qed.
Lemma lem5281111 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term695 x _69085 _69084 _69086) = (term696 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281110 x _69085 _69084) (@lem5281104 _69086 _69084)). Qed.
Lemma lem5281122 (_69084 : real -> Prop) : (term289 _69084) = (term289 _69084).
Proof. exact (eq_refl (term289 _69084)). Qed.
Lemma lem5281123 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term585 x _69085 _69084 _69086) = (term697 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281122 _69084) (@lem5281111 x _69085 _69086 _69084)). Qed.
Lemma lem5281134 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term700 x _69085 _69084 _69086) = (term697 x _69085 _69086 _69084).
Proof. exact (TRANS (@lem5281077 x _69085 _69084 _69086) (@lem5281123 x _69085 _69086 _69084)). Qed.
Lemma lem5281135 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : ((term585 x _69085 _69084 _69086) = (term700 x _69085 _69084 _69086)) = ((term697 x _69085 _69086 _69084) = (term697 x _69085 _69086 _69084)).
Proof. exact (MK_COMB (@lem5281072 x _69085 _69086 _69084) (@lem5281134 x _69085 _69086 _69084)). Qed.
Lemma lem5281137 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5281138 (x : Prop) : (x = x) = True.
Proof. exact (@lem5281137 Prop x). Qed.
Lemma lem5281139 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : ((term697 x _69085 _69086 _69084) = (term697 x _69085 _69086 _69084)) = True.
Proof. exact (@lem5281138 (term697 x _69085 _69086 _69084)). Qed.
Lemma lem5281140 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : ((term585 x _69085 _69084 _69086) = (term700 x _69085 _69084 _69086)) = True.
Proof. exact (TRANS (@lem5281135 x _69085 _69086 _69084) (@lem5281139 x _69085 _69086 _69084)). Qed.
Lemma lem5281141 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : True = ((term585 x _69085 _69084 _69086) = (term700 x _69085 _69084 _69086)).
Proof. exact (SYM (@lem5281140 x _69085 _69084 _69086)). Qed.
Lemma lem5281142 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term585 x _69085 _69084 _69086) = (term700 x _69085 _69084 _69086).
Proof. exact (EQ_MP (@lem5281141 x _69085 _69084 _69086) (@lem0)). Qed.
Lemma lem5281143 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term700 x _69085 _69084 _69086.
Proof. exact (EQ_MP (@lem5281142 x _69085 _69084 _69086) (@lem5279269 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5281145 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5281146 (_69086 : real) (x : type1021) (_69085 : real) (_69084 : real -> Prop) : (term700 x _69085 _69084 _69086) = (term701 _69086 x _69085 _69084).
Proof. exact (@lem5281145 (term702 _69084 _69086) (term536 x _69085 _69084)). Qed.
Lemma lem5281148 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5281149 (_69084 : real -> Prop) (_69086 : real) : (term703 _69084 _69086) = (term704 _69084 _69086).
Proof. exact (@lem5281148 (_69084 = (@EMPTY real)) (term293 _69084 _69086)). Qed.
Lemma lem5281151 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5281152 (_69084 : real -> Prop) (_69086 : real) : (term705 _69084 _69086) = (term706 _69084 _69086).
Proof. exact (@lem5281151 (term617 _69086 _69084) (term294 _69084 _69086)). Qed.
Lemma lem5281154 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281155 (_69086 : real) (_69084 : real -> Prop) : (term622 _69086 _69084) = (@IN real _69086 _69084).
Proof. exact (@lem5281154 (@IN real _69086 _69084)). Qed.
Lemma lem5281156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5281157 (_69086 : real) (_69084 : real -> Prop) : (term707 _69086 _69084) = (term708 _69086 _69084).
Proof. exact (MK_COMB (@lem5281156) (@lem5281155 _69086 _69084)). Qed.
Lemma lem5281158 (_69084 : real -> Prop) (_69086 : real) : (term692 _69084 _69086) = (term692 _69084 _69086).
Proof. exact (eq_refl (term692 _69084 _69086)). Qed.
Lemma lem5281159 (_69084 : real -> Prop) (_69086 : real) : (term706 _69084 _69086) = (term709 _69084 _69086).
Proof. exact (MK_COMB (@lem5281157 _69086 _69084) (@lem5281158 _69084 _69086)). Qed.
Lemma lem5281160 (_69084 : real -> Prop) (_69086 : real) : (term705 _69084 _69086) = (term709 _69084 _69086).
Proof. exact (TRANS (@lem5281152 _69084 _69086) (@lem5281159 _69084 _69086)). Qed.
Lemma lem5281161 (_69084 : real -> Prop) : (term118 _69084) = (term118 _69084).
Proof. exact (eq_refl (term118 _69084)). Qed.
Lemma lem5281162 (_69084 : real -> Prop) (_69086 : real) : (term704 _69084 _69086) = (term710 _69084 _69086).
Proof. exact (MK_COMB (@lem5281161 _69084) (@lem5281160 _69084 _69086)). Qed.
Lemma lem5281163 (_69084 : real -> Prop) (_69086 : real) : (term703 _69084 _69086) = (term710 _69084 _69086).
Proof. exact (TRANS (@lem5281149 _69084 _69086) (@lem5281162 _69084 _69086)). Qed.
Lemma lem5281164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5281165 (_69084 : real -> Prop) (_69086 : real) : (term711 _69084 _69086) = (term712 _69084 _69086).
Proof. exact (MK_COMB (@lem5281164) (@lem5281163 _69084 _69086)). Qed.
Lemma lem5281166 (x : type1021) (_69085 : real) (_69084 : real -> Prop) : (term536 x _69085 _69084) = (term536 x _69085 _69084).
Proof. exact (eq_refl (term536 x _69085 _69084)). Qed.
Lemma lem5281167 (_69086 : real) (x : type1021) (_69085 : real) (_69084 : real -> Prop) : (term701 _69086 x _69085 _69084) = (term713 _69086 x _69085 _69084).
Proof. exact (MK_COMB (@lem5281165 _69084 _69086) (@lem5281166 x _69085 _69084)). Qed.
Lemma lem5281168 (_69086 : real) (x : type1021) (_69085 : real) (_69084 : real -> Prop) : (term700 x _69085 _69084 _69086) = (term713 _69086 x _69085 _69084).
Proof. exact (TRANS (@lem5281146 _69086 x _69085 _69084) (@lem5281167 _69086 x _69085 _69084)). Qed.
Lemma lem5281170 (s : real -> Prop) (c' : real) (x' : real) (h1 : term692 s x') (h2 : term134 s c' x') : term709 s x'.
Proof. exact (conj (@lem5281004 s c' x' h2) (@lem5281012 s x' h1)). Qed.
Lemma lem5281171 (s : real -> Prop) (c' : real) (x' : real) (h1 : term31 s) (h2 : term692 s x') (h3 : term134 s c' x') : term710 s x'.
Proof. exact (conj (@lem5280997 s h1) (@lem5281170 s c' x' h2 h3)). Qed.
Lemma lem5281173 (_69086 : real) (_69085 : real) (_69084 : real -> Prop) (x : type1021) (h1 : term444 x) : term713 _69086 x _69085 _69084.
Proof. exact (EQ_MP (@lem5281168 _69086 x _69085 _69084) (@lem5281143 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5281174 (x' : real) (_69085 : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term713 x' x _69085 s.
Proof. exact (@lem5281173 x' _69085 s x h1). Qed.
Lemma lem5281177 (_69085 : real) (x : type1021) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 s x') (h4 : term134 s c' x') : term536 x _69085 s.
Proof. exact (@lem5281174 x' _69085 s x h1 (@lem5281171 s c' x' h2 h3 h4)). Qed.
Lemma lem5281178 (b : real) (x : type1021) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 s x') (h4 : term134 s c' x') : term536 x b s.
Proof. exact (@lem5281177 b x s c' x' h1 h2 h3 h4). Qed.
Lemma lem5281179 (b : real) (x : type1021) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 s x') (h4 : term134 s c' x') : term614 x b s.
Proof. exact (fun h0 : term589 x b s => @lem5281178 b x s c' x' h1 h2 h3 h4). Qed.
Lemma lem5281181 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281182 (x : type1021) (b : real) (s : real -> Prop) : (term614 x b s) = (term536 x b s).
Proof. exact (@lem5281181 (term536 x b s)). Qed.
Lemma lem5281183 (b : real) (x : type1021) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 s x') (h4 : term134 s c' x') : term536 x b s.
Proof. exact (EQ_MP (@lem5281182 x b s) (@lem5281179 b x s c' x' h1 h2 h3 h4)). Qed.
Lemma lem5281189 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281190 (b : real) (_69079 : real) (s : real -> Prop) : (term130 s b _69079) = (term616 b _69079 s).
Proof. exact (@lem5281189 (real_le b _69079) (term617 _69079 s)). Qed.
Lemma lem5281196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5281197 (b : real) (_69079 : real) (s : real -> Prop) : (term618 s b _69079) = (term619 b _69079 s).
Proof. exact (MK_COMB (@lem5281196) (@lem5281190 b _69079 s)). Qed.
Lemma lem5281203 (b : real) (_69079 : real) (s : real -> Prop) : (term616 b _69079 s) = (term616 b _69079 s).
Proof. exact (eq_refl (term616 b _69079 s)). Qed.
Lemma lem5281204 (b : real) (_69079 : real) (s : real -> Prop) : ((term130 s b _69079) = (term616 b _69079 s)) = ((term616 b _69079 s) = (term616 b _69079 s)).
Proof. exact (MK_COMB (@lem5281197 b _69079 s) (@lem5281203 b _69079 s)). Qed.
Lemma lem5281206 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5281207 (x : Prop) : (x = x) = True.
Proof. exact (@lem5281206 Prop x). Qed.
Lemma lem5281208 (b : real) (_69079 : real) (s : real -> Prop) : ((term616 b _69079 s) = (term616 b _69079 s)) = True.
Proof. exact (@lem5281207 (term616 b _69079 s)). Qed.
Lemma lem5281209 (b : real) (_69079 : real) (s : real -> Prop) : ((term130 s b _69079) = (term616 b _69079 s)) = True.
Proof. exact (TRANS (@lem5281204 b _69079 s) (@lem5281208 b _69079 s)). Qed.
Lemma lem5281210 (b : real) (_69079 : real) (s : real -> Prop) : True = ((term130 s b _69079) = (term616 b _69079 s)).
Proof. exact (SYM (@lem5281209 b _69079 s)). Qed.
Lemma lem5281211 (b : real) (_69079 : real) (s : real -> Prop) : (term130 s b _69079) = (term616 b _69079 s).
Proof. exact (EQ_MP (@lem5281210 b _69079 s) (@lem0)). Qed.
Lemma lem5281212 (_69079 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term616 b _69079 s.
Proof. exact (EQ_MP (@lem5281211 b _69079 s) (@lem5279163 _69079 s b h1)). Qed.
Lemma lem5281214 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5281215 (s : real -> Prop) (b : real) (_69079 : real) : (term616 b _69079 s) = (term620 s b _69079).
Proof. exact (@lem5281214 (term617 _69079 s) (real_le b _69079)). Qed.
Lemma lem5281217 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281218 (_69079 : real) (s : real -> Prop) : (term622 _69079 s) = (@IN real _69079 s).
Proof. exact (@lem5281217 (@IN real _69079 s)). Qed.
Lemma lem5281219 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5281220 (_69079 : real) (s : real -> Prop) : (term623 _69079 s) = (term51 _69079 s).
Proof. exact (MK_COMB (@lem5281219) (@lem5281218 _69079 s)). Qed.
Lemma lem5281221 (b : real) (_69079 : real) : (real_le b _69079) = (real_le b _69079).
Proof. exact (eq_refl (real_le b _69079)). Qed.
Lemma lem5281222 (s : real -> Prop) (b : real) (_69079 : real) : (term620 s b _69079) = (term53 s b _69079).
Proof. exact (MK_COMB (@lem5281220 _69079 s) (@lem5281221 b _69079)). Qed.
Lemma lem5281223 (s : real -> Prop) (b : real) (_69079 : real) : (term616 b _69079 s) = (term53 s b _69079).
Proof. exact (TRANS (@lem5281215 s b _69079) (@lem5281222 s b _69079)). Qed.
Lemma lem5281226 (_69079 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term53 s b _69079.
Proof. exact (EQ_MP (@lem5281223 s b _69079) (@lem5281212 _69079 s b h1)). Qed.
Lemma lem5281227 (x : type1021) (s : real -> Prop) (b : real) (h1 : term34 s b) : term624 x s b.
Proof. exact (@lem5281226 (x s b) s b h1). Qed.
Lemma lem5281230 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 s x') (h5 : term134 s c' x') : term625 x s b.
Proof. exact (@lem5281227 x s b h2 (@lem5281183 b x s c' x' h1 h3 h4 h5)). Qed.
Lemma lem5281231 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 s x') (h5 : term134 s c' x') : term626 x s b.
Proof. exact (fun h0 : term537 x s b => @lem5281230 x b s c' x' h1 h2 h3 h4 h5). Qed.
Lemma lem5281233 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281234 (x : type1021) (s : real -> Prop) (b : real) : (term626 x s b) = (term625 x s b).
Proof. exact (@lem5281233 (term625 x s b)). Qed.
Lemma lem5281235 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 s x') (h5 : term134 s c' x') : term625 x s b.
Proof. exact (EQ_MP (@lem5281234 x s b) (@lem5281231 x b s c' x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5281237 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : @IN real x' s.
Proof. exact (proj1 (@lem5277572 s c' x' h1)). Qed.
Lemma lem5281238 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : term691 x' s.
Proof. exact (fun h0 : term617 x' s => @lem5281237 s c' x' h1). Qed.
Lemma lem5281240 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281241 (x' : real) (s : real -> Prop) : (term691 x' s) = (@IN real x' s).
Proof. exact (@lem5281240 (@IN real x' s)). Qed.
Lemma lem5281242 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : @IN real x' s.
Proof. exact (EQ_MP (@lem5281241 x' s) (@lem5281238 s c' x' h1)). Qed.
Lemma lem5281260 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281261 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term714 x _69085 _69084 _69086) = (term715 x _69085 _69084 _69086).
Proof. exact (@lem5281260 (term617 _69086 _69084) (term537 x _69084 _69085) (term294 _69084 _69086)). Qed.
Lemma lem5281275 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281276 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term716 x _69085 _69084 _69086) = (term717 _69086 x _69084 _69085).
Proof. exact (@lem5281275 (term294 _69084 _69086) (term537 x _69084 _69085)). Qed.
Lemma lem5281282 (_69086 : real) (_69084 : real -> Prop) : (term718 _69086 _69084) = (term718 _69086 _69084).
Proof. exact (eq_refl (term718 _69086 _69084)). Qed.
Lemma lem5281283 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term715 x _69085 _69084 _69086) = (term719 _69086 x _69084 _69085).
Proof. exact (MK_COMB (@lem5281282 _69086 _69084) (@lem5281276 _69086 x _69084 _69085)). Qed.
Lemma lem5281287 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281288 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term719 _69086 x _69084 _69085) = (term720 _69086 x _69084 _69085).
Proof. exact (@lem5281287 (term294 _69084 _69086) (term617 _69086 _69084) (term537 x _69084 _69085)). Qed.
Lemma lem5281304 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term715 x _69085 _69084 _69086) = (term720 _69086 x _69084 _69085).
Proof. exact (TRANS (@lem5281283 _69086 x _69084 _69085) (@lem5281288 _69086 x _69084 _69085)). Qed.
Lemma lem5281305 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term714 x _69085 _69084 _69086) = (term720 _69086 x _69084 _69085).
Proof. exact (TRANS (@lem5281261 x _69085 _69084 _69086) (@lem5281304 _69086 x _69084 _69085)). Qed.
Lemma lem5281306 (_69084 : real -> Prop) : (term289 _69084) = (term289 _69084).
Proof. exact (eq_refl (term289 _69084)). Qed.
Lemma lem5281307 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term586 x _69085 _69084 _69086) = (term721 _69086 x _69084 _69085).
Proof. exact (MK_COMB (@lem5281306 _69084) (@lem5281305 _69086 x _69084 _69085)). Qed.
Lemma lem5281318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5281319 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term722 x _69085 _69084 _69086) = (term723 _69086 x _69084 _69085).
Proof. exact (MK_COMB (@lem5281318) (@lem5281307 _69086 x _69084 _69085)). Qed.
Lemma lem5281323 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281324 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term724 x _69085 _69086 _69084) = (term725 x _69085 _69086 _69084).
Proof. exact (@lem5281323 (_69084 = (@EMPTY real)) (term294 _69084 _69086) (term726 x _69085 _69086 _69084)). Qed.
Lemma lem5281350 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281351 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term726 x _69085 _69086 _69084) = (term727 _69086 x _69084 _69085).
Proof. exact (@lem5281350 (term617 _69086 _69084) (term537 x _69084 _69085)). Qed.
Lemma lem5281357 (_69084 : real -> Prop) (_69086 : real) : (term728 _69084 _69086) = (term728 _69084 _69086).
Proof. exact (eq_refl (term728 _69084 _69086)). Qed.
Lemma lem5281358 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term729 x _69085 _69086 _69084) = (term720 _69086 x _69084 _69085).
Proof. exact (MK_COMB (@lem5281357 _69084 _69086) (@lem5281351 _69086 x _69084 _69085)). Qed.
Lemma lem5281369 (_69084 : real -> Prop) : (term289 _69084) = (term289 _69084).
Proof. exact (eq_refl (term289 _69084)). Qed.
Lemma lem5281370 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term725 x _69085 _69086 _69084) = (term721 _69086 x _69084 _69085).
Proof. exact (MK_COMB (@lem5281369 _69084) (@lem5281358 _69086 x _69084 _69085)). Qed.
Lemma lem5281381 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term724 x _69085 _69086 _69084) = (term721 _69086 x _69084 _69085).
Proof. exact (TRANS (@lem5281324 x _69085 _69086 _69084) (@lem5281370 _69086 x _69084 _69085)). Qed.
Lemma lem5281382 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : ((term586 x _69085 _69084 _69086) = (term724 x _69085 _69086 _69084)) = ((term721 _69086 x _69084 _69085) = (term721 _69086 x _69084 _69085)).
Proof. exact (MK_COMB (@lem5281319 _69086 x _69084 _69085) (@lem5281381 _69086 x _69084 _69085)). Qed.
Lemma lem5281384 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5281385 (x : Prop) : (x = x) = True.
Proof. exact (@lem5281384 Prop x). Qed.
Lemma lem5281386 (_69086 : real) (x : type1021) (_69084 : real -> Prop) (_69085 : real) : ((term721 _69086 x _69084 _69085) = (term721 _69086 x _69084 _69085)) = True.
Proof. exact (@lem5281385 (term721 _69086 x _69084 _69085)). Qed.
Lemma lem5281387 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : ((term586 x _69085 _69084 _69086) = (term724 x _69085 _69086 _69084)) = True.
Proof. exact (TRANS (@lem5281382 _69086 x _69084 _69085) (@lem5281386 _69086 x _69084 _69085)). Qed.
Lemma lem5281388 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : True = ((term586 x _69085 _69084 _69086) = (term724 x _69085 _69086 _69084)).
Proof. exact (SYM (@lem5281387 x _69085 _69086 _69084)). Qed.
Lemma lem5281389 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term586 x _69085 _69084 _69086) = (term724 x _69085 _69086 _69084).
Proof. exact (EQ_MP (@lem5281388 x _69085 _69086 _69084) (@lem0)). Qed.
Lemma lem5281390 (_69085 : real) (_69086 : real) (_69084 : real -> Prop) (x : type1021) (h1 : term444 x) : term724 x _69085 _69086 _69084.
Proof. exact (EQ_MP (@lem5281389 x _69085 _69086 _69084) (@lem5279285 _69085 _69084 _69086 x h1)). Qed.
Lemma lem5281392 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5281393 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term724 x _69085 _69086 _69084) = (term730 x _69085 _69084 _69086).
Proof. exact (@lem5281392 (term731 x _69085 _69086 _69084) (term294 _69084 _69086)). Qed.
Lemma lem5281395 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5281396 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term732 x _69085 _69086 _69084) = (term733 x _69085 _69086 _69084).
Proof. exact (@lem5281395 (_69084 = (@EMPTY real)) (term726 x _69085 _69086 _69084)). Qed.
Lemma lem5281398 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5281399 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term734 x _69085 _69086 _69084) = (term735 x _69085 _69086 _69084).
Proof. exact (@lem5281398 (term537 x _69084 _69085) (term617 _69086 _69084)). Qed.
Lemma lem5281401 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281402 (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term645 x _69084 _69085) = (term625 x _69084 _69085).
Proof. exact (@lem5281401 (term625 x _69084 _69085)). Qed.
Lemma lem5281403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5281404 (x : type1021) (_69084 : real -> Prop) (_69085 : real) : (term646 x _69084 _69085) = (term647 x _69084 _69085).
Proof. exact (MK_COMB (@lem5281403) (@lem5281402 x _69084 _69085)). Qed.
Lemma lem5281406 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281407 (_69086 : real) (_69084 : real -> Prop) : (term622 _69086 _69084) = (@IN real _69086 _69084).
Proof. exact (@lem5281406 (@IN real _69086 _69084)). Qed.
Lemma lem5281408 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term735 x _69085 _69086 _69084) = (term736 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281404 x _69084 _69085) (@lem5281407 _69086 _69084)). Qed.
Lemma lem5281409 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term734 x _69085 _69086 _69084) = (term736 x _69085 _69086 _69084).
Proof. exact (TRANS (@lem5281399 x _69085 _69086 _69084) (@lem5281408 x _69085 _69086 _69084)). Qed.
Lemma lem5281410 (_69084 : real -> Prop) : (term118 _69084) = (term118 _69084).
Proof. exact (eq_refl (term118 _69084)). Qed.
Lemma lem5281411 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term733 x _69085 _69086 _69084) = (term737 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281410 _69084) (@lem5281409 x _69085 _69086 _69084)). Qed.
Lemma lem5281412 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term732 x _69085 _69086 _69084) = (term737 x _69085 _69086 _69084).
Proof. exact (TRANS (@lem5281396 x _69085 _69086 _69084) (@lem5281411 x _69085 _69086 _69084)). Qed.
Lemma lem5281413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5281414 (x : type1021) (_69085 : real) (_69086 : real) (_69084 : real -> Prop) : (term738 x _69085 _69086 _69084) = (term739 x _69085 _69086 _69084).
Proof. exact (MK_COMB (@lem5281413) (@lem5281412 x _69085 _69086 _69084)). Qed.
Lemma lem5281415 (_69084 : real -> Prop) (_69086 : real) : (term294 _69084 _69086) = (term294 _69084 _69086).
Proof. exact (eq_refl (term294 _69084 _69086)). Qed.
Lemma lem5281416 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term730 x _69085 _69084 _69086) = (term740 x _69085 _69084 _69086).
Proof. exact (MK_COMB (@lem5281414 x _69085 _69086 _69084) (@lem5281415 _69084 _69086)). Qed.
Lemma lem5281417 (x : type1021) (_69085 : real) (_69084 : real -> Prop) (_69086 : real) : (term724 x _69085 _69086 _69084) = (term740 x _69085 _69084 _69086).
Proof. exact (TRANS (@lem5281393 x _69085 _69084 _69086) (@lem5281416 x _69085 _69084 _69086)). Qed.
Lemma lem5281419 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 s x') (h5 : term134 s c' x') : term736 x b x' s.
Proof. exact (conj (@lem5281235 x b s c' x' h1 h2 h3 h4 h5) (@lem5281242 s c' x' h5)). Qed.
Lemma lem5281420 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 s x') (h5 : term134 s c' x') : term737 x b x' s.
Proof. exact (conj (@lem5280990 s h3) (@lem5281419 x b s c' x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5281422 (_69085 : real) (_69084 : real -> Prop) (_69086 : real) (x : type1021) (h1 : term444 x) : term740 x _69085 _69084 _69086.
Proof. exact (EQ_MP (@lem5281417 x _69085 _69084 _69086) (@lem5281390 _69085 _69086 _69084 x h1)). Qed.
Lemma lem5281423 (b : real) (s : real -> Prop) (x' : real) (x : type1021) (h1 : term444 x) : term740 x b s x'.
Proof. exact (@lem5281422 b s x' x h1). Qed.
Lemma lem5281426 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 s x') (h5 : term134 s c' x') : term294 s x'.
Proof. exact (@lem5281423 b s x' x h1 (@lem5281420 x b s c' x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5281427 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term134 s c' x') : term741 s x'.
Proof. exact (fun h0 : term692 s x' => @lem5281426 x b s c' x' h1 h2 h3 h0 h4). Qed.
Lemma lem5281429 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281430 (s : real -> Prop) (x' : real) : (term741 s x') = (term294 s x').
Proof. exact (@lem5281429 (term294 s x')). Qed.
Lemma lem5281431 (x : type1021) (b : real) (s : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term134 s c' x') : term294 s x'.
Proof. exact (EQ_MP (@lem5281430 s x') (@lem5281427 x b s c' x' h1 h2 h3 h4)). Qed.
Lemma lem5281447 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281448 (_69081 : real) (_69082 : real) (_69083 : real) : (term742 _69082 _69081 _69083) = (term743 _69081 _69082 _69083).
Proof. exact (@lem5281447 (real_le _69081 _69083) (term584 _69082 _69083)). Qed.
Lemma lem5281454 (_69081 : real) (_69082 : real) : (term744 _69081 _69082) = (term744 _69081 _69082).
Proof. exact (eq_refl (term744 _69081 _69082)). Qed.
Lemma lem5281455 (_69081 : real) (_69082 : real) (_69083 : real) : (term583 _69082 _69081 _69083) = (term745 _69081 _69082 _69083).
Proof. exact (MK_COMB (@lem5281454 _69081 _69082) (@lem5281448 _69081 _69082 _69083)). Qed.
Lemma lem5281459 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281460 (_69081 : real) (_69082 : real) (_69083 : real) : (term745 _69081 _69082 _69083) = (term746 _69081 _69082 _69083).
Proof. exact (@lem5281459 (real_le _69081 _69083) (term584 _69081 _69082) (term584 _69082 _69083)). Qed.
Lemma lem5281476 (_69081 : real) (_69082 : real) (_69083 : real) : (term583 _69082 _69081 _69083) = (term746 _69081 _69082 _69083).
Proof. exact (TRANS (@lem5281455 _69081 _69082 _69083) (@lem5281460 _69081 _69082 _69083)). Qed.
Lemma lem5281477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5281478 (_69081 : real) (_69082 : real) (_69083 : real) : (term747 _69082 _69081 _69083) = (term748 _69081 _69082 _69083).
Proof. exact (MK_COMB (@lem5281477) (@lem5281476 _69081 _69082 _69083)). Qed.
Lemma lem5281494 (_69081 : real) (_69082 : real) (_69083 : real) : (term746 _69081 _69082 _69083) = (term746 _69081 _69082 _69083).
Proof. exact (eq_refl (term746 _69081 _69082 _69083)). Qed.
Lemma lem5281495 (_69081 : real) (_69082 : real) (_69083 : real) : ((term583 _69082 _69081 _69083) = (term746 _69081 _69082 _69083)) = ((term746 _69081 _69082 _69083) = (term746 _69081 _69082 _69083)).
Proof. exact (MK_COMB (@lem5281478 _69081 _69082 _69083) (@lem5281494 _69081 _69082 _69083)). Qed.
Lemma lem5281497 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5281498 (x : Prop) : (x = x) = True.
Proof. exact (@lem5281497 Prop x). Qed.
Lemma lem5281499 (_69081 : real) (_69082 : real) (_69083 : real) : ((term746 _69081 _69082 _69083) = (term746 _69081 _69082 _69083)) = True.
Proof. exact (@lem5281498 (term746 _69081 _69082 _69083)). Qed.
Lemma lem5281500 (_69081 : real) (_69082 : real) (_69083 : real) : ((term583 _69082 _69081 _69083) = (term746 _69081 _69082 _69083)) = True.
Proof. exact (TRANS (@lem5281495 _69081 _69082 _69083) (@lem5281499 _69081 _69082 _69083)). Qed.
Lemma lem5281501 (_69081 : real) (_69082 : real) (_69083 : real) : True = ((term583 _69082 _69081 _69083) = (term746 _69081 _69082 _69083)).
Proof. exact (SYM (@lem5281500 _69081 _69082 _69083)). Qed.
Lemma lem5281502 (_69081 : real) (_69082 : real) (_69083 : real) : (term583 _69082 _69081 _69083) = (term746 _69081 _69082 _69083).
Proof. exact (EQ_MP (@lem5281501 _69081 _69082 _69083) (@lem0)). Qed.
Lemma lem5281503 (_69081 : real) (_69082 : real) (_69083 : real) (h1 : term129) : term746 _69081 _69082 _69083.
Proof. exact (EQ_MP (@lem5281502 _69081 _69082 _69083) (@lem5279181 _69082 _69081 _69083 h1)). Qed.
Lemma lem5281505 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5281506 (_69082 : real) (_69081 : real) (_69083 : real) : (term746 _69081 _69082 _69083) = (term749 _69082 _69081 _69083).
Proof. exact (@lem5281505 (term266 _69081 _69082 _69083) (real_le _69081 _69083)). Qed.
Lemma lem5281508 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5281509 (_69081 : real) (_69082 : real) (_69083 : real) : (term750 _69081 _69082 _69083) = (term751 _69081 _69082 _69083).
Proof. exact (@lem5281508 (term584 _69081 _69082) (term584 _69082 _69083)). Qed.
Lemma lem5281511 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281512 (_69081 : real) (_69082 : real) : (term752 _69081 _69082) = (real_le _69081 _69082).
Proof. exact (@lem5281511 (real_le _69081 _69082)). Qed.
Lemma lem5281513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5281514 (_69081 : real) (_69082 : real) : (term753 _69081 _69082) = (term754 _69081 _69082).
Proof. exact (MK_COMB (@lem5281513) (@lem5281512 _69081 _69082)). Qed.
Lemma lem5281516 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281517 (_69082 : real) (_69083 : real) : (term752 _69082 _69083) = (real_le _69082 _69083).
Proof. exact (@lem5281516 (real_le _69082 _69083)). Qed.
Lemma lem5281518 (_69081 : real) (_69082 : real) (_69083 : real) : (term751 _69081 _69082 _69083) = (term271 _69081 _69082 _69083).
Proof. exact (MK_COMB (@lem5281514 _69081 _69082) (@lem5281517 _69082 _69083)). Qed.
Lemma lem5281519 (_69081 : real) (_69082 : real) (_69083 : real) : (term750 _69081 _69082 _69083) = (term271 _69081 _69082 _69083).
Proof. exact (TRANS (@lem5281509 _69081 _69082 _69083) (@lem5281518 _69081 _69082 _69083)). Qed.
Lemma lem5281520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5281521 (_69081 : real) (_69082 : real) (_69083 : real) : (term755 _69081 _69082 _69083) = (term756 _69081 _69082 _69083).
Proof. exact (MK_COMB (@lem5281520) (@lem5281519 _69081 _69082 _69083)). Qed.
Lemma lem5281522 (_69081 : real) (_69083 : real) : (real_le _69081 _69083) = (real_le _69081 _69083).
Proof. exact (eq_refl (real_le _69081 _69083)). Qed.
Lemma lem5281523 (_69082 : real) (_69081 : real) (_69083 : real) : (term749 _69082 _69081 _69083) = (term123 _69082 _69081 _69083).
Proof. exact (MK_COMB (@lem5281521 _69081 _69082 _69083) (@lem5281522 _69081 _69083)). Qed.
Lemma lem5281524 (_69082 : real) (_69081 : real) (_69083 : real) : (term746 _69081 _69082 _69083) = (term123 _69082 _69081 _69083).
Proof. exact (TRANS (@lem5281506 _69082 _69081 _69083) (@lem5281523 _69082 _69081 _69083)). Qed.
Lemma lem5281526 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term134 s c' x') (h5 : term228 x' s c' t) : term757 c' s x'.
Proof. exact (conj (@lem5280983 x' s c' t h5) (@lem5281431 x b s c' x' h1 h2 h3 h4)). Qed.
Lemma lem5281528 (_69082 : real) (_69081 : real) (_69083 : real) (h1 : term129) : term123 _69082 _69081 _69083.
Proof. exact (EQ_MP (@lem5281524 _69082 _69081 _69083) (@lem5281503 _69081 _69082 _69083 h1)). Qed.
Lemma lem5281529 (s : real -> Prop) (c' : real) (x' : real) (h1 : term129) : term758 s c' x'.
Proof. exact (@lem5281528 (inf s) c' x' h1). Qed.
Lemma lem5281532 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : real_le c' x'.
Proof. exact (@lem5281529 s c' x' h2 (@lem5281526 x b x' s c' t h1 h3 h4 h5 h6)). Qed.
Lemma lem5281533 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : term759 c' x'.
Proof. exact (fun h0 : term584 c' x' => @lem5281532 x b x' s c' t h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5281535 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281536 (c' : real) (x' : real) : (term759 c' x') = (real_le c' x').
Proof. exact (@lem5281535 (real_le c' x')). Qed.
Lemma lem5281537 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : real_le c' x'.
Proof. exact (EQ_MP (@lem5281536 c' x') (@lem5281533 x b x' s c' t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5281540 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5281542 (c' : real) (x' : real) : (term584 c' x') = (term760 c' x').
Proof. exact (@lem5281540 (real_le c' x')). Qed.
Lemma lem5281545 (s : real -> Prop) (c' : real) (x' : real) (h1 : term134 s c' x') : term760 c' x'.
Proof. exact (EQ_MP (@lem5281542 c' x') (@lem5279189 s c' x' h1)). Qed.
Lemma lem5281548 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (@lem5281545 s c' x' h5 (@lem5281537 x b x' s c' t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5281549 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : term690.
Proof. exact (fun h0 : ~ False => @lem5281548 x b x' s c' t h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5281551 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281552 : term690 = False.
Proof. exact (@lem5281551 False). Qed.
Lemma lem5281553 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5281552) (@lem5281549 x b x' s c' t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5281620 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term108 c' t.
Proof. exact (proj2 (@lem5277568 x' s c' t h1)). Qed.
Lemma lem5281621 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term688 c' t.
Proof. exact (fun h0 : term567 c' t => @lem5281620 x' s c' t h1). Qed.
Lemma lem5281623 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281624 (c' : real) (t : real -> Prop) : (term688 c' t) = (term108 c' t).
Proof. exact (@lem5281623 (term108 c' t)). Qed.
Lemma lem5281625 (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term228 x' s c' t) : term108 c' t.
Proof. exact (EQ_MP (@lem5281624 c' t) (@lem5281621 x' s c' t h1)). Qed.
Lemma lem5281627 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5281628 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5281627 t h1). Qed.
Lemma lem5281630 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5281631 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5281630 (t = (@EMPTY real))). Qed.
Lemma lem5281632 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5281631 t) (@lem5281628 t h1)). Qed.
Lemma lem5281634 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5281635 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5281634 t h1). Qed.
Lemma lem5281637 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5281638 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5281637 (t = (@EMPTY real))). Qed.
Lemma lem5281639 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5281638 t) (@lem5281635 t h1)). Qed.
Lemma lem5281641 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : @IN real x' t.
Proof. exact (proj1 (@lem5277573 t c' x' h1)). Qed.
Lemma lem5281642 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : term691 x' t.
Proof. exact (fun h0 : term617 x' t => @lem5281641 t c' x' h1). Qed.
Lemma lem5281644 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281645 (x' : real) (t : real -> Prop) : (term691 x' t) = (@IN real x' t).
Proof. exact (@lem5281644 (@IN real x' t)). Qed.
Lemma lem5281646 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : @IN real x' t.
Proof. exact (EQ_MP (@lem5281645 x' t) (@lem5281642 t c' x' h1)). Qed.
Lemma lem5281649 (t : real -> Prop) (x' : real) (h1 : term692 t x') : term692 t x'.
Proof. exact (h1). Qed.
Lemma lem5281650 (t : real -> Prop) (x' : real) (h1 : term692 t x') : term693 t x'.
Proof. exact (fun h0 : term294 t x' => @lem5281649 t x' h1). Qed.
Lemma lem5281652 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5281653 (t : real -> Prop) (x' : real) : (term693 t x') = (term692 t x').
Proof. exact (@lem5281652 (term294 t x')). Qed.
Lemma lem5281654 (t : real -> Prop) (x' : real) (h1 : term692 t x') : term692 t x'.
Proof. exact (EQ_MP (@lem5281653 t x') (@lem5281650 t x' h1)). Qed.
Lemma lem5281682 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281683 (_69094 : real) (_69092 : real -> Prop) : (term293 _69092 _69094) = (term694 _69094 _69092).
Proof. exact (@lem5281682 (term294 _69092 _69094) (term617 _69094 _69092)). Qed.
Lemma lem5281689 (x : type1021) (_69093 : real) (_69092 : real -> Prop) : (term662 x _69093 _69092) = (term662 x _69093 _69092).
Proof. exact (eq_refl (term662 x _69093 _69092)). Qed.
Lemma lem5281690 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term695 x _69093 _69092 _69094) = (term696 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5281689 x _69093 _69092) (@lem5281683 _69094 _69092)). Qed.
Lemma lem5281701 (_69092 : real -> Prop) : (term289 _69092) = (term289 _69092).
Proof. exact (eq_refl (term289 _69092)). Qed.
Lemma lem5281702 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term585 x _69093 _69092 _69094) = (term697 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5281701 _69092) (@lem5281690 x _69093 _69094 _69092)). Qed.
Lemma lem5281713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5281714 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term698 x _69093 _69092 _69094) = (term699 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5281713) (@lem5281702 x _69093 _69094 _69092)). Qed.
Lemma lem5281718 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281719 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term700 x _69093 _69092 _69094) = (term585 x _69093 _69092 _69094).
Proof. exact (@lem5281718 (_69092 = (@EMPTY real)) (term536 x _69093 _69092) (term293 _69092 _69094)). Qed.
Lemma lem5281745 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281746 (_69094 : real) (_69092 : real -> Prop) : (term293 _69092 _69094) = (term694 _69094 _69092).
Proof. exact (@lem5281745 (term294 _69092 _69094) (term617 _69094 _69092)). Qed.
Lemma lem5281752 (x : type1021) (_69093 : real) (_69092 : real -> Prop) : (term662 x _69093 _69092) = (term662 x _69093 _69092).
Proof. exact (eq_refl (term662 x _69093 _69092)). Qed.
Lemma lem5281753 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term695 x _69093 _69092 _69094) = (term696 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5281752 x _69093 _69092) (@lem5281746 _69094 _69092)). Qed.
Lemma lem5281764 (_69092 : real -> Prop) : (term289 _69092) = (term289 _69092).
Proof. exact (eq_refl (term289 _69092)). Qed.
Lemma lem5281765 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term585 x _69093 _69092 _69094) = (term697 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5281764 _69092) (@lem5281753 x _69093 _69094 _69092)). Qed.
Lemma lem5281776 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term700 x _69093 _69092 _69094) = (term697 x _69093 _69094 _69092).
Proof. exact (TRANS (@lem5281719 x _69093 _69092 _69094) (@lem5281765 x _69093 _69094 _69092)). Qed.
Lemma lem5281777 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : ((term585 x _69093 _69092 _69094) = (term700 x _69093 _69092 _69094)) = ((term697 x _69093 _69094 _69092) = (term697 x _69093 _69094 _69092)).
Proof. exact (MK_COMB (@lem5281714 x _69093 _69094 _69092) (@lem5281776 x _69093 _69094 _69092)). Qed.
Lemma lem5281779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5281780 (x : Prop) : (x = x) = True.
Proof. exact (@lem5281779 Prop x). Qed.
Lemma lem5281781 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : ((term697 x _69093 _69094 _69092) = (term697 x _69093 _69094 _69092)) = True.
Proof. exact (@lem5281780 (term697 x _69093 _69094 _69092)). Qed.
Lemma lem5281782 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : ((term585 x _69093 _69092 _69094) = (term700 x _69093 _69092 _69094)) = True.
Proof. exact (TRANS (@lem5281777 x _69093 _69094 _69092) (@lem5281781 x _69093 _69094 _69092)). Qed.
Lemma lem5281783 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : True = ((term585 x _69093 _69092 _69094) = (term700 x _69093 _69092 _69094)).
Proof. exact (SYM (@lem5281782 x _69093 _69092 _69094)). Qed.
Lemma lem5281784 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term585 x _69093 _69092 _69094) = (term700 x _69093 _69092 _69094).
Proof. exact (EQ_MP (@lem5281783 x _69093 _69092 _69094) (@lem0)). Qed.
Lemma lem5281785 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term700 x _69093 _69092 _69094.
Proof. exact (EQ_MP (@lem5281784 x _69093 _69092 _69094) (@lem5279401 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5281787 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5281788 (_69094 : real) (x : type1021) (_69093 : real) (_69092 : real -> Prop) : (term700 x _69093 _69092 _69094) = (term701 _69094 x _69093 _69092).
Proof. exact (@lem5281787 (term702 _69092 _69094) (term536 x _69093 _69092)). Qed.
Lemma lem5281790 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5281791 (_69092 : real -> Prop) (_69094 : real) : (term703 _69092 _69094) = (term704 _69092 _69094).
Proof. exact (@lem5281790 (_69092 = (@EMPTY real)) (term293 _69092 _69094)). Qed.
Lemma lem5281793 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5281794 (_69092 : real -> Prop) (_69094 : real) : (term705 _69092 _69094) = (term706 _69092 _69094).
Proof. exact (@lem5281793 (term617 _69094 _69092) (term294 _69092 _69094)). Qed.
Lemma lem5281796 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281797 (_69094 : real) (_69092 : real -> Prop) : (term622 _69094 _69092) = (@IN real _69094 _69092).
Proof. exact (@lem5281796 (@IN real _69094 _69092)). Qed.
Lemma lem5281798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5281799 (_69094 : real) (_69092 : real -> Prop) : (term707 _69094 _69092) = (term708 _69094 _69092).
Proof. exact (MK_COMB (@lem5281798) (@lem5281797 _69094 _69092)). Qed.
Lemma lem5281800 (_69092 : real -> Prop) (_69094 : real) : (term692 _69092 _69094) = (term692 _69092 _69094).
Proof. exact (eq_refl (term692 _69092 _69094)). Qed.
Lemma lem5281801 (_69092 : real -> Prop) (_69094 : real) : (term706 _69092 _69094) = (term709 _69092 _69094).
Proof. exact (MK_COMB (@lem5281799 _69094 _69092) (@lem5281800 _69092 _69094)). Qed.
Lemma lem5281802 (_69092 : real -> Prop) (_69094 : real) : (term705 _69092 _69094) = (term709 _69092 _69094).
Proof. exact (TRANS (@lem5281794 _69092 _69094) (@lem5281801 _69092 _69094)). Qed.
Lemma lem5281803 (_69092 : real -> Prop) : (term118 _69092) = (term118 _69092).
Proof. exact (eq_refl (term118 _69092)). Qed.
Lemma lem5281804 (_69092 : real -> Prop) (_69094 : real) : (term704 _69092 _69094) = (term710 _69092 _69094).
Proof. exact (MK_COMB (@lem5281803 _69092) (@lem5281802 _69092 _69094)). Qed.
Lemma lem5281805 (_69092 : real -> Prop) (_69094 : real) : (term703 _69092 _69094) = (term710 _69092 _69094).
Proof. exact (TRANS (@lem5281791 _69092 _69094) (@lem5281804 _69092 _69094)). Qed.
Lemma lem5281806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5281807 (_69092 : real -> Prop) (_69094 : real) : (term711 _69092 _69094) = (term712 _69092 _69094).
Proof. exact (MK_COMB (@lem5281806) (@lem5281805 _69092 _69094)). Qed.
Lemma lem5281808 (x : type1021) (_69093 : real) (_69092 : real -> Prop) : (term536 x _69093 _69092) = (term536 x _69093 _69092).
Proof. exact (eq_refl (term536 x _69093 _69092)). Qed.
Lemma lem5281809 (_69094 : real) (x : type1021) (_69093 : real) (_69092 : real -> Prop) : (term701 _69094 x _69093 _69092) = (term713 _69094 x _69093 _69092).
Proof. exact (MK_COMB (@lem5281807 _69092 _69094) (@lem5281808 x _69093 _69092)). Qed.
Lemma lem5281810 (_69094 : real) (x : type1021) (_69093 : real) (_69092 : real -> Prop) : (term700 x _69093 _69092 _69094) = (term713 _69094 x _69093 _69092).
Proof. exact (TRANS (@lem5281788 _69094 x _69093 _69092) (@lem5281809 _69094 x _69093 _69092)). Qed.
Lemma lem5281812 (t : real -> Prop) (c' : real) (x' : real) (h1 : term692 t x') (h2 : term134 t c' x') : term709 t x'.
Proof. exact (conj (@lem5281646 t c' x' h2) (@lem5281654 t x' h1)). Qed.
Lemma lem5281813 (t : real -> Prop) (c' : real) (x' : real) (h1 : term31 t) (h2 : term692 t x') (h3 : term134 t c' x') : term710 t x'.
Proof. exact (conj (@lem5281639 t h1) (@lem5281812 t c' x' h2 h3)). Qed.
Lemma lem5281815 (_69094 : real) (_69093 : real) (_69092 : real -> Prop) (x : type1021) (h1 : term444 x) : term713 _69094 x _69093 _69092.
Proof. exact (EQ_MP (@lem5281810 _69094 x _69093 _69092) (@lem5281785 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5281816 (x' : real) (_69093 : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term713 x' x _69093 t.
Proof. exact (@lem5281815 x' _69093 t x h1). Qed.
Lemma lem5281819 (_69093 : real) (x : type1021) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 t x') (h4 : term134 t c' x') : term536 x _69093 t.
Proof. exact (@lem5281816 x' _69093 t x h1 (@lem5281813 t c' x' h2 h3 h4)). Qed.
Lemma lem5281820 (c : real) (x : type1021) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 t x') (h4 : term134 t c' x') : term536 x c t.
Proof. exact (@lem5281819 c x t c' x' h1 h2 h3 h4). Qed.
Lemma lem5281821 (c : real) (x : type1021) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 t x') (h4 : term134 t c' x') : term614 x c t.
Proof. exact (fun h0 : term589 x c t => @lem5281820 c x t c' x' h1 h2 h3 h4). Qed.
Lemma lem5281823 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281824 (x : type1021) (c : real) (t : real -> Prop) : (term614 x c t) = (term536 x c t).
Proof. exact (@lem5281823 (term536 x c t)). Qed.
Lemma lem5281825 (c : real) (x : type1021) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 t x') (h4 : term134 t c' x') : term536 x c t.
Proof. exact (EQ_MP (@lem5281824 x c t) (@lem5281821 c x t c' x' h1 h2 h3 h4)). Qed.
Lemma lem5281831 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281832 (c : real) (_69088 : real) (t : real -> Prop) : (term130 t c _69088) = (term616 c _69088 t).
Proof. exact (@lem5281831 (real_le c _69088) (term617 _69088 t)). Qed.
Lemma lem5281838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5281839 (c : real) (_69088 : real) (t : real -> Prop) : (term618 t c _69088) = (term619 c _69088 t).
Proof. exact (MK_COMB (@lem5281838) (@lem5281832 c _69088 t)). Qed.
Lemma lem5281845 (c : real) (_69088 : real) (t : real -> Prop) : (term616 c _69088 t) = (term616 c _69088 t).
Proof. exact (eq_refl (term616 c _69088 t)). Qed.
Lemma lem5281846 (c : real) (_69088 : real) (t : real -> Prop) : ((term130 t c _69088) = (term616 c _69088 t)) = ((term616 c _69088 t) = (term616 c _69088 t)).
Proof. exact (MK_COMB (@lem5281839 c _69088 t) (@lem5281845 c _69088 t)). Qed.
Lemma lem5281848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5281849 (x : Prop) : (x = x) = True.
Proof. exact (@lem5281848 Prop x). Qed.
Lemma lem5281850 (c : real) (_69088 : real) (t : real -> Prop) : ((term616 c _69088 t) = (term616 c _69088 t)) = True.
Proof. exact (@lem5281849 (term616 c _69088 t)). Qed.
Lemma lem5281851 (c : real) (_69088 : real) (t : real -> Prop) : ((term130 t c _69088) = (term616 c _69088 t)) = True.
Proof. exact (TRANS (@lem5281846 c _69088 t) (@lem5281850 c _69088 t)). Qed.
Lemma lem5281852 (c : real) (_69088 : real) (t : real -> Prop) : True = ((term130 t c _69088) = (term616 c _69088 t)).
Proof. exact (SYM (@lem5281851 c _69088 t)). Qed.
Lemma lem5281853 (c : real) (_69088 : real) (t : real -> Prop) : (term130 t c _69088) = (term616 c _69088 t).
Proof. exact (EQ_MP (@lem5281852 c _69088 t) (@lem0)). Qed.
Lemma lem5281854 (_69088 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term616 c _69088 t.
Proof. exact (EQ_MP (@lem5281853 c _69088 t) (@lem5279301 _69088 t c h1)). Qed.
Lemma lem5281856 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5281857 (t : real -> Prop) (c : real) (_69088 : real) : (term616 c _69088 t) = (term620 t c _69088).
Proof. exact (@lem5281856 (term617 _69088 t) (real_le c _69088)). Qed.
Lemma lem5281859 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5281860 (_69088 : real) (t : real -> Prop) : (term622 _69088 t) = (@IN real _69088 t).
Proof. exact (@lem5281859 (@IN real _69088 t)). Qed.
Lemma lem5281861 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5281862 (_69088 : real) (t : real -> Prop) : (term623 _69088 t) = (term51 _69088 t).
Proof. exact (MK_COMB (@lem5281861) (@lem5281860 _69088 t)). Qed.
Lemma lem5281863 (c : real) (_69088 : real) : (real_le c _69088) = (real_le c _69088).
Proof. exact (eq_refl (real_le c _69088)). Qed.
Lemma lem5281864 (t : real -> Prop) (c : real) (_69088 : real) : (term620 t c _69088) = (term53 t c _69088).
Proof. exact (MK_COMB (@lem5281862 _69088 t) (@lem5281863 c _69088)). Qed.
Lemma lem5281865 (t : real -> Prop) (c : real) (_69088 : real) : (term616 c _69088 t) = (term53 t c _69088).
Proof. exact (TRANS (@lem5281857 t c _69088) (@lem5281864 t c _69088)). Qed.
Lemma lem5281868 (_69088 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term53 t c _69088.
Proof. exact (EQ_MP (@lem5281865 t c _69088) (@lem5281854 _69088 t c h1)). Qed.
Lemma lem5281869 (x : type1021) (t : real -> Prop) (c : real) (h1 : term34 t c) : term624 x t c.
Proof. exact (@lem5281868 (x t c) t c h1). Qed.
Lemma lem5281872 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 t x') (h5 : term134 t c' x') : term625 x t c.
Proof. exact (@lem5281869 x t c h2 (@lem5281825 c x t c' x' h1 h3 h4 h5)). Qed.
Lemma lem5281873 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 t x') (h5 : term134 t c' x') : term626 x t c.
Proof. exact (fun h0 : term537 x t c => @lem5281872 x c t c' x' h1 h2 h3 h4 h5). Qed.
Lemma lem5281875 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281876 (x : type1021) (t : real -> Prop) (c : real) : (term626 x t c) = (term625 x t c).
Proof. exact (@lem5281875 (term625 x t c)). Qed.
Lemma lem5281877 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 t x') (h5 : term134 t c' x') : term625 x t c.
Proof. exact (EQ_MP (@lem5281876 x t c) (@lem5281873 x c t c' x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5281879 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : @IN real x' t.
Proof. exact (proj1 (@lem5277573 t c' x' h1)). Qed.
Lemma lem5281880 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : term691 x' t.
Proof. exact (fun h0 : term617 x' t => @lem5281879 t c' x' h1). Qed.
Lemma lem5281882 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5281883 (x' : real) (t : real -> Prop) : (term691 x' t) = (@IN real x' t).
Proof. exact (@lem5281882 (@IN real x' t)). Qed.
Lemma lem5281884 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : @IN real x' t.
Proof. exact (EQ_MP (@lem5281883 x' t) (@lem5281880 t c' x' h1)). Qed.
Lemma lem5281902 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281903 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term714 x _69093 _69092 _69094) = (term715 x _69093 _69092 _69094).
Proof. exact (@lem5281902 (term617 _69094 _69092) (term537 x _69092 _69093) (term294 _69092 _69094)). Qed.
Lemma lem5281917 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281918 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term716 x _69093 _69092 _69094) = (term717 _69094 x _69092 _69093).
Proof. exact (@lem5281917 (term294 _69092 _69094) (term537 x _69092 _69093)). Qed.
Lemma lem5281924 (_69094 : real) (_69092 : real -> Prop) : (term718 _69094 _69092) = (term718 _69094 _69092).
Proof. exact (eq_refl (term718 _69094 _69092)). Qed.
Lemma lem5281925 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term715 x _69093 _69092 _69094) = (term719 _69094 x _69092 _69093).
Proof. exact (MK_COMB (@lem5281924 _69094 _69092) (@lem5281918 _69094 x _69092 _69093)). Qed.
Lemma lem5281929 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281930 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term719 _69094 x _69092 _69093) = (term720 _69094 x _69092 _69093).
Proof. exact (@lem5281929 (term294 _69092 _69094) (term617 _69094 _69092) (term537 x _69092 _69093)). Qed.
Lemma lem5281946 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term715 x _69093 _69092 _69094) = (term720 _69094 x _69092 _69093).
Proof. exact (TRANS (@lem5281925 _69094 x _69092 _69093) (@lem5281930 _69094 x _69092 _69093)). Qed.
Lemma lem5281947 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term714 x _69093 _69092 _69094) = (term720 _69094 x _69092 _69093).
Proof. exact (TRANS (@lem5281903 x _69093 _69092 _69094) (@lem5281946 _69094 x _69092 _69093)). Qed.
Lemma lem5281948 (_69092 : real -> Prop) : (term289 _69092) = (term289 _69092).
Proof. exact (eq_refl (term289 _69092)). Qed.
Lemma lem5281949 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term586 x _69093 _69092 _69094) = (term721 _69094 x _69092 _69093).
Proof. exact (MK_COMB (@lem5281948 _69092) (@lem5281947 _69094 x _69092 _69093)). Qed.
Lemma lem5281960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5281961 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term722 x _69093 _69092 _69094) = (term723 _69094 x _69092 _69093).
Proof. exact (MK_COMB (@lem5281960) (@lem5281949 _69094 x _69092 _69093)). Qed.
Lemma lem5281965 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5281966 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term724 x _69093 _69094 _69092) = (term725 x _69093 _69094 _69092).
Proof. exact (@lem5281965 (_69092 = (@EMPTY real)) (term294 _69092 _69094) (term726 x _69093 _69094 _69092)). Qed.
Lemma lem5281992 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5281993 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term726 x _69093 _69094 _69092) = (term727 _69094 x _69092 _69093).
Proof. exact (@lem5281992 (term617 _69094 _69092) (term537 x _69092 _69093)). Qed.
Lemma lem5281999 (_69092 : real -> Prop) (_69094 : real) : (term728 _69092 _69094) = (term728 _69092 _69094).
Proof. exact (eq_refl (term728 _69092 _69094)). Qed.
Lemma lem5282000 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term729 x _69093 _69094 _69092) = (term720 _69094 x _69092 _69093).
Proof. exact (MK_COMB (@lem5281999 _69092 _69094) (@lem5281993 _69094 x _69092 _69093)). Qed.
Lemma lem5282011 (_69092 : real -> Prop) : (term289 _69092) = (term289 _69092).
Proof. exact (eq_refl (term289 _69092)). Qed.
Lemma lem5282012 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term725 x _69093 _69094 _69092) = (term721 _69094 x _69092 _69093).
Proof. exact (MK_COMB (@lem5282011 _69092) (@lem5282000 _69094 x _69092 _69093)). Qed.
Lemma lem5282023 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term724 x _69093 _69094 _69092) = (term721 _69094 x _69092 _69093).
Proof. exact (TRANS (@lem5281966 x _69093 _69094 _69092) (@lem5282012 _69094 x _69092 _69093)). Qed.
Lemma lem5282024 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : ((term586 x _69093 _69092 _69094) = (term724 x _69093 _69094 _69092)) = ((term721 _69094 x _69092 _69093) = (term721 _69094 x _69092 _69093)).
Proof. exact (MK_COMB (@lem5281961 _69094 x _69092 _69093) (@lem5282023 _69094 x _69092 _69093)). Qed.
Lemma lem5282026 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5282027 (x : Prop) : (x = x) = True.
Proof. exact (@lem5282026 Prop x). Qed.
Lemma lem5282028 (_69094 : real) (x : type1021) (_69092 : real -> Prop) (_69093 : real) : ((term721 _69094 x _69092 _69093) = (term721 _69094 x _69092 _69093)) = True.
Proof. exact (@lem5282027 (term721 _69094 x _69092 _69093)). Qed.
Lemma lem5282029 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : ((term586 x _69093 _69092 _69094) = (term724 x _69093 _69094 _69092)) = True.
Proof. exact (TRANS (@lem5282024 _69094 x _69092 _69093) (@lem5282028 _69094 x _69092 _69093)). Qed.
Lemma lem5282030 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : True = ((term586 x _69093 _69092 _69094) = (term724 x _69093 _69094 _69092)).
Proof. exact (SYM (@lem5282029 x _69093 _69094 _69092)). Qed.
Lemma lem5282031 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term586 x _69093 _69092 _69094) = (term724 x _69093 _69094 _69092).
Proof. exact (EQ_MP (@lem5282030 x _69093 _69094 _69092) (@lem0)). Qed.
Lemma lem5282032 (_69093 : real) (_69094 : real) (_69092 : real -> Prop) (x : type1021) (h1 : term444 x) : term724 x _69093 _69094 _69092.
Proof. exact (EQ_MP (@lem5282031 x _69093 _69094 _69092) (@lem5279417 _69093 _69092 _69094 x h1)). Qed.
Lemma lem5282034 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5282035 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term724 x _69093 _69094 _69092) = (term730 x _69093 _69092 _69094).
Proof. exact (@lem5282034 (term731 x _69093 _69094 _69092) (term294 _69092 _69094)). Qed.
Lemma lem5282037 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5282038 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term732 x _69093 _69094 _69092) = (term733 x _69093 _69094 _69092).
Proof. exact (@lem5282037 (_69092 = (@EMPTY real)) (term726 x _69093 _69094 _69092)). Qed.
Lemma lem5282040 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5282041 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term734 x _69093 _69094 _69092) = (term735 x _69093 _69094 _69092).
Proof. exact (@lem5282040 (term537 x _69092 _69093) (term617 _69094 _69092)). Qed.
Lemma lem5282043 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5282044 (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term645 x _69092 _69093) = (term625 x _69092 _69093).
Proof. exact (@lem5282043 (term625 x _69092 _69093)). Qed.
Lemma lem5282045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282046 (x : type1021) (_69092 : real -> Prop) (_69093 : real) : (term646 x _69092 _69093) = (term647 x _69092 _69093).
Proof. exact (MK_COMB (@lem5282045) (@lem5282044 x _69092 _69093)). Qed.
Lemma lem5282048 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5282049 (_69094 : real) (_69092 : real -> Prop) : (term622 _69094 _69092) = (@IN real _69094 _69092).
Proof. exact (@lem5282048 (@IN real _69094 _69092)). Qed.
Lemma lem5282050 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term735 x _69093 _69094 _69092) = (term736 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5282046 x _69092 _69093) (@lem5282049 _69094 _69092)). Qed.
Lemma lem5282051 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term734 x _69093 _69094 _69092) = (term736 x _69093 _69094 _69092).
Proof. exact (TRANS (@lem5282041 x _69093 _69094 _69092) (@lem5282050 x _69093 _69094 _69092)). Qed.
Lemma lem5282052 (_69092 : real -> Prop) : (term118 _69092) = (term118 _69092).
Proof. exact (eq_refl (term118 _69092)). Qed.
Lemma lem5282053 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term733 x _69093 _69094 _69092) = (term737 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5282052 _69092) (@lem5282051 x _69093 _69094 _69092)). Qed.
Lemma lem5282054 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term732 x _69093 _69094 _69092) = (term737 x _69093 _69094 _69092).
Proof. exact (TRANS (@lem5282038 x _69093 _69094 _69092) (@lem5282053 x _69093 _69094 _69092)). Qed.
Lemma lem5282055 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5282056 (x : type1021) (_69093 : real) (_69094 : real) (_69092 : real -> Prop) : (term738 x _69093 _69094 _69092) = (term739 x _69093 _69094 _69092).
Proof. exact (MK_COMB (@lem5282055) (@lem5282054 x _69093 _69094 _69092)). Qed.
Lemma lem5282057 (_69092 : real -> Prop) (_69094 : real) : (term294 _69092 _69094) = (term294 _69092 _69094).
Proof. exact (eq_refl (term294 _69092 _69094)). Qed.
Lemma lem5282058 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term730 x _69093 _69092 _69094) = (term740 x _69093 _69092 _69094).
Proof. exact (MK_COMB (@lem5282056 x _69093 _69094 _69092) (@lem5282057 _69092 _69094)). Qed.
Lemma lem5282059 (x : type1021) (_69093 : real) (_69092 : real -> Prop) (_69094 : real) : (term724 x _69093 _69094 _69092) = (term740 x _69093 _69092 _69094).
Proof. exact (TRANS (@lem5282035 x _69093 _69092 _69094) (@lem5282058 x _69093 _69092 _69094)). Qed.
Lemma lem5282061 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 t x') (h5 : term134 t c' x') : term736 x c x' t.
Proof. exact (conj (@lem5281877 x c t c' x' h1 h2 h3 h4 h5) (@lem5281884 t c' x' h5)). Qed.
Lemma lem5282062 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 t x') (h5 : term134 t c' x') : term737 x c x' t.
Proof. exact (conj (@lem5281632 t h3) (@lem5282061 x c t c' x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5282064 (_69093 : real) (_69092 : real -> Prop) (_69094 : real) (x : type1021) (h1 : term444 x) : term740 x _69093 _69092 _69094.
Proof. exact (EQ_MP (@lem5282059 x _69093 _69092 _69094) (@lem5282032 _69093 _69094 _69092 x h1)). Qed.
Lemma lem5282065 (c : real) (t : real -> Prop) (x' : real) (x : type1021) (h1 : term444 x) : term740 x c t x'.
Proof. exact (@lem5282064 c t x' x h1). Qed.
Lemma lem5282068 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 t x') (h5 : term134 t c' x') : term294 t x'.
Proof. exact (@lem5282065 c t x' x h1 (@lem5282062 x c t c' x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5282069 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term134 t c' x') : term741 t x'.
Proof. exact (fun h0 : term692 t x' => @lem5282068 x c t c' x' h1 h2 h3 h0 h4). Qed.
Lemma lem5282071 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5282072 (t : real -> Prop) (x' : real) : (term741 t x') = (term294 t x').
Proof. exact (@lem5282071 (term294 t x')). Qed.
Lemma lem5282073 (x : type1021) (c : real) (t : real -> Prop) (c' : real) (x' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term134 t c' x') : term294 t x'.
Proof. exact (EQ_MP (@lem5282072 t x') (@lem5282069 x c t c' x' h1 h2 h3 h4)). Qed.
Lemma lem5282089 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5282090 (_69089 : real) (_69090 : real) (_69091 : real) : (term742 _69090 _69089 _69091) = (term743 _69089 _69090 _69091).
Proof. exact (@lem5282089 (real_le _69089 _69091) (term584 _69090 _69091)). Qed.
Lemma lem5282096 (_69089 : real) (_69090 : real) : (term744 _69089 _69090) = (term744 _69089 _69090).
Proof. exact (eq_refl (term744 _69089 _69090)). Qed.
Lemma lem5282097 (_69089 : real) (_69090 : real) (_69091 : real) : (term583 _69090 _69089 _69091) = (term745 _69089 _69090 _69091).
Proof. exact (MK_COMB (@lem5282096 _69089 _69090) (@lem5282090 _69089 _69090 _69091)). Qed.
Lemma lem5282101 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5282102 (_69089 : real) (_69090 : real) (_69091 : real) : (term745 _69089 _69090 _69091) = (term746 _69089 _69090 _69091).
Proof. exact (@lem5282101 (real_le _69089 _69091) (term584 _69089 _69090) (term584 _69090 _69091)). Qed.
Lemma lem5282118 (_69089 : real) (_69090 : real) (_69091 : real) : (term583 _69090 _69089 _69091) = (term746 _69089 _69090 _69091).
Proof. exact (TRANS (@lem5282097 _69089 _69090 _69091) (@lem5282102 _69089 _69090 _69091)). Qed.
Lemma lem5282119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5282120 (_69089 : real) (_69090 : real) (_69091 : real) : (term747 _69090 _69089 _69091) = (term748 _69089 _69090 _69091).
Proof. exact (MK_COMB (@lem5282119) (@lem5282118 _69089 _69090 _69091)). Qed.
Lemma lem5282136 (_69089 : real) (_69090 : real) (_69091 : real) : (term746 _69089 _69090 _69091) = (term746 _69089 _69090 _69091).
Proof. exact (eq_refl (term746 _69089 _69090 _69091)). Qed.
Lemma lem5282137 (_69089 : real) (_69090 : real) (_69091 : real) : ((term583 _69090 _69089 _69091) = (term746 _69089 _69090 _69091)) = ((term746 _69089 _69090 _69091) = (term746 _69089 _69090 _69091)).
Proof. exact (MK_COMB (@lem5282120 _69089 _69090 _69091) (@lem5282136 _69089 _69090 _69091)). Qed.
Lemma lem5282139 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5282140 (x : Prop) : (x = x) = True.
Proof. exact (@lem5282139 Prop x). Qed.
Lemma lem5282141 (_69089 : real) (_69090 : real) (_69091 : real) : ((term746 _69089 _69090 _69091) = (term746 _69089 _69090 _69091)) = True.
Proof. exact (@lem5282140 (term746 _69089 _69090 _69091)). Qed.
Lemma lem5282142 (_69089 : real) (_69090 : real) (_69091 : real) : ((term583 _69090 _69089 _69091) = (term746 _69089 _69090 _69091)) = True.
Proof. exact (TRANS (@lem5282137 _69089 _69090 _69091) (@lem5282141 _69089 _69090 _69091)). Qed.
Lemma lem5282143 (_69089 : real) (_69090 : real) (_69091 : real) : True = ((term583 _69090 _69089 _69091) = (term746 _69089 _69090 _69091)).
Proof. exact (SYM (@lem5282142 _69089 _69090 _69091)). Qed.
Lemma lem5282144 (_69089 : real) (_69090 : real) (_69091 : real) : (term583 _69090 _69089 _69091) = (term746 _69089 _69090 _69091).
Proof. exact (EQ_MP (@lem5282143 _69089 _69090 _69091) (@lem0)). Qed.
Lemma lem5282145 (_69089 : real) (_69090 : real) (_69091 : real) (h1 : term129) : term746 _69089 _69090 _69091.
Proof. exact (EQ_MP (@lem5282144 _69089 _69090 _69091) (@lem5279313 _69090 _69089 _69091 h1)). Qed.
Lemma lem5282147 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5282148 (_69090 : real) (_69089 : real) (_69091 : real) : (term746 _69089 _69090 _69091) = (term749 _69090 _69089 _69091).
Proof. exact (@lem5282147 (term266 _69089 _69090 _69091) (real_le _69089 _69091)). Qed.
Lemma lem5282150 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5282151 (_69089 : real) (_69090 : real) (_69091 : real) : (term750 _69089 _69090 _69091) = (term751 _69089 _69090 _69091).
Proof. exact (@lem5282150 (term584 _69089 _69090) (term584 _69090 _69091)). Qed.
Lemma lem5282153 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5282154 (_69089 : real) (_69090 : real) : (term752 _69089 _69090) = (real_le _69089 _69090).
Proof. exact (@lem5282153 (real_le _69089 _69090)). Qed.
Lemma lem5282155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282156 (_69089 : real) (_69090 : real) : (term753 _69089 _69090) = (term754 _69089 _69090).
Proof. exact (MK_COMB (@lem5282155) (@lem5282154 _69089 _69090)). Qed.
Lemma lem5282158 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5282159 (_69090 : real) (_69091 : real) : (term752 _69090 _69091) = (real_le _69090 _69091).
Proof. exact (@lem5282158 (real_le _69090 _69091)). Qed.
Lemma lem5282160 (_69089 : real) (_69090 : real) (_69091 : real) : (term751 _69089 _69090 _69091) = (term271 _69089 _69090 _69091).
Proof. exact (MK_COMB (@lem5282156 _69089 _69090) (@lem5282159 _69090 _69091)). Qed.
Lemma lem5282161 (_69089 : real) (_69090 : real) (_69091 : real) : (term750 _69089 _69090 _69091) = (term271 _69089 _69090 _69091).
Proof. exact (TRANS (@lem5282151 _69089 _69090 _69091) (@lem5282160 _69089 _69090 _69091)). Qed.
Lemma lem5282162 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5282163 (_69089 : real) (_69090 : real) (_69091 : real) : (term755 _69089 _69090 _69091) = (term756 _69089 _69090 _69091).
Proof. exact (MK_COMB (@lem5282162) (@lem5282161 _69089 _69090 _69091)). Qed.
Lemma lem5282164 (_69089 : real) (_69091 : real) : (real_le _69089 _69091) = (real_le _69089 _69091).
Proof. exact (eq_refl (real_le _69089 _69091)). Qed.
Lemma lem5282165 (_69090 : real) (_69089 : real) (_69091 : real) : (term749 _69090 _69089 _69091) = (term123 _69090 _69089 _69091).
Proof. exact (MK_COMB (@lem5282163 _69089 _69090 _69091) (@lem5282164 _69089 _69091)). Qed.
Lemma lem5282166 (_69090 : real) (_69089 : real) (_69091 : real) : (term746 _69089 _69090 _69091) = (term123 _69090 _69089 _69091).
Proof. exact (TRANS (@lem5282148 _69090 _69089 _69091) (@lem5282165 _69090 _69089 _69091)). Qed.
Lemma lem5282168 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term134 t c' x') (h5 : term228 x' s c' t) : term757 c' t x'.
Proof. exact (conj (@lem5281625 x' s c' t h5) (@lem5282073 x c t c' x' h1 h2 h3 h4)). Qed.
Lemma lem5282170 (_69090 : real) (_69089 : real) (_69091 : real) (h1 : term129) : term123 _69090 _69089 _69091.
Proof. exact (EQ_MP (@lem5282166 _69090 _69089 _69091) (@lem5282145 _69089 _69090 _69091 h1)). Qed.
Lemma lem5282171 (t : real -> Prop) (c' : real) (x' : real) (h1 : term129) : term758 t c' x'.
Proof. exact (@lem5282170 (inf t) c' x' h1). Qed.
Lemma lem5282174 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : real_le c' x'.
Proof. exact (@lem5282171 t c' x' h2 (@lem5282168 x c x' s c' t h1 h3 h4 h5 h6)). Qed.
Lemma lem5282175 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : term759 c' x'.
Proof. exact (fun h0 : term584 c' x' => @lem5282174 x c x' s c' t h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5282177 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5282178 (c' : real) (x' : real) : (term759 c' x') = (real_le c' x').
Proof. exact (@lem5282177 (real_le c' x')). Qed.
Lemma lem5282179 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : real_le c' x'.
Proof. exact (EQ_MP (@lem5282178 c' x') (@lem5282175 x c x' s c' t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5282182 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5282184 (c' : real) (x' : real) : (term584 c' x') = (term760 c' x').
Proof. exact (@lem5282182 (real_le c' x')). Qed.
Lemma lem5282187 (t : real -> Prop) (c' : real) (x' : real) (h1 : term134 t c' x') : term760 c' x'.
Proof. exact (EQ_MP (@lem5282184 c' x') (@lem5279321 t c' x' h1)). Qed.
Lemma lem5282190 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (@lem5282187 t c' x' h5 (@lem5282179 x c x' s c' t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5282191 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : term690.
Proof. exact (fun h0 : ~ False => @lem5282190 x c x' s c' t h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5282193 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5282194 : term690 = False.
Proof. exact (@lem5282193 False). Qed.
Lemma lem5282195 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282194) (@lem5282191 x c x' s c' t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5282196 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : (term31 t) = False.
Proof. exact (prop_ext (fun h7 : term31 t => @lem5282195 x c x' s c' t h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5279289 t h4)). Qed.
Lemma lem5282197 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282196 x c x' s c' t h1 h2 h3 h4 h5 h6) (@lem5279289 t h4)). Qed.
Lemma lem5282198 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : (term31 s) = False.
Proof. exact (prop_ext (fun h7 : term31 s => @lem5281553 x b x' s c' t h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5279155 s h4)). Qed.
Lemma lem5282199 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282198 x b x' s c' t h1 h2 h3 h4 h5 h6) (@lem5279155 s h4)). Qed.
Lemma lem5282200 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : (term567 c' t) = False.
Proof. exact (prop_ext (fun h5 : term567 c' t => @lem5280911 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5279057 c' t h3)). Qed.
Lemma lem5282201 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282200 x s c' t h1 h2 h3 h4) (@lem5279057 c' t h3)). Qed.
Lemma lem5282202 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : (term31 t) = False.
Proof. exact (prop_ext (fun h5 : term31 t => @lem5282201 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5279019 t h2)). Qed.
Lemma lem5282203 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282202 x s c' t h1 h2 h3 h4) (@lem5279019 t h2)). Qed.
Lemma lem5282204 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : (term567 c' s) = False.
Proof. exact (prop_ext (fun h5 : term567 c' s => @lem5280164 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5278919 c' s h3)). Qed.
Lemma lem5282205 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282204 x s c' t h1 h2 h3 h4) (@lem5278919 c' s h3)). Qed.
Lemma lem5282206 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : (term31 s) = False.
Proof. exact (prop_ext (fun h5 : term31 s => @lem5282205 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5278879 s h2)). Qed.
Lemma lem5282207 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282206 x s c' t h1 h2 h3 h4) (@lem5278879 s h2)). Qed.
Lemma lem5282208 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : (term31 t) = False.
Proof. exact (prop_ext (fun h7 : term31 t => @lem5282197 x c x' s c' t h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5278456 t h4)). Qed.
Lemma lem5282209 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282208 x c x' s c' t h1 h2 h3 h4 h5 h6) (@lem5278456 t h4)). Qed.
Lemma lem5282210 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : (term31 s) = False.
Proof. exact (prop_ext (fun h7 : term31 s => @lem5282199 x b x' s c' t h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5278171 s h4)). Qed.
Lemma lem5282211 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282210 x b x' s c' t h1 h2 h3 h4 h5 h6) (@lem5278171 s h4)). Qed.
Lemma lem5282212 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : (term567 c' t) = False.
Proof. exact (prop_ext (fun h5 : term567 c' t => @lem5282203 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5278167 c' t h3)). Qed.
Lemma lem5282213 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282212 x s c' t h1 h2 h3 h4) (@lem5278167 c' t h3)). Qed.
Lemma lem5282214 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : (term31 t) = False.
Proof. exact (prop_ext (fun h5 : term31 t => @lem5282213 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5277880 t h2)). Qed.
Lemma lem5282215 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282214 x s c' t h1 h2 h3 h4) (@lem5277880 t h2)). Qed.
Lemma lem5282216 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : (term567 c' s) = False.
Proof. exact (prop_ext (fun h5 : term567 c' s => @lem5282207 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5277872 c' s h3)). Qed.
Lemma lem5282217 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282216 x s c' t h1 h2 h3 h4) (@lem5277872 c' s h3)). Qed.
Lemma lem5282218 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : (term31 s) = False.
Proof. exact (prop_ext (fun h5 : term31 s => @lem5282217 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5277581 s h2)). Qed.
Lemma lem5282219 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282218 x s c' t h1 h2 h3 h4) (@lem5277581 s h2)). Qed.
Lemma lem5282220 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : (term31 t) = False.
Proof. exact (prop_ext (fun h7 : term31 t => @lem5282209 x c x' s c' t h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5278456 t h4)). Qed.
Lemma lem5282221 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282220 x c x' s c' t h1 h2 h3 h4 h5 h6) (@lem5278456 t h4)). Qed.
Lemma lem5282222 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : (term31 s) = False.
Proof. exact (prop_ext (fun h7 : term31 s => @lem5282211 x b x' s c' t h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5278171 s h4)). Qed.
Lemma lem5282223 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s c' x') (h6 : term228 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282222 x b x' s c' t h1 h2 h3 h4 h5 h6) (@lem5278171 s h4)). Qed.
Lemma lem5282224 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : (term567 c' t) = False.
Proof. exact (prop_ext (fun h5 : term567 c' t => @lem5282215 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5278167 c' t h3)). Qed.
Lemma lem5282225 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282224 x s c' t h1 h2 h3 h4) (@lem5278167 c' t h3)). Qed.
Lemma lem5282226 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : (term31 t) = False.
Proof. exact (prop_ext (fun h5 : term31 t => @lem5282225 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5277880 t h2)). Qed.
Lemma lem5282227 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 t) (h3 : term567 c' t) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282226 x s c' t h1 h2 h3 h4) (@lem5277880 t h2)). Qed.
Lemma lem5282228 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : (term567 c' s) = False.
Proof. exact (prop_ext (fun h5 : term567 c' s => @lem5282219 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5277872 c' s h3)). Qed.
Lemma lem5282229 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282228 x s c' t h1 h2 h3 h4) (@lem5277872 c' s h3)). Qed.
Lemma lem5282230 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : (term31 s) = False.
Proof. exact (prop_ext (fun h5 : term31 s => @lem5282229 x s c' t h1 h2 h3 h4) (fun h5 : False => @lem5277581 s h2)). Qed.
Lemma lem5282231 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term567 c' s) (h4 : term160 s c' t) : False.
Proof. exact (EQ_MP (@lem5282230 x s c' t h1 h2 h3 h4) (@lem5277581 s h2)). Qed.
Lemma lem5282232 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term228 x' s c' t) : False.
Proof. exact (or_elim (@lem5277569 x' s c' t h7) (fun h0 : term134 s c' x' => @lem5282223 x b x' s c' t h1 h2 h3 h5 h0 h7) (fun h0 : term134 t c' x' => @lem5282221 x c x' s c' t h1 h2 h4 h6 h0 h7)). Qed.
Lemma lem5282233 (x : type1021) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term31 s) (h3 : term31 t) (h4 : term160 s c' t) : False.
Proof. exact (or_elim (@lem5277562 s c' t h4) (fun h0 : term567 c' s => @lem5282231 x s c' t h1 h2 h0 h4) (fun h0 : term567 c' t => @lem5282227 x s c' t h1 h3 h0 h4)). Qed.
Lemma lem5282234 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : False.
Proof. exact (or_elim (@lem5277559 x' s c' t h7) (fun h0 : term160 s c' t => @lem5282233 x s c' t h1 h5 h6 h0) (fun h0 : term228 x' s c' t => @lem5282232 x b c x' s c' t h1 h2 h3 h4 h5 h6 h0)). Qed.
Lemma lem5282235 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : (term259 x' s c' t) = False.
Proof. exact (prop_ext (fun h8 : term259 x' s c' t => @lem5282234 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5277559 x' s c' t h7)). Qed.
Lemma lem5282236 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282235 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (@lem5277559 x' s c' t h7)). Qed.
Lemma lem5282237 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : (term444 x) = False.
Proof. exact (prop_ext (fun h8 : term444 x => @lem5282236 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5277439 x h1)). Qed.
Lemma lem5282238 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282237 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (@lem5277439 x h1)). Qed.
Lemma lem5282239 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : (term31 t) = False.
Proof. exact (prop_ext (fun h8 : term31 t => @lem5282238 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5277266 t h6)). Qed.
Lemma lem5282240 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282239 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (@lem5277266 t h6)). Qed.
Lemma lem5282241 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : (term31 s) = False.
Proof. exact (prop_ext (fun h8 : term31 s => @lem5282240 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5277258 s h5)). Qed.
Lemma lem5282242 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (c' : real) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s c' t) : False.
Proof. exact (EQ_MP (@lem5282241 x b c x' s c' t h1 h2 h3 h4 h5 h6 h7) (@lem5277258 s h5)). Qed.
Lemma lem5282243 (x : type1021) (b : real) (c : real) (c' : real) (s : real -> Prop) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term262 s c' t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (ex_elim (@lem5277249 s c' t h5) (fun x' : real => fun h0 : term261 s c' t x' => @lem5282242 x b c x' s c' t h1 h2 h3 h4 h6 h7 h0)). Qed.
Lemma lem5282244 (x : type1021) (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (ex_elim (@lem5276635 s t h5) (fun c' : real => fun h0 : term263 s t c' => @lem5282243 x b c c' s t h1 h2 h3 h4 h0 h6 h7)). Qed.
Lemma lem5282245 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (ex_elim (@lem5277247 h1) (fun x : type1021 => fun h0 : term446 x => @lem5282244 x b c s t h0 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5282246 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : (term31 t) = False.
Proof. exact (prop_ext (fun h8 : term31 t => @lem5282245 b c s t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5275983 t h7)). Qed.
Lemma lem5282247 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (EQ_MP (@lem5282246 b c s t h1 h2 h3 h4 h5 h6 h7) (@lem5275983 t h7)). Qed.
Lemma lem5282248 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : (term31 s) = False.
Proof. exact (prop_ext (fun h8 : term31 s => @lem5282247 b c s t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5275977 s h6)). Qed.
Lemma lem5282249 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (EQ_MP (@lem5282248 b c s t h1 h2 h3 h4 h5 h6 h7) (@lem5275977 s h6)). Qed.
Lemma lem5282250 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term129) (h2 : term34 s b) (h3 : term34 t c) (h4 : term69 s t) (h5 : term31 s) (h6 : term31 t) : term74.
Proof. exact (fun h0 : term76 => @lem5282249 b c s t h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5282251 : term74 = term75.
Proof. exact (@lem69 term76). Qed.
Lemma lem5282252 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term129) (h2 : term34 s b) (h3 : term34 t c) (h4 : term69 s t) (h5 : term31 s) (h6 : term31 t) : term75.
Proof. exact (EQ_MP (@lem5282251) (@lem5282250 b c s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5282253 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : term79.
Proof. exact (fun h0 : term129 => @lem5282252 b c s t h0 h1 h2 h3 h4 h5). Qed.
Lemma lem5282254 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term82 s t.
Proof. exact (fun h0 : term69 s t => @lem5282253 b c s t h1 h2 h0 h3 h4). Qed.
Lemma lem5282255 (c : real) (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term31 s) (h3 : term31 t) : term85 c s t.
Proof. exact (fun h0 : term34 t c => @lem5282254 b c s t h1 h0 h2 h3). Qed.
Lemma lem5282256 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) : term87 b c s t.
Proof. exact (fun h0 : term34 s b => @lem5282255 c b s t h0 h1 h2). Qed.
Lemma lem5282257 (b : real) (c : real) (t : real -> Prop) (s : real -> Prop) (h1 : term31 s) : term90 b c s t.
Proof. exact (fun h0 : term31 t => @lem5282256 b c s t h1 h0). Qed.
Lemma lem5282258 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term91 b c s t.
Proof. exact (fun h0 : term31 s => @lem5282257 b c t s h0). Qed.
Lemma lem5282263 (c : real) (s : real -> Prop) (t : real -> Prop) : term95 c s t.
Proof. exact (fun b : real => @lem5282258 b c s t). Qed.
Lemma lem5282268 (s : real -> Prop) (t : real -> Prop) : term99 s t.
Proof. exact (fun c : real => @lem5282263 c s t). Qed.
Lemma lem5282273 (t : real -> Prop) : term103 t.
Proof. exact (fun s : real -> Prop => @lem5282268 s t). Qed.
Lemma lem5282278 : term107.
Proof. exact (fun t : real -> Prop => @lem5282273 t). Qed.
Lemma lem5282279 : term106.
Proof. exact (EQ_MP (@lem5275964) (@lem5282278)). Qed.
Lemma lem5282280 (t : real -> Prop) : term761 t.
Proof. exact (@lem5282279 t). Qed.
Lemma lem5282281 (t : real -> Prop) : (term761 t) = (term102 t).
Proof. exact (eq_refl (term761 t)). Qed.
Lemma lem5282282 (t : real -> Prop) : term102 t.
Proof. exact (EQ_MP (@lem5282281 t) (@lem5282280 t)). Qed.
Lemma lem5282283 (t : real -> Prop) (s : real -> Prop) : term762 t s.
Proof. exact (@lem5282282 t s). Qed.
Lemma lem5282284 (s : real -> Prop) (t : real -> Prop) : (term762 t s) = (term98 s t).
Proof. exact (eq_refl (term762 t s)). Qed.
Lemma lem5282285 (s : real -> Prop) (t : real -> Prop) : term98 s t.
Proof. exact (EQ_MP (@lem5282284 s t) (@lem5282283 t s)). Qed.
Lemma lem5282286 (s : real -> Prop) (t : real -> Prop) (c : real) : term763 s t c.
Proof. exact (@lem5282285 s t c). Qed.
Lemma lem5282287 (c : real) (s : real -> Prop) (t : real -> Prop) : (term763 s t c) = (term94 c s t).
Proof. exact (eq_refl (term763 s t c)). Qed.
Lemma lem5282288 (c : real) (s : real -> Prop) (t : real -> Prop) : term94 c s t.
Proof. exact (EQ_MP (@lem5282287 c s t) (@lem5282286 s t c)). Qed.
Lemma lem5282289 (c : real) (s : real -> Prop) (t : real -> Prop) (b : real) : term764 c s t b.
Proof. exact (@lem5282288 c s t b). Qed.
Lemma lem5282290 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term764 c s t b) = (term70 b c s t).
Proof. exact (eq_refl (term764 c s t b)). Qed.
Lemma lem5282291 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term70 b c s t.
Proof. exact (EQ_MP (@lem5282290 b c s t) (@lem5282289 c s t b)). Qed.
Lemma lem5282293 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term70 b c s t.
Proof. exact (@lem5275484 b c s t (@lem5282291 b c s t)). Qed.
Lemma lem5282294 (b : real) (c : real) (t : real -> Prop) (s : real -> Prop) (h1 : term31 s) : term89 b c s t.
Proof. exact (@lem5282293 b c s t (@lem5275388 s h1)). Qed.
Lemma lem5282295 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) : term86 b c s t.
Proof. exact (@lem5282294 b c t s h1 (@lem5275390 t h2)). Qed.
Lemma lem5282296 (c : real) (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term31 s) (h3 : term31 t) : term84 c s t.
Proof. exact (@lem5282295 b c s t h2 h3 (@lem5275393 s b h1)). Qed.
Lemma lem5282297 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term81 s t.
Proof. exact (@lem5282296 c b s t h1 h3 h4 (@lem5275394 t c h2)). Qed.
Lemma lem5282298 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : term78.
Proof. exact (@lem5282297 b c s t h1 h2 h4 h5 (@lem5275469 s t h3)). Qed.
Lemma lem5282299 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : term74.
Proof. exact (@lem5282298 b c s t h1 h2 h3 h4 h5 (@lem1339577)). Qed.
Lemma lem5282300 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : False.
Proof. exact (@lem5282299 b c s t h1 h2 h3 h4 h5 (@lem5214027)). Qed.
Lemma lem5282301 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : (term69 s t) = False.
Proof. exact (prop_ext (fun h6 : term69 s t => @lem5282300 b c s t h1 h2 h3 h4 h5) (fun h6 : False => @lem5275469 s t h3)). Qed.
Lemma lem5282302 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : False.
Proof. exact (EQ_MP (@lem5282301 b c s t h1 h2 h3 h4 h5) (@lem5275469 s t h3)). Qed.
Lemma lem5282303 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term68 s t.
Proof. exact (fun h0 : term69 s t => @lem5282302 b c s t h1 h2 h0 h3 h4). Qed.
Lemma lem5282304 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term66 s t.
Proof. exact (EQ_MP (@lem5275468 s t) (@lem5282303 b c s t h1 h2 h3 h4)). Qed.
Lemma lem5282305 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term65 s t.
Proof. exact (EQ_MP (@lem5275464 s t) (@lem5282304 b c s t h1 h2 h3 h4)). Qed.
Lemma lem5282306 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (@lem5275397 s t (@lem5282305 b c s t h1 h2 h3 h4)). Qed.
Lemma lem5282307 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : term30 s t.
Proof. exact (proj2 (@lem5275386 s t h1)). Qed.
Lemma lem5282308 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : term31 s.
Proof. exact (proj1 (@lem5275386 s t h1)). Qed.
Lemma lem5282309 (s : real -> Prop) (t : real -> Prop) (h1 : term30 s t) : term32 s t.
Proof. exact (proj2 (@lem5275387 s t h1)). Qed.
Lemma lem5282310 (s : real -> Prop) (t : real -> Prop) (h1 : term30 s t) : term31 t.
Proof. exact (proj1 (@lem5275387 s t h1)). Qed.
Lemma lem5282311 (s : real -> Prop) (t : real -> Prop) (h1 : term32 s t) : term33 t.
Proof. exact (proj2 (@lem5275389 s t h1)). Qed.
Lemma lem5282312 (s : real -> Prop) (t : real -> Prop) (h1 : term32 s t) : term33 s.
Proof. exact (proj1 (@lem5275389 s t h1)). Qed.
Lemma lem5282313 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : (term34 t c) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h5 : term34 t c => @lem5282306 b c s t h1 h2 h3 h4) (fun h5 : (term765 s t) = (term36 s t) => @lem5275394 t c h2)). Qed.
Lemma lem5282314 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282313 b c s t h1 h2 h3 h4) (@lem5275394 t c h2)). Qed.
Lemma lem5282315 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (ex_elim (@lem5275391 t h2) (fun c : real => fun h0 : term117 t c => @lem5282314 b c s t h1 h0 h3 h4)). Qed.
Lemma lem5282316 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term34 s b) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h5 : term34 s b => @lem5282315 b s t h1 h2 h3 h4) (fun h5 : (term765 s t) = (term36 s t) => @lem5275393 s b h1)). Qed.
Lemma lem5282317 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282316 b s t h1 h2 h3 h4) (@lem5275393 s b h1)). Qed.
Lemma lem5282318 (s : real -> Prop) (t : real -> Prop) (h1 : term33 s) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (ex_elim (@lem5275392 s h1) (fun b : real => fun h0 : term117 s b => @lem5282317 b s t h0 h2 h3 h4)). Qed.
Lemma lem5282319 (s : real -> Prop) (t : real -> Prop) (h1 : term33 s) (h2 : term31 s) (h3 : term31 t) (h4 : term32 s t) : (term33 t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h5 : term33 t => @lem5282318 s t h1 h5 h2 h3) (fun h5 : (term765 s t) = (term36 s t) => @lem5282311 s t h4)). Qed.
Lemma lem5282320 (s : real -> Prop) (t : real -> Prop) (h1 : term33 s) (h2 : term31 s) (h3 : term31 t) (h4 : term32 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282319 s t h1 h2 h3 h4) (@lem5282311 s t h4)). Qed.
Lemma lem5282321 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term33 s) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h4 : term33 s => @lem5282320 s t h4 h1 h2 h3) (fun h4 : (term765 s t) = (term36 s t) => @lem5282312 s t h3)). Qed.
Lemma lem5282322 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282321 s t h1 h2 h3) (@lem5282312 s t h3)). Qed.
Lemma lem5282323 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term31 t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h4 : term31 t => @lem5282322 s t h1 h2 h3) (fun h4 : (term765 s t) = (term36 s t) => @lem5275390 t h2)). Qed.
Lemma lem5282324 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282323 s t h1 h2 h3) (@lem5275390 t h2)). Qed.
Lemma lem5282325 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term30 s t) : (term32 s t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h4 : term32 s t => @lem5282324 s t h1 h2 h4) (fun h4 : (term765 s t) = (term36 s t) => @lem5282309 s t h3)). Qed.
Lemma lem5282326 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term30 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282325 s t h1 h2 h3) (@lem5282309 s t h3)). Qed.
Lemma lem5282327 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term31 t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h3 : term31 t => @lem5282326 s t h1 h3 h2) (fun h3 : (term765 s t) = (term36 s t) => @lem5282310 s t h2)). Qed.
Lemma lem5282328 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282327 s t h1 h2) (@lem5282310 s t h2)). Qed.
Lemma lem5282329 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term31 s) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h3 : term31 s => @lem5282328 s t h1 h2) (fun h3 : (term765 s t) = (term36 s t) => @lem5275388 s h1)). Qed.
Lemma lem5282330 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282329 s t h1 h2) (@lem5275388 s h1)). Qed.
Lemma lem5282331 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term29 s t) : (term30 s t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h3 : term30 s t => @lem5282330 s t h1 h3) (fun h3 : (term765 s t) = (term36 s t) => @lem5282307 s t h2)). Qed.
Lemma lem5282332 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term29 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282331 s t h1 h2) (@lem5282307 s t h2)). Qed.
Lemma lem5282333 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : (term31 s) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h2 : term31 s => @lem5282332 s t h2 h1) (fun h2 : (term765 s t) = (term36 s t) => @lem5282308 s t h1)). Qed.
Lemma lem5282334 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5282333 s t h1) (@lem5282308 s t h1)). Qed.
Lemma lem5282335 (s : real -> Prop) (t : real -> Prop) : term766 s t.
Proof. exact (fun h0 : term29 s t => @lem5282334 s t h0). Qed.
Lemma lem5282340 (s : real -> Prop) : term767 s.
Proof. exact (fun t : real -> Prop => @lem5282335 s t). Qed.
Lemma lem5282345 : term768.
Proof. exact (fun s : real -> Prop => @lem5282340 s). Qed.
