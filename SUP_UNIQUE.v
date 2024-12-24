Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_UNIQUE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUP_EQ_spec.
Require Import SUP_SING_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem5188260 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem5188261 (s : real -> Prop) (h1 : term0) : term1 s.
Proof. exact (@lem5188260 h1 s). Qed.
Lemma lem5188262 (s : real -> Prop) : (term1 s) = (term2 s).
Proof. exact (eq_refl (term1 s)). Qed.
Lemma lem5188263 (s : real -> Prop) (h1 : term0) : term2 s.
Proof. exact (EQ_MP (@lem5188262 s) (@lem5188261 s h1)). Qed.
Lemma lem5188264 (s : real -> Prop) (t : real -> Prop) (h1 : term0) : term3 s t.
Proof. exact (@lem5188263 s h1 t). Qed.
Lemma lem5188265 (s : real -> Prop) (t : real -> Prop) : (term3 s t) = (term4 s t).
Proof. exact (eq_refl (term3 s t)). Qed.
Lemma lem5188266 (s : real -> Prop) (t : real -> Prop) (h1 : term0) : term4 s t.
Proof. exact (EQ_MP (@lem5188265 s t) (@lem5188264 s t h1)). Qed.
Lemma lem5188267 (s : real -> Prop) (t : real -> Prop) (h1 : term5 s t) : term5 s t.
Proof. exact (h1). Qed.
Lemma lem5188268 (s : real -> Prop) (t : real -> Prop) (h1 : term0) (h2 : term5 s t) : (sup s) = (sup t).
Proof. exact (@lem5188266 s t h1 (@lem5188267 s t h2)). Qed.
Lemma lem5188269 (s : real -> Prop) (t : real -> Prop) (h1 : term5 s t) : term6 s t.
Proof. exact (fun h0 : term0 => @lem5188268 s t h0 h1). Qed.
Lemma lem5188270 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem5188271 (s : real -> Prop) (t : real -> Prop) (h1 : term0) (h2 : term5 s t) : (sup s) = (sup t).
Proof. exact (@lem5188269 s t h2 (@lem5188270 h1)). Qed.
Lemma lem5188272 (s : real -> Prop) (t : real -> Prop) (h1 : term0) : term4 s t.
Proof. exact (fun h0 : term5 s t => @lem5188271 s t h1 h0). Qed.
Lemma lem5188273 (s : real -> Prop) (h1 : term0) : term2 s.
Proof. exact (fun t : real -> Prop => @lem5188272 s t h1). Qed.
Lemma lem5188274 (h1 : term0) : term0.
Proof. exact (fun s : real -> Prop => @lem5188273 s h1). Qed.
Lemma lem5188275 : term7.
Proof. exact (fun h0 : term0 => @lem5188274 h0). Qed.
Lemma lem5188276 : term0.
Proof. exact (@lem5188275 (@lem5135108)). Qed.
Lemma lem5188277 (s : real -> Prop) : term1 s.
Proof. exact (@lem5188276 s). Qed.
Lemma lem5188278 (s : real -> Prop) : (term1 s) = (term2 s).
Proof. exact (eq_refl (term1 s)). Qed.
Lemma lem5188279 (s : real -> Prop) : term2 s.
Proof. exact (EQ_MP (@lem5188278 s) (@lem5188277 s)). Qed.
Lemma lem5188280 (s : real -> Prop) (t : real -> Prop) : term3 s t.
Proof. exact (@lem5188279 s t). Qed.
Lemma lem5188281 (s : real -> Prop) (t : real -> Prop) : (term3 s t) = (term4 s t).
Proof. exact (eq_refl (term3 s t)). Qed.
Lemma lem5188284 (a : real) (h1 : (term8 a) = a) : (term8 a) = a.
Proof. exact (h1). Qed.
Lemma lem5188285 (a : real) (h1 : (term8 a) = a) : a = (term8 a).
Proof. exact (SYM (@lem5188284 a h1)). Qed.
Lemma lem5188286 (a : real) (h1 : a = (term8 a)) : a = (term8 a).
Proof. exact (h1). Qed.
Lemma lem5188287 (a : real) (h1 : a = (term8 a)) : (term8 a) = a.
Proof. exact (SYM (@lem5188286 a h1)). Qed.
Lemma lem5188288 (a : real) : ((term8 a) = a) = (a = (term8 a)).
Proof. exact (prop_ext (fun h1 : (term8 a) = a => @lem5188285 a h1) (fun h1 : a = (term8 a) => @lem5188287 a h1)). Qed.
Lemma lem5188289 : term9 = term10.
Proof. exact (fun_ext (fun a : real => @lem5188288 a)). Qed.
Lemma lem5188290 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188291 : term11 = term12.
Proof. exact (MK_COMB (@lem5188290) (@lem5188289)). Qed.
Lemma lem5188292 : term12.
Proof. exact (EQ_MP (@lem5188291) (@lem5178241)). Qed.
Lemma lem5188293 (a : real) : term13 a.
Proof. exact (@lem5188292 a). Qed.
Lemma lem5188294 (a : real) : (term13 a) = (a = (term8 a)).
Proof. exact (eq_refl (term13 a)). Qed.
Lemma lem5188296 (s : real -> Prop) (b : real) (h1 : term14 s b) : term14 s b.
Proof. exact (h1). Qed.
Lemma lem5188298 (a : real) : a = (term8 a).
Proof. exact (EQ_MP (@lem5188294 a) (@lem5188293 a)). Qed.
Lemma lem5188299 (b : real) : b = (term8 b).
Proof. exact (@lem5188298 b). Qed.
Lemma lem5188300 (s : real -> Prop) : (term15 s) = (term15 s).
Proof. exact (eq_refl (term15 s)). Qed.
Lemma lem5188301 (s : real -> Prop) (b : real) : ((sup s) = b) = ((sup s) = (term8 b)).
Proof. exact (MK_COMB (@lem5188300 s) (@lem5188299 b)). Qed.
Lemma lem5188302 (s : real -> Prop) (b : real) : ((sup s) = (term8 b)) = ((sup s) = b).
Proof. exact (SYM (@lem5188301 s b)). Qed.
Lemma lem5188304 (s : real -> Prop) (t : real -> Prop) : term4 s t.
Proof. exact (EQ_MP (@lem5188281 s t) (@lem5188280 s t)). Qed.
Lemma lem5188305 (s : real -> Prop) (b : real) : term16 s b.
Proof. exact (@lem5188304 s (@INSERT real b (@EMPTY real))). Qed.
Lemma lem5188306 (t1 : Prop) : term17 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5188307 (t1 : Prop) : (term17 t1) = (term18 t1).
Proof. exact (eq_refl (term17 t1)). Qed.
Lemma lem5188308 (t1 : Prop) : term18 t1.
Proof. exact (EQ_MP (@lem5188307 t1) (@lem5188306 t1)). Qed.
Lemma lem5188309 (t1 : Prop) (t2 : Prop) : term19 t1 t2.
Proof. exact (@lem5188308 t1 t2). Qed.
Lemma lem5188310 (t1 : Prop) (t2 : Prop) : (term19 t1 t2) = (term20 t1 t2).
Proof. exact (eq_refl (term19 t1 t2)). Qed.
Lemma lem5188311 (t1 : Prop) (t2 : Prop) : term20 t1 t2.
Proof. exact (EQ_MP (@lem5188310 t1 t2) (@lem5188309 t1 t2)). Qed.
Lemma lem5188312 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term21 t1 t2 t3.
Proof. exact (@lem5188311 t1 t2 t3). Qed.
Lemma lem5188313 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = ((term22 t1 t2 t3) = (term23 t1 t2 t3)).
Proof. exact (eq_refl (term21 t1 t2 t3)). Qed.
Lemma lem5188314 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term22 t1 t2 t3) = (term23 t1 t2 t3).
Proof. exact (EQ_MP (@lem5188313 t1 t2 t3) (@lem5188312 t1 t2 t3)). Qed.
Lemma lem5188315 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term23 t1 t2 t3) = (term22 t1 t2 t3).
Proof. exact (SYM (@lem5188314 t1 t2 t3)). Qed.
Lemma lem5188369 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5188370 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5188369 real P x). Qed.
Lemma lem5188371 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5188370 s x). Qed.
Lemma lem5188372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5188373 (s : real -> Prop) (x : real) : (term24 x s) = (term25 s x).
Proof. exact (MK_COMB (@lem5188372) (@lem5188371 s x)). Qed.
Lemma lem5188374 (x : real) (c : real) : (real_le x c) = (real_le x c).
Proof. exact (eq_refl (real_le x c)). Qed.
Lemma lem5188375 (s : real -> Prop) (x : real) (c : real) : (term26 s x c) = (term27 s x c).
Proof. exact (MK_COMB (@lem5188373 s x) (@lem5188374 x c)). Qed.
Lemma lem5188378 (s : real -> Prop) (c : real) : (term28 s c) = (term29 s c).
Proof. exact (fun_ext (fun x : real => @lem5188375 s x c)). Qed.
Lemma lem5188379 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188380 (s : real -> Prop) (c : real) : (term30 s c) = (term31 s c).
Proof. exact (MK_COMB (@lem5188379) (@lem5188378 s c)). Qed.
Lemma lem5188385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188386 (s : real -> Prop) (c : real) : (term32 s c) = (term33 s c).
Proof. exact (MK_COMB (@lem5188385) (@lem5188380 s c)). Qed.
Lemma lem5188387 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5188388 (s : real -> Prop) (b : real) (c : real) : ((term30 s c) = (real_le b c)) = ((term31 s c) = (real_le b c)).
Proof. exact (MK_COMB (@lem5188386 s c) (@lem5188387 b c)). Qed.
Lemma lem5188391 (s : real -> Prop) (b : real) : (term34 s b) = (term35 s b).
Proof. exact (fun_ext (fun c : real => @lem5188388 s b c)). Qed.
Lemma lem5188392 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188393 (s : real -> Prop) (b : real) : (term14 s b) = (term36 s b).
Proof. exact (MK_COMB (@lem5188392) (@lem5188391 s b)). Qed.
Lemma lem5188398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5188399 (s : real -> Prop) (b : real) : (term37 s b) = (term38 s b).
Proof. exact (MK_COMB (@lem5188398) (@lem5188393 s b)). Qed.
Lemma lem5188413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5188414 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5188413 real P x). Qed.
Lemma lem5188415 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5188414 s x). Qed.
Lemma lem5188416 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5188417 (s : real -> Prop) (x : real) : (term24 x s) = (term25 s x).
Proof. exact (MK_COMB (@lem5188416) (@lem5188415 s x)). Qed.
Lemma lem5188418 (x : real) (b' : real) : (real_le x b') = (real_le x b').
Proof. exact (eq_refl (real_le x b')). Qed.
Lemma lem5188419 (s : real -> Prop) (x : real) (b' : real) : (term26 s x b') = (term27 s x b').
Proof. exact (MK_COMB (@lem5188417 s x) (@lem5188418 x b')). Qed.
Lemma lem5188422 (s : real -> Prop) (b' : real) : (term28 s b') = (term29 s b').
Proof. exact (fun_ext (fun x : real => @lem5188419 s x b')). Qed.
Lemma lem5188423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188424 (s : real -> Prop) (b' : real) : (term30 s b') = (term31 s b').
Proof. exact (MK_COMB (@lem5188423) (@lem5188422 s b')). Qed.
Lemma lem5188429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188430 (s : real -> Prop) (b' : real) : (term32 s b') = (term33 s b').
Proof. exact (MK_COMB (@lem5188429) (@lem5188424 s b')). Qed.
Lemma lem5188438 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term39 A x y s) = (term40 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5188439 (y : real) (x : real) (s : real -> Prop) : (term41 x y s) = (term42 y x s).
Proof. exact (@lem5188438 real y x s). Qed.
Lemma lem5188440 (b : real) (x : real) : (term43 x b) = (term44 b x).
Proof. exact (@lem5188439 b x (@EMPTY real)). Qed.
Lemma lem5188446 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5188447 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5188446 real x). Qed.
Lemma lem5188448 (x : real) (b : real) : (term45 x b) = (term45 x b).
Proof. exact (eq_refl (term45 x b)). Qed.
Lemma lem5188449 (x : real) (b : real) : (term44 b x) = (term46 x b).
Proof. exact (MK_COMB (@lem5188448 x b) (@lem5188447 x)). Qed.
Lemma lem5188451 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5188452 (x : real) (b : real) : (term46 x b) = (x = b).
Proof. exact (@lem5188451 (x = b)). Qed.
Lemma lem5188455 (x : real) (b : real) : (term44 b x) = (x = b).
Proof. exact (TRANS (@lem5188449 x b) (@lem5188452 x b)). Qed.
Lemma lem5188456 (x : real) (b : real) : (term43 x b) = (x = b).
Proof. exact (TRANS (@lem5188440 b x) (@lem5188455 x b)). Qed.
Lemma lem5188457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5188458 (x : real) (b : real) : (term47 x b) = (term48 x b).
Proof. exact (MK_COMB (@lem5188457) (@lem5188456 x b)). Qed.
Lemma lem5188459 (x : real) (b' : real) : (real_le x b') = (real_le x b').
Proof. exact (eq_refl (real_le x b')). Qed.
Lemma lem5188460 (b : real) (x : real) (b' : real) : (term49 b x b') = (term50 b x b').
Proof. exact (MK_COMB (@lem5188458 x b) (@lem5188459 x b')). Qed.
Lemma lem5188465 (b : real) (b' : real) : (term51 b b') = (term52 b b').
Proof. exact (fun_ext (fun x : real => @lem5188460 b x b')). Qed.
Lemma lem5188466 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188467 (b : real) (b' : real) : (term53 b b') = (term54 b b').
Proof. exact (MK_COMB (@lem5188466) (@lem5188465 b b')). Qed.
Lemma lem5188472 (s : real -> Prop) (b : real) (b' : real) : ((term30 s b') = (term53 b b')) = ((term31 s b') = (term54 b b')).
Proof. exact (MK_COMB (@lem5188430 s b') (@lem5188467 b b')). Qed.
Lemma lem5188475 (s : real -> Prop) (b : real) : (term55 s b) = (term56 s b).
Proof. exact (fun_ext (fun b' : real => @lem5188472 s b b')). Qed.
Lemma lem5188476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188477 (s : real -> Prop) (b : real) : (term57 s b) = (term58 s b).
Proof. exact (MK_COMB (@lem5188476) (@lem5188475 s b)). Qed.
Lemma lem5188482 (s : real -> Prop) (b : real) : (term59 s b) = (term60 s b).
Proof. exact (MK_COMB (@lem5188399 s b) (@lem5188477 s b)). Qed.
Lemma lem5188485 (s : real -> Prop) (b : real) : (term60 s b) = (term59 s b).
Proof. exact (SYM (@lem5188482 s b)). Qed.
Lemma lem5188487 (p : Prop) : p = (term61 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5188488 (s : real -> Prop) (b : real) : (term60 s b) = (term62 s b).
Proof. exact (@lem5188487 (term60 s b)). Qed.
Lemma lem5188489 (s : real -> Prop) (b : real) : (term62 s b) = (term60 s b).
Proof. exact (SYM (@lem5188488 s b)). Qed.
Lemma lem5188490 (s : real -> Prop) (b : real) (h1 : term63 s b) : term63 s b.
Proof. exact (h1). Qed.
Lemma lem5188493 (s : real -> Prop) (b : real) (h1 : term62 s b) : term62 s b.
Proof. exact (h1). Qed.
Lemma lem5188494 (s : real -> Prop) (b : real) : term64 s b.
Proof. exact (fun h0 : term62 s b => @lem5188493 s b h0). Qed.
Lemma lem5188495 (s : real -> Prop) (b : real) (h1 : term64 s b) : term64 s b.
Proof. exact (h1). Qed.
Lemma lem5188496 (s : real -> Prop) (b : real) (h1 : term62 s b) : term62 s b.
Proof. exact (h1). Qed.
Lemma lem5188497 (s : real -> Prop) (b : real) (h1 : term62 s b) (h2 : term64 s b) : term62 s b.
Proof. exact (@lem5188495 s b h2 (@lem5188496 s b h1)). Qed.
Lemma lem5188498 (s : real -> Prop) (b : real) (h1 : term62 s b) : term65 s b.
Proof. exact (fun h0 : term64 s b => @lem5188497 s b h1 h0). Qed.
Lemma lem5188499 (s : real -> Prop) (b : real) (h1 : term64 s b) : term64 s b.
Proof. exact (h1). Qed.
Lemma lem5188500 (s : real -> Prop) (b : real) (h1 : term62 s b) (h2 : term64 s b) : term62 s b.
Proof. exact (@lem5188498 s b h1 (@lem5188499 s b h2)). Qed.
Lemma lem5188501 (s : real -> Prop) (b : real) (h1 : term64 s b) : term64 s b.
Proof. exact (fun h0 : term62 s b => @lem5188500 s b h0 h1). Qed.
Lemma lem5188502 (s : real -> Prop) (b : real) : term66 s b.
Proof. exact (fun h0 : term64 s b => @lem5188501 s b h0). Qed.
Lemma lem5188505 (s : real -> Prop) (b : real) : term64 s b.
Proof. exact (@lem5188502 s b (@lem5188494 s b)). Qed.
Lemma lem5188515 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5188516 (s : real -> Prop) (b : real) : (term62 s b) = (term67 s b).
Proof. exact (@lem5188515 (term63 s b)). Qed.
Lemma lem5188518 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5188519 (s : real -> Prop) (b : real) : (term67 s b) = (term60 s b).
Proof. exact (@lem5188518 (term60 s b)). Qed.
Lemma lem5188522 (s : real -> Prop) (b : real) : (term62 s b) = (term60 s b).
Proof. exact (TRANS (@lem5188516 s b) (@lem5188519 s b)). Qed.
Lemma lem5188549 (b : real) : (term69 b) = (term70 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5188522 s b)). Qed.
Lemma lem5188550 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5188551 (b : real) : (term71 b) = (term72 b).
Proof. exact (MK_COMB (@lem5188550) (@lem5188549 b)). Qed.
Lemma lem5188556 : term73 = term74.
Proof. exact (fun_ext (fun b : real => @lem5188551 b)). Qed.
Lemma lem5188557 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188566 : term75 = term76.
Proof. exact (MK_COMB (@lem5188557) (@lem5188556)). Qed.
Lemma lem5188571 (b : real) (x : real) (b' : real) : (term50 b x b') = (term50 b x b').
Proof. exact (eq_refl (term50 b x b')). Qed.
Lemma lem5188572 (b : real) (b' : real) : (term52 b b') = (term52 b b').
Proof. exact (fun_ext (fun x : real => @lem5188571 b x b')). Qed.
Lemma lem5188573 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188574 (b : real) (b' : real) : (term54 b b') = (term54 b b').
Proof. exact (MK_COMB (@lem5188573) (@lem5188572 b b')). Qed.
Lemma lem5188579 (s : real -> Prop) (x : real) (b' : real) : (term27 s x b') = (term27 s x b').
Proof. exact (eq_refl (term27 s x b')). Qed.
Lemma lem5188580 (s : real -> Prop) (b' : real) : (term29 s b') = (term29 s b').
Proof. exact (fun_ext (fun x : real => @lem5188579 s x b')). Qed.
Lemma lem5188581 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188582 (s : real -> Prop) (b' : real) : (term31 s b') = (term31 s b').
Proof. exact (MK_COMB (@lem5188581) (@lem5188580 s b')). Qed.
Lemma lem5188583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188584 (s : real -> Prop) (b' : real) : (term33 s b') = (term33 s b').
Proof. exact (MK_COMB (@lem5188583) (@lem5188582 s b')). Qed.
Lemma lem5188585 (s : real -> Prop) (b : real) (b' : real) : ((term31 s b') = (term54 b b')) = ((term31 s b') = (term54 b b')).
Proof. exact (MK_COMB (@lem5188584 s b') (@lem5188574 b b')). Qed.
Lemma lem5188586 (s : real -> Prop) (b : real) : (term56 s b) = (term56 s b).
Proof. exact (fun_ext (fun b' : real => @lem5188585 s b b')). Qed.
Lemma lem5188587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188588 (s : real -> Prop) (b : real) : (term58 s b) = (term58 s b).
Proof. exact (MK_COMB (@lem5188587) (@lem5188586 s b)). Qed.
Lemma lem5188589 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5188594 (s : real -> Prop) (x : real) (c : real) : (term27 s x c) = (term27 s x c).
Proof. exact (eq_refl (term27 s x c)). Qed.
Lemma lem5188595 (s : real -> Prop) (c : real) : (term29 s c) = (term29 s c).
Proof. exact (fun_ext (fun x : real => @lem5188594 s x c)). Qed.
Lemma lem5188596 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188597 (s : real -> Prop) (c : real) : (term31 s c) = (term31 s c).
Proof. exact (MK_COMB (@lem5188596) (@lem5188595 s c)). Qed.
Lemma lem5188598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188599 (s : real -> Prop) (c : real) : (term33 s c) = (term33 s c).
Proof. exact (MK_COMB (@lem5188598) (@lem5188597 s c)). Qed.
Lemma lem5188600 (s : real -> Prop) (b : real) (c : real) : ((term31 s c) = (real_le b c)) = ((term31 s c) = (real_le b c)).
Proof. exact (MK_COMB (@lem5188599 s c) (@lem5188589 b c)). Qed.
Lemma lem5188601 (s : real -> Prop) (b : real) : (term35 s b) = (term35 s b).
Proof. exact (fun_ext (fun c : real => @lem5188600 s b c)). Qed.
Lemma lem5188602 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188603 (s : real -> Prop) (b : real) : (term36 s b) = (term36 s b).
Proof. exact (MK_COMB (@lem5188602) (@lem5188601 s b)). Qed.
Lemma lem5188604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5188605 (s : real -> Prop) (b : real) : (term38 s b) = (term38 s b).
Proof. exact (MK_COMB (@lem5188604) (@lem5188603 s b)). Qed.
Lemma lem5188606 (s : real -> Prop) (b : real) : (term60 s b) = (term60 s b).
Proof. exact (MK_COMB (@lem5188605 s b) (@lem5188588 s b)). Qed.
Lemma lem5188607 (b : real) : (term70 b) = (term70 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5188606 s b)). Qed.
Lemma lem5188608 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5188609 (b : real) : (term72 b) = (term72 b).
Proof. exact (MK_COMB (@lem5188608) (@lem5188607 b)). Qed.
Lemma lem5188610 : term74 = term74.
Proof. exact (fun_ext (fun b : real => @lem5188609 b)). Qed.
Lemma lem5188611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188612 : term76 = term76.
Proof. exact (MK_COMB (@lem5188611) (@lem5188610)). Qed.
Lemma lem5188665 : term75 = term76.
Proof. exact (TRANS (@lem5188566) (@lem5188612)). Qed.
Lemma lem5188666 : term76 = term75.
Proof. exact (SYM (@lem5188665)). Qed.
Lemma lem5188667 (s : real -> Prop) (b : real) (h1 : term36 s b) : term36 s b.
Proof. exact (h1). Qed.
Lemma lem5188669 (p : Prop) : p = (term61 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5188670 (s : real -> Prop) (b : real) (b' : real) : ((term31 s b') = (term54 b b')) = (term77 s b b').
Proof. exact (@lem5188669 ((term31 s b') = (term54 b b'))). Qed.
Lemma lem5188671 (s : real -> Prop) (b : real) (b' : real) : (term77 s b b') = ((term31 s b') = (term54 b b')).
Proof. exact (SYM (@lem5188670 s b b')). Qed.
Lemma lem5188672 (s : real -> Prop) (b : real) (b' : real) (h1 : term78 s b b') : term78 s b b'.
Proof. exact (h1). Qed.
Lemma lem5188681 (s : real -> Prop) (x : real) (c : real) : (term79 s x c) = (term80 s x c).
Proof. exact (@lem17362 (s x) (real_le x c)). Qed.
Lemma lem5188686 (s : real -> Prop) (x : real) (c : real) : (term27 s x c) = (term81 s x c).
Proof. exact (@lem17265 (s x) (real_le x c)). Qed.
Lemma lem5188687 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5188688 (s : real -> Prop) (c : real) : (term84 s c) = (term85 s c).
Proof. exact (@lem5188687 (term29 s c)). Qed.
Lemma lem5188689 (s : real -> Prop) (x : real) (c : real) : (term86 s c x) = (term27 s x c).
Proof. exact (eq_refl (term86 s c x)). Qed.
Lemma lem5188690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5188691 (s : real -> Prop) (x : real) (c : real) : (term87 s c x) = (term79 s x c).
Proof. exact (MK_COMB (@lem5188690) (@lem5188689 s x c)). Qed.
Lemma lem5188692 (s : real -> Prop) (x : real) (c : real) : (term87 s c x) = (term80 s x c).
Proof. exact (TRANS (@lem5188691 s x c) (@lem5188681 s x c)). Qed.
Lemma lem5188693 (s : real -> Prop) (c : real) : (term88 s c) = (term89 s c).
Proof. exact (fun_ext (fun x : real => @lem5188692 s x c)). Qed.
Lemma lem5188694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5188695 (s : real -> Prop) (c : real) : (term85 s c) = (term90 s c).
Proof. exact (MK_COMB (@lem5188694) (@lem5188693 s c)). Qed.
Lemma lem5188696 (s : real -> Prop) (c : real) : (term84 s c) = (term90 s c).
Proof. exact (TRANS (@lem5188688 s c) (@lem5188695 s c)). Qed.
Lemma lem5188697 (s : real -> Prop) (c : real) : (term29 s c) = (term91 s c).
Proof. exact (fun_ext (fun x : real => @lem5188686 s x c)). Qed.
Lemma lem5188698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188699 (s : real -> Prop) (c : real) : (term31 s c) = (term92 s c).
Proof. exact (MK_COMB (@lem5188698) (@lem5188697 s c)). Qed.
Lemma lem5188700 (b : real) (c : real) : (term93 b c) = (term93 b c).
Proof. exact (eq_refl (term93 b c)). Qed.
Lemma lem5188701 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5188702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5188703 (s : real -> Prop) (c : real) : (term94 s c) = (term95 s c).
Proof. exact (MK_COMB (@lem5188702) (@lem5188696 s c)). Qed.
Lemma lem5188704 (s : real -> Prop) (b : real) (c : real) : (term96 s b c) = (term97 s b c).
Proof. exact (MK_COMB (@lem5188703 s c) (@lem5188701 b c)). Qed.
Lemma lem5188705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5188706 (s : real -> Prop) (c : real) : (term98 s c) = (term99 s c).
Proof. exact (MK_COMB (@lem5188705) (@lem5188699 s c)). Qed.
Lemma lem5188707 (s : real -> Prop) (b : real) (c : real) : (term100 s b c) = (term101 s b c).
Proof. exact (MK_COMB (@lem5188706 s c) (@lem5188700 b c)). Qed.
Lemma lem5188708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5188709 (s : real -> Prop) (b : real) (c : real) : (term102 s b c) = (term103 s b c).
Proof. exact (MK_COMB (@lem5188708) (@lem5188707 s b c)). Qed.
Lemma lem5188710 (s : real -> Prop) (b : real) (c : real) : (term104 s b c) = (term105 s b c).
Proof. exact (MK_COMB (@lem5188709 s b c) (@lem5188704 s b c)). Qed.
Lemma lem5188711 (s : real -> Prop) (b : real) (c : real) : ((term31 s c) = (real_le b c)) = (term104 s b c).
Proof. exact (@lem17784 (term31 s c) (real_le b c)). Qed.
Lemma lem5188712 (s : real -> Prop) (b : real) (c : real) : ((term31 s c) = (real_le b c)) = (term105 s b c).
Proof. exact (TRANS (@lem5188711 s b c) (@lem5188710 s b c)). Qed.
Lemma lem5188713 (s : real -> Prop) (b : real) : (term35 s b) = (term106 s b).
Proof. exact (fun_ext (fun c : real => @lem5188712 s b c)). Qed.
Lemma lem5188714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188715 (s : real -> Prop) (b : real) : (term36 s b) = (term107 s b).
Proof. exact (MK_COMB (@lem5188714) (@lem5188713 s b)). Qed.
Lemma lem5188717 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5188718 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem5188717 real P Q). Qed.
Lemma lem5188719 (s : real -> Prop) (b : real) : (term112 s b) = (term113 s b).
Proof. exact (@lem5188718 (term114 s b) (term115 s b)). Qed.
Lemma lem5188720 (s : real -> Prop) (b : real) (c : real) : (term116 s b c) = (term101 s b c).
Proof. exact (eq_refl (term116 s b c)). Qed.
Lemma lem5188721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5188722 (s : real -> Prop) (b : real) (c : real) : (term117 s b c) = (term103 s b c).
Proof. exact (MK_COMB (@lem5188721) (@lem5188720 s b c)). Qed.
Lemma lem5188723 (s : real -> Prop) (b : real) (c : real) : (term118 s b c) = (term97 s b c).
Proof. exact (eq_refl (term118 s b c)). Qed.
Lemma lem5188724 (s : real -> Prop) (b : real) (c : real) : (term119 s b c) = (term105 s b c).
Proof. exact (MK_COMB (@lem5188722 s b c) (@lem5188723 s b c)). Qed.
Lemma lem5188725 (s : real -> Prop) (b : real) : (term120 s b) = (term106 s b).
Proof. exact (fun_ext (fun c : real => @lem5188724 s b c)). Qed.
Lemma lem5188726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188727 (s : real -> Prop) (b : real) : (term112 s b) = (term107 s b).
Proof. exact (MK_COMB (@lem5188726) (@lem5188725 s b)). Qed.
Lemma lem5188728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188729 (s : real -> Prop) (b : real) : (term121 s b) = (term122 s b).
Proof. exact (MK_COMB (@lem5188728) (@lem5188727 s b)). Qed.
Lemma lem5188730 (s : real -> Prop) (b : real) (c : real) : (term116 s b c) = (term101 s b c).
Proof. exact (eq_refl (term116 s b c)). Qed.
Lemma lem5188731 (s : real -> Prop) (b : real) : (term123 s b) = (term114 s b).
Proof. exact (fun_ext (fun c : real => @lem5188730 s b c)). Qed.
Lemma lem5188732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188733 (s : real -> Prop) (b : real) : (term124 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5188732) (@lem5188731 s b)). Qed.
Lemma lem5188734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5188735 (s : real -> Prop) (b : real) : (term126 s b) = (term127 s b).
Proof. exact (MK_COMB (@lem5188734) (@lem5188733 s b)). Qed.
Lemma lem5188736 (s : real -> Prop) (b : real) (c : real) : (term118 s b c) = (term97 s b c).
Proof. exact (eq_refl (term118 s b c)). Qed.
Lemma lem5188737 (s : real -> Prop) (b : real) : (term128 s b) = (term115 s b).
Proof. exact (fun_ext (fun c : real => @lem5188736 s b c)). Qed.
Lemma lem5188738 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188739 (s : real -> Prop) (b : real) : (term129 s b) = (term130 s b).
Proof. exact (MK_COMB (@lem5188738) (@lem5188737 s b)). Qed.
Lemma lem5188740 (s : real -> Prop) (b : real) : (term113 s b) = (term131 s b).
Proof. exact (MK_COMB (@lem5188735 s b) (@lem5188739 s b)). Qed.
Lemma lem5188741 (s : real -> Prop) (b : real) : ((term112 s b) = (term113 s b)) = ((term107 s b) = (term131 s b)).
Proof. exact (MK_COMB (@lem5188729 s b) (@lem5188740 s b)). Qed.
Lemma lem5188742 (s : real -> Prop) (b : real) : (term107 s b) = (term131 s b).
Proof. exact (EQ_MP (@lem5188741 s b) (@lem5188719 s b)). Qed.
Lemma lem5188916 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5188917 (P : real -> Prop) (Q : Prop) : (term134 P Q) = (term135 P Q).
Proof. exact (@lem5188916 real P Q). Qed.
Lemma lem5188918 (s : real -> Prop) (b : real) (c : real) : (term136 s b c) = (term137 s b c).
Proof. exact (@lem5188917 (term89 s c) (real_le b c)). Qed.
Lemma lem5188919 (s : real -> Prop) (x : real) (c : real) : (term138 s c x) = (term80 s x c).
Proof. exact (eq_refl (term138 s c x)). Qed.
Lemma lem5188920 (s : real -> Prop) (c : real) : (term139 s c) = (term89 s c).
Proof. exact (fun_ext (fun x : real => @lem5188919 s x c)). Qed.
Lemma lem5188921 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5188922 (s : real -> Prop) (c : real) : (term140 s c) = (term90 s c).
Proof. exact (MK_COMB (@lem5188921) (@lem5188920 s c)). Qed.
Lemma lem5188923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5188924 (s : real -> Prop) (c : real) : (term141 s c) = (term95 s c).
Proof. exact (MK_COMB (@lem5188923) (@lem5188922 s c)). Qed.
Lemma lem5188925 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5188926 (s : real -> Prop) (b : real) (c : real) : (term136 s b c) = (term97 s b c).
Proof. exact (MK_COMB (@lem5188924 s c) (@lem5188925 b c)). Qed.
Lemma lem5188927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188928 (s : real -> Prop) (b : real) (c : real) : (term142 s b c) = (term143 s b c).
Proof. exact (MK_COMB (@lem5188927) (@lem5188926 s b c)). Qed.
Lemma lem5188929 (s : real -> Prop) (x : real) (c : real) : (term138 s c x) = (term80 s x c).
Proof. exact (eq_refl (term138 s c x)). Qed.
Lemma lem5188930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5188931 (s : real -> Prop) (x : real) (c : real) : (term144 s c x) = (term145 s x c).
Proof. exact (MK_COMB (@lem5188930) (@lem5188929 s x c)). Qed.
Lemma lem5188932 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5188933 (s : real -> Prop) (x : real) (b : real) (c : real) : (term146 s x b c) = (term147 s x b c).
Proof. exact (MK_COMB (@lem5188931 s x c) (@lem5188932 b c)). Qed.
Lemma lem5188934 (s : real -> Prop) (b : real) (c : real) : (term148 s b c) = (term149 s b c).
Proof. exact (fun_ext (fun x : real => @lem5188933 s x b c)). Qed.
Lemma lem5188935 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5188936 (s : real -> Prop) (b : real) (c : real) : (term137 s b c) = (term150 s b c).
Proof. exact (MK_COMB (@lem5188935) (@lem5188934 s b c)). Qed.
Lemma lem5188937 (s : real -> Prop) (b : real) (c : real) : ((term136 s b c) = (term137 s b c)) = ((term97 s b c) = (term150 s b c)).
Proof. exact (MK_COMB (@lem5188928 s b c) (@lem5188936 s b c)). Qed.
Lemma lem5188938 (s : real -> Prop) (b : real) (c : real) : (term97 s b c) = (term150 s b c).
Proof. exact (EQ_MP (@lem5188937 s b c) (@lem5188918 s b c)). Qed.
Lemma lem5188939 (s : real -> Prop) (b : real) : (term115 s b) = (term151 s b).
Proof. exact (fun_ext (fun c : real => @lem5188938 s b c)). Qed.
Lemma lem5188940 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188941 (s : real -> Prop) (b : real) : (term130 s b) = (term152 s b).
Proof. exact (MK_COMB (@lem5188940) (@lem5188939 s b)). Qed.
Lemma lem5188943 {A B : Type'} (P : type1413 A B) : (term153 A B P) = (term154 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5188944 (P : type1626) : (term155 P) = (term156 P).
Proof. exact (@lem5188943 real real P). Qed.
Lemma lem5188945 (s : real -> Prop) (b : real) : (term157 s b) = (term158 s b).
Proof. exact (@lem5188944 (term159 s b)). Qed.
Lemma lem5188946 (s : real -> Prop) (b : real) (c : real) : (term160 s b c) = (term149 s b c).
Proof. exact (eq_refl (term160 s b c)). Qed.
Lemma lem5188947 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5188948 (s : real -> Prop) (b : real) (c : real) (x : real) : (term161 s b c x) = (term162 s b c x).
Proof. exact (MK_COMB (@lem5188946 s b c) (@lem5188947 x)). Qed.
Lemma lem5188949 (s : real -> Prop) (x : real) (b : real) (c : real) : (term162 s b c x) = (term147 s x b c).
Proof. exact (eq_refl (term162 s b c x)). Qed.
Lemma lem5188950 (s : real -> Prop) (x : real) (b : real) (c : real) : (term161 s b c x) = (term147 s x b c).
Proof. exact (TRANS (@lem5188948 s b c x) (@lem5188949 s x b c)). Qed.
Lemma lem5188951 (s : real -> Prop) (b : real) (c : real) : (term163 s b c) = (term149 s b c).
Proof. exact (fun_ext (fun x : real => @lem5188950 s x b c)). Qed.
Lemma lem5188952 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5188953 (s : real -> Prop) (b : real) (c : real) : (term164 s b c) = (term150 s b c).
Proof. exact (MK_COMB (@lem5188952) (@lem5188951 s b c)). Qed.
Lemma lem5188954 (s : real -> Prop) (b : real) : (term165 s b) = (term151 s b).
Proof. exact (fun_ext (fun c : real => @lem5188953 s b c)). Qed.
Lemma lem5188955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188956 (s : real -> Prop) (b : real) : (term157 s b) = (term152 s b).
Proof. exact (MK_COMB (@lem5188955) (@lem5188954 s b)). Qed.
Lemma lem5188957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188958 (s : real -> Prop) (b : real) : (term166 s b) = (term167 s b).
Proof. exact (MK_COMB (@lem5188957) (@lem5188956 s b)). Qed.
Lemma lem5188959 (s : real -> Prop) (b : real) (c : real) : (term160 s b c) = (term149 s b c).
Proof. exact (eq_refl (term160 s b c)). Qed.
Lemma lem5188960 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5188961 (s : real -> Prop) (b : real) (x : real -> real) (c : real) : (term168 s b x c) = (term169 s b x c).
Proof. exact (MK_COMB (@lem5188959 s b c) (@lem5188960 x c)). Qed.
Lemma lem5188962 (s : real -> Prop) (x : real -> real) (b : real) (c : real) : (term169 s b x c) = (term170 s x b c).
Proof. exact (eq_refl (term169 s b x c)). Qed.
Lemma lem5188963 (s : real -> Prop) (x : real -> real) (b : real) (c : real) : (term168 s b x c) = (term170 s x b c).
Proof. exact (TRANS (@lem5188961 s b x c) (@lem5188962 s x b c)). Qed.
Lemma lem5188964 (s : real -> Prop) (x : real -> real) (b : real) : (term171 s b x) = (term172 s x b).
Proof. exact (fun_ext (fun c : real => @lem5188963 s x b c)). Qed.
Lemma lem5188965 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5188966 (s : real -> Prop) (x : real -> real) (b : real) : (term173 s b x) = (term174 s x b).
Proof. exact (MK_COMB (@lem5188965) (@lem5188964 s x b)). Qed.
Lemma lem5188967 (s : real -> Prop) (b : real) : (term175 s b) = (term176 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5188966 s x b)). Qed.
Lemma lem5188968 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5188969 (s : real -> Prop) (b : real) : (term158 s b) = (term177 s b).
Proof. exact (MK_COMB (@lem5188968) (@lem5188967 s b)). Qed.
Lemma lem5188970 (s : real -> Prop) (b : real) : ((term157 s b) = (term158 s b)) = ((term152 s b) = (term177 s b)).
Proof. exact (MK_COMB (@lem5188958 s b) (@lem5188969 s b)). Qed.
Lemma lem5188971 (s : real -> Prop) (b : real) : (term152 s b) = (term177 s b).
Proof. exact (EQ_MP (@lem5188970 s b) (@lem5188945 s b)). Qed.
Lemma lem5188972 (s : real -> Prop) (b : real) : (term130 s b) = (term177 s b).
Proof. exact (TRANS (@lem5188941 s b) (@lem5188971 s b)). Qed.
Lemma lem5188973 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (eq_refl (term127 s b)). Qed.
Lemma lem5188974 (s : real -> Prop) (b : real) : (term131 s b) = (term178 s b).
Proof. exact (MK_COMB (@lem5188973 s b) (@lem5188972 s b)). Qed.
Lemma lem5188976 {A : Type'} (P : Prop) (Q : A -> Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5188977 (P : Prop) (Q : type1028) : (term181 P Q) = (term182 P Q).
Proof. exact (@lem5188976 (real -> real) P Q). Qed.
Lemma lem5188978 (s : real -> Prop) (b : real) : (term183 s b) = (term184 s b).
Proof. exact (@lem5188977 (term125 s b) (term176 s b)). Qed.
Lemma lem5188979 (s : real -> Prop) (x : real -> real) (b : real) : (term185 s b x) = (term174 s x b).
Proof. exact (eq_refl (term185 s b x)). Qed.
Lemma lem5188980 (s : real -> Prop) (b : real) : (term186 s b) = (term176 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5188979 s x b)). Qed.
Lemma lem5188981 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5188982 (s : real -> Prop) (b : real) : (term187 s b) = (term177 s b).
Proof. exact (MK_COMB (@lem5188981) (@lem5188980 s b)). Qed.
Lemma lem5188983 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (eq_refl (term127 s b)). Qed.
Lemma lem5188984 (s : real -> Prop) (b : real) : (term183 s b) = (term178 s b).
Proof. exact (MK_COMB (@lem5188983 s b) (@lem5188982 s b)). Qed.
Lemma lem5188985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188986 (s : real -> Prop) (b : real) : (term188 s b) = (term189 s b).
Proof. exact (MK_COMB (@lem5188985) (@lem5188984 s b)). Qed.
Lemma lem5188987 (s : real -> Prop) (x : real -> real) (b : real) : (term185 s b x) = (term174 s x b).
Proof. exact (eq_refl (term185 s b x)). Qed.
Lemma lem5188988 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (eq_refl (term127 s b)). Qed.
Lemma lem5188989 (s : real -> Prop) (x : real -> real) (b : real) : (term190 s b x) = (term191 s x b).
Proof. exact (MK_COMB (@lem5188988 s b) (@lem5188987 s x b)). Qed.
Lemma lem5188990 (s : real -> Prop) (b : real) : (term192 s b) = (term193 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5188989 s x b)). Qed.
Lemma lem5188991 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5188992 (s : real -> Prop) (b : real) : (term184 s b) = (term194 s b).
Proof. exact (MK_COMB (@lem5188991) (@lem5188990 s b)). Qed.
Lemma lem5188993 (s : real -> Prop) (b : real) : ((term183 s b) = (term184 s b)) = ((term178 s b) = (term194 s b)).
Proof. exact (MK_COMB (@lem5188986 s b) (@lem5188992 s b)). Qed.
Lemma lem5188994 (s : real -> Prop) (b : real) : (term178 s b) = (term194 s b).
Proof. exact (EQ_MP (@lem5188993 s b) (@lem5188978 s b)). Qed.
Lemma lem5188995 (s : real -> Prop) (b : real) : (term131 s b) = (term194 s b).
Proof. exact (TRANS (@lem5188974 s b) (@lem5188994 s b)). Qed.
Lemma lem5188996 (s : real -> Prop) (b : real) : (term107 s b) = (term194 s b).
Proof. exact (TRANS (@lem5188742 s b) (@lem5188995 s b)). Qed.
Lemma lem5188997 (s : real -> Prop) (b : real) : (term36 s b) = (term194 s b).
Proof. exact (TRANS (@lem5188715 s b) (@lem5188996 s b)). Qed.
Lemma lem5188998 (s : real -> Prop) (b : real) (h1 : term36 s b) : term194 s b.
Proof. exact (EQ_MP (@lem5188997 s b) (@lem5188667 s b h1)). Qed.
Lemma lem5189007 (s : real -> Prop) (x : real) (b' : real) : (term79 s x b') = (term80 s x b').
Proof. exact (@lem17362 (s x) (real_le x b')). Qed.
Lemma lem5189012 (s : real -> Prop) (x : real) (b' : real) : (term27 s x b') = (term81 s x b').
Proof. exact (@lem17265 (s x) (real_le x b')). Qed.
Lemma lem5189013 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5189014 (s : real -> Prop) (b' : real) : (term84 s b') = (term85 s b').
Proof. exact (@lem5189013 (term29 s b')). Qed.
Lemma lem5189015 (s : real -> Prop) (x : real) (b' : real) : (term86 s b' x) = (term27 s x b').
Proof. exact (eq_refl (term86 s b' x)). Qed.
Lemma lem5189016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5189017 (s : real -> Prop) (x : real) (b' : real) : (term87 s b' x) = (term79 s x b').
Proof. exact (MK_COMB (@lem5189016) (@lem5189015 s x b')). Qed.
Lemma lem5189018 (s : real -> Prop) (x : real) (b' : real) : (term87 s b' x) = (term80 s x b').
Proof. exact (TRANS (@lem5189017 s x b') (@lem5189007 s x b')). Qed.
Lemma lem5189019 (s : real -> Prop) (b' : real) : (term88 s b') = (term89 s b').
Proof. exact (fun_ext (fun x : real => @lem5189018 s x b')). Qed.
Lemma lem5189020 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189021 (s : real -> Prop) (b' : real) : (term85 s b') = (term90 s b').
Proof. exact (MK_COMB (@lem5189020) (@lem5189019 s b')). Qed.
Lemma lem5189022 (s : real -> Prop) (b' : real) : (term84 s b') = (term90 s b').
Proof. exact (TRANS (@lem5189014 s b') (@lem5189021 s b')). Qed.
Lemma lem5189023 (s : real -> Prop) (b' : real) : (term29 s b') = (term91 s b').
Proof. exact (fun_ext (fun x : real => @lem5189012 s x b')). Qed.
Lemma lem5189024 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189025 (s : real -> Prop) (b' : real) : (term31 s b') = (term92 s b').
Proof. exact (MK_COMB (@lem5189024) (@lem5189023 s b')). Qed.
Lemma lem5189034 (b : real) (x : real) (b' : real) : (term195 b x b') = (term196 b x b').
Proof. exact (@lem17362 (x = b) (real_le x b')). Qed.
Lemma lem5189039 (b : real) (x : real) (b' : real) : (term50 b x b') = (term197 b x b').
Proof. exact (@lem17265 (x = b) (real_le x b')). Qed.
Lemma lem5189040 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5189041 (b : real) (b' : real) : (term198 b b') = (term199 b b').
Proof. exact (@lem5189040 (term52 b b')). Qed.
Lemma lem5189042 (b : real) (x : real) (b' : real) : (term200 b b' x) = (term50 b x b').
Proof. exact (eq_refl (term200 b b' x)). Qed.
Lemma lem5189043 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5189044 (b : real) (x : real) (b' : real) : (term201 b b' x) = (term195 b x b').
Proof. exact (MK_COMB (@lem5189043) (@lem5189042 b x b')). Qed.
Lemma lem5189045 (b : real) (x : real) (b' : real) : (term201 b b' x) = (term196 b x b').
Proof. exact (TRANS (@lem5189044 b x b') (@lem5189034 b x b')). Qed.
Lemma lem5189046 (b : real) (b' : real) : (term202 b b') = (term203 b b').
Proof. exact (fun_ext (fun x : real => @lem5189045 b x b')). Qed.
Lemma lem5189047 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189048 (b : real) (b' : real) : (term199 b b') = (term204 b b').
Proof. exact (MK_COMB (@lem5189047) (@lem5189046 b b')). Qed.
Lemma lem5189049 (b : real) (b' : real) : (term198 b b') = (term204 b b').
Proof. exact (TRANS (@lem5189041 b b') (@lem5189048 b b')). Qed.
Lemma lem5189050 (b : real) (b' : real) : (term52 b b') = (term205 b b').
Proof. exact (fun_ext (fun x : real => @lem5189039 b x b')). Qed.
Lemma lem5189051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189052 (b : real) (b' : real) : (term54 b b') = (term206 b b').
Proof. exact (MK_COMB (@lem5189051) (@lem5189050 b b')). Qed.
Lemma lem5189053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5189054 (s : real -> Prop) (b' : real) : (term207 s b') = (term208 s b').
Proof. exact (MK_COMB (@lem5189053) (@lem5189022 s b')). Qed.
Lemma lem5189055 (s : real -> Prop) (b : real) (b' : real) : (term209 s b b') = (term210 s b b').
Proof. exact (MK_COMB (@lem5189054 s b') (@lem5189052 b b')). Qed.
Lemma lem5189056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5189057 (s : real -> Prop) (b' : real) : (term211 s b') = (term212 s b').
Proof. exact (MK_COMB (@lem5189056) (@lem5189025 s b')). Qed.
Lemma lem5189058 (s : real -> Prop) (b : real) (b' : real) : (term213 s b b') = (term214 s b b').
Proof. exact (MK_COMB (@lem5189057 s b') (@lem5189049 b b')). Qed.
Lemma lem5189059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189060 (s : real -> Prop) (b : real) (b' : real) : (term215 s b b') = (term216 s b b').
Proof. exact (MK_COMB (@lem5189059) (@lem5189058 s b b')). Qed.
Lemma lem5189061 (s : real -> Prop) (b : real) (b' : real) : (term217 s b b') = (term218 s b b').
Proof. exact (MK_COMB (@lem5189060 s b b') (@lem5189055 s b b')). Qed.
Lemma lem5189062 (s : real -> Prop) (b : real) (b' : real) : (term78 s b b') = (term217 s b b').
Proof. exact (@lem17646 (term31 s b') (term54 b b')). Qed.
Lemma lem5189063 (s : real -> Prop) (b : real) (b' : real) : (term78 s b b') = (term218 s b b').
Proof. exact (TRANS (@lem5189062 s b b') (@lem5189061 s b b')). Qed.
Lemma lem5189238 {A : Type'} (P : Prop) (Q : A -> Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5189239 (P : Prop) (Q : real -> Prop) : (term219 P Q) = (term220 P Q).
Proof. exact (@lem5189238 real P Q). Qed.
Lemma lem5189240 (s : real -> Prop) (b : real) (b' : real) : (term221 s b b') = (term222 s b b').
Proof. exact (@lem5189239 (term92 s b') (term203 b b')). Qed.
Lemma lem5189241 (b : real) (x : real) (b' : real) : (term223 b b' x) = (term196 b x b').
Proof. exact (eq_refl (term223 b b' x)). Qed.
Lemma lem5189242 (b : real) (b' : real) : (term224 b b') = (term203 b b').
Proof. exact (fun_ext (fun x : real => @lem5189241 b x b')). Qed.
Lemma lem5189243 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189244 (b : real) (b' : real) : (term225 b b') = (term204 b b').
Proof. exact (MK_COMB (@lem5189243) (@lem5189242 b b')). Qed.
Lemma lem5189245 (s : real -> Prop) (b' : real) : (term212 s b') = (term212 s b').
Proof. exact (eq_refl (term212 s b')). Qed.
Lemma lem5189246 (s : real -> Prop) (b : real) (b' : real) : (term221 s b b') = (term214 s b b').
Proof. exact (MK_COMB (@lem5189245 s b') (@lem5189244 b b')). Qed.
Lemma lem5189247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5189248 (s : real -> Prop) (b : real) (b' : real) : (term226 s b b') = (term227 s b b').
Proof. exact (MK_COMB (@lem5189247) (@lem5189246 s b b')). Qed.
Lemma lem5189249 (b : real) (x : real) (b' : real) : (term223 b b' x) = (term196 b x b').
Proof. exact (eq_refl (term223 b b' x)). Qed.
Lemma lem5189250 (s : real -> Prop) (b' : real) : (term212 s b') = (term212 s b').
Proof. exact (eq_refl (term212 s b')). Qed.
Lemma lem5189251 (s : real -> Prop) (b : real) (x : real) (b' : real) : (term228 s b b' x) = (term229 s b x b').
Proof. exact (MK_COMB (@lem5189250 s b') (@lem5189249 b x b')). Qed.
Lemma lem5189252 (s : real -> Prop) (b : real) (b' : real) : (term230 s b b') = (term231 s b b').
Proof. exact (fun_ext (fun x : real => @lem5189251 s b x b')). Qed.
Lemma lem5189253 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189254 (s : real -> Prop) (b : real) (b' : real) : (term222 s b b') = (term232 s b b').
Proof. exact (MK_COMB (@lem5189253) (@lem5189252 s b b')). Qed.
Lemma lem5189255 (s : real -> Prop) (b : real) (b' : real) : ((term221 s b b') = (term222 s b b')) = ((term214 s b b') = (term232 s b b')).
Proof. exact (MK_COMB (@lem5189248 s b b') (@lem5189254 s b b')). Qed.
Lemma lem5189256 (s : real -> Prop) (b : real) (b' : real) : (term214 s b b') = (term232 s b b').
Proof. exact (EQ_MP (@lem5189255 s b b') (@lem5189240 s b b')). Qed.
Lemma lem5189257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189258 (s : real -> Prop) (b : real) (b' : real) : (term216 s b b') = (term233 s b b').
Proof. exact (MK_COMB (@lem5189257) (@lem5189256 s b b')). Qed.
Lemma lem5189260 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5189261 (P : real -> Prop) (Q : Prop) : (term236 P Q) = (term237 P Q).
Proof. exact (@lem5189260 real P Q). Qed.
Lemma lem5189262 (s : real -> Prop) (b : real) (b' : real) : (term238 s b b') = (term239 s b b').
Proof. exact (@lem5189261 (term89 s b') (term206 b b')). Qed.
Lemma lem5189263 (s : real -> Prop) (x : real) (b' : real) : (term138 s b' x) = (term80 s x b').
Proof. exact (eq_refl (term138 s b' x)). Qed.
Lemma lem5189264 (s : real -> Prop) (b' : real) : (term139 s b') = (term89 s b').
Proof. exact (fun_ext (fun x : real => @lem5189263 s x b')). Qed.
Lemma lem5189265 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189266 (s : real -> Prop) (b' : real) : (term140 s b') = (term90 s b').
Proof. exact (MK_COMB (@lem5189265) (@lem5189264 s b')). Qed.
Lemma lem5189267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5189268 (s : real -> Prop) (b' : real) : (term240 s b') = (term208 s b').
Proof. exact (MK_COMB (@lem5189267) (@lem5189266 s b')). Qed.
Lemma lem5189269 (b : real) (b' : real) : (term206 b b') = (term206 b b').
Proof. exact (eq_refl (term206 b b')). Qed.
Lemma lem5189270 (s : real -> Prop) (b : real) (b' : real) : (term238 s b b') = (term210 s b b').
Proof. exact (MK_COMB (@lem5189268 s b') (@lem5189269 b b')). Qed.
Lemma lem5189271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5189272 (s : real -> Prop) (b : real) (b' : real) : (term241 s b b') = (term242 s b b').
Proof. exact (MK_COMB (@lem5189271) (@lem5189270 s b b')). Qed.
Lemma lem5189273 (s : real -> Prop) (x : real) (b' : real) : (term138 s b' x) = (term80 s x b').
Proof. exact (eq_refl (term138 s b' x)). Qed.
Lemma lem5189274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5189275 (s : real -> Prop) (x : real) (b' : real) : (term243 s b' x) = (term244 s x b').
Proof. exact (MK_COMB (@lem5189274) (@lem5189273 s x b')). Qed.
Lemma lem5189276 (b : real) (b' : real) : (term206 b b') = (term206 b b').
Proof. exact (eq_refl (term206 b b')). Qed.
Lemma lem5189277 (s : real -> Prop) (x : real) (b : real) (b' : real) : (term245 s x b b') = (term246 s x b b').
Proof. exact (MK_COMB (@lem5189275 s x b') (@lem5189276 b b')). Qed.
Lemma lem5189278 (s : real -> Prop) (b : real) (b' : real) : (term247 s b b') = (term248 s b b').
Proof. exact (fun_ext (fun x : real => @lem5189277 s x b b')). Qed.
Lemma lem5189279 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189280 (s : real -> Prop) (b : real) (b' : real) : (term239 s b b') = (term249 s b b').
Proof. exact (MK_COMB (@lem5189279) (@lem5189278 s b b')). Qed.
Lemma lem5189281 (s : real -> Prop) (b : real) (b' : real) : ((term238 s b b') = (term239 s b b')) = ((term210 s b b') = (term249 s b b')).
Proof. exact (MK_COMB (@lem5189272 s b b') (@lem5189280 s b b')). Qed.
Lemma lem5189282 (s : real -> Prop) (b : real) (b' : real) : (term210 s b b') = (term249 s b b').
Proof. exact (EQ_MP (@lem5189281 s b b') (@lem5189262 s b b')). Qed.
Lemma lem5189283 (s : real -> Prop) (b : real) (b' : real) : (term218 s b b') = (term250 s b b').
Proof. exact (MK_COMB (@lem5189258 s b b') (@lem5189282 s b b')). Qed.
Lemma lem5189285 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term251 A P Q) = (term252 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5189286 (P : real -> Prop) (Q : real -> Prop) : (term253 P Q) = (term254 P Q).
Proof. exact (@lem5189285 real P Q). Qed.
Lemma lem5189287 (s : real -> Prop) (b : real) (b' : real) : (term255 s b b') = (term256 s b b').
Proof. exact (@lem5189286 (term231 s b b') (term248 s b b')). Qed.
Lemma lem5189288 (s : real -> Prop) (b : real) (x : real) (b' : real) : (term257 s b b' x) = (term229 s b x b').
Proof. exact (eq_refl (term257 s b b' x)). Qed.
Lemma lem5189289 (s : real -> Prop) (b : real) (b' : real) : (term258 s b b') = (term231 s b b').
Proof. exact (fun_ext (fun x : real => @lem5189288 s b x b')). Qed.
Lemma lem5189290 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189291 (s : real -> Prop) (b : real) (b' : real) : (term259 s b b') = (term232 s b b').
Proof. exact (MK_COMB (@lem5189290) (@lem5189289 s b b')). Qed.
Lemma lem5189292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189293 (s : real -> Prop) (b : real) (b' : real) : (term260 s b b') = (term233 s b b').
Proof. exact (MK_COMB (@lem5189292) (@lem5189291 s b b')). Qed.
Lemma lem5189294 (s : real -> Prop) (x : real) (b : real) (b' : real) : (term261 s b b' x) = (term246 s x b b').
Proof. exact (eq_refl (term261 s b b' x)). Qed.
Lemma lem5189295 (s : real -> Prop) (b : real) (b' : real) : (term262 s b b') = (term248 s b b').
Proof. exact (fun_ext (fun x : real => @lem5189294 s x b b')). Qed.
Lemma lem5189296 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189297 (s : real -> Prop) (b : real) (b' : real) : (term263 s b b') = (term249 s b b').
Proof. exact (MK_COMB (@lem5189296) (@lem5189295 s b b')). Qed.
Lemma lem5189298 (s : real -> Prop) (b : real) (b' : real) : (term255 s b b') = (term250 s b b').
Proof. exact (MK_COMB (@lem5189293 s b b') (@lem5189297 s b b')). Qed.
Lemma lem5189299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5189300 (s : real -> Prop) (b : real) (b' : real) : (term264 s b b') = (term265 s b b').
Proof. exact (MK_COMB (@lem5189299) (@lem5189298 s b b')). Qed.
Lemma lem5189301 (s : real -> Prop) (b : real) (x : real) (b' : real) : (term257 s b b' x) = (term229 s b x b').
Proof. exact (eq_refl (term257 s b b' x)). Qed.
Lemma lem5189302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189303 (s : real -> Prop) (b : real) (x : real) (b' : real) : (term266 s b b' x) = (term267 s b x b').
Proof. exact (MK_COMB (@lem5189302) (@lem5189301 s b x b')). Qed.
Lemma lem5189304 (s : real -> Prop) (x : real) (b : real) (b' : real) : (term261 s b b' x) = (term246 s x b b').
Proof. exact (eq_refl (term261 s b b' x)). Qed.
Lemma lem5189305 (s : real -> Prop) (x : real) (b : real) (b' : real) : (term268 s b b' x) = (term269 s x b b').
Proof. exact (MK_COMB (@lem5189303 s b x b') (@lem5189304 s x b b')). Qed.
Lemma lem5189306 (s : real -> Prop) (b : real) (b' : real) : (term270 s b b') = (term271 s b b').
Proof. exact (fun_ext (fun x : real => @lem5189305 s x b b')). Qed.
Lemma lem5189307 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5189308 (s : real -> Prop) (b : real) (b' : real) : (term256 s b b') = (term272 s b b').
Proof. exact (MK_COMB (@lem5189307) (@lem5189306 s b b')). Qed.
Lemma lem5189309 (s : real -> Prop) (b : real) (b' : real) : ((term255 s b b') = (term256 s b b')) = ((term250 s b b') = (term272 s b b')).
Proof. exact (MK_COMB (@lem5189300 s b b') (@lem5189308 s b b')). Qed.
Lemma lem5189310 (s : real -> Prop) (b : real) (b' : real) : (term250 s b b') = (term272 s b b').
Proof. exact (EQ_MP (@lem5189309 s b b') (@lem5189287 s b b')). Qed.
Lemma lem5189312 (s : real -> Prop) (b : real) (b' : real) : (term218 s b b') = (term272 s b b').
Proof. exact (TRANS (@lem5189283 s b b') (@lem5189310 s b b')). Qed.
Lemma lem5189313 (s : real -> Prop) (b : real) (b' : real) : (term78 s b b') = (term272 s b b').
Proof. exact (TRANS (@lem5189063 s b b') (@lem5189312 s b b')). Qed.
Lemma lem5189314 (s : real -> Prop) (b : real) (b' : real) (h1 : term78 s b b') : term272 s b b'.
Proof. exact (EQ_MP (@lem5189313 s b b') (@lem5188672 s b b' h1)). Qed.
Lemma lem5189315 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term269 s x b b') : term269 s x b b'.
Proof. exact (h1). Qed.
Lemma lem5189316 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term191 s x' b.
Proof. exact (h1). Qed.
Lemma lem5189331 (b : real) (x : real) (b' : real) : (term197 b x b') = (term197 b x b').
Proof. exact (eq_refl (term197 b x b')). Qed.
Lemma lem5189332 (b : real) (b' : real) : (term205 b b') = (term205 b b').
Proof. exact (fun_ext (fun x : real => @lem5189331 b x b')). Qed.
Lemma lem5189333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189334 (b : real) (b' : real) : (term206 b b') = (term206 b b').
Proof. exact (MK_COMB (@lem5189333) (@lem5189332 b b')). Qed.
Lemma lem5189349 (s : real -> Prop) (x : real) (b' : real) : (term244 s x b') = (term244 s x b').
Proof. exact (eq_refl (term244 s x b')). Qed.
Lemma lem5189350 (s : real -> Prop) (x : real) (b : real) (b' : real) : (term246 s x b b') = (term246 s x b b').
Proof. exact (MK_COMB (@lem5189349 s x b') (@lem5189334 b b')). Qed.
Lemma lem5189365 (b : real) (x : real) (b' : real) : (term196 b x b') = (term196 b x b').
Proof. exact (eq_refl (term196 b x b')). Qed.
Lemma lem5189378 (s : real -> Prop) (x : real) (b' : real) : (term81 s x b') = (term81 s x b').
Proof. exact (eq_refl (term81 s x b')). Qed.
Lemma lem5189379 (s : real -> Prop) (b' : real) : (term91 s b') = (term91 s b').
Proof. exact (fun_ext (fun x : real => @lem5189378 s x b')). Qed.
Lemma lem5189380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189381 (s : real -> Prop) (b' : real) : (term92 s b') = (term92 s b').
Proof. exact (MK_COMB (@lem5189380) (@lem5189379 s b')). Qed.
Lemma lem5189382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5189383 (s : real -> Prop) (b' : real) : (term212 s b') = (term212 s b').
Proof. exact (MK_COMB (@lem5189382) (@lem5189381 s b')). Qed.
Lemma lem5189384 (s : real -> Prop) (b : real) (x : real) (b' : real) : (term229 s b x b') = (term229 s b x b').
Proof. exact (MK_COMB (@lem5189383 s b') (@lem5189365 b x b')). Qed.
Lemma lem5189385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189386 (s : real -> Prop) (b : real) (x : real) (b' : real) : (term267 s b x b') = (term267 s b x b').
Proof. exact (MK_COMB (@lem5189385) (@lem5189384 s b x b')). Qed.
Lemma lem5189387 (s : real -> Prop) (x : real) (b : real) (b' : real) : (term269 s x b b') = (term269 s x b b').
Proof. exact (MK_COMB (@lem5189386 s b x b') (@lem5189350 s x b b')). Qed.
Lemma lem5189388 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term269 s x b b') : term269 s x b b'.
Proof. exact (EQ_MP (@lem5189387 s x b b') (@lem5189315 s x b b' h1)). Qed.
Lemma lem5189413 (s : real -> Prop) (x' : real -> real) (b : real) (c : real) : (term170 s x' b c) = (term170 s x' b c).
Proof. exact (eq_refl (term170 s x' b c)). Qed.
Lemma lem5189414 (s : real -> Prop) (x' : real -> real) (b : real) : (term172 s x' b) = (term172 s x' b).
Proof. exact (fun_ext (fun c : real => @lem5189413 s x' b c)). Qed.
Lemma lem5189415 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189416 (s : real -> Prop) (x' : real -> real) (b : real) : (term174 s x' b) = (term174 s x' b).
Proof. exact (MK_COMB (@lem5189415) (@lem5189414 s x' b)). Qed.
Lemma lem5189423 (b : real) (c : real) : (term93 b c) = (term93 b c).
Proof. exact (eq_refl (term93 b c)). Qed.
Lemma lem5189436 (s : real -> Prop) (x : real) (c : real) : (term81 s x c) = (term81 s x c).
Proof. exact (eq_refl (term81 s x c)). Qed.
Lemma lem5189437 (s : real -> Prop) (c : real) : (term91 s c) = (term91 s c).
Proof. exact (fun_ext (fun x : real => @lem5189436 s x c)). Qed.
Lemma lem5189438 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189439 (s : real -> Prop) (c : real) : (term92 s c) = (term92 s c).
Proof. exact (MK_COMB (@lem5189438) (@lem5189437 s c)). Qed.
Lemma lem5189440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189441 (s : real -> Prop) (c : real) : (term99 s c) = (term99 s c).
Proof. exact (MK_COMB (@lem5189440) (@lem5189439 s c)). Qed.
Lemma lem5189442 (s : real -> Prop) (b : real) (c : real) : (term101 s b c) = (term101 s b c).
Proof. exact (MK_COMB (@lem5189441 s c) (@lem5189423 b c)). Qed.
Lemma lem5189443 (s : real -> Prop) (b : real) : (term114 s b) = (term114 s b).
Proof. exact (fun_ext (fun c : real => @lem5189442 s b c)). Qed.
Lemma lem5189444 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189445 (s : real -> Prop) (b : real) : (term125 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5189444) (@lem5189443 s b)). Qed.
Lemma lem5189446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5189447 (s : real -> Prop) (b : real) : (term127 s b) = (term127 s b).
Proof. exact (MK_COMB (@lem5189446) (@lem5189445 s b)). Qed.
Lemma lem5189448 (s : real -> Prop) (x' : real -> real) (b : real) : (term191 s x' b) = (term191 s x' b).
Proof. exact (MK_COMB (@lem5189447 s b) (@lem5189416 s x' b)). Qed.
Lemma lem5189449 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term191 s x' b.
Proof. exact (EQ_MP (@lem5189448 s x' b) (@lem5189316 s x' b h1)). Qed.
Lemma lem5189450 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term174 s x' b.
Proof. exact (proj2 (@lem5189449 s x' b h1)). Qed.
Lemma lem5189451 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term125 s b.
Proof. exact (proj1 (@lem5189449 s x' b h1)). Qed.
Lemma lem5189452 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term229 s b x b'.
Proof. exact (h1). Qed.
Lemma lem5189453 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term246 s x b b'.
Proof. exact (h1). Qed.
Lemma lem5189454 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term196 b x b'.
Proof. exact (proj2 (@lem5189452 s b x b' h1)). Qed.
Lemma lem5189455 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term92 s b'.
Proof. exact (proj1 (@lem5189452 s b x b' h1)). Qed.
Lemma lem5189458 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term206 b b'.
Proof. exact (proj2 (@lem5189453 s x b b' h1)). Qed.
Lemma lem5189459 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term80 s x b'.
Proof. exact (proj1 (@lem5189453 s x b b' h1)). Qed.
Lemma lem5189527 (s : real -> Prop) (x' : real -> real) (b : real) (c : real) : (term170 s x' b c) = (term273 s x' b c).
Proof. exact (@lem19699 (term274 s x' c) (term275 x' c) (real_le b c)). Qed.
Lemma lem5189528 (s : real -> Prop) (x' : real -> real) (b : real) : (term172 s x' b) = (term276 s x' b).
Proof. exact (fun_ext (fun c : real => @lem5189527 s x' b c)). Qed.
Lemma lem5189529 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189531 (s : real -> Prop) (x' : real -> real) (b : real) : (term174 s x' b) = (term277 s x' b).
Proof. exact (MK_COMB (@lem5189529) (@lem5189528 s x' b)). Qed.
Lemma lem5189532 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term277 s x' b.
Proof. exact (EQ_MP (@lem5189531 s x' b) (@lem5189450 s x' b h1)). Qed.
Lemma lem5189540 (s : real -> Prop) (x : real) (b' : real) : (term81 s x b') = (term81 s x b').
Proof. exact (eq_refl (term81 s x b')). Qed.
Lemma lem5189541 (s : real -> Prop) (b' : real) : (term91 s b') = (term91 s b').
Proof. exact (fun_ext (fun x : real => @lem5189540 s x b')). Qed.
Lemma lem5189542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189544 (s : real -> Prop) (b' : real) : (term92 s b') = (term92 s b').
Proof. exact (MK_COMB (@lem5189542) (@lem5189541 s b')). Qed.
Lemma lem5189545 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term92 s b'.
Proof. exact (EQ_MP (@lem5189544 s b') (@lem5189455 s b x b' h1)). Qed.
Lemma lem5189555 {A : Type'} (P : A -> Prop) (Q : Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5189556 (P : real -> Prop) (Q : Prop) : (term280 P Q) = (term281 P Q).
Proof. exact (@lem5189555 real P Q). Qed.
Lemma lem5189557 (s : real -> Prop) (b : real) (c : real) : (term282 s b c) = (term283 s b c).
Proof. exact (@lem5189556 (term91 s c) (term93 b c)). Qed.
Lemma lem5189558 (s : real -> Prop) (x : real) (c : real) : (term284 s c x) = (term81 s x c).
Proof. exact (eq_refl (term284 s c x)). Qed.
Lemma lem5189559 (s : real -> Prop) (c : real) : (term285 s c) = (term91 s c).
Proof. exact (fun_ext (fun x : real => @lem5189558 s x c)). Qed.
Lemma lem5189560 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189561 (s : real -> Prop) (c : real) : (term286 s c) = (term92 s c).
Proof. exact (MK_COMB (@lem5189560) (@lem5189559 s c)). Qed.
Lemma lem5189562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189563 (s : real -> Prop) (c : real) : (term287 s c) = (term99 s c).
Proof. exact (MK_COMB (@lem5189562) (@lem5189561 s c)). Qed.
Lemma lem5189564 (b : real) (c : real) : (term93 b c) = (term93 b c).
Proof. exact (eq_refl (term93 b c)). Qed.
Lemma lem5189565 (s : real -> Prop) (b : real) (c : real) : (term282 s b c) = (term101 s b c).
Proof. exact (MK_COMB (@lem5189563 s c) (@lem5189564 b c)). Qed.
Lemma lem5189566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5189567 (s : real -> Prop) (b : real) (c : real) : (term288 s b c) = (term289 s b c).
Proof. exact (MK_COMB (@lem5189566) (@lem5189565 s b c)). Qed.
Lemma lem5189568 (s : real -> Prop) (x : real) (c : real) : (term284 s c x) = (term81 s x c).
Proof. exact (eq_refl (term284 s c x)). Qed.
Lemma lem5189569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5189570 (s : real -> Prop) (x : real) (c : real) : (term290 s c x) = (term291 s x c).
Proof. exact (MK_COMB (@lem5189569) (@lem5189568 s x c)). Qed.
Lemma lem5189571 (b : real) (c : real) : (term93 b c) = (term93 b c).
Proof. exact (eq_refl (term93 b c)). Qed.
Lemma lem5189572 (s : real -> Prop) (x : real) (b : real) (c : real) : (term292 s x b c) = (term293 s x b c).
Proof. exact (MK_COMB (@lem5189570 s x c) (@lem5189571 b c)). Qed.
Lemma lem5189573 (s : real -> Prop) (b : real) (c : real) : (term294 s b c) = (term295 s b c).
Proof. exact (fun_ext (fun x : real => @lem5189572 s x b c)). Qed.
Lemma lem5189574 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189575 (s : real -> Prop) (b : real) (c : real) : (term283 s b c) = (term296 s b c).
Proof. exact (MK_COMB (@lem5189574) (@lem5189573 s b c)). Qed.
Lemma lem5189576 (s : real -> Prop) (b : real) (c : real) : ((term282 s b c) = (term283 s b c)) = ((term101 s b c) = (term296 s b c)).
Proof. exact (MK_COMB (@lem5189567 s b c) (@lem5189575 s b c)). Qed.
Lemma lem5189577 (s : real -> Prop) (b : real) (c : real) : (term101 s b c) = (term296 s b c).
Proof. exact (EQ_MP (@lem5189576 s b c) (@lem5189557 s b c)). Qed.
Lemma lem5189578 (s : real -> Prop) (b : real) : (term114 s b) = (term297 s b).
Proof. exact (fun_ext (fun c : real => @lem5189577 s b c)). Qed.
Lemma lem5189579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189580 (s : real -> Prop) (b : real) : (term125 s b) = (term298 s b).
Proof. exact (MK_COMB (@lem5189579) (@lem5189578 s b)). Qed.
Lemma lem5189593 (s : real -> Prop) (x : real) (b : real) (c : real) : (term293 s x b c) = (term293 s x b c).
Proof. exact (eq_refl (term293 s x b c)). Qed.
Lemma lem5189594 (s : real -> Prop) (b : real) (c : real) : (term295 s b c) = (term295 s b c).
Proof. exact (fun_ext (fun x : real => @lem5189593 s x b c)). Qed.
Lemma lem5189595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189596 (s : real -> Prop) (b : real) (c : real) : (term296 s b c) = (term296 s b c).
Proof. exact (MK_COMB (@lem5189595) (@lem5189594 s b c)). Qed.
Lemma lem5189597 (s : real -> Prop) (b : real) : (term297 s b) = (term297 s b).
Proof. exact (fun_ext (fun c : real => @lem5189596 s b c)). Qed.
Lemma lem5189598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189599 (s : real -> Prop) (b : real) : (term298 s b) = (term298 s b).
Proof. exact (MK_COMB (@lem5189598) (@lem5189597 s b)). Qed.
Lemma lem5189600 (s : real -> Prop) (b : real) : (term125 s b) = (term298 s b).
Proof. exact (TRANS (@lem5189580 s b) (@lem5189599 s b)). Qed.
Lemma lem5189601 (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term298 s b.
Proof. exact (EQ_MP (@lem5189600 s b) (@lem5189451 s x' b h1)). Qed.
Lemma lem5189632 (b : real) (x : real) (b' : real) : (term197 b x b') = (term197 b x b').
Proof. exact (eq_refl (term197 b x b')). Qed.
Lemma lem5189633 (b : real) (b' : real) : (term205 b b') = (term205 b b').
Proof. exact (fun_ext (fun x : real => @lem5189632 b x b')). Qed.
Lemma lem5189634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5189636 (b : real) (b' : real) : (term206 b b') = (term206 b b').
Proof. exact (MK_COMB (@lem5189634) (@lem5189633 b b')). Qed.
Lemma lem5189637 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term206 b b'.
Proof. exact (EQ_MP (@lem5189636 b b') (@lem5189458 s x b b' h1)). Qed.
Lemma lem5189652 (_67728 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term299 s x' b _67728.
Proof. exact (@lem5189532 s x' b h1 _67728). Qed.
Lemma lem5189653 (s : real -> Prop) (x' : real -> real) (b : real) (_67728 : real) : (term299 s x' b _67728) = (term273 s x' b _67728).
Proof. exact (eq_refl (term299 s x' b _67728)). Qed.
Lemma lem5189654 (_67728 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term273 s x' b _67728.
Proof. exact (EQ_MP (@lem5189653 s x' b _67728) (@lem5189652 _67728 s x' b h1)). Qed.
Lemma lem5189655 (_67729 : real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term284 s b' _67729.
Proof. exact (@lem5189545 s b x b' h1 _67729). Qed.
Lemma lem5189656 (s : real -> Prop) (_67729 : real) (b' : real) : (term284 s b' _67729) = (term81 s _67729 b').
Proof. exact (eq_refl (term284 s b' _67729)). Qed.
Lemma lem5189658 (_67730 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term300 s b _67730.
Proof. exact (@lem5189601 s x' b h1 _67730). Qed.
Lemma lem5189659 (s : real -> Prop) (b : real) (_67730 : real) : (term300 s b _67730) = (term296 s b _67730).
Proof. exact (eq_refl (term300 s b _67730)). Qed.
Lemma lem5189660 (_67730 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term296 s b _67730.
Proof. exact (EQ_MP (@lem5189659 s b _67730) (@lem5189658 _67730 s x' b h1)). Qed.
Lemma lem5189661 (_67730 : real) (_67731 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term301 s b _67730 _67731.
Proof. exact (@lem5189660 _67730 s x' b h1 _67731). Qed.
Lemma lem5189662 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term301 s b _67730 _67731) = (term293 s _67731 b _67730).
Proof. exact (eq_refl (term301 s b _67730 _67731)). Qed.
Lemma lem5189663 (_67731 : real) (_67730 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term293 s _67731 b _67730.
Proof. exact (EQ_MP (@lem5189662 s _67731 b _67730) (@lem5189661 _67730 _67731 s x' b h1)). Qed.
Lemma lem5189667 (_67733 : real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term302 b b' _67733.
Proof. exact (@lem5189637 s x b b' h1 _67733). Qed.
Lemma lem5189668 (b : real) (_67733 : real) (b' : real) : (term302 b b' _67733) = (term197 b _67733 b').
Proof. exact (eq_refl (term302 b b' _67733)). Qed.
Lemma lem5189693 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : x = b.
Proof. exact (proj1 (@lem5189454 s b x b' h1)). Qed.
Lemma lem5189695 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term93 x b'.
Proof. exact (proj2 (@lem5189454 s b x b' h1)). Qed.
Lemma lem5189718 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term293 s _67731 b _67730) = (term303 s _67731 b _67730).
Proof. exact (@lem5188315 (term304 s _67731) (real_le _67731 _67730) (term93 b _67730)). Qed.
Lemma lem5189719 (_67731 : real) (_67730 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term303 s _67731 b _67730.
Proof. exact (EQ_MP (@lem5189718 s _67731 b _67730) (@lem5189663 _67731 _67730 s x' b h1)). Qed.
Lemma lem5189725 (_67733 : real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term197 b _67733 b'.
Proof. exact (EQ_MP (@lem5189668 b _67733 b') (@lem5189667 _67733 s x b b' h1)). Qed.
Lemma lem5189729 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term93 x b'.
Proof. exact (proj2 (@lem5189459 s x b b' h1)). Qed.
Lemma lem5189783 (_67729 : real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term81 s _67729 b'.
Proof. exact (EQ_MP (@lem5189656 s _67729 b') (@lem5189655 _67729 s b x b' h1)). Qed.
Lemma lem5189784 (b' : real) : (term305 b') = (term305 b').
Proof. exact (eq_refl (term305 b')). Qed.
Lemma lem5189785 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : (term306 b' x) = (term306 b' b).
Proof. exact (MK_COMB (@lem5189784 b') (@lem5189693 s b x b' h1)). Qed.
Lemma lem5189786 (b : real) (b' : real) : (term306 b' b) = (term93 b b').
Proof. exact (eq_refl (term306 b' b)). Qed.
Lemma lem5189787 (b' : real) (x : real) : (term307 b' x) = (term307 b' x).
Proof. exact (eq_refl (term307 b' x)). Qed.
Lemma lem5189788 (x : real) (b : real) (b' : real) : ((term306 b' x) = (term306 b' b)) = ((term306 b' x) = (term93 b b')).
Proof. exact (MK_COMB (@lem5189787 b' x) (@lem5189786 b b')). Qed.
Lemma lem5189789 (x : real) (b' : real) : (term306 b' x) = (term93 x b').
Proof. exact (eq_refl (term306 b' x)). Qed.
Lemma lem5189790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5189791 (x : real) (b' : real) : (term307 b' x) = (term308 x b').
Proof. exact (MK_COMB (@lem5189790) (@lem5189789 x b')). Qed.
Lemma lem5189792 (b : real) (b' : real) : (term93 b b') = (term93 b b').
Proof. exact (eq_refl (term93 b b')). Qed.
Lemma lem5189793 (x : real) (b : real) (b' : real) : ((term306 b' x) = (term93 b b')) = ((term93 x b') = (term93 b b')).
Proof. exact (MK_COMB (@lem5189791 x b') (@lem5189792 b b')). Qed.
Lemma lem5189794 (x : real) (b : real) (b' : real) : ((term306 b' x) = (term306 b' b)) = ((term93 x b') = (term93 b b')).
Proof. exact (TRANS (@lem5189788 x b b') (@lem5189793 x b b')). Qed.
Lemma lem5189795 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : (term93 x b') = (term93 b b').
Proof. exact (EQ_MP (@lem5189794 x b b') (@lem5189785 s b x b' h1)). Qed.
Lemma lem5189796 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term93 b b'.
Proof. exact (EQ_MP (@lem5189795 s b x b' h1) (@lem5189695 s b x b' h1)). Qed.
Lemma lem5189810 (_67728 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term309 s x' b _67728.
Proof. exact (proj1 (@lem5189654 _67728 s x' b h1)). Qed.
Lemma lem5189824 (_67728 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term310 x' b _67728.
Proof. exact (proj2 (@lem5189654 _67728 s x' b h1)). Qed.
Lemma lem5189827 (b : real) (b' : real) (h1 : term93 b b') : term93 b b'.
Proof. exact (h1). Qed.
Lemma lem5189828 (b : real) (b' : real) (h1 : term93 b b') : term311 b b'.
Proof. exact (fun h0 : real_le b b' => @lem5189827 b b' h1). Qed.
Lemma lem5189830 (p : Prop) : (term312 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5189831 (b : real) (b' : real) : (term311 b b') = (term93 b b').
Proof. exact (@lem5189830 (real_le b b')). Qed.
Lemma lem5189832 (b : real) (b' : real) (h1 : term93 b b') : term93 b b'.
Proof. exact (EQ_MP (@lem5189831 b b') (@lem5189828 b b' h1)). Qed.
Lemma lem5189834 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5189837 (b : real) (s : real -> Prop) (x' : real -> real) (_67728 : real) : (term309 s x' b _67728) = (term314 b s x' _67728).
Proof. exact (@lem5189834 (real_le b _67728) (term274 s x' _67728)). Qed.
Lemma lem5189840 (_67728 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term314 b s x' _67728.
Proof. exact (EQ_MP (@lem5189837 b s x' _67728) (@lem5189810 _67728 s x' b h1)). Qed.
Lemma lem5189841 (b' : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term314 b s x' b'.
Proof. exact (@lem5189840 b' s x' b h1). Qed.
Lemma lem5189844 (b' : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term93 b b') (h2 : term191 s x' b) : term274 s x' b'.
Proof. exact (@lem5189841 b' s x' b h2 (@lem5189832 b b' h1)). Qed.
Lemma lem5189845 (b' : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term93 b b') (h2 : term191 s x' b) : term315 s x' b'.
Proof. exact (fun h0 : term316 s x' b' => @lem5189844 b' s x' b h1 h2). Qed.
Lemma lem5189847 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5189848 (s : real -> Prop) (x' : real -> real) (b' : real) : (term315 s x' b') = (term274 s x' b').
Proof. exact (@lem5189847 (term274 s x' b')). Qed.
Lemma lem5189849 (b' : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term93 b b') (h2 : term191 s x' b) : term274 s x' b'.
Proof. exact (EQ_MP (@lem5189848 s x' b') (@lem5189845 b' s x' b h1 h2)). Qed.
Lemma lem5189855 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5189856 (b' : real) (s : real -> Prop) (_67729 : real) : (term81 s _67729 b') = (term318 b' s _67729).
Proof. exact (@lem5189855 (real_le _67729 b') (term304 s _67729)). Qed.
Lemma lem5189862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5189863 (b' : real) (s : real -> Prop) (_67729 : real) : (term319 s _67729 b') = (term320 b' s _67729).
Proof. exact (MK_COMB (@lem5189862) (@lem5189856 b' s _67729)). Qed.
Lemma lem5189869 (b' : real) (s : real -> Prop) (_67729 : real) : (term318 b' s _67729) = (term318 b' s _67729).
Proof. exact (eq_refl (term318 b' s _67729)). Qed.
Lemma lem5189870 (b' : real) (s : real -> Prop) (_67729 : real) : ((term81 s _67729 b') = (term318 b' s _67729)) = ((term318 b' s _67729) = (term318 b' s _67729)).
Proof. exact (MK_COMB (@lem5189863 b' s _67729) (@lem5189869 b' s _67729)). Qed.
Lemma lem5189872 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5189873 (x : Prop) : (x = x) = True.
Proof. exact (@lem5189872 Prop x). Qed.
Lemma lem5189874 (b' : real) (s : real -> Prop) (_67729 : real) : ((term318 b' s _67729) = (term318 b' s _67729)) = True.
Proof. exact (@lem5189873 (term318 b' s _67729)). Qed.
Lemma lem5189875 (b' : real) (s : real -> Prop) (_67729 : real) : ((term81 s _67729 b') = (term318 b' s _67729)) = True.
Proof. exact (TRANS (@lem5189870 b' s _67729) (@lem5189874 b' s _67729)). Qed.
Lemma lem5189876 (b' : real) (s : real -> Prop) (_67729 : real) : True = ((term81 s _67729 b') = (term318 b' s _67729)).
Proof. exact (SYM (@lem5189875 b' s _67729)). Qed.
Lemma lem5189877 (b' : real) (s : real -> Prop) (_67729 : real) : (term81 s _67729 b') = (term318 b' s _67729).
Proof. exact (EQ_MP (@lem5189876 b' s _67729) (@lem0)). Qed.
Lemma lem5189878 (_67729 : real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term318 b' s _67729.
Proof. exact (EQ_MP (@lem5189877 b' s _67729) (@lem5189783 _67729 s b x b' h1)). Qed.
Lemma lem5189880 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5189881 (s : real -> Prop) (_67729 : real) (b' : real) : (term318 b' s _67729) = (term321 s _67729 b').
Proof. exact (@lem5189880 (term304 s _67729) (real_le _67729 b')). Qed.
Lemma lem5189883 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5189884 (s : real -> Prop) (_67729 : real) : (term322 s _67729) = (s _67729).
Proof. exact (@lem5189883 (s _67729)). Qed.
Lemma lem5189885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5189886 (s : real -> Prop) (_67729 : real) : (term323 s _67729) = (term25 s _67729).
Proof. exact (MK_COMB (@lem5189885) (@lem5189884 s _67729)). Qed.
Lemma lem5189887 (_67729 : real) (b' : real) : (real_le _67729 b') = (real_le _67729 b').
Proof. exact (eq_refl (real_le _67729 b')). Qed.
Lemma lem5189888 (s : real -> Prop) (_67729 : real) (b' : real) : (term321 s _67729 b') = (term27 s _67729 b').
Proof. exact (MK_COMB (@lem5189886 s _67729) (@lem5189887 _67729 b')). Qed.
Lemma lem5189889 (s : real -> Prop) (_67729 : real) (b' : real) : (term318 b' s _67729) = (term27 s _67729 b').
Proof. exact (TRANS (@lem5189881 s _67729 b') (@lem5189888 s _67729 b')). Qed.
Lemma lem5189892 (_67729 : real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term27 s _67729 b'.
Proof. exact (EQ_MP (@lem5189889 s _67729 b') (@lem5189878 _67729 s b x b' h1)). Qed.
Lemma lem5189893 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term324 s x' b'.
Proof. exact (@lem5189892 (x' b') s b x b' h1). Qed.
Lemma lem5189896 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term93 b b') (h2 : term191 s x' b) (h3 : term229 s b x b') : term325 x' b'.
Proof. exact (@lem5189893 x' s b x b' h3 (@lem5189849 b' s x' b h1 h2)). Qed.
Lemma lem5189897 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term93 b b') (h2 : term191 s x' b) (h3 : term229 s b x b') : term326 x' b'.
Proof. exact (fun h0 : term275 x' b' => @lem5189896 x' s b x b' h1 h2 h3). Qed.
Lemma lem5189899 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5189900 (x' : real -> real) (b' : real) : (term326 x' b') = (term325 x' b').
Proof. exact (@lem5189899 (term325 x' b')). Qed.
Lemma lem5189901 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term93 b b') (h2 : term191 s x' b) (h3 : term229 s b x b') : term325 x' b'.
Proof. exact (EQ_MP (@lem5189900 x' b') (@lem5189897 x' s b x b' h1 h2 h3)). Qed.
Lemma lem5189907 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5189908 (b : real) (x' : real -> real) (_67728 : real) : (term310 x' b _67728) = (term327 b x' _67728).
Proof. exact (@lem5189907 (real_le b _67728) (term275 x' _67728)). Qed.
Lemma lem5189914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5189915 (b : real) (x' : real -> real) (_67728 : real) : (term328 x' b _67728) = (term329 b x' _67728).
Proof. exact (MK_COMB (@lem5189914) (@lem5189908 b x' _67728)). Qed.
Lemma lem5189921 (b : real) (x' : real -> real) (_67728 : real) : (term327 b x' _67728) = (term327 b x' _67728).
Proof. exact (eq_refl (term327 b x' _67728)). Qed.
Lemma lem5189922 (b : real) (x' : real -> real) (_67728 : real) : ((term310 x' b _67728) = (term327 b x' _67728)) = ((term327 b x' _67728) = (term327 b x' _67728)).
Proof. exact (MK_COMB (@lem5189915 b x' _67728) (@lem5189921 b x' _67728)). Qed.
Lemma lem5189924 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5189925 (x : Prop) : (x = x) = True.
Proof. exact (@lem5189924 Prop x). Qed.
Lemma lem5189926 (b : real) (x' : real -> real) (_67728 : real) : ((term327 b x' _67728) = (term327 b x' _67728)) = True.
Proof. exact (@lem5189925 (term327 b x' _67728)). Qed.
Lemma lem5189927 (b : real) (x' : real -> real) (_67728 : real) : ((term310 x' b _67728) = (term327 b x' _67728)) = True.
Proof. exact (TRANS (@lem5189922 b x' _67728) (@lem5189926 b x' _67728)). Qed.
Lemma lem5189928 (b : real) (x' : real -> real) (_67728 : real) : True = ((term310 x' b _67728) = (term327 b x' _67728)).
Proof. exact (SYM (@lem5189927 b x' _67728)). Qed.
Lemma lem5189929 (b : real) (x' : real -> real) (_67728 : real) : (term310 x' b _67728) = (term327 b x' _67728).
Proof. exact (EQ_MP (@lem5189928 b x' _67728) (@lem0)). Qed.
Lemma lem5189930 (_67728 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term327 b x' _67728.
Proof. exact (EQ_MP (@lem5189929 b x' _67728) (@lem5189824 _67728 s x' b h1)). Qed.
Lemma lem5189932 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5189933 (x' : real -> real) (b : real) (_67728 : real) : (term327 b x' _67728) = (term330 x' b _67728).
Proof. exact (@lem5189932 (term275 x' _67728) (real_le b _67728)). Qed.
Lemma lem5189935 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5189936 (x' : real -> real) (_67728 : real) : (term331 x' _67728) = (term325 x' _67728).
Proof. exact (@lem5189935 (term325 x' _67728)). Qed.
Lemma lem5189937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5189938 (x' : real -> real) (_67728 : real) : (term332 x' _67728) = (term333 x' _67728).
Proof. exact (MK_COMB (@lem5189937) (@lem5189936 x' _67728)). Qed.
Lemma lem5189939 (b : real) (_67728 : real) : (real_le b _67728) = (real_le b _67728).
Proof. exact (eq_refl (real_le b _67728)). Qed.
Lemma lem5189940 (x' : real -> real) (b : real) (_67728 : real) : (term330 x' b _67728) = (term334 x' b _67728).
Proof. exact (MK_COMB (@lem5189938 x' _67728) (@lem5189939 b _67728)). Qed.
Lemma lem5189941 (x' : real -> real) (b : real) (_67728 : real) : (term327 b x' _67728) = (term334 x' b _67728).
Proof. exact (TRANS (@lem5189933 x' b _67728) (@lem5189940 x' b _67728)). Qed.
Lemma lem5189944 (_67728 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term334 x' b _67728.
Proof. exact (EQ_MP (@lem5189941 x' b _67728) (@lem5189930 _67728 s x' b h1)). Qed.
Lemma lem5189945 (b' : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term334 x' b b'.
Proof. exact (@lem5189944 b' s x' b h1). Qed.
Lemma lem5189948 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term93 b b') (h2 : term191 s x' b) (h3 : term229 s b x b') : real_le b b'.
Proof. exact (@lem5189945 b' s x' b h2 (@lem5189901 x' s b x b' h1 h2 h3)). Qed.
Lemma lem5189949 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term191 s x' b) (h2 : term229 s b x b') : term335 b b'.
Proof. exact (fun h0 : term93 b b' => @lem5189948 x' s b x b' h0 h1 h2). Qed.
Lemma lem5189951 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5189952 (b : real) (b' : real) : (term335 b b') = (real_le b b').
Proof. exact (@lem5189951 (real_le b b')). Qed.
Lemma lem5189953 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term191 s x' b) (h2 : term229 s b x b') : real_le b b'.
Proof. exact (EQ_MP (@lem5189952 b b') (@lem5189949 x' s b x b' h1 h2)). Qed.
Lemma lem5189956 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5189958 (b : real) (b' : real) : (term93 b b') = (term336 b b').
Proof. exact (@lem5189956 (real_le b b')). Qed.
Lemma lem5189961 (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term229 s b x b') : term336 b b'.
Proof. exact (EQ_MP (@lem5189958 b b') (@lem5189796 s b x b' h1)). Qed.
Lemma lem5189964 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term191 s x' b) (h2 : term229 s b x b') : False.
Proof. exact (@lem5189961 s b x b' h2 (@lem5189953 x' s b x b' h1 h2)). Qed.
Lemma lem5189965 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term191 s x' b) (h2 : term229 s b x b') : term337.
Proof. exact (fun h0 : ~ False => @lem5189964 x' s b x b' h1 h2). Qed.
Lemma lem5189967 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5189968 : term337 = False.
Proof. exact (@lem5189967 False). Qed.
Lemma lem5190012 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : s x.
Proof. exact (proj1 (@lem5189459 s x b b' h1)). Qed.
Lemma lem5190013 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term338 s x.
Proof. exact (fun h0 : term304 s x => @lem5190012 s x b b' h1). Qed.
Lemma lem5190015 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5190016 (s : real -> Prop) (x : real) : (term338 s x) = (s x).
Proof. exact (@lem5190015 (s x)). Qed.
Lemma lem5190017 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : s x.
Proof. exact (EQ_MP (@lem5190016 s x) (@lem5190013 s x b b' h1)). Qed.
Lemma lem5190019 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5190020 (b : real) : b = b.
Proof. exact (@lem5190019 b). Qed.
Lemma lem5190021 (b : real) : term339 b.
Proof. exact (fun h0 : term340 b => @lem5190020 b). Qed.
Lemma lem5190023 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5190024 (b : real) : (term339 b) = (b = b).
Proof. exact (@lem5190023 (b = b)). Qed.
Lemma lem5190025 (b : real) : b = b.
Proof. exact (EQ_MP (@lem5190024 b) (@lem5190021 b)). Qed.
Lemma lem5190031 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5190032 (b' : real) (_67733 : real) (b : real) : (term197 b _67733 b') = (term341 b' _67733 b).
Proof. exact (@lem5190031 (real_le _67733 b') (term342 _67733 b)). Qed.
Lemma lem5190040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5190041 (b' : real) (_67733 : real) (b : real) : (term343 b _67733 b') = (term344 b' _67733 b).
Proof. exact (MK_COMB (@lem5190040) (@lem5190032 b' _67733 b)). Qed.
Lemma lem5190049 (b' : real) (_67733 : real) (b : real) : (term341 b' _67733 b) = (term341 b' _67733 b).
Proof. exact (eq_refl (term341 b' _67733 b)). Qed.
Lemma lem5190050 (b' : real) (_67733 : real) (b : real) : ((term197 b _67733 b') = (term341 b' _67733 b)) = ((term341 b' _67733 b) = (term341 b' _67733 b)).
Proof. exact (MK_COMB (@lem5190041 b' _67733 b) (@lem5190049 b' _67733 b)). Qed.
Lemma lem5190052 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5190053 (x : Prop) : (x = x) = True.
Proof. exact (@lem5190052 Prop x). Qed.
Lemma lem5190054 (b' : real) (_67733 : real) (b : real) : ((term341 b' _67733 b) = (term341 b' _67733 b)) = True.
Proof. exact (@lem5190053 (term341 b' _67733 b)). Qed.
Lemma lem5190055 (b' : real) (_67733 : real) (b : real) : ((term197 b _67733 b') = (term341 b' _67733 b)) = True.
Proof. exact (TRANS (@lem5190050 b' _67733 b) (@lem5190054 b' _67733 b)). Qed.
Lemma lem5190056 (b' : real) (_67733 : real) (b : real) : True = ((term197 b _67733 b') = (term341 b' _67733 b)).
Proof. exact (SYM (@lem5190055 b' _67733 b)). Qed.
Lemma lem5190057 (b' : real) (_67733 : real) (b : real) : (term197 b _67733 b') = (term341 b' _67733 b).
Proof. exact (EQ_MP (@lem5190056 b' _67733 b) (@lem0)). Qed.
Lemma lem5190058 (_67733 : real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term341 b' _67733 b.
Proof. exact (EQ_MP (@lem5190057 b' _67733 b) (@lem5189725 _67733 s x b b' h1)). Qed.
Lemma lem5190060 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5190061 (b : real) (_67733 : real) (b' : real) : (term341 b' _67733 b) = (term345 b _67733 b').
Proof. exact (@lem5190060 (term342 _67733 b) (real_le _67733 b')). Qed.
Lemma lem5190063 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5190064 (_67733 : real) (b : real) : (term346 _67733 b) = (_67733 = b).
Proof. exact (@lem5190063 (_67733 = b)). Qed.
Lemma lem5190065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190066 (_67733 : real) (b : real) : (term347 _67733 b) = (term48 _67733 b).
Proof. exact (MK_COMB (@lem5190065) (@lem5190064 _67733 b)). Qed.
Lemma lem5190067 (_67733 : real) (b' : real) : (real_le _67733 b') = (real_le _67733 b').
Proof. exact (eq_refl (real_le _67733 b')). Qed.
Lemma lem5190068 (b : real) (_67733 : real) (b' : real) : (term345 b _67733 b') = (term50 b _67733 b').
Proof. exact (MK_COMB (@lem5190066 _67733 b) (@lem5190067 _67733 b')). Qed.
Lemma lem5190069 (b : real) (_67733 : real) (b' : real) : (term341 b' _67733 b) = (term50 b _67733 b').
Proof. exact (TRANS (@lem5190061 b _67733 b') (@lem5190068 b _67733 b')). Qed.
Lemma lem5190072 (_67733 : real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term50 b _67733 b'.
Proof. exact (EQ_MP (@lem5190069 b _67733 b') (@lem5190058 _67733 s x b b' h1)). Qed.
Lemma lem5190073 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term348 b b'.
Proof. exact (@lem5190072 b s x b b' h1). Qed.
Lemma lem5190076 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : real_le b b'.
Proof. exact (@lem5190073 s x b b' h1 (@lem5190025 b)). Qed.
Lemma lem5190077 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term335 b b'.
Proof. exact (fun h0 : term93 b b' => @lem5190076 s x b b' h1). Qed.
Lemma lem5190079 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5190080 (b : real) (b' : real) : (term335 b b') = (real_le b b').
Proof. exact (@lem5190079 (real_le b b')). Qed.
Lemma lem5190081 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : real_le b b'.
Proof. exact (EQ_MP (@lem5190080 b b') (@lem5190077 s x b b' h1)). Qed.
Lemma lem5190087 (q : Prop) (p : Prop) (r : Prop) : (term22 p q r) = (term22 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5190088 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term303 s _67731 b _67730) = (term349 s _67731 b _67730).
Proof. exact (@lem5190087 (real_le _67731 _67730) (term304 s _67731) (term93 b _67730)). Qed.
Lemma lem5190104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5190105 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term350 s _67731 b _67730) = (term351 s _67731 b _67730).
Proof. exact (MK_COMB (@lem5190104) (@lem5190088 s _67731 b _67730)). Qed.
Lemma lem5190121 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term349 s _67731 b _67730) = (term349 s _67731 b _67730).
Proof. exact (eq_refl (term349 s _67731 b _67730)). Qed.
Lemma lem5190122 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : ((term303 s _67731 b _67730) = (term349 s _67731 b _67730)) = ((term349 s _67731 b _67730) = (term349 s _67731 b _67730)).
Proof. exact (MK_COMB (@lem5190105 s _67731 b _67730) (@lem5190121 s _67731 b _67730)). Qed.
Lemma lem5190124 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5190125 (x : Prop) : (x = x) = True.
Proof. exact (@lem5190124 Prop x). Qed.
Lemma lem5190126 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : ((term349 s _67731 b _67730) = (term349 s _67731 b _67730)) = True.
Proof. exact (@lem5190125 (term349 s _67731 b _67730)). Qed.
Lemma lem5190127 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : ((term303 s _67731 b _67730) = (term349 s _67731 b _67730)) = True.
Proof. exact (TRANS (@lem5190122 s _67731 b _67730) (@lem5190126 s _67731 b _67730)). Qed.
Lemma lem5190128 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : True = ((term303 s _67731 b _67730) = (term349 s _67731 b _67730)).
Proof. exact (SYM (@lem5190127 s _67731 b _67730)). Qed.
Lemma lem5190129 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term303 s _67731 b _67730) = (term349 s _67731 b _67730).
Proof. exact (EQ_MP (@lem5190128 s _67731 b _67730) (@lem0)). Qed.
Lemma lem5190130 (_67731 : real) (_67730 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term349 s _67731 b _67730.
Proof. exact (EQ_MP (@lem5190129 s _67731 b _67730) (@lem5189719 _67731 _67730 s x' b h1)). Qed.
Lemma lem5190132 (b : Prop) (a : Prop) : (a \/ b) = (term313 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5190133 (s : real -> Prop) (b : real) (_67731 : real) (_67730 : real) : (term349 s _67731 b _67730) = (term352 s b _67731 _67730).
Proof. exact (@lem5190132 (term353 s _67731 b _67730) (real_le _67731 _67730)). Qed.
Lemma lem5190135 (a : Prop) (b : Prop) : (term354 a b) = (term355 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5190136 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term356 s _67731 b _67730) = (term357 s _67731 b _67730).
Proof. exact (@lem5190135 (term304 s _67731) (term93 b _67730)). Qed.
Lemma lem5190138 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5190139 (s : real -> Prop) (_67731 : real) : (term322 s _67731) = (s _67731).
Proof. exact (@lem5190138 (s _67731)). Qed.
Lemma lem5190140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5190141 (s : real -> Prop) (_67731 : real) : (term358 s _67731) = (term359 s _67731).
Proof. exact (MK_COMB (@lem5190140) (@lem5190139 s _67731)). Qed.
Lemma lem5190143 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5190144 (b : real) (_67730 : real) : (term360 b _67730) = (real_le b _67730).
Proof. exact (@lem5190143 (real_le b _67730)). Qed.
Lemma lem5190145 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term357 s _67731 b _67730) = (term361 s _67731 b _67730).
Proof. exact (MK_COMB (@lem5190141 s _67731) (@lem5190144 b _67730)). Qed.
Lemma lem5190146 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term356 s _67731 b _67730) = (term361 s _67731 b _67730).
Proof. exact (TRANS (@lem5190136 s _67731 b _67730) (@lem5190145 s _67731 b _67730)). Qed.
Lemma lem5190147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190148 (s : real -> Prop) (_67731 : real) (b : real) (_67730 : real) : (term362 s _67731 b _67730) = (term363 s _67731 b _67730).
Proof. exact (MK_COMB (@lem5190147) (@lem5190146 s _67731 b _67730)). Qed.
Lemma lem5190149 (_67731 : real) (_67730 : real) : (real_le _67731 _67730) = (real_le _67731 _67730).
Proof. exact (eq_refl (real_le _67731 _67730)). Qed.
Lemma lem5190150 (s : real -> Prop) (b : real) (_67731 : real) (_67730 : real) : (term352 s b _67731 _67730) = (term364 s b _67731 _67730).
Proof. exact (MK_COMB (@lem5190148 s _67731 b _67730) (@lem5190149 _67731 _67730)). Qed.
Lemma lem5190151 (s : real -> Prop) (b : real) (_67731 : real) (_67730 : real) : (term349 s _67731 b _67730) = (term364 s b _67731 _67730).
Proof. exact (TRANS (@lem5190133 s b _67731 _67730) (@lem5190150 s b _67731 _67730)). Qed.
Lemma lem5190153 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term361 s x b b'.
Proof. exact (conj (@lem5190017 s x b b' h1) (@lem5190081 s x b b' h1)). Qed.
Lemma lem5190155 (_67731 : real) (_67730 : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term364 s b _67731 _67730.
Proof. exact (EQ_MP (@lem5190151 s b _67731 _67730) (@lem5190130 _67731 _67730 s x' b h1)). Qed.
Lemma lem5190156 (x : real) (b' : real) (s : real -> Prop) (x' : real -> real) (b : real) (h1 : term191 s x' b) : term364 s b x b'.
Proof. exact (@lem5190155 x b' s x' b h1). Qed.
Lemma lem5190159 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term246 s x b b') : real_le x b'.
Proof. exact (@lem5190156 x b' s x' b h1 (@lem5190153 s x b b' h2)). Qed.
Lemma lem5190160 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term246 s x b b') : term335 x b'.
Proof. exact (fun h0 : term93 x b' => @lem5190159 x' s x b b' h1 h2). Qed.
Lemma lem5190162 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5190163 (x : real) (b' : real) : (term335 x b') = (real_le x b').
Proof. exact (@lem5190162 (real_le x b')). Qed.
Lemma lem5190164 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term246 s x b b') : real_le x b'.
Proof. exact (EQ_MP (@lem5190163 x b') (@lem5190160 x' s x b b' h1 h2)). Qed.
Lemma lem5190167 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5190169 (x : real) (b' : real) : (term93 x b') = (term336 x b').
Proof. exact (@lem5190167 (real_le x b')). Qed.
Lemma lem5190172 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term246 s x b b') : term336 x b'.
Proof. exact (EQ_MP (@lem5190169 x b') (@lem5189729 s x b b' h1)). Qed.
Lemma lem5190175 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term246 s x b b') : False.
Proof. exact (@lem5190172 s x b b' h2 (@lem5190164 x' s x b b' h1 h2)). Qed.
Lemma lem5190176 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term246 s x b b') : term337.
Proof. exact (fun h0 : ~ False => @lem5190175 x' s x b b' h1 h2). Qed.
Lemma lem5190178 (p : Prop) : (term317 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5190179 : term337 = False.
Proof. exact (@lem5190178 False). Qed.
Lemma lem5190180 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term246 s x b b') : False.
Proof. exact (EQ_MP (@lem5190179) (@lem5190176 x' s x b b' h1 h2)). Qed.
Lemma lem5190181 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (b' : real) (h1 : term191 s x' b) (h2 : term229 s b x b') : False.
Proof. exact (EQ_MP (@lem5189968) (@lem5189965 x' s b x b' h1 h2)). Qed.
Lemma lem5190182 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term269 s x b b') : False.
Proof. exact (or_elim (@lem5189388 s x b b' h2) (fun h0 : term229 s b x b' => @lem5190181 x' s b x b' h1 h0) (fun h0 : term246 s x b b' => @lem5190180 x' s x b b' h1 h0)). Qed.
Lemma lem5190183 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term269 s x b b') : (term191 s x' b) = False.
Proof. exact (prop_ext (fun h3 : term191 s x' b => @lem5190182 x' s x b b' h1 h2) (fun h3 : False => @lem5189449 s x' b h1)). Qed.
Lemma lem5190184 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term269 s x b b') : False.
Proof. exact (EQ_MP (@lem5190183 x' s x b b' h1 h2) (@lem5189449 s x' b h1)). Qed.
Lemma lem5190185 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term269 s x b b') : (term269 s x b b') = False.
Proof. exact (prop_ext (fun h3 : term269 s x b b' => @lem5190184 x' s x b b' h1 h2) (fun h3 : False => @lem5189388 s x b b' h2)). Qed.
Lemma lem5190186 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term191 s x' b) (h2 : term269 s x b b') : False.
Proof. exact (EQ_MP (@lem5190185 x' s x b b' h1 h2) (@lem5189388 s x b b' h2)). Qed.
Lemma lem5190187 (s : real -> Prop) (x : real) (b : real) (b' : real) (h1 : term36 s b) (h2 : term269 s x b b') : False.
Proof. exact (ex_elim (@lem5188998 s b h1) (fun x' : real -> real => fun h0 : term193 s b x' => @lem5190186 x' s x b b' h0 h2)). Qed.
Lemma lem5190188 (s : real -> Prop) (b : real) (b' : real) (h1 : term36 s b) (h2 : term78 s b b') : False.
Proof. exact (ex_elim (@lem5189314 s b b' h2) (fun x : real => fun h0 : term271 s b b' x => @lem5190187 s x b b' h1 h0)). Qed.
Lemma lem5190189 (s : real -> Prop) (b : real) (b' : real) (h1 : term36 s b) (h2 : term78 s b b') : (term78 s b b') = False.
Proof. exact (prop_ext (fun h3 : term78 s b b' => @lem5190188 s b b' h1 h2) (fun h3 : False => @lem5188672 s b b' h2)). Qed.
Lemma lem5190190 (s : real -> Prop) (b : real) (b' : real) (h1 : term36 s b) (h2 : term78 s b b') : False.
Proof. exact (EQ_MP (@lem5190189 s b b' h1 h2) (@lem5188672 s b b' h2)). Qed.
Lemma lem5190191 (b' : real) (s : real -> Prop) (b : real) (h1 : term36 s b) : term77 s b b'.
Proof. exact (fun h0 : term78 s b b' => @lem5190190 s b b' h1 h0). Qed.
Lemma lem5190192 (b' : real) (s : real -> Prop) (b : real) (h1 : term36 s b) : (term31 s b') = (term54 b b').
Proof. exact (EQ_MP (@lem5188671 s b b') (@lem5190191 b' s b h1)). Qed.
Lemma lem5190197 (s : real -> Prop) (b : real) (h1 : term36 s b) : term58 s b.
Proof. exact (fun b' : real => @lem5190192 b' s b h1). Qed.
Lemma lem5190198 (s : real -> Prop) (b : real) : term60 s b.
Proof. exact (fun h0 : term36 s b => @lem5190197 s b h0). Qed.
Lemma lem5190203 (b : real) : term72 b.
Proof. exact (fun s : real -> Prop => @lem5190198 s b). Qed.
Lemma lem5190208 : term76.
Proof. exact (fun b : real => @lem5190203 b). Qed.
Lemma lem5190209 : term75.
Proof. exact (EQ_MP (@lem5188666) (@lem5190208)). Qed.
Lemma lem5190210 (b : real) : term365 b.
Proof. exact (@lem5190209 b). Qed.
Lemma lem5190211 (b : real) : (term365 b) = (term71 b).
Proof. exact (eq_refl (term365 b)). Qed.
Lemma lem5190212 (b : real) : term71 b.
Proof. exact (EQ_MP (@lem5190211 b) (@lem5190210 b)). Qed.
Lemma lem5190213 (b : real) (s : real -> Prop) : term366 b s.
Proof. exact (@lem5190212 b s). Qed.
Lemma lem5190214 (s : real -> Prop) (b : real) : (term366 b s) = (term62 s b).
Proof. exact (eq_refl (term366 b s)). Qed.
Lemma lem5190215 (s : real -> Prop) (b : real) : term62 s b.
Proof. exact (EQ_MP (@lem5190214 s b) (@lem5190213 b s)). Qed.
Lemma lem5190217 (s : real -> Prop) (b : real) : term62 s b.
Proof. exact (@lem5188505 s b (@lem5190215 s b)). Qed.
Lemma lem5190218 (s : real -> Prop) (b : real) (h1 : term63 s b) : False.
Proof. exact (@lem5190217 s b (@lem5188490 s b h1)). Qed.
Lemma lem5190219 (s : real -> Prop) (b : real) (h1 : term63 s b) : (term63 s b) = False.
Proof. exact (prop_ext (fun h2 : term63 s b => @lem5190218 s b h1) (fun h2 : False => @lem5188490 s b h1)). Qed.
Lemma lem5190220 (s : real -> Prop) (b : real) (h1 : term63 s b) : False.
Proof. exact (EQ_MP (@lem5190219 s b h1) (@lem5188490 s b h1)). Qed.
Lemma lem5190221 (s : real -> Prop) (b : real) : term62 s b.
Proof. exact (fun h0 : term63 s b => @lem5190220 s b h0). Qed.
Lemma lem5190222 (s : real -> Prop) (b : real) : term60 s b.
Proof. exact (EQ_MP (@lem5188489 s b) (@lem5190221 s b)). Qed.
Lemma lem5190224 (s : real -> Prop) (b : real) : term59 s b.
Proof. exact (EQ_MP (@lem5188485 s b) (@lem5190222 s b)). Qed.
Lemma lem5190225 (s : real -> Prop) (b : real) (h1 : term14 s b) : term57 s b.
Proof. exact (@lem5190224 s b (@lem5188296 s b h1)). Qed.
Lemma lem5190226 (s : real -> Prop) (b : real) (h1 : term14 s b) : (sup s) = (term8 b).
Proof. exact (@lem5188305 s b (@lem5190225 s b h1)). Qed.
Lemma lem5190227 (s : real -> Prop) (b : real) (h1 : term14 s b) : (sup s) = b.
Proof. exact (EQ_MP (@lem5188302 s b) (@lem5190226 s b h1)). Qed.
Lemma lem5190228 (s : real -> Prop) (b : real) (h1 : term14 s b) : (term14 s b) = ((sup s) = b).
Proof. exact (prop_ext (fun h2 : term14 s b => @lem5190227 s b h1) (fun h2 : (sup s) = b => @lem5188296 s b h1)). Qed.
Lemma lem5190229 (s : real -> Prop) (b : real) (h1 : term14 s b) : (sup s) = b.
Proof. exact (EQ_MP (@lem5190228 s b h1) (@lem5188296 s b h1)). Qed.
Lemma lem5190230 (s : real -> Prop) (b : real) : term367 s b.
Proof. exact (fun h0 : term14 s b => @lem5190229 s b h0). Qed.
Lemma lem5190235 (s : real -> Prop) : term368 s.
Proof. exact (fun b : real => @lem5190230 s b). Qed.
Lemma lem5190240 : term369.
Proof. exact (fun s : real -> Prop => @lem5190235 s). Qed.
