Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_IN_UNION_spec.
Require Import REAL_MAX_LE_spec.
Require Import SUP_spec.
Require Import SUP_UNIQUE_spec.
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
Lemma lem5190241 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5190242 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5190243 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5190242 t1) (@lem5190241 t1)). Qed.
Lemma lem5190244 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5190243 t1 t2). Qed.
Lemma lem5190245 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5190246 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5190245 t1 t2) (@lem5190244 t1 t2)). Qed.
Lemma lem5190247 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5190246 t1 t2 t3). Qed.
Lemma lem5190248 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5190249 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5190248 t1 t2 t3) (@lem5190247 t1 t2 t3)). Qed.
Lemma lem5190250 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5190249 t1 t2 t3)). Qed.
Lemma lem5190251 (x : real) : term7 x.
Proof. exact (@lem1566936 x). Qed.
Lemma lem5190252 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem5190253 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem5190252 x) (@lem5190251 x)). Qed.
Lemma lem5190254 (x : real) (y : real) : term9 x y.
Proof. exact (@lem5190253 x y). Qed.
Lemma lem5190255 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem5190256 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem5190255 x y) (@lem5190254 x y)). Qed.
Lemma lem5190257 (x : real) (y : real) (z : real) : term11 x y z.
Proof. exact (@lem5190256 x y z). Qed.
Lemma lem5190258 (x : real) (y : real) (z : real) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem5190260 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (@lem3210122 A P). Qed.
Lemma lem5190261 {A : Type'} (P : A -> Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem5190262 {A : Type'} (P : A -> Prop) : term15 A P.
Proof. exact (EQ_MP (@lem5190261 A P) (@lem5190260 A P)). Qed.
Lemma lem5190263 {A : Type'} (P : A -> Prop) (s : A -> Prop) : term16 A P s.
Proof. exact (@lem5190262 A P s). Qed.
Lemma lem5190264 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term16 A P s) = (term17 A s P).
Proof. exact (eq_refl (term16 A P s)). Qed.
Lemma lem5190265 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term17 A s P.
Proof. exact (EQ_MP (@lem5190264 A s P) (@lem5190263 A P s)). Qed.
Lemma lem5190266 {A : Type'} (s : A -> Prop) (P : A -> Prop) (t : A -> Prop) : term18 A s P t.
Proof. exact (@lem5190265 A s P t). Qed.
Lemma lem5190267 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term18 A s P t) = ((term19 A s t P) = (term20 A s t P)).
Proof. exact (eq_refl (term18 A s P t)). Qed.
Lemma lem5190269 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem5190270 (s : real -> Prop) (h1 : term21) : term22 s.
Proof. exact (@lem5190269 h1 s). Qed.
Lemma lem5190271 (s : real -> Prop) : (term22 s) = (term23 s).
Proof. exact (eq_refl (term22 s)). Qed.
Lemma lem5190272 (s : real -> Prop) (h1 : term21) : term23 s.
Proof. exact (EQ_MP (@lem5190271 s) (@lem5190270 s h1)). Qed.
Lemma lem5190273 (s : real -> Prop) (b : real) (h1 : term21) : term24 s b.
Proof. exact (@lem5190272 s h1 b). Qed.
Lemma lem5190274 (s : real -> Prop) (b : real) : (term24 s b) = (term25 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5190275 (s : real -> Prop) (b : real) (h1 : term21) : term25 s b.
Proof. exact (EQ_MP (@lem5190274 s b) (@lem5190273 s b h1)). Qed.
Lemma lem5190276 (s : real -> Prop) (b : real) (h1 : term26 s b) : term26 s b.
Proof. exact (h1). Qed.
Lemma lem5190277 (s : real -> Prop) (b : real) (h1 : term21) (h2 : term26 s b) : (sup s) = b.
Proof. exact (@lem5190275 s b h1 (@lem5190276 s b h2)). Qed.
Lemma lem5190278 (s : real -> Prop) (b : real) (h1 : term26 s b) : term27 s b.
Proof. exact (fun h0 : term21 => @lem5190277 s b h0 h1). Qed.
Lemma lem5190279 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem5190280 (s : real -> Prop) (b : real) (h1 : term21) (h2 : term26 s b) : (sup s) = b.
Proof. exact (@lem5190278 s b h2 (@lem5190279 h1)). Qed.
Lemma lem5190281 (s : real -> Prop) (b : real) (h1 : term21) : term25 s b.
Proof. exact (fun h0 : term26 s b => @lem5190280 s b h1 h0). Qed.
Lemma lem5190282 (s : real -> Prop) (h1 : term21) : term23 s.
Proof. exact (fun b : real => @lem5190281 s b h1). Qed.
Lemma lem5190283 (h1 : term21) : term21.
Proof. exact (fun s : real -> Prop => @lem5190282 s h1). Qed.
Lemma lem5190284 : term28.
Proof. exact (fun h0 : term21 => @lem5190283 h0). Qed.
Lemma lem5190285 : term21.
Proof. exact (@lem5190284 (@lem5190240)). Qed.
Lemma lem5190286 (s : real -> Prop) : term22 s.
Proof. exact (@lem5190285 s). Qed.
Lemma lem5190287 (s : real -> Prop) : (term22 s) = (term23 s).
Proof. exact (eq_refl (term22 s)). Qed.
Lemma lem5190288 (s : real -> Prop) : term23 s.
Proof. exact (EQ_MP (@lem5190287 s) (@lem5190286 s)). Qed.
Lemma lem5190289 (s : real -> Prop) (b : real) : term24 s b.
Proof. exact (@lem5190288 s b). Qed.
Lemma lem5190290 (s : real -> Prop) (b : real) : (term24 s b) = (term25 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5190292 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : term29 s t.
Proof. exact (h1). Qed.
Lemma lem5190293 (s : real -> Prop) (t : real -> Prop) (h1 : term30 s t) : term30 s t.
Proof. exact (h1). Qed.
Lemma lem5190294 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5190295 (s : real -> Prop) (t : real -> Prop) (h1 : term32 s t) : term32 s t.
Proof. exact (h1). Qed.
Lemma lem5190296 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5190297 (t : real -> Prop) (h1 : term33 t) : term33 t.
Proof. exact (h1). Qed.
Lemma lem5190298 (s : real -> Prop) (h1 : term33 s) : term33 s.
Proof. exact (h1). Qed.
Lemma lem5190299 (s : real -> Prop) (b : real) (h1 : term34 s b) : term34 s b.
Proof. exact (h1). Qed.
Lemma lem5190300 (t : real -> Prop) (c : real) (h1 : term34 t c) : term34 t c.
Proof. exact (h1). Qed.
Lemma lem5190302 (s : real -> Prop) (b : real) : term25 s b.
Proof. exact (EQ_MP (@lem5190290 s b) (@lem5190289 s b)). Qed.
Lemma lem5190303 (s : real -> Prop) (t : real -> Prop) : term35 s t.
Proof. exact (@lem5190302 (@UNION real s t) (term36 s t)). Qed.
Lemma lem5190311 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term19 A s t P) = (term20 A s t P).
Proof. exact (EQ_MP (@lem5190267 A s t P) (@lem5190266 A s P t)). Qed.
Lemma lem5190312 (s : real -> Prop) (t : real -> Prop) (P : real -> Prop) : (term37 s t P) = (term38 s t P).
Proof. exact (@lem5190311 real s t P). Qed.
Lemma lem5190313 (s : real -> Prop) (t : real -> Prop) (c : real) : (term39 s t c) = (term40 s t c).
Proof. exact (@lem5190312 s t (term41 c)). Qed.
Lemma lem5190314 (x : real) (c : real) : (term42 c x) = (real_le x c).
Proof. exact (eq_refl (term42 c x)). Qed.
Lemma lem5190315 (x : real) (s : real -> Prop) (t : real -> Prop) : (term43 x s t) = (term43 x s t).
Proof. exact (eq_refl (term43 x s t)). Qed.
Lemma lem5190316 (s : real -> Prop) (t : real -> Prop) (x : real) (c : real) : (term44 s t c x) = (term45 s t x c).
Proof. exact (MK_COMB (@lem5190315 x s t) (@lem5190314 x c)). Qed.
Lemma lem5190317 (s : real -> Prop) (t : real -> Prop) (c : real) : (term46 s t c) = (term47 s t c).
Proof. exact (fun_ext (fun x : real => @lem5190316 s t x c)). Qed.
Lemma lem5190318 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190319 (s : real -> Prop) (t : real -> Prop) (c : real) : (term39 s t c) = (term48 s t c).
Proof. exact (MK_COMB (@lem5190318) (@lem5190317 s t c)). Qed.
Lemma lem5190320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5190321 (s : real -> Prop) (t : real -> Prop) (c : real) : (term49 s t c) = (term50 s t c).
Proof. exact (MK_COMB (@lem5190320) (@lem5190319 s t c)). Qed.
Lemma lem5190322 (x : real) (c : real) : (term42 c x) = (real_le x c).
Proof. exact (eq_refl (term42 c x)). Qed.
Lemma lem5190323 (x : real) (s : real -> Prop) : (term51 x s) = (term51 x s).
Proof. exact (eq_refl (term51 x s)). Qed.
Lemma lem5190324 (s : real -> Prop) (x : real) (c : real) : (term52 s c x) = (term53 s x c).
Proof. exact (MK_COMB (@lem5190323 x s) (@lem5190322 x c)). Qed.
Lemma lem5190325 (s : real -> Prop) (c : real) : (term54 s c) = (term55 s c).
Proof. exact (fun_ext (fun x : real => @lem5190324 s x c)). Qed.
Lemma lem5190326 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190327 (s : real -> Prop) (c : real) : (term56 s c) = (term34 s c).
Proof. exact (MK_COMB (@lem5190326) (@lem5190325 s c)). Qed.
Lemma lem5190328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5190329 (s : real -> Prop) (c : real) : (term57 s c) = (term58 s c).
Proof. exact (MK_COMB (@lem5190328) (@lem5190327 s c)). Qed.
Lemma lem5190330 (x : real) (c : real) : (term42 c x) = (real_le x c).
Proof. exact (eq_refl (term42 c x)). Qed.
Lemma lem5190331 (x : real) (t : real -> Prop) : (term51 x t) = (term51 x t).
Proof. exact (eq_refl (term51 x t)). Qed.
Lemma lem5190332 (t : real -> Prop) (x : real) (c : real) : (term52 t c x) = (term53 t x c).
Proof. exact (MK_COMB (@lem5190331 x t) (@lem5190330 x c)). Qed.
Lemma lem5190333 (t : real -> Prop) (c : real) : (term54 t c) = (term55 t c).
Proof. exact (fun_ext (fun x : real => @lem5190332 t x c)). Qed.
Lemma lem5190334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190335 (t : real -> Prop) (c : real) : (term56 t c) = (term34 t c).
Proof. exact (MK_COMB (@lem5190334) (@lem5190333 t c)). Qed.
Lemma lem5190336 (s : real -> Prop) (t : real -> Prop) (c : real) : (term40 s t c) = (term59 s t c).
Proof. exact (MK_COMB (@lem5190329 s c) (@lem5190335 t c)). Qed.
Lemma lem5190337 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term39 s t c) = (term40 s t c)) = ((term48 s t c) = (term59 s t c)).
Proof. exact (MK_COMB (@lem5190321 s t c) (@lem5190336 s t c)). Qed.
Lemma lem5190338 (s : real -> Prop) (t : real -> Prop) (c : real) : (term48 s t c) = (term59 s t c).
Proof. exact (EQ_MP (@lem5190337 s t c) (@lem5190313 s t c)). Qed.
Lemma lem5190353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5190354 (s : real -> Prop) (t : real -> Prop) (c : real) : (term50 s t c) = (term60 s t c).
Proof. exact (MK_COMB (@lem5190353) (@lem5190338 s t c)). Qed.
Lemma lem5190356 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem5190258 x y z) (@lem5190257 x y z)). Qed.
Lemma lem5190357 (s : real -> Prop) (t : real -> Prop) (c : real) : (term61 s t c) = (term62 s t c).
Proof. exact (@lem5190356 (sup s) (sup t) c). Qed.
Lemma lem5190360 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term48 s t c) = (term61 s t c)) = ((term59 s t c) = (term62 s t c)).
Proof. exact (MK_COMB (@lem5190354 s t c) (@lem5190357 s t c)). Qed.
Lemma lem5190363 (s : real -> Prop) (t : real -> Prop) : (term63 s t) = (term64 s t).
Proof. exact (fun_ext (fun c : real => @lem5190360 s t c)). Qed.
Lemma lem5190364 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190365 (s : real -> Prop) (t : real -> Prop) : (term65 s t) = (term66 s t).
Proof. exact (MK_COMB (@lem5190364) (@lem5190363 s t)). Qed.
Lemma lem5190370 (s : real -> Prop) (t : real -> Prop) : (term66 s t) = (term65 s t).
Proof. exact (SYM (@lem5190365 s t)). Qed.
Lemma lem5190372 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5190373 (s : real -> Prop) (t : real -> Prop) : (term66 s t) = (term68 s t).
Proof. exact (@lem5190372 (term66 s t)). Qed.
Lemma lem5190374 (s : real -> Prop) (t : real -> Prop) : (term68 s t) = (term66 s t).
Proof. exact (SYM (@lem5190373 s t)). Qed.
Lemma lem5190375 (s : real -> Prop) (t : real -> Prop) (h1 : term69 s t) : term69 s t.
Proof. exact (h1). Qed.
Lemma lem5190378 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) : term70 b c s t.
Proof. exact (h1). Qed.
Lemma lem5190379 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term71 b c s t.
Proof. exact (fun h0 : term70 b c s t => @lem5190378 b c s t h0). Qed.
Lemma lem5190380 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term71 b c s t) : term71 b c s t.
Proof. exact (h1). Qed.
Lemma lem5190381 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) : term70 b c s t.
Proof. exact (h1). Qed.
Lemma lem5190382 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) (h2 : term71 b c s t) : term70 b c s t.
Proof. exact (@lem5190380 b c s t h2 (@lem5190381 b c s t h1)). Qed.
Lemma lem5190383 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) : term72 b c s t.
Proof. exact (fun h0 : term71 b c s t => @lem5190382 b c s t h1 h0). Qed.
Lemma lem5190384 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term71 b c s t) : term71 b c s t.
Proof. exact (h1). Qed.
Lemma lem5190385 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term70 b c s t) (h2 : term71 b c s t) : term70 b c s t.
Proof. exact (@lem5190383 b c s t h1 (@lem5190384 b c s t h2)). Qed.
Lemma lem5190386 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term71 b c s t) : term71 b c s t.
Proof. exact (fun h0 : term70 b c s t => @lem5190385 b c s t h0 h1). Qed.
Lemma lem5190387 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term73 b c s t.
Proof. exact (fun h0 : term71 b c s t => @lem5190386 b c s t h0). Qed.
Lemma lem5190390 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term71 b c s t.
Proof. exact (@lem5190387 b c s t (@lem5190379 b c s t)). Qed.
Lemma lem5190468 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5190469 : term74 = term75.
Proof. exact (@lem5190468 term76). Qed.
Lemma lem5190508 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem5190509 : term78 = term79.
Proof. exact (MK_COMB (@lem5190508) (@lem5190469)). Qed.
Lemma lem5190512 (s : real -> Prop) (t : real -> Prop) : (term80 s t) = (term80 s t).
Proof. exact (eq_refl (term80 s t)). Qed.
Lemma lem5190513 (s : real -> Prop) (t : real -> Prop) : (term81 s t) = (term82 s t).
Proof. exact (MK_COMB (@lem5190512 s t) (@lem5190509)). Qed.
Lemma lem5190516 (t : real -> Prop) (c : real) : (term83 t c) = (term83 t c).
Proof. exact (eq_refl (term83 t c)). Qed.
Lemma lem5190517 (c : real) (s : real -> Prop) (t : real -> Prop) : (term84 c s t) = (term85 c s t).
Proof. exact (MK_COMB (@lem5190516 t c) (@lem5190513 s t)). Qed.
Lemma lem5190520 (s : real -> Prop) (b : real) : (term83 s b) = (term83 s b).
Proof. exact (eq_refl (term83 s b)). Qed.
Lemma lem5190521 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term86 b c s t) = (term87 b c s t).
Proof. exact (MK_COMB (@lem5190520 s b) (@lem5190517 c s t)). Qed.
Lemma lem5190524 (t : real -> Prop) : (term88 t) = (term88 t).
Proof. exact (eq_refl (term88 t)). Qed.
Lemma lem5190525 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term89 b c s t) = (term90 b c s t).
Proof. exact (MK_COMB (@lem5190524 t) (@lem5190521 b c s t)). Qed.
Lemma lem5190528 (s : real -> Prop) : (term88 s) = (term88 s).
Proof. exact (eq_refl (term88 s)). Qed.
Lemma lem5190529 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term70 b c s t) = (term91 b c s t).
Proof. exact (MK_COMB (@lem5190528 s) (@lem5190525 b c s t)). Qed.
Lemma lem5190532 (c : real) (s : real -> Prop) (t : real -> Prop) : (term92 c s t) = (term93 c s t).
Proof. exact (fun_ext (fun b : real => @lem5190529 b c s t)). Qed.
Lemma lem5190533 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190534 (c : real) (s : real -> Prop) (t : real -> Prop) : (term94 c s t) = (term95 c s t).
Proof. exact (MK_COMB (@lem5190533) (@lem5190532 c s t)). Qed.
Lemma lem5190539 (s : real -> Prop) (t : real -> Prop) : (term96 s t) = (term97 s t).
Proof. exact (fun_ext (fun c : real => @lem5190534 c s t)). Qed.
Lemma lem5190540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190541 (s : real -> Prop) (t : real -> Prop) : (term98 s t) = (term99 s t).
Proof. exact (MK_COMB (@lem5190540) (@lem5190539 s t)). Qed.
Lemma lem5190546 (t : real -> Prop) : (term100 t) = (term101 t).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5190541 s t)). Qed.
Lemma lem5190547 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5190548 (t : real -> Prop) : (term102 t) = (term103 t).
Proof. exact (MK_COMB (@lem5190547) (@lem5190546 t)). Qed.
Lemma lem5190553 : term104 = term105.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5190548 t)). Qed.
Lemma lem5190554 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5190563 : term106 = term107.
Proof. exact (MK_COMB (@lem5190554) (@lem5190553)). Qed.
Lemma lem5190564 (s : real -> Prop) (b : real) : (term108 s b) = (term108 s b).
Proof. exact (eq_refl (term108 s b)). Qed.
Lemma lem5190569 (s : real -> Prop) (x : real) (b : real) : (term53 s x b) = (term53 s x b).
Proof. exact (eq_refl (term53 s x b)). Qed.
Lemma lem5190570 (s : real -> Prop) (b : real) : (term55 s b) = (term55 s b).
Proof. exact (fun_ext (fun x : real => @lem5190569 s x b)). Qed.
Lemma lem5190571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190572 (s : real -> Prop) (b : real) : (term34 s b) = (term34 s b).
Proof. exact (MK_COMB (@lem5190571) (@lem5190570 s b)). Qed.
Lemma lem5190573 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190574 (s : real -> Prop) (b : real) : (term83 s b) = (term83 s b).
Proof. exact (MK_COMB (@lem5190573) (@lem5190572 s b)). Qed.
Lemma lem5190575 (s : real -> Prop) (b : real) : (term109 s b) = (term109 s b).
Proof. exact (MK_COMB (@lem5190574 s b) (@lem5190564 s b)). Qed.
Lemma lem5190576 (s : real -> Prop) : (term110 s) = (term110 s).
Proof. exact (fun_ext (fun b : real => @lem5190575 s b)). Qed.
Lemma lem5190577 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190578 (s : real -> Prop) : (term111 s) = (term111 s).
Proof. exact (MK_COMB (@lem5190577) (@lem5190576 s)). Qed.
Lemma lem5190583 (x : real) (s : real -> Prop) : (term112 x s) = (term112 x s).
Proof. exact (eq_refl (term112 x s)). Qed.
Lemma lem5190584 (s : real -> Prop) : (term113 s) = (term113 s).
Proof. exact (fun_ext (fun x : real => @lem5190583 x s)). Qed.
Lemma lem5190585 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190586 (s : real -> Prop) : (term114 s) = (term114 s).
Proof. exact (MK_COMB (@lem5190585) (@lem5190584 s)). Qed.
Lemma lem5190587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5190588 (s : real -> Prop) : (term115 s) = (term115 s).
Proof. exact (MK_COMB (@lem5190587) (@lem5190586 s)). Qed.
Lemma lem5190589 (s : real -> Prop) : (term116 s) = (term116 s).
Proof. exact (MK_COMB (@lem5190588 s) (@lem5190578 s)). Qed.
Lemma lem5190594 (s : real -> Prop) (x : real) (b : real) : (term53 s x b) = (term53 s x b).
Proof. exact (eq_refl (term53 s x b)). Qed.
Lemma lem5190595 (s : real -> Prop) (b : real) : (term55 s b) = (term55 s b).
Proof. exact (fun_ext (fun x : real => @lem5190594 s x b)). Qed.
Lemma lem5190596 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190597 (s : real -> Prop) (b : real) : (term34 s b) = (term34 s b).
Proof. exact (MK_COMB (@lem5190596) (@lem5190595 s b)). Qed.
Lemma lem5190598 (s : real -> Prop) : (term117 s) = (term117 s).
Proof. exact (fun_ext (fun b : real => @lem5190597 s b)). Qed.
Lemma lem5190599 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5190600 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (MK_COMB (@lem5190599) (@lem5190598 s)). Qed.
Lemma lem5190605 (s : real -> Prop) : (term118 s) = (term118 s).
Proof. exact (eq_refl (term118 s)). Qed.
Lemma lem5190606 (s : real -> Prop) : (term119 s) = (term119 s).
Proof. exact (MK_COMB (@lem5190605 s) (@lem5190600 s)). Qed.
Lemma lem5190607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190608 (s : real -> Prop) : (term120 s) = (term120 s).
Proof. exact (MK_COMB (@lem5190607) (@lem5190606 s)). Qed.
Lemma lem5190609 (s : real -> Prop) : (term121 s) = (term121 s).
Proof. exact (MK_COMB (@lem5190608 s) (@lem5190589 s)). Qed.
Lemma lem5190610 : term122 = term122.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5190609 s)). Qed.
Lemma lem5190611 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5190612 : term76 = term76.
Proof. exact (MK_COMB (@lem5190611) (@lem5190610)). Qed.
Lemma lem5190613 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5190614 : term75 = term75.
Proof. exact (MK_COMB (@lem5190613) (@lem5190612)). Qed.
Lemma lem5190623 (y : real) (x : real) (z : real) : (term123 y x z) = (term123 y x z).
Proof. exact (eq_refl (term123 y x z)). Qed.
Lemma lem5190624 (y : real) (x : real) : (term124 y x) = (term124 y x).
Proof. exact (fun_ext (fun z : real => @lem5190623 y x z)). Qed.
Lemma lem5190625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190626 (y : real) (x : real) : (term125 y x) = (term125 y x).
Proof. exact (MK_COMB (@lem5190625) (@lem5190624 y x)). Qed.
Lemma lem5190627 (x : real) : (term126 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem5190626 y x)). Qed.
Lemma lem5190628 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190629 (x : real) : (term127 x) = (term127 x).
Proof. exact (MK_COMB (@lem5190628) (@lem5190627 x)). Qed.
Lemma lem5190630 : term128 = term128.
Proof. exact (fun_ext (fun x : real => @lem5190629 x)). Qed.
Lemma lem5190631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190632 : term129 = term129.
Proof. exact (MK_COMB (@lem5190631) (@lem5190630)). Qed.
Lemma lem5190633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190634 : term77 = term77.
Proof. exact (MK_COMB (@lem5190633) (@lem5190632)). Qed.
Lemma lem5190635 : term79 = term79.
Proof. exact (MK_COMB (@lem5190634) (@lem5190614)). Qed.
Lemma lem5190640 (s : real -> Prop) (t : real -> Prop) (c : real) : (term62 s t c) = (term62 s t c).
Proof. exact (eq_refl (term62 s t c)). Qed.
Lemma lem5190645 (t : real -> Prop) (x : real) (c : real) : (term53 t x c) = (term53 t x c).
Proof. exact (eq_refl (term53 t x c)). Qed.
Lemma lem5190646 (t : real -> Prop) (c : real) : (term55 t c) = (term55 t c).
Proof. exact (fun_ext (fun x : real => @lem5190645 t x c)). Qed.
Lemma lem5190647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190648 (t : real -> Prop) (c : real) : (term34 t c) = (term34 t c).
Proof. exact (MK_COMB (@lem5190647) (@lem5190646 t c)). Qed.
Lemma lem5190653 (s : real -> Prop) (x : real) (c : real) : (term53 s x c) = (term53 s x c).
Proof. exact (eq_refl (term53 s x c)). Qed.
Lemma lem5190654 (s : real -> Prop) (c : real) : (term55 s c) = (term55 s c).
Proof. exact (fun_ext (fun x : real => @lem5190653 s x c)). Qed.
Lemma lem5190655 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190656 (s : real -> Prop) (c : real) : (term34 s c) = (term34 s c).
Proof. exact (MK_COMB (@lem5190655) (@lem5190654 s c)). Qed.
Lemma lem5190657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5190658 (s : real -> Prop) (c : real) : (term58 s c) = (term58 s c).
Proof. exact (MK_COMB (@lem5190657) (@lem5190656 s c)). Qed.
Lemma lem5190659 (s : real -> Prop) (t : real -> Prop) (c : real) : (term59 s t c) = (term59 s t c).
Proof. exact (MK_COMB (@lem5190658 s c) (@lem5190648 t c)). Qed.
Lemma lem5190660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5190661 (s : real -> Prop) (t : real -> Prop) (c : real) : (term60 s t c) = (term60 s t c).
Proof. exact (MK_COMB (@lem5190660) (@lem5190659 s t c)). Qed.
Lemma lem5190662 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term59 s t c) = (term62 s t c)) = ((term59 s t c) = (term62 s t c)).
Proof. exact (MK_COMB (@lem5190661 s t c) (@lem5190640 s t c)). Qed.
Lemma lem5190663 (s : real -> Prop) (t : real -> Prop) : (term64 s t) = (term64 s t).
Proof. exact (fun_ext (fun c : real => @lem5190662 s t c)). Qed.
Lemma lem5190664 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190665 (s : real -> Prop) (t : real -> Prop) : (term66 s t) = (term66 s t).
Proof. exact (MK_COMB (@lem5190664) (@lem5190663 s t)). Qed.
Lemma lem5190666 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5190667 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term69 s t).
Proof. exact (MK_COMB (@lem5190666) (@lem5190665 s t)). Qed.
Lemma lem5190668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190669 (s : real -> Prop) (t : real -> Prop) : (term80 s t) = (term80 s t).
Proof. exact (MK_COMB (@lem5190668) (@lem5190667 s t)). Qed.
Lemma lem5190670 (s : real -> Prop) (t : real -> Prop) : (term82 s t) = (term82 s t).
Proof. exact (MK_COMB (@lem5190669 s t) (@lem5190635)). Qed.
Lemma lem5190675 (t : real -> Prop) (x : real) (c : real) : (term53 t x c) = (term53 t x c).
Proof. exact (eq_refl (term53 t x c)). Qed.
Lemma lem5190676 (t : real -> Prop) (c : real) : (term55 t c) = (term55 t c).
Proof. exact (fun_ext (fun x : real => @lem5190675 t x c)). Qed.
Lemma lem5190677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190678 (t : real -> Prop) (c : real) : (term34 t c) = (term34 t c).
Proof. exact (MK_COMB (@lem5190677) (@lem5190676 t c)). Qed.
Lemma lem5190679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190680 (t : real -> Prop) (c : real) : (term83 t c) = (term83 t c).
Proof. exact (MK_COMB (@lem5190679) (@lem5190678 t c)). Qed.
Lemma lem5190681 (c : real) (s : real -> Prop) (t : real -> Prop) : (term85 c s t) = (term85 c s t).
Proof. exact (MK_COMB (@lem5190680 t c) (@lem5190670 s t)). Qed.
Lemma lem5190686 (s : real -> Prop) (x : real) (b : real) : (term53 s x b) = (term53 s x b).
Proof. exact (eq_refl (term53 s x b)). Qed.
Lemma lem5190687 (s : real -> Prop) (b : real) : (term55 s b) = (term55 s b).
Proof. exact (fun_ext (fun x : real => @lem5190686 s x b)). Qed.
Lemma lem5190688 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190689 (s : real -> Prop) (b : real) : (term34 s b) = (term34 s b).
Proof. exact (MK_COMB (@lem5190688) (@lem5190687 s b)). Qed.
Lemma lem5190690 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5190691 (s : real -> Prop) (b : real) : (term83 s b) = (term83 s b).
Proof. exact (MK_COMB (@lem5190690) (@lem5190689 s b)). Qed.
Lemma lem5190692 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term87 b c s t) = (term87 b c s t).
Proof. exact (MK_COMB (@lem5190691 s b) (@lem5190681 c s t)). Qed.
Lemma lem5190697 (t : real -> Prop) : (term88 t) = (term88 t).
Proof. exact (eq_refl (term88 t)). Qed.
Lemma lem5190698 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term90 b c s t) = (term90 b c s t).
Proof. exact (MK_COMB (@lem5190697 t) (@lem5190692 b c s t)). Qed.
Lemma lem5190703 (s : real -> Prop) : (term88 s) = (term88 s).
Proof. exact (eq_refl (term88 s)). Qed.
Lemma lem5190704 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term91 b c s t) = (term91 b c s t).
Proof. exact (MK_COMB (@lem5190703 s) (@lem5190698 b c s t)). Qed.
Lemma lem5190705 (c : real) (s : real -> Prop) (t : real -> Prop) : (term93 c s t) = (term93 c s t).
Proof. exact (fun_ext (fun b : real => @lem5190704 b c s t)). Qed.
Lemma lem5190706 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190707 (c : real) (s : real -> Prop) (t : real -> Prop) : (term95 c s t) = (term95 c s t).
Proof. exact (MK_COMB (@lem5190706) (@lem5190705 c s t)). Qed.
Lemma lem5190708 (s : real -> Prop) (t : real -> Prop) : (term97 s t) = (term97 s t).
Proof. exact (fun_ext (fun c : real => @lem5190707 c s t)). Qed.
Lemma lem5190709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190710 (s : real -> Prop) (t : real -> Prop) : (term99 s t) = (term99 s t).
Proof. exact (MK_COMB (@lem5190709) (@lem5190708 s t)). Qed.
Lemma lem5190711 (t : real -> Prop) : (term101 t) = (term101 t).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5190710 s t)). Qed.
Lemma lem5190712 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5190713 (t : real -> Prop) : (term103 t) = (term103 t).
Proof. exact (MK_COMB (@lem5190712) (@lem5190711 t)). Qed.
Lemma lem5190714 : term105 = term105.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5190713 t)). Qed.
Lemma lem5190715 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5190716 : term107 = term107.
Proof. exact (MK_COMB (@lem5190715) (@lem5190714)). Qed.
Lemma lem5190869 : term106 = term107.
Proof. exact (TRANS (@lem5190563) (@lem5190716)). Qed.
Lemma lem5190870 : term107 = term106.
Proof. exact (SYM (@lem5190869)). Qed.
Lemma lem5190873 (s : real -> Prop) (b : real) (h1 : term34 s b) : term34 s b.
Proof. exact (h1). Qed.
Lemma lem5190874 (t : real -> Prop) (c : real) (h1 : term34 t c) : term34 t c.
Proof. exact (h1). Qed.
Lemma lem5190875 (s : real -> Prop) (t : real -> Prop) (h1 : term69 s t) : term69 s t.
Proof. exact (h1). Qed.
Lemma lem5190876 (h1 : term129) : term129.
Proof. exact (h1). Qed.
Lemma lem5190877 (h1 : term76) : term76.
Proof. exact (h1). Qed.
Lemma lem5190883 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5190889 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5190896 (s : real -> Prop) (x : real) (b : real) : (term53 s x b) = (term130 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5190897 (s : real -> Prop) (b : real) : (term55 s b) = (term131 s b).
Proof. exact (fun_ext (fun x : real => @lem5190896 s x b)). Qed.
Lemma lem5190898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5190951 (s : real -> Prop) (b : real) : (term34 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5190898) (@lem5190897 s b)). Qed.
Lemma lem5190952 (s : real -> Prop) (b : real) (h1 : term34 s b) : term132 s b.
Proof. exact (EQ_MP (@lem5190951 s b) (@lem5190873 s b h1)). Qed.
Lemma lem5190959 (t : real -> Prop) (x : real) (c : real) : (term53 t x c) = (term130 t x c).
Proof. exact (@lem17265 (@IN real x t) (real_le x c)). Qed.
Lemma lem5190960 (t : real -> Prop) (c : real) : (term55 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5190959 t x c)). Qed.
Lemma lem5190961 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191014 (t : real -> Prop) (c : real) : (term34 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5190961) (@lem5190960 t c)). Qed.
Lemma lem5191015 (t : real -> Prop) (c : real) (h1 : term34 t c) : term132 t c.
Proof. exact (EQ_MP (@lem5191014 t c) (@lem5190874 t c h1)). Qed.
Lemma lem5191024 (s : real -> Prop) (x : real) (c : real) : (term133 s x c) = (term134 s x c).
Proof. exact (@lem17362 (@IN real x s) (real_le x c)). Qed.
Lemma lem5191029 (s : real -> Prop) (x : real) (c : real) : (term53 s x c) = (term130 s x c).
Proof. exact (@lem17265 (@IN real x s) (real_le x c)). Qed.
Lemma lem5191030 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5191031 (s : real -> Prop) (c : real) : (term137 s c) = (term138 s c).
Proof. exact (@lem5191030 (term55 s c)). Qed.
Lemma lem5191032 (s : real -> Prop) (x : real) (c : real) : (term139 s c x) = (term53 s x c).
Proof. exact (eq_refl (term139 s c x)). Qed.
Lemma lem5191033 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5191034 (s : real -> Prop) (x : real) (c : real) : (term140 s c x) = (term133 s x c).
Proof. exact (MK_COMB (@lem5191033) (@lem5191032 s x c)). Qed.
Lemma lem5191035 (s : real -> Prop) (x : real) (c : real) : (term140 s c x) = (term134 s x c).
Proof. exact (TRANS (@lem5191034 s x c) (@lem5191024 s x c)). Qed.
Lemma lem5191036 (s : real -> Prop) (c : real) : (term141 s c) = (term142 s c).
Proof. exact (fun_ext (fun x : real => @lem5191035 s x c)). Qed.
Lemma lem5191037 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191038 (s : real -> Prop) (c : real) : (term138 s c) = (term143 s c).
Proof. exact (MK_COMB (@lem5191037) (@lem5191036 s c)). Qed.
Lemma lem5191039 (s : real -> Prop) (c : real) : (term137 s c) = (term143 s c).
Proof. exact (TRANS (@lem5191031 s c) (@lem5191038 s c)). Qed.
Lemma lem5191040 (s : real -> Prop) (c : real) : (term55 s c) = (term131 s c).
Proof. exact (fun_ext (fun x : real => @lem5191029 s x c)). Qed.
Lemma lem5191041 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191042 (s : real -> Prop) (c : real) : (term34 s c) = (term132 s c).
Proof. exact (MK_COMB (@lem5191041) (@lem5191040 s c)). Qed.
Lemma lem5191051 (t : real -> Prop) (x : real) (c : real) : (term133 t x c) = (term134 t x c).
Proof. exact (@lem17362 (@IN real x t) (real_le x c)). Qed.
Lemma lem5191056 (t : real -> Prop) (x : real) (c : real) : (term53 t x c) = (term130 t x c).
Proof. exact (@lem17265 (@IN real x t) (real_le x c)). Qed.
Lemma lem5191057 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5191058 (t : real -> Prop) (c : real) : (term137 t c) = (term138 t c).
Proof. exact (@lem5191057 (term55 t c)). Qed.
Lemma lem5191059 (t : real -> Prop) (x : real) (c : real) : (term139 t c x) = (term53 t x c).
Proof. exact (eq_refl (term139 t c x)). Qed.
Lemma lem5191060 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5191061 (t : real -> Prop) (x : real) (c : real) : (term140 t c x) = (term133 t x c).
Proof. exact (MK_COMB (@lem5191060) (@lem5191059 t x c)). Qed.
Lemma lem5191062 (t : real -> Prop) (x : real) (c : real) : (term140 t c x) = (term134 t x c).
Proof. exact (TRANS (@lem5191061 t x c) (@lem5191051 t x c)). Qed.
Lemma lem5191063 (t : real -> Prop) (c : real) : (term141 t c) = (term142 t c).
Proof. exact (fun_ext (fun x : real => @lem5191062 t x c)). Qed.
Lemma lem5191064 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191065 (t : real -> Prop) (c : real) : (term138 t c) = (term143 t c).
Proof. exact (MK_COMB (@lem5191064) (@lem5191063 t c)). Qed.
Lemma lem5191066 (t : real -> Prop) (c : real) : (term137 t c) = (term143 t c).
Proof. exact (TRANS (@lem5191058 t c) (@lem5191065 t c)). Qed.
Lemma lem5191067 (t : real -> Prop) (c : real) : (term55 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5191056 t x c)). Qed.
Lemma lem5191068 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191069 (t : real -> Prop) (c : real) : (term34 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5191068) (@lem5191067 t c)). Qed.
Lemma lem5191070 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191071 (s : real -> Prop) (c : real) : (term144 s c) = (term145 s c).
Proof. exact (MK_COMB (@lem5191070) (@lem5191039 s c)). Qed.
Lemma lem5191072 (s : real -> Prop) (t : real -> Prop) (c : real) : (term146 s t c) = (term147 s t c).
Proof. exact (MK_COMB (@lem5191071 s c) (@lem5191066 t c)). Qed.
Lemma lem5191073 (s : real -> Prop) (t : real -> Prop) (c : real) : (term148 s t c) = (term146 s t c).
Proof. exact (@lem17045 (term34 s c) (term34 t c)). Qed.
Lemma lem5191074 (s : real -> Prop) (t : real -> Prop) (c : real) : (term148 s t c) = (term147 s t c).
Proof. exact (TRANS (@lem5191073 s t c) (@lem5191072 s t c)). Qed.
Lemma lem5191075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5191076 (s : real -> Prop) (c : real) : (term58 s c) = (term149 s c).
Proof. exact (MK_COMB (@lem5191075) (@lem5191042 s c)). Qed.
Lemma lem5191077 (s : real -> Prop) (t : real -> Prop) (c : real) : (term59 s t c) = (term150 s t c).
Proof. exact (MK_COMB (@lem5191076 s c) (@lem5191069 t c)). Qed.
Lemma lem5191086 (s : real -> Prop) (t : real -> Prop) (c : real) : (term151 s t c) = (term152 s t c).
Proof. exact (@lem17045 (term108 s c) (term108 t c)). Qed.
Lemma lem5191089 (s : real -> Prop) (t : real -> Prop) (c : real) : (term62 s t c) = (term62 s t c).
Proof. exact (eq_refl (term62 s t c)). Qed.
Lemma lem5191090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5191091 (s : real -> Prop) (t : real -> Prop) (c : real) : (term153 s t c) = (term154 s t c).
Proof. exact (MK_COMB (@lem5191090) (@lem5191074 s t c)). Qed.
Lemma lem5191092 (s : real -> Prop) (t : real -> Prop) (c : real) : (term155 s t c) = (term156 s t c).
Proof. exact (MK_COMB (@lem5191091 s t c) (@lem5191089 s t c)). Qed.
Lemma lem5191093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5191094 (s : real -> Prop) (t : real -> Prop) (c : real) : (term157 s t c) = (term158 s t c).
Proof. exact (MK_COMB (@lem5191093) (@lem5191077 s t c)). Qed.
Lemma lem5191095 (s : real -> Prop) (t : real -> Prop) (c : real) : (term159 s t c) = (term160 s t c).
Proof. exact (MK_COMB (@lem5191094 s t c) (@lem5191086 s t c)). Qed.
Lemma lem5191096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191097 (s : real -> Prop) (t : real -> Prop) (c : real) : (term161 s t c) = (term162 s t c).
Proof. exact (MK_COMB (@lem5191096) (@lem5191095 s t c)). Qed.
Lemma lem5191098 (s : real -> Prop) (t : real -> Prop) (c : real) : (term163 s t c) = (term164 s t c).
Proof. exact (MK_COMB (@lem5191097 s t c) (@lem5191092 s t c)). Qed.
Lemma lem5191099 (s : real -> Prop) (t : real -> Prop) (c : real) : (term165 s t c) = (term163 s t c).
Proof. exact (@lem17646 (term59 s t c) (term62 s t c)). Qed.
Lemma lem5191100 (s : real -> Prop) (t : real -> Prop) (c : real) : (term165 s t c) = (term164 s t c).
Proof. exact (TRANS (@lem5191099 s t c) (@lem5191098 s t c)). Qed.
Lemma lem5191101 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5191102 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term166 s t).
Proof. exact (@lem5191101 (term64 s t)). Qed.
Lemma lem5191103 (s : real -> Prop) (t : real -> Prop) (c : real) : (term167 s t c) = ((term59 s t c) = (term62 s t c)).
Proof. exact (eq_refl (term167 s t c)). Qed.
Lemma lem5191104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5191105 (s : real -> Prop) (t : real -> Prop) (c : real) : (term168 s t c) = (term165 s t c).
Proof. exact (MK_COMB (@lem5191104) (@lem5191103 s t c)). Qed.
Lemma lem5191106 (s : real -> Prop) (t : real -> Prop) (c : real) : (term168 s t c) = (term164 s t c).
Proof. exact (TRANS (@lem5191105 s t c) (@lem5191100 s t c)). Qed.
Lemma lem5191107 (s : real -> Prop) (t : real -> Prop) : (term169 s t) = (term170 s t).
Proof. exact (fun_ext (fun c : real => @lem5191106 s t c)). Qed.
Lemma lem5191108 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191109 (s : real -> Prop) (t : real -> Prop) : (term166 s t) = (term171 s t).
Proof. exact (MK_COMB (@lem5191108) (@lem5191107 s t)). Qed.
Lemma lem5191110 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term171 s t).
Proof. exact (TRANS (@lem5191102 s t) (@lem5191109 s t)). Qed.
Lemma lem5191112 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5191113 (P : real -> Prop) (Q : real -> Prop) : (term174 P Q) = (term175 P Q).
Proof. exact (@lem5191112 real P Q). Qed.
Lemma lem5191114 (s : real -> Prop) (t : real -> Prop) : (term176 s t) = (term177 s t).
Proof. exact (@lem5191113 (term178 s t) (term179 s t)). Qed.
Lemma lem5191115 (s : real -> Prop) (t : real -> Prop) (c : real) : (term180 s t c) = (term160 s t c).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5191116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191117 (s : real -> Prop) (t : real -> Prop) (c : real) : (term181 s t c) = (term162 s t c).
Proof. exact (MK_COMB (@lem5191116) (@lem5191115 s t c)). Qed.
Lemma lem5191118 (s : real -> Prop) (t : real -> Prop) (c : real) : (term182 s t c) = (term156 s t c).
Proof. exact (eq_refl (term182 s t c)). Qed.
Lemma lem5191119 (s : real -> Prop) (t : real -> Prop) (c : real) : (term183 s t c) = (term164 s t c).
Proof. exact (MK_COMB (@lem5191117 s t c) (@lem5191118 s t c)). Qed.
Lemma lem5191120 (s : real -> Prop) (t : real -> Prop) : (term184 s t) = (term170 s t).
Proof. exact (fun_ext (fun c : real => @lem5191119 s t c)). Qed.
Lemma lem5191121 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191122 (s : real -> Prop) (t : real -> Prop) : (term176 s t) = (term171 s t).
Proof. exact (MK_COMB (@lem5191121) (@lem5191120 s t)). Qed.
Lemma lem5191123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5191124 (s : real -> Prop) (t : real -> Prop) : (term185 s t) = (term186 s t).
Proof. exact (MK_COMB (@lem5191123) (@lem5191122 s t)). Qed.
Lemma lem5191125 (s : real -> Prop) (t : real -> Prop) (c : real) : (term180 s t c) = (term160 s t c).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5191126 (s : real -> Prop) (t : real -> Prop) : (term187 s t) = (term178 s t).
Proof. exact (fun_ext (fun c : real => @lem5191125 s t c)). Qed.
Lemma lem5191127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191128 (s : real -> Prop) (t : real -> Prop) : (term188 s t) = (term189 s t).
Proof. exact (MK_COMB (@lem5191127) (@lem5191126 s t)). Qed.
Lemma lem5191129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191130 (s : real -> Prop) (t : real -> Prop) : (term190 s t) = (term191 s t).
Proof. exact (MK_COMB (@lem5191129) (@lem5191128 s t)). Qed.
Lemma lem5191131 (s : real -> Prop) (t : real -> Prop) (c : real) : (term182 s t c) = (term156 s t c).
Proof. exact (eq_refl (term182 s t c)). Qed.
Lemma lem5191132 (s : real -> Prop) (t : real -> Prop) : (term192 s t) = (term179 s t).
Proof. exact (fun_ext (fun c : real => @lem5191131 s t c)). Qed.
Lemma lem5191133 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191134 (s : real -> Prop) (t : real -> Prop) : (term193 s t) = (term194 s t).
Proof. exact (MK_COMB (@lem5191133) (@lem5191132 s t)). Qed.
Lemma lem5191135 (s : real -> Prop) (t : real -> Prop) : (term177 s t) = (term195 s t).
Proof. exact (MK_COMB (@lem5191130 s t) (@lem5191134 s t)). Qed.
Lemma lem5191136 (s : real -> Prop) (t : real -> Prop) : ((term176 s t) = (term177 s t)) = ((term171 s t) = (term195 s t)).
Proof. exact (MK_COMB (@lem5191124 s t) (@lem5191135 s t)). Qed.
Lemma lem5191137 (s : real -> Prop) (t : real -> Prop) : (term171 s t) = (term195 s t).
Proof. exact (EQ_MP (@lem5191136 s t) (@lem5191114 s t)). Qed.
Lemma lem5191427 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term173 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5191428 (P : real -> Prop) (Q : real -> Prop) : (term175 P Q) = (term174 P Q).
Proof. exact (@lem5191427 real P Q). Qed.
Lemma lem5191429 (s : real -> Prop) (t : real -> Prop) (c : real) : (term196 s t c) = (term197 s t c).
Proof. exact (@lem5191428 (term142 s c) (term142 t c)). Qed.
Lemma lem5191430 (s : real -> Prop) (x : real) (c : real) : (term198 s c x) = (term134 s x c).
Proof. exact (eq_refl (term198 s c x)). Qed.
Lemma lem5191431 (s : real -> Prop) (c : real) : (term199 s c) = (term142 s c).
Proof. exact (fun_ext (fun x : real => @lem5191430 s x c)). Qed.
Lemma lem5191432 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191433 (s : real -> Prop) (c : real) : (term200 s c) = (term143 s c).
Proof. exact (MK_COMB (@lem5191432) (@lem5191431 s c)). Qed.
Lemma lem5191434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191435 (s : real -> Prop) (c : real) : (term201 s c) = (term145 s c).
Proof. exact (MK_COMB (@lem5191434) (@lem5191433 s c)). Qed.
Lemma lem5191436 (t : real -> Prop) (x : real) (c : real) : (term198 t c x) = (term134 t x c).
Proof. exact (eq_refl (term198 t c x)). Qed.
Lemma lem5191437 (t : real -> Prop) (c : real) : (term199 t c) = (term142 t c).
Proof. exact (fun_ext (fun x : real => @lem5191436 t x c)). Qed.
Lemma lem5191438 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191439 (t : real -> Prop) (c : real) : (term200 t c) = (term143 t c).
Proof. exact (MK_COMB (@lem5191438) (@lem5191437 t c)). Qed.
Lemma lem5191440 (s : real -> Prop) (t : real -> Prop) (c : real) : (term196 s t c) = (term147 s t c).
Proof. exact (MK_COMB (@lem5191435 s c) (@lem5191439 t c)). Qed.
Lemma lem5191441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5191442 (s : real -> Prop) (t : real -> Prop) (c : real) : (term202 s t c) = (term203 s t c).
Proof. exact (MK_COMB (@lem5191441) (@lem5191440 s t c)). Qed.
Lemma lem5191443 (s : real -> Prop) (x : real) (c : real) : (term198 s c x) = (term134 s x c).
Proof. exact (eq_refl (term198 s c x)). Qed.
Lemma lem5191444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191445 (s : real -> Prop) (x : real) (c : real) : (term204 s c x) = (term205 s x c).
Proof. exact (MK_COMB (@lem5191444) (@lem5191443 s x c)). Qed.
Lemma lem5191446 (t : real -> Prop) (x : real) (c : real) : (term198 t c x) = (term134 t x c).
Proof. exact (eq_refl (term198 t c x)). Qed.
Lemma lem5191447 (s : real -> Prop) (t : real -> Prop) (x : real) (c : real) : (term206 s t c x) = (term207 s t x c).
Proof. exact (MK_COMB (@lem5191445 s x c) (@lem5191446 t x c)). Qed.
Lemma lem5191448 (s : real -> Prop) (t : real -> Prop) (c : real) : (term208 s t c) = (term209 s t c).
Proof. exact (fun_ext (fun x : real => @lem5191447 s t x c)). Qed.
Lemma lem5191449 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191450 (s : real -> Prop) (t : real -> Prop) (c : real) : (term197 s t c) = (term210 s t c).
Proof. exact (MK_COMB (@lem5191449) (@lem5191448 s t c)). Qed.
Lemma lem5191451 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term196 s t c) = (term197 s t c)) = ((term147 s t c) = (term210 s t c)).
Proof. exact (MK_COMB (@lem5191442 s t c) (@lem5191450 s t c)). Qed.
Lemma lem5191452 (s : real -> Prop) (t : real -> Prop) (c : real) : (term147 s t c) = (term210 s t c).
Proof. exact (EQ_MP (@lem5191451 s t c) (@lem5191429 s t c)). Qed.
Lemma lem5191453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5191454 (s : real -> Prop) (t : real -> Prop) (c : real) : (term154 s t c) = (term211 s t c).
Proof. exact (MK_COMB (@lem5191453) (@lem5191452 s t c)). Qed.
Lemma lem5191455 (s : real -> Prop) (t : real -> Prop) (c : real) : (term62 s t c) = (term62 s t c).
Proof. exact (eq_refl (term62 s t c)). Qed.
Lemma lem5191456 (s : real -> Prop) (t : real -> Prop) (c : real) : (term156 s t c) = (term212 s t c).
Proof. exact (MK_COMB (@lem5191454 s t c) (@lem5191455 s t c)). Qed.
Lemma lem5191458 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5191459 (P : real -> Prop) (Q : Prop) : (term215 P Q) = (term216 P Q).
Proof. exact (@lem5191458 real P Q). Qed.
Lemma lem5191460 (s : real -> Prop) (t : real -> Prop) (c : real) : (term217 s t c) = (term218 s t c).
Proof. exact (@lem5191459 (term209 s t c) (term62 s t c)). Qed.
Lemma lem5191461 (s : real -> Prop) (t : real -> Prop) (x : real) (c : real) : (term219 s t c x) = (term207 s t x c).
Proof. exact (eq_refl (term219 s t c x)). Qed.
Lemma lem5191462 (s : real -> Prop) (t : real -> Prop) (c : real) : (term220 s t c) = (term209 s t c).
Proof. exact (fun_ext (fun x : real => @lem5191461 s t x c)). Qed.
Lemma lem5191463 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191464 (s : real -> Prop) (t : real -> Prop) (c : real) : (term221 s t c) = (term210 s t c).
Proof. exact (MK_COMB (@lem5191463) (@lem5191462 s t c)). Qed.
Lemma lem5191465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5191466 (s : real -> Prop) (t : real -> Prop) (c : real) : (term222 s t c) = (term211 s t c).
Proof. exact (MK_COMB (@lem5191465) (@lem5191464 s t c)). Qed.
Lemma lem5191467 (s : real -> Prop) (t : real -> Prop) (c : real) : (term62 s t c) = (term62 s t c).
Proof. exact (eq_refl (term62 s t c)). Qed.
Lemma lem5191468 (s : real -> Prop) (t : real -> Prop) (c : real) : (term217 s t c) = (term212 s t c).
Proof. exact (MK_COMB (@lem5191466 s t c) (@lem5191467 s t c)). Qed.
Lemma lem5191469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5191470 (s : real -> Prop) (t : real -> Prop) (c : real) : (term223 s t c) = (term224 s t c).
Proof. exact (MK_COMB (@lem5191469) (@lem5191468 s t c)). Qed.
Lemma lem5191471 (s : real -> Prop) (t : real -> Prop) (x : real) (c : real) : (term219 s t c x) = (term207 s t x c).
Proof. exact (eq_refl (term219 s t c x)). Qed.
Lemma lem5191472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5191473 (s : real -> Prop) (t : real -> Prop) (x : real) (c : real) : (term225 s t c x) = (term226 s t x c).
Proof. exact (MK_COMB (@lem5191472) (@lem5191471 s t x c)). Qed.
Lemma lem5191474 (s : real -> Prop) (t : real -> Prop) (c : real) : (term62 s t c) = (term62 s t c).
Proof. exact (eq_refl (term62 s t c)). Qed.
Lemma lem5191475 (x : real) (s : real -> Prop) (t : real -> Prop) (c : real) : (term227 x s t c) = (term228 x s t c).
Proof. exact (MK_COMB (@lem5191473 s t x c) (@lem5191474 s t c)). Qed.
Lemma lem5191476 (s : real -> Prop) (t : real -> Prop) (c : real) : (term229 s t c) = (term230 s t c).
Proof. exact (fun_ext (fun x : real => @lem5191475 x s t c)). Qed.
Lemma lem5191477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191478 (s : real -> Prop) (t : real -> Prop) (c : real) : (term218 s t c) = (term231 s t c).
Proof. exact (MK_COMB (@lem5191477) (@lem5191476 s t c)). Qed.
Lemma lem5191479 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term217 s t c) = (term218 s t c)) = ((term212 s t c) = (term231 s t c)).
Proof. exact (MK_COMB (@lem5191470 s t c) (@lem5191478 s t c)). Qed.
Lemma lem5191480 (s : real -> Prop) (t : real -> Prop) (c : real) : (term212 s t c) = (term231 s t c).
Proof. exact (EQ_MP (@lem5191479 s t c) (@lem5191460 s t c)). Qed.
Lemma lem5191481 (s : real -> Prop) (t : real -> Prop) (c : real) : (term156 s t c) = (term231 s t c).
Proof. exact (TRANS (@lem5191456 s t c) (@lem5191480 s t c)). Qed.
Lemma lem5191482 (s : real -> Prop) (t : real -> Prop) : (term179 s t) = (term232 s t).
Proof. exact (fun_ext (fun c : real => @lem5191481 s t c)). Qed.
Lemma lem5191483 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191484 (s : real -> Prop) (t : real -> Prop) : (term194 s t) = (term233 s t).
Proof. exact (MK_COMB (@lem5191483) (@lem5191482 s t)). Qed.
Lemma lem5191485 (s : real -> Prop) (t : real -> Prop) : (term191 s t) = (term191 s t).
Proof. exact (eq_refl (term191 s t)). Qed.
Lemma lem5191486 (s : real -> Prop) (t : real -> Prop) : (term195 s t) = (term234 s t).
Proof. exact (MK_COMB (@lem5191485 s t) (@lem5191484 s t)). Qed.
Lemma lem5191488 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term173 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5191489 (P : real -> Prop) (Q : real -> Prop) : (term175 P Q) = (term174 P Q).
Proof. exact (@lem5191488 real P Q). Qed.
Lemma lem5191490 (s : real -> Prop) (t : real -> Prop) : (term235 s t) = (term236 s t).
Proof. exact (@lem5191489 (term178 s t) (term232 s t)). Qed.
Lemma lem5191491 (s : real -> Prop) (t : real -> Prop) (c : real) : (term180 s t c) = (term160 s t c).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5191492 (s : real -> Prop) (t : real -> Prop) : (term187 s t) = (term178 s t).
Proof. exact (fun_ext (fun c : real => @lem5191491 s t c)). Qed.
Lemma lem5191493 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191494 (s : real -> Prop) (t : real -> Prop) : (term188 s t) = (term189 s t).
Proof. exact (MK_COMB (@lem5191493) (@lem5191492 s t)). Qed.
Lemma lem5191495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191496 (s : real -> Prop) (t : real -> Prop) : (term190 s t) = (term191 s t).
Proof. exact (MK_COMB (@lem5191495) (@lem5191494 s t)). Qed.
Lemma lem5191497 (s : real -> Prop) (t : real -> Prop) (c : real) : (term237 s t c) = (term231 s t c).
Proof. exact (eq_refl (term237 s t c)). Qed.
Lemma lem5191498 (s : real -> Prop) (t : real -> Prop) : (term238 s t) = (term232 s t).
Proof. exact (fun_ext (fun c : real => @lem5191497 s t c)). Qed.
Lemma lem5191499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191500 (s : real -> Prop) (t : real -> Prop) : (term239 s t) = (term233 s t).
Proof. exact (MK_COMB (@lem5191499) (@lem5191498 s t)). Qed.
Lemma lem5191501 (s : real -> Prop) (t : real -> Prop) : (term235 s t) = (term234 s t).
Proof. exact (MK_COMB (@lem5191496 s t) (@lem5191500 s t)). Qed.
Lemma lem5191502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5191503 (s : real -> Prop) (t : real -> Prop) : (term240 s t) = (term241 s t).
Proof. exact (MK_COMB (@lem5191502) (@lem5191501 s t)). Qed.
Lemma lem5191504 (s : real -> Prop) (t : real -> Prop) (c : real) : (term180 s t c) = (term160 s t c).
Proof. exact (eq_refl (term180 s t c)). Qed.
Lemma lem5191505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191506 (s : real -> Prop) (t : real -> Prop) (c : real) : (term181 s t c) = (term162 s t c).
Proof. exact (MK_COMB (@lem5191505) (@lem5191504 s t c)). Qed.
Lemma lem5191507 (s : real -> Prop) (t : real -> Prop) (c : real) : (term237 s t c) = (term231 s t c).
Proof. exact (eq_refl (term237 s t c)). Qed.
Lemma lem5191508 (s : real -> Prop) (t : real -> Prop) (c : real) : (term242 s t c) = (term243 s t c).
Proof. exact (MK_COMB (@lem5191506 s t c) (@lem5191507 s t c)). Qed.
Lemma lem5191509 (s : real -> Prop) (t : real -> Prop) : (term244 s t) = (term245 s t).
Proof. exact (fun_ext (fun c : real => @lem5191508 s t c)). Qed.
Lemma lem5191510 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191511 (s : real -> Prop) (t : real -> Prop) : (term236 s t) = (term246 s t).
Proof. exact (MK_COMB (@lem5191510) (@lem5191509 s t)). Qed.
Lemma lem5191512 (s : real -> Prop) (t : real -> Prop) : ((term235 s t) = (term236 s t)) = ((term234 s t) = (term246 s t)).
Proof. exact (MK_COMB (@lem5191503 s t) (@lem5191511 s t)). Qed.
Lemma lem5191513 (s : real -> Prop) (t : real -> Prop) : (term234 s t) = (term246 s t).
Proof. exact (EQ_MP (@lem5191512 s t) (@lem5191490 s t)). Qed.
Lemma lem5191515 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5191516 (P : Prop) (Q : real -> Prop) : (term249 P Q) = (term250 P Q).
Proof. exact (@lem5191515 real P Q). Qed.
Lemma lem5191517 (s : real -> Prop) (t : real -> Prop) (c : real) : (term251 s t c) = (term252 s t c).
Proof. exact (@lem5191516 (term160 s t c) (term230 s t c)). Qed.
Lemma lem5191518 (x : real) (s : real -> Prop) (t : real -> Prop) (c : real) : (term253 s t c x) = (term228 x s t c).
Proof. exact (eq_refl (term253 s t c x)). Qed.
Lemma lem5191519 (s : real -> Prop) (t : real -> Prop) (c : real) : (term254 s t c) = (term230 s t c).
Proof. exact (fun_ext (fun x : real => @lem5191518 x s t c)). Qed.
Lemma lem5191520 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191521 (s : real -> Prop) (t : real -> Prop) (c : real) : (term255 s t c) = (term231 s t c).
Proof. exact (MK_COMB (@lem5191520) (@lem5191519 s t c)). Qed.
Lemma lem5191522 (s : real -> Prop) (t : real -> Prop) (c : real) : (term162 s t c) = (term162 s t c).
Proof. exact (eq_refl (term162 s t c)). Qed.
Lemma lem5191523 (s : real -> Prop) (t : real -> Prop) (c : real) : (term251 s t c) = (term243 s t c).
Proof. exact (MK_COMB (@lem5191522 s t c) (@lem5191521 s t c)). Qed.
Lemma lem5191524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5191525 (s : real -> Prop) (t : real -> Prop) (c : real) : (term256 s t c) = (term257 s t c).
Proof. exact (MK_COMB (@lem5191524) (@lem5191523 s t c)). Qed.
Lemma lem5191526 (x : real) (s : real -> Prop) (t : real -> Prop) (c : real) : (term253 s t c x) = (term228 x s t c).
Proof. exact (eq_refl (term253 s t c x)). Qed.
Lemma lem5191527 (s : real -> Prop) (t : real -> Prop) (c : real) : (term162 s t c) = (term162 s t c).
Proof. exact (eq_refl (term162 s t c)). Qed.
Lemma lem5191528 (x : real) (s : real -> Prop) (t : real -> Prop) (c : real) : (term258 s t c x) = (term259 x s t c).
Proof. exact (MK_COMB (@lem5191527 s t c) (@lem5191526 x s t c)). Qed.
Lemma lem5191529 (s : real -> Prop) (t : real -> Prop) (c : real) : (term260 s t c) = (term261 s t c).
Proof. exact (fun_ext (fun x : real => @lem5191528 x s t c)). Qed.
Lemma lem5191530 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191531 (s : real -> Prop) (t : real -> Prop) (c : real) : (term252 s t c) = (term262 s t c).
Proof. exact (MK_COMB (@lem5191530) (@lem5191529 s t c)). Qed.
Lemma lem5191532 (s : real -> Prop) (t : real -> Prop) (c : real) : ((term251 s t c) = (term252 s t c)) = ((term243 s t c) = (term262 s t c)).
Proof. exact (MK_COMB (@lem5191525 s t c) (@lem5191531 s t c)). Qed.
Lemma lem5191533 (s : real -> Prop) (t : real -> Prop) (c : real) : (term243 s t c) = (term262 s t c).
Proof. exact (EQ_MP (@lem5191532 s t c) (@lem5191517 s t c)). Qed.
Lemma lem5191534 (s : real -> Prop) (t : real -> Prop) : (term245 s t) = (term263 s t).
Proof. exact (fun_ext (fun c : real => @lem5191533 s t c)). Qed.
Lemma lem5191535 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191536 (s : real -> Prop) (t : real -> Prop) : (term246 s t) = (term264 s t).
Proof. exact (MK_COMB (@lem5191535) (@lem5191534 s t)). Qed.
Lemma lem5191537 (s : real -> Prop) (t : real -> Prop) : (term234 s t) = (term264 s t).
Proof. exact (TRANS (@lem5191513 s t) (@lem5191536 s t)). Qed.
Lemma lem5191538 (s : real -> Prop) (t : real -> Prop) : (term195 s t) = (term264 s t).
Proof. exact (TRANS (@lem5191486 s t) (@lem5191537 s t)). Qed.
Lemma lem5191539 (s : real -> Prop) (t : real -> Prop) : (term171 s t) = (term264 s t).
Proof. exact (TRANS (@lem5191137 s t) (@lem5191538 s t)). Qed.
Lemma lem5191540 (s : real -> Prop) (t : real -> Prop) : (term69 s t) = (term264 s t).
Proof. exact (TRANS (@lem5191110 s t) (@lem5191539 s t)). Qed.
Lemma lem5191541 (s : real -> Prop) (t : real -> Prop) (h1 : term69 s t) : term264 s t.
Proof. exact (EQ_MP (@lem5191540 s t) (@lem5190875 s t h1)). Qed.
Lemma lem5191548 (x : real) (y : real) (z : real) : (term265 x y z) = (term266 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5191549 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5191550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191551 (x : real) (y : real) (z : real) : (term267 x y z) = (term268 x y z).
Proof. exact (MK_COMB (@lem5191550) (@lem5191548 x y z)). Qed.
Lemma lem5191552 (y : real) (x : real) (z : real) : (term269 y x z) = (term270 y x z).
Proof. exact (MK_COMB (@lem5191551 x y z) (@lem5191549 x z)). Qed.
Lemma lem5191553 (y : real) (x : real) (z : real) : (term123 y x z) = (term269 y x z).
Proof. exact (@lem17265 (term271 x y z) (real_le x z)). Qed.
Lemma lem5191554 (y : real) (x : real) (z : real) : (term123 y x z) = (term270 y x z).
Proof. exact (TRANS (@lem5191553 y x z) (@lem5191552 y x z)). Qed.
Lemma lem5191555 (y : real) (x : real) : (term124 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5191554 y x z)). Qed.
Lemma lem5191556 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191557 (y : real) (x : real) : (term125 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5191556) (@lem5191555 y x)). Qed.
Lemma lem5191558 (x : real) : (term126 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5191557 y x)). Qed.
Lemma lem5191559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191560 (x : real) : (term127 x) = (term275 x).
Proof. exact (MK_COMB (@lem5191559) (@lem5191558 x)). Qed.
Lemma lem5191561 : term128 = term276.
Proof. exact (fun_ext (fun x : real => @lem5191560 x)). Qed.
Lemma lem5191562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191623 : term129 = term277.
Proof. exact (MK_COMB (@lem5191562) (@lem5191561)). Qed.
Lemma lem5191624 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5191623) (@lem5190876 h1)). Qed.
Lemma lem5191627 (s : real -> Prop) : (term278 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5191634 (s : real -> Prop) (x : real) (b : real) : (term133 s x b) = (term134 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5191635 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5191636 (s : real -> Prop) (b : real) : (term137 s b) = (term138 s b).
Proof. exact (@lem5191635 (term55 s b)). Qed.
Lemma lem5191637 (s : real -> Prop) (x : real) (b : real) : (term139 s b x) = (term53 s x b).
Proof. exact (eq_refl (term139 s b x)). Qed.
Lemma lem5191638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5191639 (s : real -> Prop) (x : real) (b : real) : (term140 s b x) = (term133 s x b).
Proof. exact (MK_COMB (@lem5191638) (@lem5191637 s x b)). Qed.
Lemma lem5191640 (s : real -> Prop) (x : real) (b : real) : (term140 s b x) = (term134 s x b).
Proof. exact (TRANS (@lem5191639 s x b) (@lem5191634 s x b)). Qed.
Lemma lem5191641 (s : real -> Prop) (b : real) : (term141 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5191640 s x b)). Qed.
Lemma lem5191642 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191643 (s : real -> Prop) (b : real) : (term138 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5191642) (@lem5191641 s b)). Qed.
Lemma lem5191644 (s : real -> Prop) (b : real) : (term137 s b) = (term143 s b).
Proof. exact (TRANS (@lem5191636 s b) (@lem5191643 s b)). Qed.
Lemma lem5191645 (P : real -> Prop) : (term279 P) = (term280 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5191646 (s : real -> Prop) : (term281 s) = (term282 s).
Proof. exact (@lem5191645 (term117 s)). Qed.
Lemma lem5191647 (s : real -> Prop) (b : real) : (term283 s b) = (term34 s b).
Proof. exact (eq_refl (term283 s b)). Qed.
Lemma lem5191648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5191649 (s : real -> Prop) (b : real) : (term284 s b) = (term137 s b).
Proof. exact (MK_COMB (@lem5191648) (@lem5191647 s b)). Qed.
Lemma lem5191650 (s : real -> Prop) (b : real) : (term284 s b) = (term143 s b).
Proof. exact (TRANS (@lem5191649 s b) (@lem5191644 s b)). Qed.
Lemma lem5191651 (s : real -> Prop) : (term285 s) = (term286 s).
Proof. exact (fun_ext (fun b : real => @lem5191650 s b)). Qed.
Lemma lem5191652 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191653 (s : real -> Prop) : (term282 s) = (term287 s).
Proof. exact (MK_COMB (@lem5191652) (@lem5191651 s)). Qed.
Lemma lem5191654 (s : real -> Prop) : (term281 s) = (term287 s).
Proof. exact (TRANS (@lem5191646 s) (@lem5191653 s)). Qed.
Lemma lem5191655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191656 (s : real -> Prop) : (term288 s) = (term289 s).
Proof. exact (MK_COMB (@lem5191655) (@lem5191627 s)). Qed.
Lemma lem5191657 (s : real -> Prop) : (term290 s) = (term291 s).
Proof. exact (MK_COMB (@lem5191656 s) (@lem5191654 s)). Qed.
Lemma lem5191658 (s : real -> Prop) : (term292 s) = (term290 s).
Proof. exact (@lem17045 (term31 s) (term33 s)). Qed.
Lemma lem5191659 (s : real -> Prop) : (term292 s) = (term291 s).
Proof. exact (TRANS (@lem5191658 s) (@lem5191657 s)). Qed.
Lemma lem5191666 (x : real) (s : real -> Prop) : (term112 x s) = (term293 x s).
Proof. exact (@lem17265 (@IN real x s) (term294 x s)). Qed.
Lemma lem5191667 (s : real -> Prop) : (term113 s) = (term295 s).
Proof. exact (fun_ext (fun x : real => @lem5191666 x s)). Qed.
Lemma lem5191668 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191669 (s : real -> Prop) : (term114 s) = (term296 s).
Proof. exact (MK_COMB (@lem5191668) (@lem5191667 s)). Qed.
Lemma lem5191676 (s : real -> Prop) (x : real) (b : real) : (term133 s x b) = (term134 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5191677 (P : real -> Prop) : (term135 P) = (term136 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5191678 (s : real -> Prop) (b : real) : (term137 s b) = (term138 s b).
Proof. exact (@lem5191677 (term55 s b)). Qed.
Lemma lem5191679 (s : real -> Prop) (x : real) (b : real) : (term139 s b x) = (term53 s x b).
Proof. exact (eq_refl (term139 s b x)). Qed.
Lemma lem5191680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5191681 (s : real -> Prop) (x : real) (b : real) : (term140 s b x) = (term133 s x b).
Proof. exact (MK_COMB (@lem5191680) (@lem5191679 s x b)). Qed.
Lemma lem5191682 (s : real -> Prop) (x : real) (b : real) : (term140 s b x) = (term134 s x b).
Proof. exact (TRANS (@lem5191681 s x b) (@lem5191676 s x b)). Qed.
Lemma lem5191683 (s : real -> Prop) (b : real) : (term141 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5191682 s x b)). Qed.
Lemma lem5191684 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191685 (s : real -> Prop) (b : real) : (term138 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5191684) (@lem5191683 s b)). Qed.
Lemma lem5191686 (s : real -> Prop) (b : real) : (term137 s b) = (term143 s b).
Proof. exact (TRANS (@lem5191678 s b) (@lem5191685 s b)). Qed.
Lemma lem5191687 (s : real -> Prop) (b : real) : (term108 s b) = (term108 s b).
Proof. exact (eq_refl (term108 s b)). Qed.
Lemma lem5191688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191689 (s : real -> Prop) (b : real) : (term144 s b) = (term145 s b).
Proof. exact (MK_COMB (@lem5191688) (@lem5191686 s b)). Qed.
Lemma lem5191690 (s : real -> Prop) (b : real) : (term297 s b) = (term298 s b).
Proof. exact (MK_COMB (@lem5191689 s b) (@lem5191687 s b)). Qed.
Lemma lem5191691 (s : real -> Prop) (b : real) : (term109 s b) = (term297 s b).
Proof. exact (@lem17265 (term34 s b) (term108 s b)). Qed.
Lemma lem5191692 (s : real -> Prop) (b : real) : (term109 s b) = (term298 s b).
Proof. exact (TRANS (@lem5191691 s b) (@lem5191690 s b)). Qed.
Lemma lem5191693 (s : real -> Prop) : (term110 s) = (term299 s).
Proof. exact (fun_ext (fun b : real => @lem5191692 s b)). Qed.
Lemma lem5191694 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191695 (s : real -> Prop) : (term111 s) = (term300 s).
Proof. exact (MK_COMB (@lem5191694) (@lem5191693 s)). Qed.
Lemma lem5191696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5191697 (s : real -> Prop) : (term115 s) = (term301 s).
Proof. exact (MK_COMB (@lem5191696) (@lem5191669 s)). Qed.
Lemma lem5191698 (s : real -> Prop) : (term116 s) = (term302 s).
Proof. exact (MK_COMB (@lem5191697 s) (@lem5191695 s)). Qed.
Lemma lem5191699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5191700 (s : real -> Prop) : (term303 s) = (term304 s).
Proof. exact (MK_COMB (@lem5191699) (@lem5191659 s)). Qed.
Lemma lem5191701 (s : real -> Prop) : (term305 s) = (term306 s).
Proof. exact (MK_COMB (@lem5191700 s) (@lem5191698 s)). Qed.
Lemma lem5191702 (s : real -> Prop) : (term121 s) = (term305 s).
Proof. exact (@lem17265 (term119 s) (term116 s)). Qed.
Lemma lem5191703 (s : real -> Prop) : (term121 s) = (term306 s).
Proof. exact (TRANS (@lem5191702 s) (@lem5191701 s)). Qed.
Lemma lem5191704 : term122 = term307.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5191703 s)). Qed.
Lemma lem5191705 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5191706 : term76 = term308.
Proof. exact (MK_COMB (@lem5191705) (@lem5191704)). Qed.
Lemma lem5191953 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5191954 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5191953 real real P). Qed.
Lemma lem5191955 (s : real -> Prop) : (term313 s) = (term314 s).
Proof. exact (@lem5191954 (term315 s)). Qed.
Lemma lem5191956 (s : real -> Prop) (b : real) : (term316 s b) = (term142 s b).
Proof. exact (eq_refl (term316 s b)). Qed.
Lemma lem5191957 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5191958 (s : real -> Prop) (b : real) (x : real) : (term317 s b x) = (term198 s b x).
Proof. exact (MK_COMB (@lem5191956 s b) (@lem5191957 x)). Qed.
Lemma lem5191959 (s : real -> Prop) (x : real) (b : real) : (term198 s b x) = (term134 s x b).
Proof. exact (eq_refl (term198 s b x)). Qed.
Lemma lem5191960 (s : real -> Prop) (x : real) (b : real) : (term317 s b x) = (term134 s x b).
Proof. exact (TRANS (@lem5191958 s b x) (@lem5191959 s x b)). Qed.
Lemma lem5191961 (s : real -> Prop) (b : real) : (term318 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5191960 s x b)). Qed.
Lemma lem5191962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5191963 (s : real -> Prop) (b : real) : (term319 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5191962) (@lem5191961 s b)). Qed.
Lemma lem5191964 (s : real -> Prop) : (term320 s) = (term286 s).
Proof. exact (fun_ext (fun b : real => @lem5191963 s b)). Qed.
Lemma lem5191965 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191966 (s : real -> Prop) : (term313 s) = (term287 s).
Proof. exact (MK_COMB (@lem5191965) (@lem5191964 s)). Qed.
Lemma lem5191967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5191968 (s : real -> Prop) : (term321 s) = (term322 s).
Proof. exact (MK_COMB (@lem5191967) (@lem5191966 s)). Qed.
Lemma lem5191969 (s : real -> Prop) (b : real) : (term316 s b) = (term142 s b).
Proof. exact (eq_refl (term316 s b)). Qed.
Lemma lem5191970 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5191971 (s : real -> Prop) (x : real -> real) (b : real) : (term323 s x b) = (term324 s x b).
Proof. exact (MK_COMB (@lem5191969 s b) (@lem5191970 x b)). Qed.
Lemma lem5191972 (s : real -> Prop) (x : real -> real) (b : real) : (term324 s x b) = (term325 s x b).
Proof. exact (eq_refl (term324 s x b)). Qed.
Lemma lem5191973 (s : real -> Prop) (x : real -> real) (b : real) : (term323 s x b) = (term325 s x b).
Proof. exact (TRANS (@lem5191971 s x b) (@lem5191972 s x b)). Qed.
Lemma lem5191974 (s : real -> Prop) (x : real -> real) : (term326 s x) = (term327 s x).
Proof. exact (fun_ext (fun b : real => @lem5191973 s x b)). Qed.
Lemma lem5191975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5191976 (s : real -> Prop) (x : real -> real) : (term328 s x) = (term329 s x).
Proof. exact (MK_COMB (@lem5191975) (@lem5191974 s x)). Qed.
Lemma lem5191977 (s : real -> Prop) : (term330 s) = (term331 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5191976 s x)). Qed.
Lemma lem5191978 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5191979 (s : real -> Prop) : (term314 s) = (term332 s).
Proof. exact (MK_COMB (@lem5191978) (@lem5191977 s)). Qed.
Lemma lem5191980 (s : real -> Prop) : ((term313 s) = (term314 s)) = ((term287 s) = (term332 s)).
Proof. exact (MK_COMB (@lem5191968 s) (@lem5191979 s)). Qed.
Lemma lem5191981 (s : real -> Prop) : (term287 s) = (term332 s).
Proof. exact (EQ_MP (@lem5191980 s) (@lem5191955 s)). Qed.
Lemma lem5191982 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5191983 (s : real -> Prop) : (term291 s) = (term333 s).
Proof. exact (MK_COMB (@lem5191982 s) (@lem5191981 s)). Qed.
Lemma lem5191985 {A : Type'} (P : Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5191986 (P : Prop) (Q : type1028) : (term334 P Q) = (term335 P Q).
Proof. exact (@lem5191985 (real -> real) P Q). Qed.
Lemma lem5191987 (s : real -> Prop) : (term336 s) = (term337 s).
Proof. exact (@lem5191986 (s = (@EMPTY real)) (term331 s)). Qed.
Lemma lem5191988 (s : real -> Prop) (x : real -> real) : (term338 s x) = (term329 s x).
Proof. exact (eq_refl (term338 s x)). Qed.
Lemma lem5191989 (s : real -> Prop) : (term339 s) = (term331 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5191988 s x)). Qed.
Lemma lem5191990 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5191991 (s : real -> Prop) : (term340 s) = (term332 s).
Proof. exact (MK_COMB (@lem5191990) (@lem5191989 s)). Qed.
Lemma lem5191992 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5191993 (s : real -> Prop) : (term336 s) = (term333 s).
Proof. exact (MK_COMB (@lem5191992 s) (@lem5191991 s)). Qed.
Lemma lem5191994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5191995 (s : real -> Prop) : (term341 s) = (term342 s).
Proof. exact (MK_COMB (@lem5191994) (@lem5191993 s)). Qed.
Lemma lem5191996 (s : real -> Prop) (x : real -> real) : (term338 s x) = (term329 s x).
Proof. exact (eq_refl (term338 s x)). Qed.
Lemma lem5191997 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5191998 (s : real -> Prop) (x : real -> real) : (term343 s x) = (term344 s x).
Proof. exact (MK_COMB (@lem5191997 s) (@lem5191996 s x)). Qed.
Lemma lem5191999 (s : real -> Prop) : (term345 s) = (term346 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5191998 s x)). Qed.
Lemma lem5192000 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192001 (s : real -> Prop) : (term337 s) = (term347 s).
Proof. exact (MK_COMB (@lem5192000) (@lem5191999 s)). Qed.
Lemma lem5192002 (s : real -> Prop) : ((term336 s) = (term337 s)) = ((term333 s) = (term347 s)).
Proof. exact (MK_COMB (@lem5191995 s) (@lem5192001 s)). Qed.
Lemma lem5192003 (s : real -> Prop) : (term333 s) = (term347 s).
Proof. exact (EQ_MP (@lem5192002 s) (@lem5191987 s)). Qed.
Lemma lem5192004 (s : real -> Prop) : (term291 s) = (term347 s).
Proof. exact (TRANS (@lem5191983 s) (@lem5192003 s)). Qed.
Lemma lem5192005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192006 (s : real -> Prop) : (term304 s) = (term348 s).
Proof. exact (MK_COMB (@lem5192005) (@lem5192004 s)). Qed.
Lemma lem5192008 {A : Type'} (P : A -> Prop) (Q : Prop) : (term349 A P Q) = (term350 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5192009 (P : real -> Prop) (Q : Prop) : (term351 P Q) = (term352 P Q).
Proof. exact (@lem5192008 real P Q). Qed.
Lemma lem5192010 (s : real -> Prop) (b : real) : (term353 s b) = (term354 s b).
Proof. exact (@lem5192009 (term142 s b) (term108 s b)). Qed.
Lemma lem5192011 (s : real -> Prop) (x : real) (b : real) : (term198 s b x) = (term134 s x b).
Proof. exact (eq_refl (term198 s b x)). Qed.
Lemma lem5192012 (s : real -> Prop) (b : real) : (term199 s b) = (term142 s b).
Proof. exact (fun_ext (fun x : real => @lem5192011 s x b)). Qed.
Lemma lem5192013 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5192014 (s : real -> Prop) (b : real) : (term200 s b) = (term143 s b).
Proof. exact (MK_COMB (@lem5192013) (@lem5192012 s b)). Qed.
Lemma lem5192015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192016 (s : real -> Prop) (b : real) : (term201 s b) = (term145 s b).
Proof. exact (MK_COMB (@lem5192015) (@lem5192014 s b)). Qed.
Lemma lem5192017 (s : real -> Prop) (b : real) : (term108 s b) = (term108 s b).
Proof. exact (eq_refl (term108 s b)). Qed.
Lemma lem5192018 (s : real -> Prop) (b : real) : (term353 s b) = (term298 s b).
Proof. exact (MK_COMB (@lem5192016 s b) (@lem5192017 s b)). Qed.
Lemma lem5192019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192020 (s : real -> Prop) (b : real) : (term355 s b) = (term356 s b).
Proof. exact (MK_COMB (@lem5192019) (@lem5192018 s b)). Qed.
Lemma lem5192021 (s : real -> Prop) (x : real) (b : real) : (term198 s b x) = (term134 s x b).
Proof. exact (eq_refl (term198 s b x)). Qed.
Lemma lem5192022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192023 (s : real -> Prop) (x : real) (b : real) : (term204 s b x) = (term205 s x b).
Proof. exact (MK_COMB (@lem5192022) (@lem5192021 s x b)). Qed.
Lemma lem5192024 (s : real -> Prop) (b : real) : (term108 s b) = (term108 s b).
Proof. exact (eq_refl (term108 s b)). Qed.
Lemma lem5192025 (x : real) (s : real -> Prop) (b : real) : (term357 x s b) = (term358 x s b).
Proof. exact (MK_COMB (@lem5192023 s x b) (@lem5192024 s b)). Qed.
Lemma lem5192026 (s : real -> Prop) (b : real) : (term359 s b) = (term360 s b).
Proof. exact (fun_ext (fun x : real => @lem5192025 x s b)). Qed.
Lemma lem5192027 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5192028 (s : real -> Prop) (b : real) : (term354 s b) = (term361 s b).
Proof. exact (MK_COMB (@lem5192027) (@lem5192026 s b)). Qed.
Lemma lem5192029 (s : real -> Prop) (b : real) : ((term353 s b) = (term354 s b)) = ((term298 s b) = (term361 s b)).
Proof. exact (MK_COMB (@lem5192020 s b) (@lem5192028 s b)). Qed.
Lemma lem5192030 (s : real -> Prop) (b : real) : (term298 s b) = (term361 s b).
Proof. exact (EQ_MP (@lem5192029 s b) (@lem5192010 s b)). Qed.
Lemma lem5192031 (s : real -> Prop) : (term299 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5192030 s b)). Qed.
Lemma lem5192032 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192033 (s : real -> Prop) : (term300 s) = (term363 s).
Proof. exact (MK_COMB (@lem5192032) (@lem5192031 s)). Qed.
Lemma lem5192035 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5192036 (P : type1626) : (term311 P) = (term312 P).
Proof. exact (@lem5192035 real real P). Qed.
Lemma lem5192037 (s : real -> Prop) : (term364 s) = (term365 s).
Proof. exact (@lem5192036 (term366 s)). Qed.
Lemma lem5192038 (s : real -> Prop) (b : real) : (term367 s b) = (term360 s b).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5192039 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5192040 (s : real -> Prop) (b : real) (x : real) : (term368 s b x) = (term369 s b x).
Proof. exact (MK_COMB (@lem5192038 s b) (@lem5192039 x)). Qed.
Lemma lem5192041 (x : real) (s : real -> Prop) (b : real) : (term369 s b x) = (term358 x s b).
Proof. exact (eq_refl (term369 s b x)). Qed.
Lemma lem5192042 (x : real) (s : real -> Prop) (b : real) : (term368 s b x) = (term358 x s b).
Proof. exact (TRANS (@lem5192040 s b x) (@lem5192041 x s b)). Qed.
Lemma lem5192043 (s : real -> Prop) (b : real) : (term370 s b) = (term360 s b).
Proof. exact (fun_ext (fun x : real => @lem5192042 x s b)). Qed.
Lemma lem5192044 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5192045 (s : real -> Prop) (b : real) : (term371 s b) = (term361 s b).
Proof. exact (MK_COMB (@lem5192044) (@lem5192043 s b)). Qed.
Lemma lem5192046 (s : real -> Prop) : (term372 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5192045 s b)). Qed.
Lemma lem5192047 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192048 (s : real -> Prop) : (term364 s) = (term363 s).
Proof. exact (MK_COMB (@lem5192047) (@lem5192046 s)). Qed.
Lemma lem5192049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192050 (s : real -> Prop) : (term373 s) = (term374 s).
Proof. exact (MK_COMB (@lem5192049) (@lem5192048 s)). Qed.
Lemma lem5192051 (s : real -> Prop) (b : real) : (term367 s b) = (term360 s b).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5192052 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5192053 (s : real -> Prop) (x : real -> real) (b : real) : (term375 s x b) = (term376 s x b).
Proof. exact (MK_COMB (@lem5192051 s b) (@lem5192052 x b)). Qed.
Lemma lem5192054 (x : real -> real) (s : real -> Prop) (b : real) : (term376 s x b) = (term377 x s b).
Proof. exact (eq_refl (term376 s x b)). Qed.
Lemma lem5192055 (x : real -> real) (s : real -> Prop) (b : real) : (term375 s x b) = (term377 x s b).
Proof. exact (TRANS (@lem5192053 s x b) (@lem5192054 x s b)). Qed.
Lemma lem5192056 (x : real -> real) (s : real -> Prop) : (term378 s x) = (term379 x s).
Proof. exact (fun_ext (fun b : real => @lem5192055 x s b)). Qed.
Lemma lem5192057 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192058 (x : real -> real) (s : real -> Prop) : (term380 s x) = (term381 x s).
Proof. exact (MK_COMB (@lem5192057) (@lem5192056 x s)). Qed.
Lemma lem5192059 (s : real -> Prop) : (term382 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5192058 x s)). Qed.
Lemma lem5192060 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192061 (s : real -> Prop) : (term365 s) = (term384 s).
Proof. exact (MK_COMB (@lem5192060) (@lem5192059 s)). Qed.
Lemma lem5192062 (s : real -> Prop) : ((term364 s) = (term365 s)) = ((term363 s) = (term384 s)).
Proof. exact (MK_COMB (@lem5192050 s) (@lem5192061 s)). Qed.
Lemma lem5192063 (s : real -> Prop) : (term363 s) = (term384 s).
Proof. exact (EQ_MP (@lem5192062 s) (@lem5192037 s)). Qed.
Lemma lem5192064 (s : real -> Prop) : (term300 s) = (term384 s).
Proof. exact (TRANS (@lem5192033 s) (@lem5192063 s)). Qed.
Lemma lem5192065 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5192066 (s : real -> Prop) : (term302 s) = (term385 s).
Proof. exact (MK_COMB (@lem5192065 s) (@lem5192064 s)). Qed.
Lemma lem5192068 {A : Type'} (P : Prop) (Q : A -> Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5192069 (P : Prop) (Q : type1028) : (term388 P Q) = (term389 P Q).
Proof. exact (@lem5192068 (real -> real) P Q). Qed.
Lemma lem5192070 (s : real -> Prop) : (term390 s) = (term391 s).
Proof. exact (@lem5192069 (term296 s) (term383 s)). Qed.
Lemma lem5192071 (x : real -> real) (s : real -> Prop) : (term392 s x) = (term381 x s).
Proof. exact (eq_refl (term392 s x)). Qed.
Lemma lem5192072 (s : real -> Prop) : (term393 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5192071 x s)). Qed.
Lemma lem5192073 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192074 (s : real -> Prop) : (term394 s) = (term384 s).
Proof. exact (MK_COMB (@lem5192073) (@lem5192072 s)). Qed.
Lemma lem5192075 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5192076 (s : real -> Prop) : (term390 s) = (term385 s).
Proof. exact (MK_COMB (@lem5192075 s) (@lem5192074 s)). Qed.
Lemma lem5192077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192078 (s : real -> Prop) : (term395 s) = (term396 s).
Proof. exact (MK_COMB (@lem5192077) (@lem5192076 s)). Qed.
Lemma lem5192079 (x : real -> real) (s : real -> Prop) : (term392 s x) = (term381 x s).
Proof. exact (eq_refl (term392 s x)). Qed.
Lemma lem5192080 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (eq_refl (term301 s)). Qed.
Lemma lem5192081 (x : real -> real) (s : real -> Prop) : (term397 s x) = (term398 x s).
Proof. exact (MK_COMB (@lem5192080 s) (@lem5192079 x s)). Qed.
Lemma lem5192082 (s : real -> Prop) : (term399 s) = (term400 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5192081 x s)). Qed.
Lemma lem5192083 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192084 (s : real -> Prop) : (term391 s) = (term401 s).
Proof. exact (MK_COMB (@lem5192083) (@lem5192082 s)). Qed.
Lemma lem5192085 (s : real -> Prop) : ((term390 s) = (term391 s)) = ((term385 s) = (term401 s)).
Proof. exact (MK_COMB (@lem5192078 s) (@lem5192084 s)). Qed.
Lemma lem5192086 (s : real -> Prop) : (term385 s) = (term401 s).
Proof. exact (EQ_MP (@lem5192085 s) (@lem5192070 s)). Qed.
Lemma lem5192087 (s : real -> Prop) : (term302 s) = (term401 s).
Proof. exact (TRANS (@lem5192066 s) (@lem5192086 s)). Qed.
Lemma lem5192088 (s : real -> Prop) : (term306 s) = (term402 s).
Proof. exact (MK_COMB (@lem5192006 s) (@lem5192087 s)). Qed.
Lemma lem5192090 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term173 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5192091 (P : type1028) (Q : type1028) : (term403 P Q) = (term404 P Q).
Proof. exact (@lem5192090 (real -> real) P Q). Qed.
Lemma lem5192092 (s : real -> Prop) : (term405 s) = (term406 s).
Proof. exact (@lem5192091 (term346 s) (term400 s)). Qed.
Lemma lem5192093 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term344 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5192094 (s : real -> Prop) : (term408 s) = (term346 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5192093 s x)). Qed.
Lemma lem5192095 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192096 (s : real -> Prop) : (term409 s) = (term347 s).
Proof. exact (MK_COMB (@lem5192095) (@lem5192094 s)). Qed.
Lemma lem5192097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192098 (s : real -> Prop) : (term410 s) = (term348 s).
Proof. exact (MK_COMB (@lem5192097) (@lem5192096 s)). Qed.
Lemma lem5192099 (x : real -> real) (s : real -> Prop) : (term411 s x) = (term398 x s).
Proof. exact (eq_refl (term411 s x)). Qed.
Lemma lem5192100 (s : real -> Prop) : (term412 s) = (term400 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5192099 x s)). Qed.
Lemma lem5192101 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192102 (s : real -> Prop) : (term413 s) = (term401 s).
Proof. exact (MK_COMB (@lem5192101) (@lem5192100 s)). Qed.
Lemma lem5192103 (s : real -> Prop) : (term405 s) = (term402 s).
Proof. exact (MK_COMB (@lem5192098 s) (@lem5192102 s)). Qed.
Lemma lem5192104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192105 (s : real -> Prop) : (term414 s) = (term415 s).
Proof. exact (MK_COMB (@lem5192104) (@lem5192103 s)). Qed.
Lemma lem5192106 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term344 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5192107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192108 (s : real -> Prop) (x : real -> real) : (term416 s x) = (term417 s x).
Proof. exact (MK_COMB (@lem5192107) (@lem5192106 s x)). Qed.
Lemma lem5192109 (x : real -> real) (s : real -> Prop) : (term411 s x) = (term398 x s).
Proof. exact (eq_refl (term411 s x)). Qed.
Lemma lem5192110 (x : real -> real) (s : real -> Prop) : (term418 s x) = (term419 x s).
Proof. exact (MK_COMB (@lem5192108 s x) (@lem5192109 x s)). Qed.
Lemma lem5192111 (s : real -> Prop) : (term420 s) = (term421 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5192110 x s)). Qed.
Lemma lem5192112 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192113 (s : real -> Prop) : (term406 s) = (term422 s).
Proof. exact (MK_COMB (@lem5192112) (@lem5192111 s)). Qed.
Lemma lem5192114 (s : real -> Prop) : ((term405 s) = (term406 s)) = ((term402 s) = (term422 s)).
Proof. exact (MK_COMB (@lem5192105 s) (@lem5192113 s)). Qed.
Lemma lem5192115 (s : real -> Prop) : (term402 s) = (term422 s).
Proof. exact (EQ_MP (@lem5192114 s) (@lem5192092 s)). Qed.
Lemma lem5192116 (s : real -> Prop) : (term306 s) = (term422 s).
Proof. exact (TRANS (@lem5192088 s) (@lem5192115 s)). Qed.
Lemma lem5192117 : term307 = term423.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5192116 s)). Qed.
Lemma lem5192118 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5192119 : term308 = term424.
Proof. exact (MK_COMB (@lem5192118) (@lem5192117)). Qed.
Lemma lem5192121 {A B : Type'} (P : type1413 A B) : (term309 A B P) = (term310 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5192122 (P : type1017) : (term425 P) = (term426 P).
Proof. exact (@lem5192121 (real -> Prop) (real -> real) P). Qed.
Lemma lem5192123 : term427 = term428.
Proof. exact (@lem5192122 term429). Qed.
Lemma lem5192124 (s : real -> Prop) : (term430 s) = (term421 s).
Proof. exact (eq_refl (term430 s)). Qed.
Lemma lem5192125 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5192126 (s : real -> Prop) (x : real -> real) : (term431 s x) = (term432 s x).
Proof. exact (MK_COMB (@lem5192124 s) (@lem5192125 x)). Qed.
Lemma lem5192127 (x : real -> real) (s : real -> Prop) : (term432 s x) = (term419 x s).
Proof. exact (eq_refl (term432 s x)). Qed.
Lemma lem5192128 (x : real -> real) (s : real -> Prop) : (term431 s x) = (term419 x s).
Proof. exact (TRANS (@lem5192126 s x) (@lem5192127 x s)). Qed.
Lemma lem5192129 (s : real -> Prop) : (term433 s) = (term421 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5192128 x s)). Qed.
Lemma lem5192130 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5192131 (s : real -> Prop) : (term434 s) = (term422 s).
Proof. exact (MK_COMB (@lem5192130) (@lem5192129 s)). Qed.
Lemma lem5192132 : term435 = term423.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5192131 s)). Qed.
Lemma lem5192133 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5192134 : term427 = term424.
Proof. exact (MK_COMB (@lem5192133) (@lem5192132)). Qed.
Lemma lem5192135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192136 : term436 = term437.
Proof. exact (MK_COMB (@lem5192135) (@lem5192134)). Qed.
Lemma lem5192137 (s : real -> Prop) : (term430 s) = (term421 s).
Proof. exact (eq_refl (term430 s)). Qed.
Lemma lem5192138 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5192139 (x : type1021) (s : real -> Prop) : (term438 x s) = (term439 x s).
Proof. exact (MK_COMB (@lem5192137 s) (@lem5192138 x s)). Qed.
Lemma lem5192140 (x : type1021) (s : real -> Prop) : (term439 x s) = (term440 x s).
Proof. exact (eq_refl (term439 x s)). Qed.
Lemma lem5192141 (x : type1021) (s : real -> Prop) : (term438 x s) = (term440 x s).
Proof. exact (TRANS (@lem5192139 x s) (@lem5192140 x s)). Qed.
Lemma lem5192142 (x : type1021) : (term441 x) = (term442 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5192141 x s)). Qed.
Lemma lem5192143 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5192144 (x : type1021) : (term443 x) = (term444 x).
Proof. exact (MK_COMB (@lem5192143) (@lem5192142 x)). Qed.
Lemma lem5192145 : term445 = term446.
Proof. exact (fun_ext (fun x : type1021 => @lem5192144 x)). Qed.
Lemma lem5192146 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5192147 : term428 = term447.
Proof. exact (MK_COMB (@lem5192146) (@lem5192145)). Qed.
Lemma lem5192148 : (term427 = term428) = (term424 = term447).
Proof. exact (MK_COMB (@lem5192136) (@lem5192147)). Qed.
Lemma lem5192149 : term424 = term447.
Proof. exact (EQ_MP (@lem5192148) (@lem5192123)). Qed.
Lemma lem5192151 : term308 = term447.
Proof. exact (TRANS (@lem5192119) (@lem5192149)). Qed.
Lemma lem5192152 : term76 = term447.
Proof. exact (TRANS (@lem5191706) (@lem5192151)). Qed.
Lemma lem5192153 (h1 : term76) : term447.
Proof. exact (EQ_MP (@lem5192152) (@lem5190877 h1)). Qed.
Lemma lem5192154 (x : type1021) (h1 : term444 x) : term444 x.
Proof. exact (h1). Qed.
Lemma lem5192155 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term262 s t c') : term262 s t c'.
Proof. exact (h1). Qed.
Lemma lem5192156 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term259 x' s t c') : term259 x' s t c'.
Proof. exact (h1). Qed.
Lemma lem5192164 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5192172 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5192187 (s : real -> Prop) (x : real) (b : real) : (term130 s x b) = (term130 s x b).
Proof. exact (eq_refl (term130 s x b)). Qed.
Lemma lem5192188 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (fun_ext (fun x : real => @lem5192187 s x b)). Qed.
Lemma lem5192189 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192190 (s : real -> Prop) (b : real) : (term132 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5192189) (@lem5192188 s b)). Qed.
Lemma lem5192191 (s : real -> Prop) (b : real) (h1 : term34 s b) : term132 s b.
Proof. exact (EQ_MP (@lem5192190 s b) (@lem5190952 s b h1)). Qed.
Lemma lem5192206 (t : real -> Prop) (x : real) (c : real) : (term130 t x c) = (term130 t x c).
Proof. exact (eq_refl (term130 t x c)). Qed.
Lemma lem5192207 (t : real -> Prop) (c : real) : (term131 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5192206 t x c)). Qed.
Lemma lem5192208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192209 (t : real -> Prop) (c : real) : (term132 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5192208) (@lem5192207 t c)). Qed.
Lemma lem5192210 (t : real -> Prop) (c : real) (h1 : term34 t c) : term132 t c.
Proof. exact (EQ_MP (@lem5192209 t c) (@lem5191015 t c h1)). Qed.
Lemma lem5192235 (y : real) (x : real) (z : real) : (term270 y x z) = (term270 y x z).
Proof. exact (eq_refl (term270 y x z)). Qed.
Lemma lem5192236 (y : real) (x : real) : (term272 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5192235 y x z)). Qed.
Lemma lem5192237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192238 (y : real) (x : real) : (term273 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5192237) (@lem5192236 y x)). Qed.
Lemma lem5192239 (x : real) : (term274 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5192238 y x)). Qed.
Lemma lem5192240 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192241 (x : real) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5192240) (@lem5192239 x)). Qed.
Lemma lem5192242 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem5192241 x)). Qed.
Lemma lem5192243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192244 : term277 = term277.
Proof. exact (MK_COMB (@lem5192243) (@lem5192242)). Qed.
Lemma lem5192245 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5192244) (@lem5191624 h1)). Qed.
Lemma lem5192278 (x : type1021) (s : real -> Prop) (b : real) : (term448 x s b) = (term448 x s b).
Proof. exact (eq_refl (term448 x s b)). Qed.
Lemma lem5192279 (x : type1021) (s : real -> Prop) : (term449 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5192278 x s b)). Qed.
Lemma lem5192280 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192281 (x : type1021) (s : real -> Prop) : (term450 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5192280) (@lem5192279 x s)). Qed.
Lemma lem5192298 (x : real) (s : real -> Prop) : (term293 x s) = (term293 x s).
Proof. exact (eq_refl (term293 x s)). Qed.
Lemma lem5192299 (s : real -> Prop) : (term295 s) = (term295 s).
Proof. exact (fun_ext (fun x : real => @lem5192298 x s)). Qed.
Lemma lem5192300 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192301 (s : real -> Prop) : (term296 s) = (term296 s).
Proof. exact (MK_COMB (@lem5192300) (@lem5192299 s)). Qed.
Lemma lem5192302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192303 (s : real -> Prop) : (term301 s) = (term301 s).
Proof. exact (MK_COMB (@lem5192302) (@lem5192301 s)). Qed.
Lemma lem5192304 (x : type1021) (s : real -> Prop) : (term451 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5192303 s) (@lem5192281 x s)). Qed.
Lemma lem5192327 (x : type1021) (s : real -> Prop) (b : real) : (term452 x s b) = (term452 x s b).
Proof. exact (eq_refl (term452 x s b)). Qed.
Lemma lem5192328 (x : type1021) (s : real -> Prop) : (term453 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5192327 x s b)). Qed.
Lemma lem5192329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192330 (x : type1021) (s : real -> Prop) : (term454 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5192329) (@lem5192328 x s)). Qed.
Lemma lem5192337 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5192338 (x : type1021) (s : real -> Prop) : (term455 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5192337 s) (@lem5192330 x s)). Qed.
Lemma lem5192339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192340 (x : type1021) (s : real -> Prop) : (term456 x s) = (term456 x s).
Proof. exact (MK_COMB (@lem5192339) (@lem5192338 x s)). Qed.
Lemma lem5192341 (x : type1021) (s : real -> Prop) : (term440 x s) = (term440 x s).
Proof. exact (MK_COMB (@lem5192340 x s) (@lem5192304 x s)). Qed.
Lemma lem5192342 (x : type1021) : (term442 x) = (term442 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5192341 x s)). Qed.
Lemma lem5192343 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5192344 (x : type1021) : (term444 x) = (term444 x).
Proof. exact (MK_COMB (@lem5192343) (@lem5192342 x)). Qed.
Lemma lem5192345 (x : type1021) (h1 : term444 x) : term444 x.
Proof. exact (EQ_MP (@lem5192344 x) (@lem5192154 x h1)). Qed.
Lemma lem5192398 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) : (term228 x' s t c') = (term228 x' s t c').
Proof. exact (eq_refl (term228 x' s t c')). Qed.
Lemma lem5192419 (s : real -> Prop) (t : real -> Prop) (c' : real) : (term152 s t c') = (term152 s t c').
Proof. exact (eq_refl (term152 s t c')). Qed.
Lemma lem5192434 (t : real -> Prop) (x : real) (c' : real) : (term130 t x c') = (term130 t x c').
Proof. exact (eq_refl (term130 t x c')). Qed.
Lemma lem5192435 (t : real -> Prop) (c' : real) : (term131 t c') = (term131 t c').
Proof. exact (fun_ext (fun x : real => @lem5192434 t x c')). Qed.
Lemma lem5192436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192437 (t : real -> Prop) (c' : real) : (term132 t c') = (term132 t c').
Proof. exact (MK_COMB (@lem5192436) (@lem5192435 t c')). Qed.
Lemma lem5192452 (s : real -> Prop) (x : real) (c' : real) : (term130 s x c') = (term130 s x c').
Proof. exact (eq_refl (term130 s x c')). Qed.
Lemma lem5192453 (s : real -> Prop) (c' : real) : (term131 s c') = (term131 s c').
Proof. exact (fun_ext (fun x : real => @lem5192452 s x c')). Qed.
Lemma lem5192454 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192455 (s : real -> Prop) (c' : real) : (term132 s c') = (term132 s c').
Proof. exact (MK_COMB (@lem5192454) (@lem5192453 s c')). Qed.
Lemma lem5192456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192457 (s : real -> Prop) (c' : real) : (term149 s c') = (term149 s c').
Proof. exact (MK_COMB (@lem5192456) (@lem5192455 s c')). Qed.
Lemma lem5192458 (s : real -> Prop) (t : real -> Prop) (c' : real) : (term150 s t c') = (term150 s t c').
Proof. exact (MK_COMB (@lem5192457 s c') (@lem5192437 t c')). Qed.
Lemma lem5192459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192460 (s : real -> Prop) (t : real -> Prop) (c' : real) : (term158 s t c') = (term158 s t c').
Proof. exact (MK_COMB (@lem5192459) (@lem5192458 s t c')). Qed.
Lemma lem5192461 (s : real -> Prop) (t : real -> Prop) (c' : real) : (term160 s t c') = (term160 s t c').
Proof. exact (MK_COMB (@lem5192460 s t c') (@lem5192419 s t c')). Qed.
Lemma lem5192462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192463 (s : real -> Prop) (t : real -> Prop) (c' : real) : (term162 s t c') = (term162 s t c').
Proof. exact (MK_COMB (@lem5192462) (@lem5192461 s t c')). Qed.
Lemma lem5192464 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) : (term259 x' s t c') = (term259 x' s t c').
Proof. exact (MK_COMB (@lem5192463 s t c') (@lem5192398 x' s t c')). Qed.
Lemma lem5192465 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term259 x' s t c') : term259 x' s t c'.
Proof. exact (EQ_MP (@lem5192464 x' s t c') (@lem5192156 x' s t c' h1)). Qed.
Lemma lem5192466 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term160 s t c'.
Proof. exact (h1). Qed.
Lemma lem5192467 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term228 x' s t c'.
Proof. exact (h1). Qed.
Lemma lem5192468 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term152 s t c'.
Proof. exact (proj2 (@lem5192466 s t c' h1)). Qed.
Lemma lem5192469 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term150 s t c'.
Proof. exact (proj1 (@lem5192466 s t c' h1)). Qed.
Lemma lem5192470 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term132 t c'.
Proof. exact (proj2 (@lem5192469 s t c' h1)). Qed.
Lemma lem5192471 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term132 s c'.
Proof. exact (proj1 (@lem5192469 s t c' h1)). Qed.
Lemma lem5192474 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term62 s t c'.
Proof. exact (proj2 (@lem5192467 x' s t c' h1)). Qed.
Lemma lem5192475 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term207 s t x' c'.
Proof. exact (proj1 (@lem5192467 x' s t c' h1)). Qed.
Lemma lem5192478 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : term134 s x' c'.
Proof. exact (h1). Qed.
Lemma lem5192479 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : term134 t x' c'.
Proof. exact (h1). Qed.
Lemma lem5192487 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5192544 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5192545 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5192544 real P Q). Qed.
Lemma lem5192546 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5192545 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5192547 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5192548 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5192547 x s b)). Qed.
Lemma lem5192549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192550 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5192549) (@lem5192548 x s)). Qed.
Lemma lem5192551 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5192552 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5192551 s) (@lem5192550 x s)). Qed.
Lemma lem5192553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192554 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5192553) (@lem5192552 x s)). Qed.
Lemma lem5192555 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5192556 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5192557 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5192556 s) (@lem5192555 x s b)). Qed.
Lemma lem5192558 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5192557 x s b)). Qed.
Lemma lem5192559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192560 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5192559) (@lem5192558 x s)). Qed.
Lemma lem5192561 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5192554 x s) (@lem5192560 x s)). Qed.
Lemma lem5192562 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5192561 x s) (@lem5192546 x s)). Qed.
Lemma lem5192563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192564 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5192563) (@lem5192562 x s)). Qed.
Lemma lem5192566 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5192567 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5192566 real P Q). Qed.
Lemma lem5192568 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5192567 (term295 s) (term449 x s)). Qed.
Lemma lem5192569 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5192570 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5192569 b s)). Qed.
Lemma lem5192571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192572 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5192571) (@lem5192570 s)). Qed.
Lemma lem5192573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192574 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5192573) (@lem5192572 s)). Qed.
Lemma lem5192575 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5192576 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5192575 x s b)). Qed.
Lemma lem5192577 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192578 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5192577) (@lem5192576 x s)). Qed.
Lemma lem5192579 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5192574 s) (@lem5192578 x s)). Qed.
Lemma lem5192580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192581 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5192580) (@lem5192579 x s)). Qed.
Lemma lem5192582 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5192583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192584 (b : real) (s : real -> Prop) : (term489 s b) = (term490 b s).
Proof. exact (MK_COMB (@lem5192583) (@lem5192582 b s)). Qed.
Lemma lem5192585 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5192586 (x : type1021) (s : real -> Prop) (b : real) : (term491 x s b) = (term492 x s b).
Proof. exact (MK_COMB (@lem5192584 b s) (@lem5192585 x s b)). Qed.
Lemma lem5192587 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5192586 x s b)). Qed.
Lemma lem5192588 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192589 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5192588) (@lem5192587 x s)). Qed.
Lemma lem5192590 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5192581 x s) (@lem5192589 x s)). Qed.
Lemma lem5192591 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5192590 x s) (@lem5192568 x s)). Qed.
Lemma lem5192594 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5192595 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5192596 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5192597 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5192596 x s) (@lem5192595 x s)). Qed.
Lemma lem5192598 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5192599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192600 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5192599) (@lem5192598 x s)). Qed.
Lemma lem5192601 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5192602 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5192600 x s) (@lem5192601 x s)). Qed.
Lemma lem5192603 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5192597 x s) (@lem5192602 x s)). Qed.
Lemma lem5192604 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5192603 x s) (@lem5192594 x s)). Qed.
Lemma lem5192605 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5192604 x s) (@lem5192591 x s)). Qed.
Lemma lem5192606 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5192564 x s) (@lem5192605 x s)). Qed.
Lemma lem5192608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5192609 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5192608 real P Q). Qed.
Lemma lem5192610 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5192609 (term471 x s) (term495 x s)). Qed.
Lemma lem5192611 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5192612 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5192611 x s b)). Qed.
Lemma lem5192613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192614 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5192613) (@lem5192612 x s)). Qed.
Lemma lem5192615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192616 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5192615) (@lem5192614 x s)). Qed.
Lemma lem5192617 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5192618 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5192616 x s) (@lem5192617 x s)). Qed.
Lemma lem5192619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192620 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5192619) (@lem5192618 x s)). Qed.
Lemma lem5192621 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5192622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192623 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5192622) (@lem5192621 x s b)). Qed.
Lemma lem5192624 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5192625 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5192623 x s b) (@lem5192624 x s)). Qed.
Lemma lem5192626 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5192625 b x s)). Qed.
Lemma lem5192627 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192628 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5192627) (@lem5192626 x s)). Qed.
Lemma lem5192629 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5192620 x s) (@lem5192628 x s)). Qed.
Lemma lem5192630 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5192629 x s) (@lem5192610 x s)). Qed.
Lemma lem5192632 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5192633 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5192632 real P Q). Qed.
Lemma lem5192634 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5192633 (term469 x s b) (term494 x s)). Qed.
Lemma lem5192635 (x : type1021) (s : real -> Prop) (b : real) : (term521 x s b) = (term492 x s b).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5192636 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5192635 x s b)). Qed.
Lemma lem5192637 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192638 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5192637) (@lem5192636 x s)). Qed.
Lemma lem5192639 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5192640 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5192639 x s b) (@lem5192638 x s)). Qed.
Lemma lem5192641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192642 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5192641) (@lem5192640 b x s)). Qed.
Lemma lem5192643 (x : type1021) (s : real -> Prop) (b' : real) : (term521 x s b') = (term492 x s b').
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5192644 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5192645 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term526 b x s b') = (term527 b x s b').
Proof. exact (MK_COMB (@lem5192644 x s b) (@lem5192643 x s b')). Qed.
Lemma lem5192646 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5192645 b x s b')). Qed.
Lemma lem5192647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192648 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5192647) (@lem5192646 b x s)). Qed.
Lemma lem5192649 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5192642 b x s) (@lem5192648 b x s)). Qed.
Lemma lem5192650 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5192649 b x s) (@lem5192634 b x s)). Qed.
Lemma lem5192651 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5192650 b x s)). Qed.
Lemma lem5192652 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192653 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5192652) (@lem5192651 x s)). Qed.
Lemma lem5192654 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5192630 x s) (@lem5192653 x s)). Qed.
Lemma lem5192655 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5192606 x s) (@lem5192654 x s)). Qed.
Lemma lem5192656 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5192655 x s)). Qed.
Lemma lem5192657 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5192658 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5192657) (@lem5192656 x)). Qed.
Lemma lem5192675 (x : type1021) (s : real -> Prop) (b' : real) : (term448 x s b') = (term535 x s b').
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 s b')). Qed.
Lemma lem5192684 (b' : real) (s : real -> Prop) : (term490 b' s) = (term490 b' s).
Proof. exact (eq_refl (term490 b' s)). Qed.
Lemma lem5192685 (x : type1021) (s : real -> Prop) (b' : real) : (term492 x s b') = (term538 x s b').
Proof. exact (MK_COMB (@lem5192684 b' s) (@lem5192675 x s b')). Qed.
Lemma lem5192702 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5192703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192704 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5192703) (@lem5192702 x s b)). Qed.
Lemma lem5192705 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term541 b x s b').
Proof. exact (MK_COMB (@lem5192704 x s b) (@lem5192685 x s b')). Qed.
Lemma lem5192706 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term542 b x s b').
Proof. exact (@lem19490 (term293 b' s) (term539 x s b) (term535 x s b')). Qed.
Lemma lem5192707 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term544 b x s b').
Proof. exact (@lem19490 (term545 x s b') (term539 x s b) (term546 x s b')). Qed.
Lemma lem5192714 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term547 b x s b') = (term548 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x s b')). Qed.
Lemma lem5192721 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term551 b x s b') = (term552 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x s b')). Qed.
Lemma lem5192722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192723 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term553 b x s b') = (term554 b x s b').
Proof. exact (MK_COMB (@lem5192722) (@lem5192721 b x s b')). Qed.
Lemma lem5192724 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term544 b x s b') = (term555 b x s b').
Proof. exact (MK_COMB (@lem5192723 b x s b') (@lem5192714 b x s b')). Qed.
Lemma lem5192725 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term555 b x s b').
Proof. exact (TRANS (@lem5192707 b x s b') (@lem5192724 b x s b')). Qed.
Lemma lem5192732 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term556 x b b' s) = (term557 x b b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 b' s)). Qed.
Lemma lem5192733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192734 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term558 x b b' s) = (term559 x b b' s).
Proof. exact (MK_COMB (@lem5192733) (@lem5192732 x b b' s)). Qed.
Lemma lem5192735 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term560 b x s b').
Proof. exact (MK_COMB (@lem5192734 x b b' s) (@lem5192725 b x s b')). Qed.
Lemma lem5192736 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5192706 b x s b') (@lem5192735 b x s b')). Qed.
Lemma lem5192737 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5192705 b x s b') (@lem5192736 b x s b')). Qed.
Lemma lem5192738 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5192737 b x s b')). Qed.
Lemma lem5192739 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192740 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5192739) (@lem5192738 b x s)). Qed.
Lemma lem5192741 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5192740 b x s)). Qed.
Lemma lem5192742 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192743 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5192742) (@lem5192741 x s)). Qed.
Lemma lem5192744 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5192743 x s)). Qed.
Lemma lem5192745 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5192746 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5192745) (@lem5192744 x)). Qed.
Lemma lem5192747 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5192658 x) (@lem5192746 x)). Qed.
Lemma lem5192748 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5192747 x) (@lem5192345 x h1)). Qed.
Lemma lem5192756 (s : real -> Prop) (x : real) (c' : real) : (term130 s x c') = (term130 s x c').
Proof. exact (eq_refl (term130 s x c')). Qed.
Lemma lem5192757 (s : real -> Prop) (c' : real) : (term131 s c') = (term131 s c').
Proof. exact (fun_ext (fun x : real => @lem5192756 s x c')). Qed.
Lemma lem5192758 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192760 (s : real -> Prop) (c' : real) : (term132 s c') = (term132 s c').
Proof. exact (MK_COMB (@lem5192758) (@lem5192757 s c')). Qed.
Lemma lem5192761 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term132 s c'.
Proof. exact (EQ_MP (@lem5192760 s c') (@lem5192471 s t c' h1)). Qed.
Lemma lem5192778 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (h1). Qed.
Lemma lem5192786 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5192839 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5192840 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5192839 real P Q). Qed.
Lemma lem5192841 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5192840 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5192842 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5192843 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5192842 x s b)). Qed.
Lemma lem5192844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192845 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5192844) (@lem5192843 x s)). Qed.
Lemma lem5192846 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5192847 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5192846 s) (@lem5192845 x s)). Qed.
Lemma lem5192848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192849 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5192848) (@lem5192847 x s)). Qed.
Lemma lem5192850 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5192851 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5192852 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5192851 s) (@lem5192850 x s b)). Qed.
Lemma lem5192853 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5192852 x s b)). Qed.
Lemma lem5192854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192855 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5192854) (@lem5192853 x s)). Qed.
Lemma lem5192856 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5192849 x s) (@lem5192855 x s)). Qed.
Lemma lem5192857 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5192856 x s) (@lem5192841 x s)). Qed.
Lemma lem5192858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192859 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5192858) (@lem5192857 x s)). Qed.
Lemma lem5192861 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5192862 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5192861 real P Q). Qed.
Lemma lem5192863 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5192862 (term295 s) (term449 x s)). Qed.
Lemma lem5192864 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5192865 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5192864 b s)). Qed.
Lemma lem5192866 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192867 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5192866) (@lem5192865 s)). Qed.
Lemma lem5192868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192869 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5192868) (@lem5192867 s)). Qed.
Lemma lem5192870 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5192871 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5192870 x s b)). Qed.
Lemma lem5192872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192873 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5192872) (@lem5192871 x s)). Qed.
Lemma lem5192874 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5192869 s) (@lem5192873 x s)). Qed.
Lemma lem5192875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192876 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5192875) (@lem5192874 x s)). Qed.
Lemma lem5192877 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5192878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5192879 (b : real) (s : real -> Prop) : (term489 s b) = (term490 b s).
Proof. exact (MK_COMB (@lem5192878) (@lem5192877 b s)). Qed.
Lemma lem5192880 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5192881 (x : type1021) (s : real -> Prop) (b : real) : (term491 x s b) = (term492 x s b).
Proof. exact (MK_COMB (@lem5192879 b s) (@lem5192880 x s b)). Qed.
Lemma lem5192882 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5192881 x s b)). Qed.
Lemma lem5192883 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192884 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5192883) (@lem5192882 x s)). Qed.
Lemma lem5192885 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5192876 x s) (@lem5192884 x s)). Qed.
Lemma lem5192886 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5192885 x s) (@lem5192863 x s)). Qed.
Lemma lem5192889 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5192890 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5192891 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5192892 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5192891 x s) (@lem5192890 x s)). Qed.
Lemma lem5192893 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5192894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192895 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5192894) (@lem5192893 x s)). Qed.
Lemma lem5192896 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5192897 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5192895 x s) (@lem5192896 x s)). Qed.
Lemma lem5192898 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5192892 x s) (@lem5192897 x s)). Qed.
Lemma lem5192899 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5192898 x s) (@lem5192889 x s)). Qed.
Lemma lem5192900 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5192899 x s) (@lem5192886 x s)). Qed.
Lemma lem5192901 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5192859 x s) (@lem5192900 x s)). Qed.
Lemma lem5192903 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5192904 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5192903 real P Q). Qed.
Lemma lem5192905 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5192904 (term471 x s) (term495 x s)). Qed.
Lemma lem5192906 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5192907 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5192906 x s b)). Qed.
Lemma lem5192908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192909 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5192908) (@lem5192907 x s)). Qed.
Lemma lem5192910 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192911 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5192910) (@lem5192909 x s)). Qed.
Lemma lem5192912 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5192913 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5192911 x s) (@lem5192912 x s)). Qed.
Lemma lem5192914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192915 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5192914) (@lem5192913 x s)). Qed.
Lemma lem5192916 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5192917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192918 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5192917) (@lem5192916 x s b)). Qed.
Lemma lem5192919 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5192920 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5192918 x s b) (@lem5192919 x s)). Qed.
Lemma lem5192921 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5192920 b x s)). Qed.
Lemma lem5192922 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192923 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5192922) (@lem5192921 x s)). Qed.
Lemma lem5192924 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5192915 x s) (@lem5192923 x s)). Qed.
Lemma lem5192925 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5192924 x s) (@lem5192905 x s)). Qed.
Lemma lem5192927 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5192928 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5192927 real P Q). Qed.
Lemma lem5192929 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5192928 (term469 x s b) (term494 x s)). Qed.
Lemma lem5192930 (x : type1021) (s : real -> Prop) (b : real) : (term521 x s b) = (term492 x s b).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5192931 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5192930 x s b)). Qed.
Lemma lem5192932 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192933 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5192932) (@lem5192931 x s)). Qed.
Lemma lem5192934 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5192935 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5192934 x s b) (@lem5192933 x s)). Qed.
Lemma lem5192936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5192937 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5192936) (@lem5192935 b x s)). Qed.
Lemma lem5192938 (x : type1021) (s : real -> Prop) (b' : real) : (term521 x s b') = (term492 x s b').
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5192939 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5192940 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term526 b x s b') = (term527 b x s b').
Proof. exact (MK_COMB (@lem5192939 x s b) (@lem5192938 x s b')). Qed.
Lemma lem5192941 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5192940 b x s b')). Qed.
Lemma lem5192942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192943 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5192942) (@lem5192941 b x s)). Qed.
Lemma lem5192944 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5192937 b x s) (@lem5192943 b x s)). Qed.
Lemma lem5192945 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5192944 b x s) (@lem5192929 b x s)). Qed.
Lemma lem5192946 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5192945 b x s)). Qed.
Lemma lem5192947 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5192948 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5192947) (@lem5192946 x s)). Qed.
Lemma lem5192949 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5192925 x s) (@lem5192948 x s)). Qed.
Lemma lem5192950 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5192901 x s) (@lem5192949 x s)). Qed.
Lemma lem5192951 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5192950 x s)). Qed.
Lemma lem5192952 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5192953 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5192952) (@lem5192951 x)). Qed.
Lemma lem5192970 (x : type1021) (s : real -> Prop) (b' : real) : (term448 x s b') = (term535 x s b').
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 s b')). Qed.
Lemma lem5192979 (b' : real) (s : real -> Prop) : (term490 b' s) = (term490 b' s).
Proof. exact (eq_refl (term490 b' s)). Qed.
Lemma lem5192980 (x : type1021) (s : real -> Prop) (b' : real) : (term492 x s b') = (term538 x s b').
Proof. exact (MK_COMB (@lem5192979 b' s) (@lem5192970 x s b')). Qed.
Lemma lem5192997 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5192998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5192999 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5192998) (@lem5192997 x s b)). Qed.
Lemma lem5193000 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term541 b x s b').
Proof. exact (MK_COMB (@lem5192999 x s b) (@lem5192980 x s b')). Qed.
Lemma lem5193001 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term542 b x s b').
Proof. exact (@lem19490 (term293 b' s) (term539 x s b) (term535 x s b')). Qed.
Lemma lem5193002 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term544 b x s b').
Proof. exact (@lem19490 (term545 x s b') (term539 x s b) (term546 x s b')). Qed.
Lemma lem5193009 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term547 b x s b') = (term548 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x s b')). Qed.
Lemma lem5193016 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term551 b x s b') = (term552 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x s b')). Qed.
Lemma lem5193017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193018 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term553 b x s b') = (term554 b x s b').
Proof. exact (MK_COMB (@lem5193017) (@lem5193016 b x s b')). Qed.
Lemma lem5193019 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term544 b x s b') = (term555 b x s b').
Proof. exact (MK_COMB (@lem5193018 b x s b') (@lem5193009 b x s b')). Qed.
Lemma lem5193020 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term555 b x s b').
Proof. exact (TRANS (@lem5193002 b x s b') (@lem5193019 b x s b')). Qed.
Lemma lem5193027 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term556 x b b' s) = (term557 x b b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 b' s)). Qed.
Lemma lem5193028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193029 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term558 x b b' s) = (term559 x b b' s).
Proof. exact (MK_COMB (@lem5193028) (@lem5193027 x b b' s)). Qed.
Lemma lem5193030 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term560 b x s b').
Proof. exact (MK_COMB (@lem5193029 x b b' s) (@lem5193020 b x s b')). Qed.
Lemma lem5193031 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5193001 b x s b') (@lem5193030 b x s b')). Qed.
Lemma lem5193032 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5193000 b x s b') (@lem5193031 b x s b')). Qed.
Lemma lem5193033 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5193032 b x s b')). Qed.
Lemma lem5193034 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193035 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5193034) (@lem5193033 b x s)). Qed.
Lemma lem5193036 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5193035 b x s)). Qed.
Lemma lem5193037 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193038 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5193037) (@lem5193036 x s)). Qed.
Lemma lem5193039 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5193038 x s)). Qed.
Lemma lem5193040 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5193041 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5193040) (@lem5193039 x)). Qed.
Lemma lem5193042 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5192953 x) (@lem5193041 x)). Qed.
Lemma lem5193043 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5193042 x) (@lem5192345 x h1)). Qed.
Lemma lem5193064 (t : real -> Prop) (x : real) (c' : real) : (term130 t x c') = (term130 t x c').
Proof. exact (eq_refl (term130 t x c')). Qed.
Lemma lem5193065 (t : real -> Prop) (c' : real) : (term131 t c') = (term131 t c').
Proof. exact (fun_ext (fun x : real => @lem5193064 t x c')). Qed.
Lemma lem5193066 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193068 (t : real -> Prop) (c' : real) : (term132 t c') = (term132 t c').
Proof. exact (MK_COMB (@lem5193066) (@lem5193065 t c')). Qed.
Lemma lem5193069 (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term132 t c'.
Proof. exact (EQ_MP (@lem5193068 t c') (@lem5192470 s t c' h1)). Qed.
Lemma lem5193073 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (h1). Qed.
Lemma lem5193077 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5193089 (s : real -> Prop) (x : real) (b : real) : (term130 s x b) = (term130 s x b).
Proof. exact (eq_refl (term130 s x b)). Qed.
Lemma lem5193090 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (fun_ext (fun x : real => @lem5193089 s x b)). Qed.
Lemma lem5193091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193093 (s : real -> Prop) (b : real) : (term132 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5193091) (@lem5193090 s b)). Qed.
Lemma lem5193094 (s : real -> Prop) (b : real) (h1 : term34 s b) : term132 s b.
Proof. exact (EQ_MP (@lem5193093 s b) (@lem5192191 s b h1)). Qed.
Lemma lem5193121 (y : real) (x : real) (z : real) : (term270 y x z) = (term270 y x z).
Proof. exact (eq_refl (term270 y x z)). Qed.
Lemma lem5193122 (y : real) (x : real) : (term272 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5193121 y x z)). Qed.
Lemma lem5193123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193124 (y : real) (x : real) : (term273 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5193123) (@lem5193122 y x)). Qed.
Lemma lem5193125 (x : real) : (term274 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5193124 y x)). Qed.
Lemma lem5193126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193127 (x : real) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5193126) (@lem5193125 x)). Qed.
Lemma lem5193128 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem5193127 x)). Qed.
Lemma lem5193129 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193131 : term277 = term277.
Proof. exact (MK_COMB (@lem5193129) (@lem5193128)). Qed.
Lemma lem5193132 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5193131) (@lem5192245 h1)). Qed.
Lemma lem5193134 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5193135 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5193134 real P Q). Qed.
Lemma lem5193136 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5193135 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5193137 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5193138 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5193137 x s b)). Qed.
Lemma lem5193139 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193140 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5193139) (@lem5193138 x s)). Qed.
Lemma lem5193141 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5193142 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5193141 s) (@lem5193140 x s)). Qed.
Lemma lem5193143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193144 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5193143) (@lem5193142 x s)). Qed.
Lemma lem5193145 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5193146 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5193147 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5193146 s) (@lem5193145 x s b)). Qed.
Lemma lem5193148 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5193147 x s b)). Qed.
Lemma lem5193149 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193150 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5193149) (@lem5193148 x s)). Qed.
Lemma lem5193151 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5193144 x s) (@lem5193150 x s)). Qed.
Lemma lem5193152 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5193151 x s) (@lem5193136 x s)). Qed.
Lemma lem5193153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193154 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5193153) (@lem5193152 x s)). Qed.
Lemma lem5193156 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5193157 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5193156 real P Q). Qed.
Lemma lem5193158 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5193157 (term295 s) (term449 x s)). Qed.
Lemma lem5193159 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5193160 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5193159 b s)). Qed.
Lemma lem5193161 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193162 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5193161) (@lem5193160 s)). Qed.
Lemma lem5193163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193164 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5193163) (@lem5193162 s)). Qed.
Lemma lem5193165 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5193166 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5193165 x s b)). Qed.
Lemma lem5193167 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193168 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5193167) (@lem5193166 x s)). Qed.
Lemma lem5193169 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5193164 s) (@lem5193168 x s)). Qed.
Lemma lem5193170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193171 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5193170) (@lem5193169 x s)). Qed.
Lemma lem5193172 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5193173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193174 (b : real) (s : real -> Prop) : (term489 s b) = (term490 b s).
Proof. exact (MK_COMB (@lem5193173) (@lem5193172 b s)). Qed.
Lemma lem5193175 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5193176 (x : type1021) (s : real -> Prop) (b : real) : (term491 x s b) = (term492 x s b).
Proof. exact (MK_COMB (@lem5193174 b s) (@lem5193175 x s b)). Qed.
Lemma lem5193177 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5193176 x s b)). Qed.
Lemma lem5193178 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193179 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5193178) (@lem5193177 x s)). Qed.
Lemma lem5193180 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5193171 x s) (@lem5193179 x s)). Qed.
Lemma lem5193181 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5193180 x s) (@lem5193158 x s)). Qed.
Lemma lem5193184 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5193185 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5193186 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5193187 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5193186 x s) (@lem5193185 x s)). Qed.
Lemma lem5193188 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5193189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193190 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5193189) (@lem5193188 x s)). Qed.
Lemma lem5193191 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5193192 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5193190 x s) (@lem5193191 x s)). Qed.
Lemma lem5193193 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5193187 x s) (@lem5193192 x s)). Qed.
Lemma lem5193194 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5193193 x s) (@lem5193184 x s)). Qed.
Lemma lem5193195 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5193194 x s) (@lem5193181 x s)). Qed.
Lemma lem5193196 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5193154 x s) (@lem5193195 x s)). Qed.
Lemma lem5193198 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5193199 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5193198 real P Q). Qed.
Lemma lem5193200 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5193199 (term471 x s) (term495 x s)). Qed.
Lemma lem5193201 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5193202 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5193201 x s b)). Qed.
Lemma lem5193203 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193204 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5193203) (@lem5193202 x s)). Qed.
Lemma lem5193205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193206 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5193205) (@lem5193204 x s)). Qed.
Lemma lem5193207 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5193208 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5193206 x s) (@lem5193207 x s)). Qed.
Lemma lem5193209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193210 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5193209) (@lem5193208 x s)). Qed.
Lemma lem5193211 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5193212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193213 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5193212) (@lem5193211 x s b)). Qed.
Lemma lem5193214 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5193215 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5193213 x s b) (@lem5193214 x s)). Qed.
Lemma lem5193216 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5193215 b x s)). Qed.
Lemma lem5193217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193218 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5193217) (@lem5193216 x s)). Qed.
Lemma lem5193219 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5193210 x s) (@lem5193218 x s)). Qed.
Lemma lem5193220 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5193219 x s) (@lem5193200 x s)). Qed.
Lemma lem5193222 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5193223 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5193222 real P Q). Qed.
Lemma lem5193224 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5193223 (term469 x s b) (term494 x s)). Qed.
Lemma lem5193225 (x : type1021) (s : real -> Prop) (b : real) : (term521 x s b) = (term492 x s b).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5193226 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5193225 x s b)). Qed.
Lemma lem5193227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193228 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5193227) (@lem5193226 x s)). Qed.
Lemma lem5193229 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5193230 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5193229 x s b) (@lem5193228 x s)). Qed.
Lemma lem5193231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193232 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5193231) (@lem5193230 b x s)). Qed.
Lemma lem5193233 (x : type1021) (s : real -> Prop) (b' : real) : (term521 x s b') = (term492 x s b').
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5193234 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5193235 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term526 b x s b') = (term527 b x s b').
Proof. exact (MK_COMB (@lem5193234 x s b) (@lem5193233 x s b')). Qed.
Lemma lem5193236 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5193235 b x s b')). Qed.
Lemma lem5193237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193238 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5193237) (@lem5193236 b x s)). Qed.
Lemma lem5193239 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5193232 b x s) (@lem5193238 b x s)). Qed.
Lemma lem5193240 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5193239 b x s) (@lem5193224 b x s)). Qed.
Lemma lem5193241 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5193240 b x s)). Qed.
Lemma lem5193242 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193243 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5193242) (@lem5193241 x s)). Qed.
Lemma lem5193244 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5193220 x s) (@lem5193243 x s)). Qed.
Lemma lem5193245 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5193196 x s) (@lem5193244 x s)). Qed.
Lemma lem5193246 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5193245 x s)). Qed.
Lemma lem5193247 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5193248 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5193247) (@lem5193246 x)). Qed.
Lemma lem5193265 (x : type1021) (s : real -> Prop) (b' : real) : (term448 x s b') = (term535 x s b').
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 s b')). Qed.
Lemma lem5193274 (b' : real) (s : real -> Prop) : (term490 b' s) = (term490 b' s).
Proof. exact (eq_refl (term490 b' s)). Qed.
Lemma lem5193275 (x : type1021) (s : real -> Prop) (b' : real) : (term492 x s b') = (term538 x s b').
Proof. exact (MK_COMB (@lem5193274 b' s) (@lem5193265 x s b')). Qed.
Lemma lem5193292 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5193293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193294 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5193293) (@lem5193292 x s b)). Qed.
Lemma lem5193295 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term541 b x s b').
Proof. exact (MK_COMB (@lem5193294 x s b) (@lem5193275 x s b')). Qed.
Lemma lem5193296 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term542 b x s b').
Proof. exact (@lem19490 (term293 b' s) (term539 x s b) (term535 x s b')). Qed.
Lemma lem5193297 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term544 b x s b').
Proof. exact (@lem19490 (term545 x s b') (term539 x s b) (term546 x s b')). Qed.
Lemma lem5193304 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term547 b x s b') = (term548 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x s b')). Qed.
Lemma lem5193311 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term551 b x s b') = (term552 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x s b')). Qed.
Lemma lem5193312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193313 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term553 b x s b') = (term554 b x s b').
Proof. exact (MK_COMB (@lem5193312) (@lem5193311 b x s b')). Qed.
Lemma lem5193314 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term544 b x s b') = (term555 b x s b').
Proof. exact (MK_COMB (@lem5193313 b x s b') (@lem5193304 b x s b')). Qed.
Lemma lem5193315 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term555 b x s b').
Proof. exact (TRANS (@lem5193297 b x s b') (@lem5193314 b x s b')). Qed.
Lemma lem5193322 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term556 x b b' s) = (term557 x b b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 b' s)). Qed.
Lemma lem5193323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193324 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term558 x b b' s) = (term559 x b b' s).
Proof. exact (MK_COMB (@lem5193323) (@lem5193322 x b b' s)). Qed.
Lemma lem5193325 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term560 b x s b').
Proof. exact (MK_COMB (@lem5193324 x b b' s) (@lem5193315 b x s b')). Qed.
Lemma lem5193326 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5193296 b x s b') (@lem5193325 b x s b')). Qed.
Lemma lem5193327 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5193295 b x s b') (@lem5193326 b x s b')). Qed.
Lemma lem5193328 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5193327 b x s b')). Qed.
Lemma lem5193329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193330 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5193329) (@lem5193328 b x s)). Qed.
Lemma lem5193331 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5193330 b x s)). Qed.
Lemma lem5193332 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193333 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5193332) (@lem5193331 x s)). Qed.
Lemma lem5193334 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5193333 x s)). Qed.
Lemma lem5193335 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5193336 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5193335) (@lem5193334 x)). Qed.
Lemma lem5193337 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5193248 x) (@lem5193336 x)). Qed.
Lemma lem5193338 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5193337 x) (@lem5192345 x h1)). Qed.
Lemma lem5193362 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5193383 (t : real -> Prop) (x : real) (c : real) : (term130 t x c) = (term130 t x c).
Proof. exact (eq_refl (term130 t x c)). Qed.
Lemma lem5193384 (t : real -> Prop) (c : real) : (term131 t c) = (term131 t c).
Proof. exact (fun_ext (fun x : real => @lem5193383 t x c)). Qed.
Lemma lem5193385 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193387 (t : real -> Prop) (c : real) : (term132 t c) = (term132 t c).
Proof. exact (MK_COMB (@lem5193385) (@lem5193384 t c)). Qed.
Lemma lem5193388 (t : real -> Prop) (c : real) (h1 : term34 t c) : term132 t c.
Proof. exact (EQ_MP (@lem5193387 t c) (@lem5192210 t c h1)). Qed.
Lemma lem5193402 (y : real) (x : real) (z : real) : (term270 y x z) = (term270 y x z).
Proof. exact (eq_refl (term270 y x z)). Qed.
Lemma lem5193403 (y : real) (x : real) : (term272 y x) = (term272 y x).
Proof. exact (fun_ext (fun z : real => @lem5193402 y x z)). Qed.
Lemma lem5193404 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193405 (y : real) (x : real) : (term273 y x) = (term273 y x).
Proof. exact (MK_COMB (@lem5193404) (@lem5193403 y x)). Qed.
Lemma lem5193406 (x : real) : (term274 x) = (term274 x).
Proof. exact (fun_ext (fun y : real => @lem5193405 y x)). Qed.
Lemma lem5193407 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193408 (x : real) : (term275 x) = (term275 x).
Proof. exact (MK_COMB (@lem5193407) (@lem5193406 x)). Qed.
Lemma lem5193409 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem5193408 x)). Qed.
Lemma lem5193410 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193412 : term277 = term277.
Proof. exact (MK_COMB (@lem5193410) (@lem5193409)). Qed.
Lemma lem5193413 (h1 : term129) : term277.
Proof. exact (EQ_MP (@lem5193412) (@lem5192245 h1)). Qed.
Lemma lem5193415 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5193416 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5193415 real P Q). Qed.
Lemma lem5193417 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5193416 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5193418 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5193419 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5193418 x s b)). Qed.
Lemma lem5193420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193421 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5193420) (@lem5193419 x s)). Qed.
Lemma lem5193422 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5193423 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5193422 s) (@lem5193421 x s)). Qed.
Lemma lem5193424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193425 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5193424) (@lem5193423 x s)). Qed.
Lemma lem5193426 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5193427 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (eq_refl (term289 s)). Qed.
Lemma lem5193428 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5193427 s) (@lem5193426 x s b)). Qed.
Lemma lem5193429 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5193428 x s b)). Qed.
Lemma lem5193430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193431 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5193430) (@lem5193429 x s)). Qed.
Lemma lem5193432 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5193425 x s) (@lem5193431 x s)). Qed.
Lemma lem5193433 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5193432 x s) (@lem5193417 x s)). Qed.
Lemma lem5193434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193435 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5193434) (@lem5193433 x s)). Qed.
Lemma lem5193437 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term474 A P Q) = (term475 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5193438 (P : real -> Prop) (Q : real -> Prop) : (term476 P Q) = (term477 P Q).
Proof. exact (@lem5193437 real P Q). Qed.
Lemma lem5193439 (x : type1021) (s : real -> Prop) : (term478 x s) = (term479 x s).
Proof. exact (@lem5193438 (term295 s) (term449 x s)). Qed.
Lemma lem5193440 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5193441 (s : real -> Prop) : (term481 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5193440 b s)). Qed.
Lemma lem5193442 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193443 (s : real -> Prop) : (term482 s) = (term296 s).
Proof. exact (MK_COMB (@lem5193442) (@lem5193441 s)). Qed.
Lemma lem5193444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193445 (s : real -> Prop) : (term483 s) = (term301 s).
Proof. exact (MK_COMB (@lem5193444) (@lem5193443 s)). Qed.
Lemma lem5193446 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5193447 (x : type1021) (s : real -> Prop) : (term485 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5193446 x s b)). Qed.
Lemma lem5193448 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193449 (x : type1021) (s : real -> Prop) : (term486 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5193448) (@lem5193447 x s)). Qed.
Lemma lem5193450 (x : type1021) (s : real -> Prop) : (term478 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5193445 s) (@lem5193449 x s)). Qed.
Lemma lem5193451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193452 (x : type1021) (s : real -> Prop) : (term487 x s) = (term488 x s).
Proof. exact (MK_COMB (@lem5193451) (@lem5193450 x s)). Qed.
Lemma lem5193453 (b : real) (s : real -> Prop) : (term480 s b) = (term293 b s).
Proof. exact (eq_refl (term480 s b)). Qed.
Lemma lem5193454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193455 (b : real) (s : real -> Prop) : (term489 s b) = (term490 b s).
Proof. exact (MK_COMB (@lem5193454) (@lem5193453 b s)). Qed.
Lemma lem5193456 (x : type1021) (s : real -> Prop) (b : real) : (term484 x s b) = (term448 x s b).
Proof. exact (eq_refl (term484 x s b)). Qed.
Lemma lem5193457 (x : type1021) (s : real -> Prop) (b : real) : (term491 x s b) = (term492 x s b).
Proof. exact (MK_COMB (@lem5193455 b s) (@lem5193456 x s b)). Qed.
Lemma lem5193458 (x : type1021) (s : real -> Prop) : (term493 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5193457 x s b)). Qed.
Lemma lem5193459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193460 (x : type1021) (s : real -> Prop) : (term479 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5193459) (@lem5193458 x s)). Qed.
Lemma lem5193461 (x : type1021) (s : real -> Prop) : ((term478 x s) = (term479 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (MK_COMB (@lem5193452 x s) (@lem5193460 x s)). Qed.
Lemma lem5193462 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5193461 x s) (@lem5193439 x s)). Qed.
Lemma lem5193465 (x : type1021) (s : real -> Prop) : (term496 x s) = (term496 x s).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5193466 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5193467 (x : type1021) (s : real -> Prop) : (term497 x s) = (term497 x s).
Proof. exact (eq_refl (term497 x s)). Qed.
Lemma lem5193468 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = ((term496 x s) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5193467 x s) (@lem5193466 x s)). Qed.
Lemma lem5193469 (x : type1021) (s : real -> Prop) : (term496 x s) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl (term496 x s)). Qed.
Lemma lem5193470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193471 (x : type1021) (s : real -> Prop) : (term497 x s) = (term498 x s).
Proof. exact (MK_COMB (@lem5193470) (@lem5193469 x s)). Qed.
Lemma lem5193472 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (eq_refl ((term451 x s) = (term495 x s))). Qed.
Lemma lem5193473 (x : type1021) (s : real -> Prop) : ((term496 x s) = ((term451 x s) = (term495 x s))) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (MK_COMB (@lem5193471 x s) (@lem5193472 x s)). Qed.
Lemma lem5193474 (x : type1021) (s : real -> Prop) : ((term496 x s) = (term496 x s)) = (((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s))).
Proof. exact (TRANS (@lem5193468 x s) (@lem5193473 x s)). Qed.
Lemma lem5193475 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term495 x s)) = ((term451 x s) = (term495 x s)).
Proof. exact (EQ_MP (@lem5193474 x s) (@lem5193465 x s)). Qed.
Lemma lem5193476 (x : type1021) (s : real -> Prop) : (term451 x s) = (term495 x s).
Proof. exact (EQ_MP (@lem5193475 x s) (@lem5193462 x s)). Qed.
Lemma lem5193477 (x : type1021) (s : real -> Prop) : (term440 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5193435 x s) (@lem5193476 x s)). Qed.
Lemma lem5193479 {A : Type'} (P : A -> Prop) (Q : Prop) : (term500 A P Q) = (term501 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5193480 (P : real -> Prop) (Q : Prop) : (term502 P Q) = (term503 P Q).
Proof. exact (@lem5193479 real P Q). Qed.
Lemma lem5193481 (x : type1021) (s : real -> Prop) : (term504 x s) = (term505 x s).
Proof. exact (@lem5193480 (term471 x s) (term495 x s)). Qed.
Lemma lem5193482 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5193483 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5193482 x s b)). Qed.
Lemma lem5193484 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193485 (x : type1021) (s : real -> Prop) : (term508 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5193484) (@lem5193483 x s)). Qed.
Lemma lem5193486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193487 (x : type1021) (s : real -> Prop) : (term509 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5193486) (@lem5193485 x s)). Qed.
Lemma lem5193488 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5193489 (x : type1021) (s : real -> Prop) : (term504 x s) = (term499 x s).
Proof. exact (MK_COMB (@lem5193487 x s) (@lem5193488 x s)). Qed.
Lemma lem5193490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193491 (x : type1021) (s : real -> Prop) : (term510 x s) = (term511 x s).
Proof. exact (MK_COMB (@lem5193490) (@lem5193489 x s)). Qed.
Lemma lem5193492 (x : type1021) (s : real -> Prop) (b : real) : (term506 x s b) = (term469 x s b).
Proof. exact (eq_refl (term506 x s b)). Qed.
Lemma lem5193493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193494 (x : type1021) (s : real -> Prop) (b : real) : (term512 x s b) = (term513 x s b).
Proof. exact (MK_COMB (@lem5193493) (@lem5193492 x s b)). Qed.
Lemma lem5193495 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5193496 (b : real) (x : type1021) (s : real -> Prop) : (term514 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5193494 x s b) (@lem5193495 x s)). Qed.
Lemma lem5193497 (x : type1021) (s : real -> Prop) : (term516 x s) = (term517 x s).
Proof. exact (fun_ext (fun b : real => @lem5193496 b x s)). Qed.
Lemma lem5193498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193499 (x : type1021) (s : real -> Prop) : (term505 x s) = (term518 x s).
Proof. exact (MK_COMB (@lem5193498) (@lem5193497 x s)). Qed.
Lemma lem5193500 (x : type1021) (s : real -> Prop) : ((term504 x s) = (term505 x s)) = ((term499 x s) = (term518 x s)).
Proof. exact (MK_COMB (@lem5193491 x s) (@lem5193499 x s)). Qed.
Lemma lem5193501 (x : type1021) (s : real -> Prop) : (term499 x s) = (term518 x s).
Proof. exact (EQ_MP (@lem5193500 x s) (@lem5193481 x s)). Qed.
Lemma lem5193503 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5193504 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5193503 real P Q). Qed.
Lemma lem5193505 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term520 b x s).
Proof. exact (@lem5193504 (term469 x s b) (term494 x s)). Qed.
Lemma lem5193506 (x : type1021) (s : real -> Prop) (b : real) : (term521 x s b) = (term492 x s b).
Proof. exact (eq_refl (term521 x s b)). Qed.
Lemma lem5193507 (x : type1021) (s : real -> Prop) : (term522 x s) = (term494 x s).
Proof. exact (fun_ext (fun b : real => @lem5193506 x s b)). Qed.
Lemma lem5193508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193509 (x : type1021) (s : real -> Prop) : (term523 x s) = (term495 x s).
Proof. exact (MK_COMB (@lem5193508) (@lem5193507 x s)). Qed.
Lemma lem5193510 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5193511 (b : real) (x : type1021) (s : real -> Prop) : (term519 b x s) = (term515 b x s).
Proof. exact (MK_COMB (@lem5193510 x s b) (@lem5193509 x s)). Qed.
Lemma lem5193512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5193513 (b : real) (x : type1021) (s : real -> Prop) : (term524 b x s) = (term525 b x s).
Proof. exact (MK_COMB (@lem5193512) (@lem5193511 b x s)). Qed.
Lemma lem5193514 (x : type1021) (s : real -> Prop) (b' : real) : (term521 x s b') = (term492 x s b').
Proof. exact (eq_refl (term521 x s b')). Qed.
Lemma lem5193515 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term513 x s b).
Proof. exact (eq_refl (term513 x s b)). Qed.
Lemma lem5193516 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term526 b x s b') = (term527 b x s b').
Proof. exact (MK_COMB (@lem5193515 x s b) (@lem5193514 x s b')). Qed.
Lemma lem5193517 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term529 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5193516 b x s b')). Qed.
Lemma lem5193518 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193519 (b : real) (x : type1021) (s : real -> Prop) : (term520 b x s) = (term530 b x s).
Proof. exact (MK_COMB (@lem5193518) (@lem5193517 b x s)). Qed.
Lemma lem5193520 (b : real) (x : type1021) (s : real -> Prop) : ((term519 b x s) = (term520 b x s)) = ((term515 b x s) = (term530 b x s)).
Proof. exact (MK_COMB (@lem5193513 b x s) (@lem5193519 b x s)). Qed.
Lemma lem5193521 (b : real) (x : type1021) (s : real -> Prop) : (term515 b x s) = (term530 b x s).
Proof. exact (EQ_MP (@lem5193520 b x s) (@lem5193505 b x s)). Qed.
Lemma lem5193522 (x : type1021) (s : real -> Prop) : (term517 x s) = (term531 x s).
Proof. exact (fun_ext (fun b : real => @lem5193521 b x s)). Qed.
Lemma lem5193523 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193524 (x : type1021) (s : real -> Prop) : (term518 x s) = (term532 x s).
Proof. exact (MK_COMB (@lem5193523) (@lem5193522 x s)). Qed.
Lemma lem5193525 (x : type1021) (s : real -> Prop) : (term499 x s) = (term532 x s).
Proof. exact (TRANS (@lem5193501 x s) (@lem5193524 x s)). Qed.
Lemma lem5193526 (x : type1021) (s : real -> Prop) : (term440 x s) = (term532 x s).
Proof. exact (TRANS (@lem5193477 x s) (@lem5193525 x s)). Qed.
Lemma lem5193527 (x : type1021) : (term442 x) = (term533 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5193526 x s)). Qed.
Lemma lem5193528 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5193529 (x : type1021) : (term444 x) = (term534 x).
Proof. exact (MK_COMB (@lem5193528) (@lem5193527 x)). Qed.
Lemma lem5193546 (x : type1021) (s : real -> Prop) (b' : real) : (term448 x s b') = (term535 x s b').
Proof. exact (@lem19699 (term536 x b' s) (term537 x s b') (term108 s b')). Qed.
Lemma lem5193555 (b' : real) (s : real -> Prop) : (term490 b' s) = (term490 b' s).
Proof. exact (eq_refl (term490 b' s)). Qed.
Lemma lem5193556 (x : type1021) (s : real -> Prop) (b' : real) : (term492 x s b') = (term538 x s b').
Proof. exact (MK_COMB (@lem5193555 b' s) (@lem5193546 x s b')). Qed.
Lemma lem5193573 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term539 x s b).
Proof. exact (@lem19490 (term536 x b s) (s = (@EMPTY real)) (term537 x s b)). Qed.
Lemma lem5193574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5193575 (x : type1021) (s : real -> Prop) (b : real) : (term513 x s b) = (term540 x s b).
Proof. exact (MK_COMB (@lem5193574) (@lem5193573 x s b)). Qed.
Lemma lem5193576 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term541 b x s b').
Proof. exact (MK_COMB (@lem5193575 x s b) (@lem5193556 x s b')). Qed.
Lemma lem5193577 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term542 b x s b').
Proof. exact (@lem19490 (term293 b' s) (term539 x s b) (term535 x s b')). Qed.
Lemma lem5193578 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term544 b x s b').
Proof. exact (@lem19490 (term545 x s b') (term539 x s b) (term546 x s b')). Qed.
Lemma lem5193585 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term547 b x s b') = (term548 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term546 x s b')). Qed.
Lemma lem5193592 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term551 b x s b') = (term552 b x s b').
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term545 x s b')). Qed.
Lemma lem5193593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193594 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term553 b x s b') = (term554 b x s b').
Proof. exact (MK_COMB (@lem5193593) (@lem5193592 b x s b')). Qed.
Lemma lem5193595 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term544 b x s b') = (term555 b x s b').
Proof. exact (MK_COMB (@lem5193594 b x s b') (@lem5193585 b x s b')). Qed.
Lemma lem5193596 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term543 b x s b') = (term555 b x s b').
Proof. exact (TRANS (@lem5193578 b x s b') (@lem5193595 b x s b')). Qed.
Lemma lem5193603 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term556 x b b' s) = (term557 x b b' s).
Proof. exact (@lem19699 (term549 x b s) (term550 x s b) (term293 b' s)). Qed.
Lemma lem5193604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5193605 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term558 x b b' s) = (term559 x b b' s).
Proof. exact (MK_COMB (@lem5193604) (@lem5193603 x b b' s)). Qed.
Lemma lem5193606 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term560 b x s b').
Proof. exact (MK_COMB (@lem5193605 x b b' s) (@lem5193596 b x s b')). Qed.
Lemma lem5193607 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5193577 b x s b') (@lem5193606 b x s b')). Qed.
Lemma lem5193608 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term527 b x s b') = (term560 b x s b').
Proof. exact (TRANS (@lem5193576 b x s b') (@lem5193607 b x s b')). Qed.
Lemma lem5193609 (b : real) (x : type1021) (s : real -> Prop) : (term529 b x s) = (term561 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5193608 b x s b')). Qed.
Lemma lem5193610 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193611 (b : real) (x : type1021) (s : real -> Prop) : (term530 b x s) = (term562 b x s).
Proof. exact (MK_COMB (@lem5193610) (@lem5193609 b x s)). Qed.
Lemma lem5193612 (x : type1021) (s : real -> Prop) : (term531 x s) = (term563 x s).
Proof. exact (fun_ext (fun b : real => @lem5193611 b x s)). Qed.
Lemma lem5193613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5193614 (x : type1021) (s : real -> Prop) : (term532 x s) = (term564 x s).
Proof. exact (MK_COMB (@lem5193613) (@lem5193612 x s)). Qed.
Lemma lem5193615 (x : type1021) : (term533 x) = (term565 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5193614 x s)). Qed.
Lemma lem5193616 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5193617 (x : type1021) : (term534 x) = (term566 x).
Proof. exact (MK_COMB (@lem5193616) (@lem5193615 x)). Qed.
Lemma lem5193618 (x : type1021) : (term444 x) = (term566 x).
Proof. exact (TRANS (@lem5193529 x) (@lem5193617 x)). Qed.
Lemma lem5193619 (x : type1021) (h1 : term444 x) : term566 x.
Proof. exact (EQ_MP (@lem5193618 x) (@lem5192345 x h1)). Qed.
Lemma lem5193651 (_67767 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _67767.
Proof. exact (@lem5192748 x h1 _67767). Qed.
Lemma lem5193652 (x : type1021) (_67767 : real -> Prop) : (term568 x _67767) = (term564 x _67767).
Proof. exact (eq_refl (term568 x _67767)). Qed.
Lemma lem5193653 (_67767 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _67767.
Proof. exact (EQ_MP (@lem5193652 x _67767) (@lem5193651 _67767 x h1)). Qed.
Lemma lem5193654 (_67767 : real -> Prop) (_67768 : real) (x : type1021) (h1 : term444 x) : term569 x _67767 _67768.
Proof. exact (@lem5193653 _67767 x h1 _67768). Qed.
Lemma lem5193655 (_67768 : real) (x : type1021) (_67767 : real -> Prop) : (term569 x _67767 _67768) = (term562 _67768 x _67767).
Proof. exact (eq_refl (term569 x _67767 _67768)). Qed.
Lemma lem5193656 (_67768 : real) (_67767 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _67768 x _67767.
Proof. exact (EQ_MP (@lem5193655 _67768 x _67767) (@lem5193654 _67767 _67768 x h1)). Qed.
Lemma lem5193657 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term570 _67768 x _67767 _67769.
Proof. exact (@lem5193656 _67768 _67767 x h1 _67769). Qed.
Lemma lem5193658 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term570 _67768 x _67767 _67769) = (term560 _67768 x _67767 _67769).
Proof. exact (eq_refl (term570 _67768 x _67767 _67769)). Qed.
Lemma lem5193659 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term560 _67768 x _67767 _67769.
Proof. exact (EQ_MP (@lem5193658 _67768 x _67767 _67769) (@lem5193657 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193660 (_67770 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term571 s c' _67770.
Proof. exact (@lem5192761 s t c' h1 _67770). Qed.
Lemma lem5193661 (s : real -> Prop) (_67770 : real) (c' : real) : (term571 s c' _67770) = (term130 s _67770 c').
Proof. exact (eq_refl (term571 s c' _67770)). Qed.
Lemma lem5193681 (_67777 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _67777.
Proof. exact (@lem5193043 x h1 _67777). Qed.
Lemma lem5193682 (x : type1021) (_67777 : real -> Prop) : (term568 x _67777) = (term564 x _67777).
Proof. exact (eq_refl (term568 x _67777)). Qed.
Lemma lem5193683 (_67777 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _67777.
Proof. exact (EQ_MP (@lem5193682 x _67777) (@lem5193681 _67777 x h1)). Qed.
Lemma lem5193684 (_67777 : real -> Prop) (_67778 : real) (x : type1021) (h1 : term444 x) : term569 x _67777 _67778.
Proof. exact (@lem5193683 _67777 x h1 _67778). Qed.
Lemma lem5193685 (_67778 : real) (x : type1021) (_67777 : real -> Prop) : (term569 x _67777 _67778) = (term562 _67778 x _67777).
Proof. exact (eq_refl (term569 x _67777 _67778)). Qed.
Lemma lem5193686 (_67778 : real) (_67777 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _67778 x _67777.
Proof. exact (EQ_MP (@lem5193685 _67778 x _67777) (@lem5193684 _67777 _67778 x h1)). Qed.
Lemma lem5193687 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term570 _67778 x _67777 _67779.
Proof. exact (@lem5193686 _67778 _67777 x h1 _67779). Qed.
Lemma lem5193688 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term570 _67778 x _67777 _67779) = (term560 _67778 x _67777 _67779).
Proof. exact (eq_refl (term570 _67778 x _67777 _67779)). Qed.
Lemma lem5193689 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term560 _67778 x _67777 _67779.
Proof. exact (EQ_MP (@lem5193688 _67778 x _67777 _67779) (@lem5193687 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5193693 (_67781 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term571 t c' _67781.
Proof. exact (@lem5193069 s t c' h1 _67781). Qed.
Lemma lem5193694 (t : real -> Prop) (_67781 : real) (c' : real) : (term571 t c' _67781) = (term130 t _67781 c').
Proof. exact (eq_refl (term571 t c' _67781)). Qed.
Lemma lem5193696 (_67782 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term571 s b _67782.
Proof. exact (@lem5193094 s b h1 _67782). Qed.
Lemma lem5193697 (s : real -> Prop) (_67782 : real) (b : real) : (term571 s b _67782) = (term130 s _67782 b).
Proof. exact (eq_refl (term571 s b _67782)). Qed.
Lemma lem5193702 (_67784 : real) (h1 : term129) : term572 _67784.
Proof. exact (@lem5193132 h1 _67784). Qed.
Lemma lem5193703 (_67784 : real) : (term572 _67784) = (term275 _67784).
Proof. exact (eq_refl (term572 _67784)). Qed.
Lemma lem5193704 (_67784 : real) (h1 : term129) : term275 _67784.
Proof. exact (EQ_MP (@lem5193703 _67784) (@lem5193702 _67784 h1)). Qed.
Lemma lem5193705 (_67784 : real) (_67785 : real) (h1 : term129) : term573 _67784 _67785.
Proof. exact (@lem5193704 _67784 h1 _67785). Qed.
Lemma lem5193706 (_67785 : real) (_67784 : real) : (term573 _67784 _67785) = (term273 _67785 _67784).
Proof. exact (eq_refl (term573 _67784 _67785)). Qed.
Lemma lem5193707 (_67785 : real) (_67784 : real) (h1 : term129) : term273 _67785 _67784.
Proof. exact (EQ_MP (@lem5193706 _67785 _67784) (@lem5193705 _67784 _67785 h1)). Qed.
Lemma lem5193708 (_67785 : real) (_67784 : real) (_67786 : real) (h1 : term129) : term574 _67785 _67784 _67786.
Proof. exact (@lem5193707 _67785 _67784 h1 _67786). Qed.
Lemma lem5193709 (_67785 : real) (_67784 : real) (_67786 : real) : (term574 _67785 _67784 _67786) = (term270 _67785 _67784 _67786).
Proof. exact (eq_refl (term574 _67785 _67784 _67786)). Qed.
Lemma lem5193710 (_67785 : real) (_67784 : real) (_67786 : real) (h1 : term129) : term270 _67785 _67784 _67786.
Proof. exact (EQ_MP (@lem5193709 _67785 _67784 _67786) (@lem5193708 _67785 _67784 _67786 h1)). Qed.
Lemma lem5193711 (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _67787.
Proof. exact (@lem5193338 x h1 _67787). Qed.
Lemma lem5193712 (x : type1021) (_67787 : real -> Prop) : (term568 x _67787) = (term564 x _67787).
Proof. exact (eq_refl (term568 x _67787)). Qed.
Lemma lem5193713 (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _67787.
Proof. exact (EQ_MP (@lem5193712 x _67787) (@lem5193711 _67787 x h1)). Qed.
Lemma lem5193714 (_67787 : real -> Prop) (_67788 : real) (x : type1021) (h1 : term444 x) : term569 x _67787 _67788.
Proof. exact (@lem5193713 _67787 x h1 _67788). Qed.
Lemma lem5193715 (_67788 : real) (x : type1021) (_67787 : real -> Prop) : (term569 x _67787 _67788) = (term562 _67788 x _67787).
Proof. exact (eq_refl (term569 x _67787 _67788)). Qed.
Lemma lem5193716 (_67788 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _67788 x _67787.
Proof. exact (EQ_MP (@lem5193715 _67788 x _67787) (@lem5193714 _67787 _67788 x h1)). Qed.
Lemma lem5193717 (_67788 : real) (_67787 : real -> Prop) (_67789 : real) (x : type1021) (h1 : term444 x) : term570 _67788 x _67787 _67789.
Proof. exact (@lem5193716 _67788 _67787 x h1 _67789). Qed.
Lemma lem5193718 (_67788 : real) (x : type1021) (_67787 : real -> Prop) (_67789 : real) : (term570 _67788 x _67787 _67789) = (term560 _67788 x _67787 _67789).
Proof. exact (eq_refl (term570 _67788 x _67787 _67789)). Qed.
Lemma lem5193719 (_67788 : real) (_67787 : real -> Prop) (_67789 : real) (x : type1021) (h1 : term444 x) : term560 _67788 x _67787 _67789.
Proof. exact (EQ_MP (@lem5193718 _67788 x _67787 _67789) (@lem5193717 _67788 _67787 _67789 x h1)). Qed.
Lemma lem5193723 (_67791 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term571 t c _67791.
Proof. exact (@lem5193388 t c h1 _67791). Qed.
Lemma lem5193724 (t : real -> Prop) (_67791 : real) (c : real) : (term571 t c _67791) = (term130 t _67791 c).
Proof. exact (eq_refl (term571 t c _67791)). Qed.
Lemma lem5193726 (_67792 : real) (h1 : term129) : term572 _67792.
Proof. exact (@lem5193413 h1 _67792). Qed.
Lemma lem5193727 (_67792 : real) : (term572 _67792) = (term275 _67792).
Proof. exact (eq_refl (term572 _67792)). Qed.
Lemma lem5193728 (_67792 : real) (h1 : term129) : term275 _67792.
Proof. exact (EQ_MP (@lem5193727 _67792) (@lem5193726 _67792 h1)). Qed.
Lemma lem5193729 (_67792 : real) (_67793 : real) (h1 : term129) : term573 _67792 _67793.
Proof. exact (@lem5193728 _67792 h1 _67793). Qed.
Lemma lem5193730 (_67793 : real) (_67792 : real) : (term573 _67792 _67793) = (term273 _67793 _67792).
Proof. exact (eq_refl (term573 _67792 _67793)). Qed.
Lemma lem5193731 (_67793 : real) (_67792 : real) (h1 : term129) : term273 _67793 _67792.
Proof. exact (EQ_MP (@lem5193730 _67793 _67792) (@lem5193729 _67792 _67793 h1)). Qed.
Lemma lem5193732 (_67793 : real) (_67792 : real) (_67794 : real) (h1 : term129) : term574 _67793 _67792 _67794.
Proof. exact (@lem5193731 _67793 _67792 h1 _67794). Qed.
Lemma lem5193733 (_67793 : real) (_67792 : real) (_67794 : real) : (term574 _67793 _67792 _67794) = (term270 _67793 _67792 _67794).
Proof. exact (eq_refl (term574 _67793 _67792 _67794)). Qed.
Lemma lem5193734 (_67793 : real) (_67792 : real) (_67794 : real) (h1 : term129) : term270 _67793 _67792 _67794.
Proof. exact (EQ_MP (@lem5193733 _67793 _67792 _67794) (@lem5193732 _67793 _67792 _67794 h1)). Qed.
Lemma lem5193735 (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term568 x _67795.
Proof. exact (@lem5193619 x h1 _67795). Qed.
Lemma lem5193736 (x : type1021) (_67795 : real -> Prop) : (term568 x _67795) = (term564 x _67795).
Proof. exact (eq_refl (term568 x _67795)). Qed.
Lemma lem5193737 (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term564 x _67795.
Proof. exact (EQ_MP (@lem5193736 x _67795) (@lem5193735 _67795 x h1)). Qed.
Lemma lem5193738 (_67795 : real -> Prop) (_67796 : real) (x : type1021) (h1 : term444 x) : term569 x _67795 _67796.
Proof. exact (@lem5193737 _67795 x h1 _67796). Qed.
Lemma lem5193739 (_67796 : real) (x : type1021) (_67795 : real -> Prop) : (term569 x _67795 _67796) = (term562 _67796 x _67795).
Proof. exact (eq_refl (term569 x _67795 _67796)). Qed.
Lemma lem5193740 (_67796 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 _67796 x _67795.
Proof. exact (EQ_MP (@lem5193739 _67796 x _67795) (@lem5193738 _67795 _67796 x h1)). Qed.
Lemma lem5193741 (_67796 : real) (_67795 : real -> Prop) (_67797 : real) (x : type1021) (h1 : term444 x) : term570 _67796 x _67795 _67797.
Proof. exact (@lem5193740 _67796 _67795 x h1 _67797). Qed.
Lemma lem5193742 (_67796 : real) (x : type1021) (_67795 : real -> Prop) (_67797 : real) : (term570 _67796 x _67795 _67797) = (term560 _67796 x _67795 _67797).
Proof. exact (eq_refl (term570 _67796 x _67795 _67797)). Qed.
Lemma lem5193743 (_67796 : real) (_67795 : real -> Prop) (_67797 : real) (x : type1021) (h1 : term444 x) : term560 _67796 x _67795 _67797.
Proof. exact (EQ_MP (@lem5193742 _67796 x _67795 _67797) (@lem5193741 _67796 _67795 _67797 x h1)). Qed.
Lemma lem5193744 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term555 _67768 x _67767 _67769.
Proof. exact (proj2 (@lem5193659 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193746 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term548 _67768 x _67767 _67769.
Proof. exact (proj2 (@lem5193744 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193747 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term552 _67768 x _67767 _67769.
Proof. exact (proj1 (@lem5193744 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193748 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term575 _67768 x _67767 _67769.
Proof. exact (proj2 (@lem5193746 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193750 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term576 _67768 x _67767 _67769.
Proof. exact (proj2 (@lem5193747 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193751 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term577 _67768 x _67767 _67769.
Proof. exact (proj1 (@lem5193747 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193754 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term555 _67778 x _67777 _67779.
Proof. exact (proj2 (@lem5193689 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5193756 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term548 _67778 x _67777 _67779.
Proof. exact (proj2 (@lem5193754 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5193757 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term552 _67778 x _67777 _67779.
Proof. exact (proj1 (@lem5193754 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5193758 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term575 _67778 x _67777 _67779.
Proof. exact (proj2 (@lem5193756 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5193760 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term576 _67778 x _67777 _67779.
Proof. exact (proj2 (@lem5193757 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5193761 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term577 _67778 x _67777 _67779.
Proof. exact (proj1 (@lem5193757 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5193765 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term557 x _67788 _67789 _67787.
Proof. exact (proj1 (@lem5193719 _67788 _67787 _67789 x h1)). Qed.
Lemma lem5193772 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term578 x _67788 _67789 _67787.
Proof. exact (proj2 (@lem5193765 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5193773 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term579 x _67788 _67789 _67787.
Proof. exact (proj1 (@lem5193765 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5193775 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term557 x _67796 _67797 _67795.
Proof. exact (proj1 (@lem5193743 _67796 _67795 _67797 x h1)). Qed.
Lemma lem5193782 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term578 x _67796 _67797 _67795.
Proof. exact (proj2 (@lem5193775 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5193783 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term579 x _67796 _67797 _67795.
Proof. exact (proj1 (@lem5193775 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5193785 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5193817 (_67770 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term130 s _67770 c'.
Proof. exact (EQ_MP (@lem5193661 s _67770 c') (@lem5193660 _67770 s t c' h1)). Qed.
Lemma lem5193825 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (h1). Qed.
Lemma lem5193856 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term575 _67768 x _67767 _67769) = (term580 _67768 x _67767 _67769).
Proof. exact (@lem5190250 (_67767 = (@EMPTY real)) (term537 x _67767 _67768) (term546 x _67767 _67769)). Qed.
Lemma lem5193857 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term580 _67768 x _67767 _67769.
Proof. exact (EQ_MP (@lem5193856 _67768 x _67767 _67769) (@lem5193748 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193872 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term577 _67768 x _67767 _67769) = (term581 _67768 x _67767 _67769).
Proof. exact (@lem5190250 (_67767 = (@EMPTY real)) (term536 x _67768 _67767) (term545 x _67767 _67769)). Qed.
Lemma lem5193873 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term581 _67768 x _67767 _67769.
Proof. exact (EQ_MP (@lem5193872 _67768 x _67767 _67769) (@lem5193751 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193888 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term576 _67768 x _67767 _67769) = (term582 _67768 x _67767 _67769).
Proof. exact (@lem5190250 (_67767 = (@EMPTY real)) (term537 x _67767 _67768) (term545 x _67767 _67769)). Qed.
Lemma lem5193889 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term582 _67768 x _67767 _67769.
Proof. exact (EQ_MP (@lem5193888 _67768 x _67767 _67769) (@lem5193750 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5193925 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5193961 (_67781 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term130 t _67781 c'.
Proof. exact (EQ_MP (@lem5193694 t _67781 c') (@lem5193693 _67781 s t c' h1)). Qed.
Lemma lem5193963 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (h1). Qed.
Lemma lem5193994 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term575 _67778 x _67777 _67779) = (term580 _67778 x _67777 _67779).
Proof. exact (@lem5190250 (_67777 = (@EMPTY real)) (term537 x _67777 _67778) (term546 x _67777 _67779)). Qed.
Lemma lem5193995 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term580 _67778 x _67777 _67779.
Proof. exact (EQ_MP (@lem5193994 _67778 x _67777 _67779) (@lem5193758 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5194010 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term577 _67778 x _67777 _67779) = (term581 _67778 x _67777 _67779).
Proof. exact (@lem5190250 (_67777 = (@EMPTY real)) (term536 x _67778 _67777) (term545 x _67777 _67779)). Qed.
Lemma lem5194011 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term581 _67778 x _67777 _67779.
Proof. exact (EQ_MP (@lem5194010 _67778 x _67777 _67779) (@lem5193761 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5194026 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term576 _67778 x _67777 _67779) = (term582 _67778 x _67777 _67779).
Proof. exact (@lem5190250 (_67777 = (@EMPTY real)) (term537 x _67777 _67778) (term545 x _67777 _67779)). Qed.
Lemma lem5194027 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term582 _67778 x _67777 _67779.
Proof. exact (EQ_MP (@lem5194026 _67778 x _67777 _67779) (@lem5193760 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5194061 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5194069 (_67782 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term130 s _67782 b.
Proof. exact (EQ_MP (@lem5193697 s _67782 b) (@lem5193696 _67782 s b h1)). Qed.
Lemma lem5194086 (_67785 : real) (_67784 : real) (_67786 : real) : (term270 _67785 _67784 _67786) = (term583 _67785 _67784 _67786).
Proof. exact (@lem5190250 (term584 _67784 _67785) (term584 _67785 _67786) (real_le _67784 _67786)). Qed.
Lemma lem5194087 (_67785 : real) (_67784 : real) (_67786 : real) (h1 : term129) : term583 _67785 _67784 _67786.
Proof. exact (EQ_MP (@lem5194086 _67785 _67784 _67786) (@lem5193710 _67785 _67784 _67786 h1)). Qed.
Lemma lem5194095 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : term584 x' c'.
Proof. exact (proj2 (@lem5192478 s x' c' h1)). Qed.
Lemma lem5194174 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term579 x _67788 _67789 _67787) = (term585 x _67788 _67789 _67787).
Proof. exact (@lem5190250 (_67787 = (@EMPTY real)) (term536 x _67788 _67787) (term293 _67789 _67787)). Qed.
Lemma lem5194175 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term585 x _67788 _67789 _67787.
Proof. exact (EQ_MP (@lem5194174 x _67788 _67789 _67787) (@lem5193773 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5194190 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term578 x _67788 _67789 _67787) = (term586 x _67788 _67789 _67787).
Proof. exact (@lem5190250 (_67787 = (@EMPTY real)) (term537 x _67787 _67788) (term293 _67789 _67787)). Qed.
Lemma lem5194191 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term586 x _67788 _67789 _67787.
Proof. exact (EQ_MP (@lem5194190 x _67788 _67789 _67787) (@lem5193772 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5194195 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5194207 (_67791 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term130 t _67791 c.
Proof. exact (EQ_MP (@lem5193724 t _67791 c) (@lem5193723 _67791 t c h1)). Qed.
Lemma lem5194218 (_67793 : real) (_67792 : real) (_67794 : real) : (term270 _67793 _67792 _67794) = (term583 _67793 _67792 _67794).
Proof. exact (@lem5190250 (term584 _67792 _67793) (term584 _67793 _67794) (real_le _67792 _67794)). Qed.
Lemma lem5194219 (_67793 : real) (_67792 : real) (_67794 : real) (h1 : term129) : term583 _67793 _67792 _67794.
Proof. exact (EQ_MP (@lem5194218 _67793 _67792 _67794) (@lem5193734 _67793 _67792 _67794 h1)). Qed.
Lemma lem5194227 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : term584 x' c'.
Proof. exact (proj2 (@lem5192479 t x' c' h1)). Qed.
Lemma lem5194306 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term579 x _67796 _67797 _67795) = (term585 x _67796 _67797 _67795).
Proof. exact (@lem5190250 (_67795 = (@EMPTY real)) (term536 x _67796 _67795) (term293 _67797 _67795)). Qed.
Lemma lem5194307 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term585 x _67796 _67797 _67795.
Proof. exact (EQ_MP (@lem5194306 x _67796 _67797 _67795) (@lem5193783 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5194322 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term578 x _67796 _67797 _67795) = (term586 x _67796 _67797 _67795).
Proof. exact (@lem5190250 (_67795 = (@EMPTY real)) (term537 x _67795 _67796) (term293 _67797 _67795)). Qed.
Lemma lem5194323 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term586 x _67796 _67797 _67795.
Proof. exact (EQ_MP (@lem5194322 x _67796 _67797 _67795) (@lem5193782 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5194390 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5194391 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5194390 s h1). Qed.
Lemma lem5194393 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194394 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5194393 (s = (@EMPTY real))). Qed.
Lemma lem5194395 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5194394 s) (@lem5194391 s h1)). Qed.
Lemma lem5194397 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5194398 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5194397 s h1). Qed.
Lemma lem5194400 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194401 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5194400 (s = (@EMPTY real))). Qed.
Lemma lem5194402 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5194401 s) (@lem5194398 s h1)). Qed.
Lemma lem5194405 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (h1). Qed.
Lemma lem5194406 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term590 x c' s.
Proof. exact (fun h0 : term536 x c' s => @lem5194405 x c' s h1). Qed.
Lemma lem5194408 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194409 (x : type1021) (c' : real) (s : real -> Prop) : (term590 x c' s) = (term589 x c' s).
Proof. exact (@lem5194408 (term536 x c' s)). Qed.
Lemma lem5194410 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (EQ_MP (@lem5194409 x c' s) (@lem5194406 x c' s h1)). Qed.
Lemma lem5194413 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (h1). Qed.
Lemma lem5194414 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term591 s c'.
Proof. exact (fun h0 : term108 s c' => @lem5194413 s c' h1). Qed.
Lemma lem5194416 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194417 (s : real -> Prop) (c' : real) : (term591 s c') = (term567 s c').
Proof. exact (@lem5194416 (term108 s c')). Qed.
Lemma lem5194418 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (EQ_MP (@lem5194417 s c') (@lem5194414 s c' h1)). Qed.
Lemma lem5194451 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194452 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term592 x _67768 _67767 _67769) = (term593 x _67768 _67767 _67769).
Proof. exact (@lem5194451 (_67767 = (@EMPTY real)) (term536 x _67769 _67767) (term594 x _67768 _67767 _67769)). Qed.
Lemma lem5194468 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194469 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term595 x _67768 _67767 _67769) = (term596 _67768 x _67767 _67769).
Proof. exact (@lem5194468 (term536 x _67768 _67767) (term536 x _67769 _67767) (term108 _67767 _67769)). Qed.
Lemma lem5194485 (_67767 : real -> Prop) : (term289 _67767) = (term289 _67767).
Proof. exact (eq_refl (term289 _67767)). Qed.
Lemma lem5194486 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term593 x _67768 _67767 _67769) = (term581 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5194485 _67767) (@lem5194469 _67768 x _67767 _67769)). Qed.
Lemma lem5194497 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term592 x _67768 _67767 _67769) = (term581 _67768 x _67767 _67769).
Proof. exact (TRANS (@lem5194452 x _67768 _67767 _67769) (@lem5194486 _67768 x _67767 _67769)). Qed.
Lemma lem5194498 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term597 _67768 x _67767 _67769) = (term597 _67768 x _67767 _67769).
Proof. exact (eq_refl (term597 _67768 x _67767 _67769)). Qed.
Lemma lem5194499 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : ((term581 _67768 x _67767 _67769) = (term592 x _67768 _67767 _67769)) = ((term581 _67768 x _67767 _67769) = (term581 _67768 x _67767 _67769)).
Proof. exact (MK_COMB (@lem5194498 _67768 x _67767 _67769) (@lem5194497 _67768 x _67767 _67769)). Qed.
Lemma lem5194501 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5194502 (x : Prop) : (x = x) = True.
Proof. exact (@lem5194501 Prop x). Qed.
Lemma lem5194503 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : ((term581 _67768 x _67767 _67769) = (term581 _67768 x _67767 _67769)) = True.
Proof. exact (@lem5194502 (term581 _67768 x _67767 _67769)). Qed.
Lemma lem5194504 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : ((term581 _67768 x _67767 _67769) = (term592 x _67768 _67767 _67769)) = True.
Proof. exact (TRANS (@lem5194499 _67768 x _67767 _67769) (@lem5194503 _67768 x _67767 _67769)). Qed.
Lemma lem5194505 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : True = ((term581 _67768 x _67767 _67769) = (term592 x _67768 _67767 _67769)).
Proof. exact (SYM (@lem5194504 x _67768 _67767 _67769)). Qed.
Lemma lem5194506 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term581 _67768 x _67767 _67769) = (term592 x _67768 _67767 _67769).
Proof. exact (EQ_MP (@lem5194505 x _67768 _67767 _67769) (@lem0)). Qed.
Lemma lem5194507 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term592 x _67768 _67767 _67769.
Proof. exact (EQ_MP (@lem5194506 x _67768 _67767 _67769) (@lem5193873 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5194509 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5194510 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term592 x _67768 _67767 _67769) = (term599 _67768 x _67769 _67767).
Proof. exact (@lem5194509 (term600 x _67768 _67767 _67769) (term536 x _67769 _67767)). Qed.
Lemma lem5194512 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5194513 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term603 x _67768 _67767 _67769) = (term604 x _67768 _67767 _67769).
Proof. exact (@lem5194512 (_67767 = (@EMPTY real)) (term594 x _67768 _67767 _67769)). Qed.
Lemma lem5194515 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5194516 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term605 x _67768 _67767 _67769) = (term606 x _67768 _67767 _67769).
Proof. exact (@lem5194515 (term536 x _67768 _67767) (term108 _67767 _67769)). Qed.
Lemma lem5194517 (_67767 : real -> Prop) : (term118 _67767) = (term118 _67767).
Proof. exact (eq_refl (term118 _67767)). Qed.
Lemma lem5194518 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term604 x _67768 _67767 _67769) = (term607 x _67768 _67767 _67769).
Proof. exact (MK_COMB (@lem5194517 _67767) (@lem5194516 x _67768 _67767 _67769)). Qed.
Lemma lem5194519 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term603 x _67768 _67767 _67769) = (term607 x _67768 _67767 _67769).
Proof. exact (TRANS (@lem5194513 x _67768 _67767 _67769) (@lem5194518 x _67768 _67767 _67769)). Qed.
Lemma lem5194520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5194521 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term608 x _67768 _67767 _67769) = (term609 x _67768 _67767 _67769).
Proof. exact (MK_COMB (@lem5194520) (@lem5194519 x _67768 _67767 _67769)). Qed.
Lemma lem5194522 (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term536 x _67769 _67767) = (term536 x _67769 _67767).
Proof. exact (eq_refl (term536 x _67769 _67767)). Qed.
Lemma lem5194523 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term599 _67768 x _67769 _67767) = (term610 _67768 x _67769 _67767).
Proof. exact (MK_COMB (@lem5194521 x _67768 _67767 _67769) (@lem5194522 x _67769 _67767)). Qed.
Lemma lem5194524 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term592 x _67768 _67767 _67769) = (term610 _67768 x _67769 _67767).
Proof. exact (TRANS (@lem5194510 _67768 x _67769 _67767) (@lem5194523 _67768 x _67769 _67767)). Qed.
Lemma lem5194526 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term589 x c' s) (h2 : term567 s c') : term611 x s c'.
Proof. exact (conj (@lem5194410 x c' s h1) (@lem5194418 s c' h2)). Qed.
Lemma lem5194527 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term31 s) (h2 : term589 x c' s) (h3 : term567 s c') : term612 x s c'.
Proof. exact (conj (@lem5194402 s h1) (@lem5194526 x s c' h2 h3)). Qed.
Lemma lem5194529 (_67768 : real) (_67769 : real) (_67767 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _67768 x _67769 _67767.
Proof. exact (EQ_MP (@lem5194524 _67768 x _67769 _67767) (@lem5194507 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5194530 (c' : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' s.
Proof. exact (@lem5194529 c' c' s x h1). Qed.
Lemma lem5194533 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term589 x c' s) (h4 : term567 s c') : term536 x c' s.
Proof. exact (@lem5194530 c' s x h1 (@lem5194527 x s c' h2 h3 h4)). Qed.
Lemma lem5194534 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') : term614 x c' s.
Proof. exact (fun h0 : term589 x c' s => @lem5194533 x s c' h1 h2 h0 h3). Qed.
Lemma lem5194536 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5194537 (x : type1021) (c' : real) (s : real -> Prop) : (term614 x c' s) = (term536 x c' s).
Proof. exact (@lem5194536 (term536 x c' s)). Qed.
Lemma lem5194538 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') : term536 x c' s.
Proof. exact (EQ_MP (@lem5194537 x c' s) (@lem5194534 x s c' h1 h2 h3)). Qed.
Lemma lem5194544 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5194545 (c' : real) (_67770 : real) (s : real -> Prop) : (term130 s _67770 c') = (term616 c' _67770 s).
Proof. exact (@lem5194544 (real_le _67770 c') (term617 _67770 s)). Qed.
Lemma lem5194551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5194552 (c' : real) (_67770 : real) (s : real -> Prop) : (term618 s _67770 c') = (term619 c' _67770 s).
Proof. exact (MK_COMB (@lem5194551) (@lem5194545 c' _67770 s)). Qed.
Lemma lem5194558 (c' : real) (_67770 : real) (s : real -> Prop) : (term616 c' _67770 s) = (term616 c' _67770 s).
Proof. exact (eq_refl (term616 c' _67770 s)). Qed.
Lemma lem5194559 (c' : real) (_67770 : real) (s : real -> Prop) : ((term130 s _67770 c') = (term616 c' _67770 s)) = ((term616 c' _67770 s) = (term616 c' _67770 s)).
Proof. exact (MK_COMB (@lem5194552 c' _67770 s) (@lem5194558 c' _67770 s)). Qed.
Lemma lem5194561 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5194562 (x : Prop) : (x = x) = True.
Proof. exact (@lem5194561 Prop x). Qed.
Lemma lem5194563 (c' : real) (_67770 : real) (s : real -> Prop) : ((term616 c' _67770 s) = (term616 c' _67770 s)) = True.
Proof. exact (@lem5194562 (term616 c' _67770 s)). Qed.
Lemma lem5194564 (c' : real) (_67770 : real) (s : real -> Prop) : ((term130 s _67770 c') = (term616 c' _67770 s)) = True.
Proof. exact (TRANS (@lem5194559 c' _67770 s) (@lem5194563 c' _67770 s)). Qed.
Lemma lem5194565 (c' : real) (_67770 : real) (s : real -> Prop) : True = ((term130 s _67770 c') = (term616 c' _67770 s)).
Proof. exact (SYM (@lem5194564 c' _67770 s)). Qed.
Lemma lem5194566 (c' : real) (_67770 : real) (s : real -> Prop) : (term130 s _67770 c') = (term616 c' _67770 s).
Proof. exact (EQ_MP (@lem5194565 c' _67770 s) (@lem0)). Qed.
Lemma lem5194567 (_67770 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term616 c' _67770 s.
Proof. exact (EQ_MP (@lem5194566 c' _67770 s) (@lem5193817 _67770 s t c' h1)). Qed.
Lemma lem5194569 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5194570 (s : real -> Prop) (_67770 : real) (c' : real) : (term616 c' _67770 s) = (term620 s _67770 c').
Proof. exact (@lem5194569 (term617 _67770 s) (real_le _67770 c')). Qed.
Lemma lem5194572 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5194573 (_67770 : real) (s : real -> Prop) : (term622 _67770 s) = (@IN real _67770 s).
Proof. exact (@lem5194572 (@IN real _67770 s)). Qed.
Lemma lem5194574 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5194575 (_67770 : real) (s : real -> Prop) : (term623 _67770 s) = (term51 _67770 s).
Proof. exact (MK_COMB (@lem5194574) (@lem5194573 _67770 s)). Qed.
Lemma lem5194576 (_67770 : real) (c' : real) : (real_le _67770 c') = (real_le _67770 c').
Proof. exact (eq_refl (real_le _67770 c')). Qed.
Lemma lem5194577 (s : real -> Prop) (_67770 : real) (c' : real) : (term620 s _67770 c') = (term53 s _67770 c').
Proof. exact (MK_COMB (@lem5194575 _67770 s) (@lem5194576 _67770 c')). Qed.
Lemma lem5194578 (s : real -> Prop) (_67770 : real) (c' : real) : (term616 c' _67770 s) = (term53 s _67770 c').
Proof. exact (TRANS (@lem5194570 s _67770 c') (@lem5194577 s _67770 c')). Qed.
Lemma lem5194581 (_67770 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term53 s _67770 c'.
Proof. exact (EQ_MP (@lem5194578 s _67770 c') (@lem5194567 _67770 s t c' h1)). Qed.
Lemma lem5194582 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term624 x s c'.
Proof. exact (@lem5194581 (x s c') s t c' h1). Qed.
Lemma lem5194585 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term625 x s c'.
Proof. exact (@lem5194582 x s t c' h4 (@lem5194538 x s c' h1 h2 h3)). Qed.
Lemma lem5194586 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term626 x s c'.
Proof. exact (fun h0 : term537 x s c' => @lem5194585 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5194588 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5194589 (x : type1021) (s : real -> Prop) (c' : real) : (term626 x s c') = (term625 x s c').
Proof. exact (@lem5194588 (term625 x s c')). Qed.
Lemma lem5194590 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term625 x s c'.
Proof. exact (EQ_MP (@lem5194589 x s c') (@lem5194586 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5194592 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5194593 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5194592 s h1). Qed.
Lemma lem5194595 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194596 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5194595 (s = (@EMPTY real))). Qed.
Lemma lem5194597 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5194596 s) (@lem5194593 s h1)). Qed.
Lemma lem5194599 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5194600 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5194599 s h1). Qed.
Lemma lem5194602 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194603 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5194602 (s = (@EMPTY real))). Qed.
Lemma lem5194604 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5194603 s) (@lem5194600 s h1)). Qed.
Lemma lem5194607 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (h1). Qed.
Lemma lem5194608 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term590 x c' s.
Proof. exact (fun h0 : term536 x c' s => @lem5194607 x c' s h1). Qed.
Lemma lem5194610 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194611 (x : type1021) (c' : real) (s : real -> Prop) : (term590 x c' s) = (term589 x c' s).
Proof. exact (@lem5194610 (term536 x c' s)). Qed.
Lemma lem5194612 (x : type1021) (c' : real) (s : real -> Prop) (h1 : term589 x c' s) : term589 x c' s.
Proof. exact (EQ_MP (@lem5194611 x c' s) (@lem5194608 x c' s h1)). Qed.
Lemma lem5194615 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (h1). Qed.
Lemma lem5194616 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term591 s c'.
Proof. exact (fun h0 : term108 s c' => @lem5194615 s c' h1). Qed.
Lemma lem5194618 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194619 (s : real -> Prop) (c' : real) : (term591 s c') = (term567 s c').
Proof. exact (@lem5194618 (term108 s c')). Qed.
Lemma lem5194620 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (EQ_MP (@lem5194619 s c') (@lem5194616 s c' h1)). Qed.
Lemma lem5194621 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term589 x c' s) (h2 : term567 s c') : term611 x s c'.
Proof. exact (conj (@lem5194612 x c' s h1) (@lem5194620 s c' h2)). Qed.
Lemma lem5194622 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term31 s) (h2 : term589 x c' s) (h3 : term567 s c') : term612 x s c'.
Proof. exact (conj (@lem5194604 s h1) (@lem5194621 x s c' h2 h3)). Qed.
Lemma lem5194624 (_67768 : real) (_67769 : real) (_67767 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _67768 x _67769 _67767.
Proof. exact (EQ_MP (@lem5194524 _67768 x _67769 _67767) (@lem5194507 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5194625 (c' : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' s.
Proof. exact (@lem5194624 c' c' s x h1). Qed.
Lemma lem5194628 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term589 x c' s) (h4 : term567 s c') : term536 x c' s.
Proof. exact (@lem5194625 c' s x h1 (@lem5194622 x s c' h2 h3 h4)). Qed.
Lemma lem5194629 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') : term614 x c' s.
Proof. exact (fun h0 : term589 x c' s => @lem5194628 x s c' h1 h2 h0 h3). Qed.
Lemma lem5194631 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5194632 (x : type1021) (c' : real) (s : real -> Prop) : (term614 x c' s) = (term536 x c' s).
Proof. exact (@lem5194631 (term536 x c' s)). Qed.
Lemma lem5194633 (x : type1021) (s : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') : term536 x c' s.
Proof. exact (EQ_MP (@lem5194632 x c' s) (@lem5194629 x s c' h1 h2 h3)). Qed.
Lemma lem5194635 (_67770 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term53 s _67770 c'.
Proof. exact (EQ_MP (@lem5194578 s _67770 c') (@lem5194567 _67770 s t c' h1)). Qed.
Lemma lem5194636 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term624 x s c'.
Proof. exact (@lem5194635 (x s c') s t c' h1). Qed.
Lemma lem5194639 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term625 x s c'.
Proof. exact (@lem5194636 x s t c' h4 (@lem5194633 x s c' h1 h2 h3)). Qed.
Lemma lem5194640 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term626 x s c'.
Proof. exact (fun h0 : term537 x s c' => @lem5194639 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5194642 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5194643 (x : type1021) (s : real -> Prop) (c' : real) : (term626 x s c') = (term625 x s c').
Proof. exact (@lem5194642 (term625 x s c')). Qed.
Lemma lem5194644 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term625 x s c'.
Proof. exact (EQ_MP (@lem5194643 x s c') (@lem5194640 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5194647 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (h1). Qed.
Lemma lem5194648 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term591 s c'.
Proof. exact (fun h0 : term108 s c' => @lem5194647 s c' h1). Qed.
Lemma lem5194650 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194651 (s : real -> Prop) (c' : real) : (term591 s c') = (term567 s c').
Proof. exact (@lem5194650 (term108 s c')). Qed.
Lemma lem5194652 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term567 s c'.
Proof. exact (EQ_MP (@lem5194651 s c') (@lem5194648 s c' h1)). Qed.
Lemma lem5194680 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5194681 (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term546 x _67767 _67769) = (term627 x _67767 _67769).
Proof. exact (@lem5194680 (term108 _67767 _67769) (term537 x _67767 _67769)). Qed.
Lemma lem5194687 (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term628 x _67767 _67768) = (term628 x _67767 _67768).
Proof. exact (eq_refl (term628 x _67767 _67768)). Qed.
Lemma lem5194688 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term629 _67768 x _67767 _67769) = (term630 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5194687 x _67767 _67768) (@lem5194681 x _67767 _67769)). Qed.
Lemma lem5194692 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194693 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term630 _67768 x _67767 _67769) = (term631 _67768 x _67767 _67769).
Proof. exact (@lem5194692 (term108 _67767 _67769) (term537 x _67767 _67768) (term537 x _67767 _67769)). Qed.
Lemma lem5194709 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term629 _67768 x _67767 _67769) = (term631 _67768 x _67767 _67769).
Proof. exact (TRANS (@lem5194688 _67768 x _67767 _67769) (@lem5194693 _67768 x _67767 _67769)). Qed.
Lemma lem5194710 (_67767 : real -> Prop) : (term289 _67767) = (term289 _67767).
Proof. exact (eq_refl (term289 _67767)). Qed.
Lemma lem5194711 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term580 _67768 x _67767 _67769) = (term632 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5194710 _67767) (@lem5194709 _67768 x _67767 _67769)). Qed.
Lemma lem5194722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5194723 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term633 _67768 x _67767 _67769) = (term634 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5194722) (@lem5194711 _67768 x _67767 _67769)). Qed.
Lemma lem5194727 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194728 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term635 x _67768 _67767 _67769) = (term636 x _67768 _67767 _67769).
Proof. exact (@lem5194727 (_67767 = (@EMPTY real)) (term537 x _67767 _67769) (term637 x _67768 _67767 _67769)). Qed.
Lemma lem5194744 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194745 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term638 x _67768 _67767 _67769) = (term629 _67768 x _67767 _67769).
Proof. exact (@lem5194744 (term537 x _67767 _67768) (term537 x _67767 _67769) (term108 _67767 _67769)). Qed.
Lemma lem5194759 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5194760 (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term546 x _67767 _67769) = (term627 x _67767 _67769).
Proof. exact (@lem5194759 (term108 _67767 _67769) (term537 x _67767 _67769)). Qed.
Lemma lem5194766 (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term628 x _67767 _67768) = (term628 x _67767 _67768).
Proof. exact (eq_refl (term628 x _67767 _67768)). Qed.
Lemma lem5194767 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term629 _67768 x _67767 _67769) = (term630 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5194766 x _67767 _67768) (@lem5194760 x _67767 _67769)). Qed.
Lemma lem5194771 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194772 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term630 _67768 x _67767 _67769) = (term631 _67768 x _67767 _67769).
Proof. exact (@lem5194771 (term108 _67767 _67769) (term537 x _67767 _67768) (term537 x _67767 _67769)). Qed.
Lemma lem5194788 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term629 _67768 x _67767 _67769) = (term631 _67768 x _67767 _67769).
Proof. exact (TRANS (@lem5194767 _67768 x _67767 _67769) (@lem5194772 _67768 x _67767 _67769)). Qed.
Lemma lem5194789 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term638 x _67768 _67767 _67769) = (term631 _67768 x _67767 _67769).
Proof. exact (TRANS (@lem5194745 _67768 x _67767 _67769) (@lem5194788 _67768 x _67767 _67769)). Qed.
Lemma lem5194790 (_67767 : real -> Prop) : (term289 _67767) = (term289 _67767).
Proof. exact (eq_refl (term289 _67767)). Qed.
Lemma lem5194791 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term636 x _67768 _67767 _67769) = (term632 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5194790 _67767) (@lem5194789 _67768 x _67767 _67769)). Qed.
Lemma lem5194802 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term635 x _67768 _67767 _67769) = (term632 _67768 x _67767 _67769).
Proof. exact (TRANS (@lem5194728 x _67768 _67767 _67769) (@lem5194791 _67768 x _67767 _67769)). Qed.
Lemma lem5194803 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : ((term580 _67768 x _67767 _67769) = (term635 x _67768 _67767 _67769)) = ((term632 _67768 x _67767 _67769) = (term632 _67768 x _67767 _67769)).
Proof. exact (MK_COMB (@lem5194723 _67768 x _67767 _67769) (@lem5194802 _67768 x _67767 _67769)). Qed.
Lemma lem5194805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5194806 (x : Prop) : (x = x) = True.
Proof. exact (@lem5194805 Prop x). Qed.
Lemma lem5194807 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : ((term632 _67768 x _67767 _67769) = (term632 _67768 x _67767 _67769)) = True.
Proof. exact (@lem5194806 (term632 _67768 x _67767 _67769)). Qed.
Lemma lem5194808 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : ((term580 _67768 x _67767 _67769) = (term635 x _67768 _67767 _67769)) = True.
Proof. exact (TRANS (@lem5194803 _67768 x _67767 _67769) (@lem5194807 _67768 x _67767 _67769)). Qed.
Lemma lem5194809 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : True = ((term580 _67768 x _67767 _67769) = (term635 x _67768 _67767 _67769)).
Proof. exact (SYM (@lem5194808 x _67768 _67767 _67769)). Qed.
Lemma lem5194810 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term580 _67768 x _67767 _67769) = (term635 x _67768 _67767 _67769).
Proof. exact (EQ_MP (@lem5194809 x _67768 _67767 _67769) (@lem0)). Qed.
Lemma lem5194811 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term635 x _67768 _67767 _67769.
Proof. exact (EQ_MP (@lem5194810 x _67768 _67767 _67769) (@lem5193857 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5194813 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5194814 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term635 x _67768 _67767 _67769) = (term639 _67768 x _67767 _67769).
Proof. exact (@lem5194813 (term640 x _67768 _67767 _67769) (term537 x _67767 _67769)). Qed.
Lemma lem5194816 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5194817 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term641 x _67768 _67767 _67769) = (term642 x _67768 _67767 _67769).
Proof. exact (@lem5194816 (_67767 = (@EMPTY real)) (term637 x _67768 _67767 _67769)). Qed.
Lemma lem5194819 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5194820 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term643 x _67768 _67767 _67769) = (term644 x _67768 _67767 _67769).
Proof. exact (@lem5194819 (term537 x _67767 _67768) (term108 _67767 _67769)). Qed.
Lemma lem5194822 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5194823 (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term645 x _67767 _67768) = (term625 x _67767 _67768).
Proof. exact (@lem5194822 (term625 x _67767 _67768)). Qed.
Lemma lem5194824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5194825 (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term646 x _67767 _67768) = (term647 x _67767 _67768).
Proof. exact (MK_COMB (@lem5194824) (@lem5194823 x _67767 _67768)). Qed.
Lemma lem5194826 (_67767 : real -> Prop) (_67769 : real) : (term567 _67767 _67769) = (term567 _67767 _67769).
Proof. exact (eq_refl (term567 _67767 _67769)). Qed.
Lemma lem5194827 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term644 x _67768 _67767 _67769) = (term648 x _67768 _67767 _67769).
Proof. exact (MK_COMB (@lem5194825 x _67767 _67768) (@lem5194826 _67767 _67769)). Qed.
Lemma lem5194828 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term643 x _67768 _67767 _67769) = (term648 x _67768 _67767 _67769).
Proof. exact (TRANS (@lem5194820 x _67768 _67767 _67769) (@lem5194827 x _67768 _67767 _67769)). Qed.
Lemma lem5194829 (_67767 : real -> Prop) : (term118 _67767) = (term118 _67767).
Proof. exact (eq_refl (term118 _67767)). Qed.
Lemma lem5194830 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term642 x _67768 _67767 _67769) = (term649 x _67768 _67767 _67769).
Proof. exact (MK_COMB (@lem5194829 _67767) (@lem5194828 x _67768 _67767 _67769)). Qed.
Lemma lem5194831 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term641 x _67768 _67767 _67769) = (term649 x _67768 _67767 _67769).
Proof. exact (TRANS (@lem5194817 x _67768 _67767 _67769) (@lem5194830 x _67768 _67767 _67769)). Qed.
Lemma lem5194832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5194833 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term650 x _67768 _67767 _67769) = (term651 x _67768 _67767 _67769).
Proof. exact (MK_COMB (@lem5194832) (@lem5194831 x _67768 _67767 _67769)). Qed.
Lemma lem5194834 (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term537 x _67767 _67769) = (term537 x _67767 _67769).
Proof. exact (eq_refl (term537 x _67767 _67769)). Qed.
Lemma lem5194835 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term639 _67768 x _67767 _67769) = (term652 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5194833 x _67768 _67767 _67769) (@lem5194834 x _67767 _67769)). Qed.
Lemma lem5194836 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term635 x _67768 _67767 _67769) = (term652 _67768 x _67767 _67769).
Proof. exact (TRANS (@lem5194814 _67768 x _67767 _67769) (@lem5194835 _67768 x _67767 _67769)). Qed.
Lemma lem5194838 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term653 x s c'.
Proof. exact (conj (@lem5194644 x s t c' h1 h2 h3 h4) (@lem5194652 s c' h3)). Qed.
Lemma lem5194839 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term654 x s c'.
Proof. exact (conj (@lem5194597 s h2) (@lem5194838 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5194841 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term652 _67768 x _67767 _67769.
Proof. exact (EQ_MP (@lem5194836 _67768 x _67767 _67769) (@lem5194811 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5194842 (s : real -> Prop) (c' : real) (x : type1021) (h1 : term444 x) : term655 x s c'.
Proof. exact (@lem5194841 c' s c' x h1). Qed.
Lemma lem5194845 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term537 x s c'.
Proof. exact (@lem5194842 s c' x h1 (@lem5194839 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5194846 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term656 x s c'.
Proof. exact (fun h0 : term625 x s c' => @lem5194845 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5194848 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194849 (x : type1021) (s : real -> Prop) (c' : real) : (term656 x s c') = (term537 x s c').
Proof. exact (@lem5194848 (term625 x s c')). Qed.
Lemma lem5194850 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term537 x s c'.
Proof. exact (EQ_MP (@lem5194849 x s c') (@lem5194846 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5194852 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5194855 (c' : real) (_67770 : real) (s : real -> Prop) : (term130 s _67770 c') = (term657 c' _67770 s).
Proof. exact (@lem5194852 (real_le _67770 c') (term617 _67770 s)). Qed.
Lemma lem5194858 (_67770 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term657 c' _67770 s.
Proof. exact (EQ_MP (@lem5194855 c' _67770 s) (@lem5193817 _67770 s t c' h1)). Qed.
Lemma lem5194859 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term658 x c' s.
Proof. exact (@lem5194858 (x s c') s t c' h1). Qed.
Lemma lem5194862 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term589 x c' s.
Proof. exact (@lem5194859 x s t c' h4 (@lem5194850 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5194863 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term590 x c' s.
Proof. exact (fun h0 : term536 x c' s => @lem5194862 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5194865 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5194866 (x : type1021) (c' : real) (s : real -> Prop) : (term590 x c' s) = (term589 x c' s).
Proof. exact (@lem5194865 (term536 x c' s)). Qed.
Lemma lem5194867 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term589 x c' s.
Proof. exact (EQ_MP (@lem5194866 x c' s) (@lem5194863 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5194885 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194886 (x : type1021) (_67768 : real) (_67767 : real -> Prop) (_67769 : real) : (term659 _67768 x _67767 _67769) = (term660 x _67768 _67767 _67769).
Proof. exact (@lem5194885 (term536 x _67769 _67767) (term537 x _67767 _67768) (term108 _67767 _67769)). Qed.
Lemma lem5194900 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5194901 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term637 x _67768 _67767 _67769) = (term661 _67769 x _67767 _67768).
Proof. exact (@lem5194900 (term108 _67767 _67769) (term537 x _67767 _67768)). Qed.
Lemma lem5194907 (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term662 x _67769 _67767) = (term662 x _67769 _67767).
Proof. exact (eq_refl (term662 x _67769 _67767)). Qed.
Lemma lem5194908 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term660 x _67768 _67767 _67769) = (term663 _67769 x _67767 _67768).
Proof. exact (MK_COMB (@lem5194907 x _67769 _67767) (@lem5194901 _67769 x _67767 _67768)). Qed.
Lemma lem5194919 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term659 _67768 x _67767 _67769) = (term663 _67769 x _67767 _67768).
Proof. exact (TRANS (@lem5194886 x _67768 _67767 _67769) (@lem5194908 _67769 x _67767 _67768)). Qed.
Lemma lem5194920 (_67767 : real -> Prop) : (term289 _67767) = (term289 _67767).
Proof. exact (eq_refl (term289 _67767)). Qed.
Lemma lem5194921 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term582 _67768 x _67767 _67769) = (term664 _67769 x _67767 _67768).
Proof. exact (MK_COMB (@lem5194920 _67767) (@lem5194919 _67769 x _67767 _67768)). Qed.
Lemma lem5194932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5194933 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term665 _67768 x _67767 _67769) = (term666 _67769 x _67767 _67768).
Proof. exact (MK_COMB (@lem5194932) (@lem5194921 _67769 x _67767 _67768)). Qed.
Lemma lem5194937 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194938 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term667 _67768 x _67769 _67767) = (term668 _67768 x _67769 _67767).
Proof. exact (@lem5194937 (_67767 = (@EMPTY real)) (term108 _67767 _67769) (term669 _67768 x _67769 _67767)). Qed.
Lemma lem5194964 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5194965 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term669 _67768 x _67769 _67767) = (term670 _67769 x _67767 _67768).
Proof. exact (@lem5194964 (term536 x _67769 _67767) (term537 x _67767 _67768)). Qed.
Lemma lem5194971 (_67767 : real -> Prop) (_67769 : real) : (term671 _67767 _67769) = (term671 _67767 _67769).
Proof. exact (eq_refl (term671 _67767 _67769)). Qed.
Lemma lem5194972 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term672 _67768 x _67769 _67767) = (term673 _67769 x _67767 _67768).
Proof. exact (MK_COMB (@lem5194971 _67767 _67769) (@lem5194965 _67769 x _67767 _67768)). Qed.
Lemma lem5194976 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5194977 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term673 _67769 x _67767 _67768) = (term663 _67769 x _67767 _67768).
Proof. exact (@lem5194976 (term536 x _67769 _67767) (term108 _67767 _67769) (term537 x _67767 _67768)). Qed.
Lemma lem5194993 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term672 _67768 x _67769 _67767) = (term663 _67769 x _67767 _67768).
Proof. exact (TRANS (@lem5194972 _67769 x _67767 _67768) (@lem5194977 _67769 x _67767 _67768)). Qed.
Lemma lem5194994 (_67767 : real -> Prop) : (term289 _67767) = (term289 _67767).
Proof. exact (eq_refl (term289 _67767)). Qed.
Lemma lem5194995 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term668 _67768 x _67769 _67767) = (term664 _67769 x _67767 _67768).
Proof. exact (MK_COMB (@lem5194994 _67767) (@lem5194993 _67769 x _67767 _67768)). Qed.
Lemma lem5195006 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term667 _67768 x _67769 _67767) = (term664 _67769 x _67767 _67768).
Proof. exact (TRANS (@lem5194938 _67768 x _67769 _67767) (@lem5194995 _67769 x _67767 _67768)). Qed.
Lemma lem5195007 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : ((term582 _67768 x _67767 _67769) = (term667 _67768 x _67769 _67767)) = ((term664 _67769 x _67767 _67768) = (term664 _67769 x _67767 _67768)).
Proof. exact (MK_COMB (@lem5194933 _67769 x _67767 _67768) (@lem5195006 _67769 x _67767 _67768)). Qed.
Lemma lem5195009 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5195010 (x : Prop) : (x = x) = True.
Proof. exact (@lem5195009 Prop x). Qed.
Lemma lem5195011 (_67769 : real) (x : type1021) (_67767 : real -> Prop) (_67768 : real) : ((term664 _67769 x _67767 _67768) = (term664 _67769 x _67767 _67768)) = True.
Proof. exact (@lem5195010 (term664 _67769 x _67767 _67768)). Qed.
Lemma lem5195012 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : ((term582 _67768 x _67767 _67769) = (term667 _67768 x _67769 _67767)) = True.
Proof. exact (TRANS (@lem5195007 _67769 x _67767 _67768) (@lem5195011 _67769 x _67767 _67768)). Qed.
Lemma lem5195013 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : True = ((term582 _67768 x _67767 _67769) = (term667 _67768 x _67769 _67767)).
Proof. exact (SYM (@lem5195012 _67768 x _67769 _67767)). Qed.
Lemma lem5195014 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term582 _67768 x _67767 _67769) = (term667 _67768 x _67769 _67767).
Proof. exact (EQ_MP (@lem5195013 _67768 x _67769 _67767) (@lem0)). Qed.
Lemma lem5195015 (_67768 : real) (_67769 : real) (_67767 : real -> Prop) (x : type1021) (h1 : term444 x) : term667 _67768 x _67769 _67767.
Proof. exact (EQ_MP (@lem5195014 _67768 x _67769 _67767) (@lem5193889 _67768 _67767 _67769 x h1)). Qed.
Lemma lem5195017 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5195018 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term667 _67768 x _67769 _67767) = (term674 _67768 x _67767 _67769).
Proof. exact (@lem5195017 (term675 _67768 x _67769 _67767) (term108 _67767 _67769)). Qed.
Lemma lem5195020 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195021 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term676 _67768 x _67769 _67767) = (term677 _67768 x _67769 _67767).
Proof. exact (@lem5195020 (_67767 = (@EMPTY real)) (term669 _67768 x _67769 _67767)). Qed.
Lemma lem5195023 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195024 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term678 _67768 x _67769 _67767) = (term679 _67768 x _67769 _67767).
Proof. exact (@lem5195023 (term537 x _67767 _67768) (term536 x _67769 _67767)). Qed.
Lemma lem5195026 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5195027 (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term645 x _67767 _67768) = (term625 x _67767 _67768).
Proof. exact (@lem5195026 (term625 x _67767 _67768)). Qed.
Lemma lem5195028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5195029 (x : type1021) (_67767 : real -> Prop) (_67768 : real) : (term646 x _67767 _67768) = (term647 x _67767 _67768).
Proof. exact (MK_COMB (@lem5195028) (@lem5195027 x _67767 _67768)). Qed.
Lemma lem5195030 (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term589 x _67769 _67767) = (term589 x _67769 _67767).
Proof. exact (eq_refl (term589 x _67769 _67767)). Qed.
Lemma lem5195031 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term679 _67768 x _67769 _67767) = (term680 _67768 x _67769 _67767).
Proof. exact (MK_COMB (@lem5195029 x _67767 _67768) (@lem5195030 x _67769 _67767)). Qed.
Lemma lem5195032 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term678 _67768 x _67769 _67767) = (term680 _67768 x _67769 _67767).
Proof. exact (TRANS (@lem5195024 _67768 x _67769 _67767) (@lem5195031 _67768 x _67769 _67767)). Qed.
Lemma lem5195033 (_67767 : real -> Prop) : (term118 _67767) = (term118 _67767).
Proof. exact (eq_refl (term118 _67767)). Qed.
Lemma lem5195034 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term677 _67768 x _67769 _67767) = (term681 _67768 x _67769 _67767).
Proof. exact (MK_COMB (@lem5195033 _67767) (@lem5195032 _67768 x _67769 _67767)). Qed.
Lemma lem5195035 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term676 _67768 x _67769 _67767) = (term681 _67768 x _67769 _67767).
Proof. exact (TRANS (@lem5195021 _67768 x _67769 _67767) (@lem5195034 _67768 x _67769 _67767)). Qed.
Lemma lem5195036 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5195037 (_67768 : real) (x : type1021) (_67769 : real) (_67767 : real -> Prop) : (term682 _67768 x _67769 _67767) = (term683 _67768 x _67769 _67767).
Proof. exact (MK_COMB (@lem5195036) (@lem5195035 _67768 x _67769 _67767)). Qed.
Lemma lem5195038 (_67767 : real -> Prop) (_67769 : real) : (term108 _67767 _67769) = (term108 _67767 _67769).
Proof. exact (eq_refl (term108 _67767 _67769)). Qed.
Lemma lem5195039 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term674 _67768 x _67767 _67769) = (term684 _67768 x _67767 _67769).
Proof. exact (MK_COMB (@lem5195037 _67768 x _67769 _67767) (@lem5195038 _67767 _67769)). Qed.
Lemma lem5195040 (_67768 : real) (x : type1021) (_67767 : real -> Prop) (_67769 : real) : (term667 _67768 x _67769 _67767) = (term684 _67768 x _67767 _67769).
Proof. exact (TRANS (@lem5195018 _67768 x _67767 _67769) (@lem5195039 _67768 x _67767 _67769)). Qed.
Lemma lem5195042 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term685 x c' s.
Proof. exact (conj (@lem5194590 x s t c' h1 h2 h3 h4) (@lem5194867 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195043 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term686 x c' s.
Proof. exact (conj (@lem5194395 s h2) (@lem5195042 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195045 (_67768 : real) (_67767 : real -> Prop) (_67769 : real) (x : type1021) (h1 : term444 x) : term684 _67768 x _67767 _67769.
Proof. exact (EQ_MP (@lem5195040 _67768 x _67767 _67769) (@lem5195015 _67768 _67769 _67767 x h1)). Qed.
Lemma lem5195046 (s : real -> Prop) (c' : real) (x : type1021) (h1 : term444 x) : term687 x s c'.
Proof. exact (@lem5195045 c' s c' x h1). Qed.
Lemma lem5195049 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term108 s c'.
Proof. exact (@lem5195046 s c' x h1 (@lem5195043 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195050 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term160 s t c') : term688 s c'.
Proof. exact (fun h0 : term567 s c' => @lem5195049 x s t c' h1 h2 h0 h3). Qed.
Lemma lem5195052 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195053 (s : real -> Prop) (c' : real) : (term688 s c') = (term108 s c').
Proof. exact (@lem5195052 (term108 s c')). Qed.
Lemma lem5195054 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term160 s t c') : term108 s c'.
Proof. exact (EQ_MP (@lem5195053 s c') (@lem5195050 x s t c' h1 h2 h3)). Qed.
Lemma lem5195057 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5195059 (s : real -> Prop) (c' : real) : (term567 s c') = (term689 s c').
Proof. exact (@lem5195057 (term108 s c')). Qed.
Lemma lem5195062 (s : real -> Prop) (c' : real) (h1 : term567 s c') : term689 s c'.
Proof. exact (EQ_MP (@lem5195059 s c') (@lem5193825 s c' h1)). Qed.
Lemma lem5195065 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (@lem5195062 s c' h3 (@lem5195054 x s t c' h1 h2 h4)). Qed.
Lemma lem5195066 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : term690.
Proof. exact (fun h0 : ~ False => @lem5195065 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5195068 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195069 : term690 = False.
Proof. exact (@lem5195068 False). Qed.
Lemma lem5195070 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5195069) (@lem5195066 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195137 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5195138 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5195137 t h1). Qed.
Lemma lem5195140 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195141 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5195140 (t = (@EMPTY real))). Qed.
Lemma lem5195142 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5195141 t) (@lem5195138 t h1)). Qed.
Lemma lem5195144 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5195145 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5195144 t h1). Qed.
Lemma lem5195147 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195148 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5195147 (t = (@EMPTY real))). Qed.
Lemma lem5195149 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5195148 t) (@lem5195145 t h1)). Qed.
Lemma lem5195152 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (h1). Qed.
Lemma lem5195153 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term590 x c' t.
Proof. exact (fun h0 : term536 x c' t => @lem5195152 x c' t h1). Qed.
Lemma lem5195155 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195156 (x : type1021) (c' : real) (t : real -> Prop) : (term590 x c' t) = (term589 x c' t).
Proof. exact (@lem5195155 (term536 x c' t)). Qed.
Lemma lem5195157 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (EQ_MP (@lem5195156 x c' t) (@lem5195153 x c' t h1)). Qed.
Lemma lem5195160 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (h1). Qed.
Lemma lem5195161 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term591 t c'.
Proof. exact (fun h0 : term108 t c' => @lem5195160 t c' h1). Qed.
Lemma lem5195163 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195164 (t : real -> Prop) (c' : real) : (term591 t c') = (term567 t c').
Proof. exact (@lem5195163 (term108 t c')). Qed.
Lemma lem5195165 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (EQ_MP (@lem5195164 t c') (@lem5195161 t c' h1)). Qed.
Lemma lem5195198 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195199 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term592 x _67778 _67777 _67779) = (term593 x _67778 _67777 _67779).
Proof. exact (@lem5195198 (_67777 = (@EMPTY real)) (term536 x _67779 _67777) (term594 x _67778 _67777 _67779)). Qed.
Lemma lem5195215 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195216 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term595 x _67778 _67777 _67779) = (term596 _67778 x _67777 _67779).
Proof. exact (@lem5195215 (term536 x _67778 _67777) (term536 x _67779 _67777) (term108 _67777 _67779)). Qed.
Lemma lem5195232 (_67777 : real -> Prop) : (term289 _67777) = (term289 _67777).
Proof. exact (eq_refl (term289 _67777)). Qed.
Lemma lem5195233 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term593 x _67778 _67777 _67779) = (term581 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195232 _67777) (@lem5195216 _67778 x _67777 _67779)). Qed.
Lemma lem5195244 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term592 x _67778 _67777 _67779) = (term581 _67778 x _67777 _67779).
Proof. exact (TRANS (@lem5195199 x _67778 _67777 _67779) (@lem5195233 _67778 x _67777 _67779)). Qed.
Lemma lem5195245 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term597 _67778 x _67777 _67779) = (term597 _67778 x _67777 _67779).
Proof. exact (eq_refl (term597 _67778 x _67777 _67779)). Qed.
Lemma lem5195246 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : ((term581 _67778 x _67777 _67779) = (term592 x _67778 _67777 _67779)) = ((term581 _67778 x _67777 _67779) = (term581 _67778 x _67777 _67779)).
Proof. exact (MK_COMB (@lem5195245 _67778 x _67777 _67779) (@lem5195244 _67778 x _67777 _67779)). Qed.
Lemma lem5195248 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5195249 (x : Prop) : (x = x) = True.
Proof. exact (@lem5195248 Prop x). Qed.
Lemma lem5195250 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : ((term581 _67778 x _67777 _67779) = (term581 _67778 x _67777 _67779)) = True.
Proof. exact (@lem5195249 (term581 _67778 x _67777 _67779)). Qed.
Lemma lem5195251 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : ((term581 _67778 x _67777 _67779) = (term592 x _67778 _67777 _67779)) = True.
Proof. exact (TRANS (@lem5195246 _67778 x _67777 _67779) (@lem5195250 _67778 x _67777 _67779)). Qed.
Lemma lem5195252 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : True = ((term581 _67778 x _67777 _67779) = (term592 x _67778 _67777 _67779)).
Proof. exact (SYM (@lem5195251 x _67778 _67777 _67779)). Qed.
Lemma lem5195253 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term581 _67778 x _67777 _67779) = (term592 x _67778 _67777 _67779).
Proof. exact (EQ_MP (@lem5195252 x _67778 _67777 _67779) (@lem0)). Qed.
Lemma lem5195254 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term592 x _67778 _67777 _67779.
Proof. exact (EQ_MP (@lem5195253 x _67778 _67777 _67779) (@lem5194011 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5195256 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5195257 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term592 x _67778 _67777 _67779) = (term599 _67778 x _67779 _67777).
Proof. exact (@lem5195256 (term600 x _67778 _67777 _67779) (term536 x _67779 _67777)). Qed.
Lemma lem5195259 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195260 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term603 x _67778 _67777 _67779) = (term604 x _67778 _67777 _67779).
Proof. exact (@lem5195259 (_67777 = (@EMPTY real)) (term594 x _67778 _67777 _67779)). Qed.
Lemma lem5195262 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195263 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term605 x _67778 _67777 _67779) = (term606 x _67778 _67777 _67779).
Proof. exact (@lem5195262 (term536 x _67778 _67777) (term108 _67777 _67779)). Qed.
Lemma lem5195264 (_67777 : real -> Prop) : (term118 _67777) = (term118 _67777).
Proof. exact (eq_refl (term118 _67777)). Qed.
Lemma lem5195265 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term604 x _67778 _67777 _67779) = (term607 x _67778 _67777 _67779).
Proof. exact (MK_COMB (@lem5195264 _67777) (@lem5195263 x _67778 _67777 _67779)). Qed.
Lemma lem5195266 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term603 x _67778 _67777 _67779) = (term607 x _67778 _67777 _67779).
Proof. exact (TRANS (@lem5195260 x _67778 _67777 _67779) (@lem5195265 x _67778 _67777 _67779)). Qed.
Lemma lem5195267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5195268 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term608 x _67778 _67777 _67779) = (term609 x _67778 _67777 _67779).
Proof. exact (MK_COMB (@lem5195267) (@lem5195266 x _67778 _67777 _67779)). Qed.
Lemma lem5195269 (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term536 x _67779 _67777) = (term536 x _67779 _67777).
Proof. exact (eq_refl (term536 x _67779 _67777)). Qed.
Lemma lem5195270 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term599 _67778 x _67779 _67777) = (term610 _67778 x _67779 _67777).
Proof. exact (MK_COMB (@lem5195268 x _67778 _67777 _67779) (@lem5195269 x _67779 _67777)). Qed.
Lemma lem5195271 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term592 x _67778 _67777 _67779) = (term610 _67778 x _67779 _67777).
Proof. exact (TRANS (@lem5195257 _67778 x _67779 _67777) (@lem5195270 _67778 x _67779 _67777)). Qed.
Lemma lem5195273 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term589 x c' t) (h2 : term567 t c') : term611 x t c'.
Proof. exact (conj (@lem5195157 x c' t h1) (@lem5195165 t c' h2)). Qed.
Lemma lem5195274 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term31 t) (h2 : term589 x c' t) (h3 : term567 t c') : term612 x t c'.
Proof. exact (conj (@lem5195149 t h1) (@lem5195273 x t c' h2 h3)). Qed.
Lemma lem5195276 (_67778 : real) (_67779 : real) (_67777 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _67778 x _67779 _67777.
Proof. exact (EQ_MP (@lem5195271 _67778 x _67779 _67777) (@lem5195254 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5195277 (c' : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' t.
Proof. exact (@lem5195276 c' c' t x h1). Qed.
Lemma lem5195280 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term589 x c' t) (h4 : term567 t c') : term536 x c' t.
Proof. exact (@lem5195277 c' t x h1 (@lem5195274 x t c' h2 h3 h4)). Qed.
Lemma lem5195281 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') : term614 x c' t.
Proof. exact (fun h0 : term589 x c' t => @lem5195280 x t c' h1 h2 h0 h3). Qed.
Lemma lem5195283 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195284 (x : type1021) (c' : real) (t : real -> Prop) : (term614 x c' t) = (term536 x c' t).
Proof. exact (@lem5195283 (term536 x c' t)). Qed.
Lemma lem5195285 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') : term536 x c' t.
Proof. exact (EQ_MP (@lem5195284 x c' t) (@lem5195281 x t c' h1 h2 h3)). Qed.
Lemma lem5195291 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5195292 (c' : real) (_67781 : real) (t : real -> Prop) : (term130 t _67781 c') = (term616 c' _67781 t).
Proof. exact (@lem5195291 (real_le _67781 c') (term617 _67781 t)). Qed.
Lemma lem5195298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5195299 (c' : real) (_67781 : real) (t : real -> Prop) : (term618 t _67781 c') = (term619 c' _67781 t).
Proof. exact (MK_COMB (@lem5195298) (@lem5195292 c' _67781 t)). Qed.
Lemma lem5195305 (c' : real) (_67781 : real) (t : real -> Prop) : (term616 c' _67781 t) = (term616 c' _67781 t).
Proof. exact (eq_refl (term616 c' _67781 t)). Qed.
Lemma lem5195306 (c' : real) (_67781 : real) (t : real -> Prop) : ((term130 t _67781 c') = (term616 c' _67781 t)) = ((term616 c' _67781 t) = (term616 c' _67781 t)).
Proof. exact (MK_COMB (@lem5195299 c' _67781 t) (@lem5195305 c' _67781 t)). Qed.
Lemma lem5195308 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5195309 (x : Prop) : (x = x) = True.
Proof. exact (@lem5195308 Prop x). Qed.
Lemma lem5195310 (c' : real) (_67781 : real) (t : real -> Prop) : ((term616 c' _67781 t) = (term616 c' _67781 t)) = True.
Proof. exact (@lem5195309 (term616 c' _67781 t)). Qed.
Lemma lem5195311 (c' : real) (_67781 : real) (t : real -> Prop) : ((term130 t _67781 c') = (term616 c' _67781 t)) = True.
Proof. exact (TRANS (@lem5195306 c' _67781 t) (@lem5195310 c' _67781 t)). Qed.
Lemma lem5195312 (c' : real) (_67781 : real) (t : real -> Prop) : True = ((term130 t _67781 c') = (term616 c' _67781 t)).
Proof. exact (SYM (@lem5195311 c' _67781 t)). Qed.
Lemma lem5195313 (c' : real) (_67781 : real) (t : real -> Prop) : (term130 t _67781 c') = (term616 c' _67781 t).
Proof. exact (EQ_MP (@lem5195312 c' _67781 t) (@lem0)). Qed.
Lemma lem5195314 (_67781 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term616 c' _67781 t.
Proof. exact (EQ_MP (@lem5195313 c' _67781 t) (@lem5193961 _67781 s t c' h1)). Qed.
Lemma lem5195316 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5195317 (t : real -> Prop) (_67781 : real) (c' : real) : (term616 c' _67781 t) = (term620 t _67781 c').
Proof. exact (@lem5195316 (term617 _67781 t) (real_le _67781 c')). Qed.
Lemma lem5195319 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5195320 (_67781 : real) (t : real -> Prop) : (term622 _67781 t) = (@IN real _67781 t).
Proof. exact (@lem5195319 (@IN real _67781 t)). Qed.
Lemma lem5195321 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5195322 (_67781 : real) (t : real -> Prop) : (term623 _67781 t) = (term51 _67781 t).
Proof. exact (MK_COMB (@lem5195321) (@lem5195320 _67781 t)). Qed.
Lemma lem5195323 (_67781 : real) (c' : real) : (real_le _67781 c') = (real_le _67781 c').
Proof. exact (eq_refl (real_le _67781 c')). Qed.
Lemma lem5195324 (t : real -> Prop) (_67781 : real) (c' : real) : (term620 t _67781 c') = (term53 t _67781 c').
Proof. exact (MK_COMB (@lem5195322 _67781 t) (@lem5195323 _67781 c')). Qed.
Lemma lem5195325 (t : real -> Prop) (_67781 : real) (c' : real) : (term616 c' _67781 t) = (term53 t _67781 c').
Proof. exact (TRANS (@lem5195317 t _67781 c') (@lem5195324 t _67781 c')). Qed.
Lemma lem5195328 (_67781 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term53 t _67781 c'.
Proof. exact (EQ_MP (@lem5195325 t _67781 c') (@lem5195314 _67781 s t c' h1)). Qed.
Lemma lem5195329 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term624 x t c'.
Proof. exact (@lem5195328 (x t c') s t c' h1). Qed.
Lemma lem5195332 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term625 x t c'.
Proof. exact (@lem5195329 x s t c' h4 (@lem5195285 x t c' h1 h2 h3)). Qed.
Lemma lem5195333 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term626 x t c'.
Proof. exact (fun h0 : term537 x t c' => @lem5195332 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5195335 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195336 (x : type1021) (t : real -> Prop) (c' : real) : (term626 x t c') = (term625 x t c').
Proof. exact (@lem5195335 (term625 x t c')). Qed.
Lemma lem5195337 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term625 x t c'.
Proof. exact (EQ_MP (@lem5195336 x t c') (@lem5195333 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195339 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5195340 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5195339 t h1). Qed.
Lemma lem5195342 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195343 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5195342 (t = (@EMPTY real))). Qed.
Lemma lem5195344 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5195343 t) (@lem5195340 t h1)). Qed.
Lemma lem5195346 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5195347 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5195346 t h1). Qed.
Lemma lem5195349 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195350 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5195349 (t = (@EMPTY real))). Qed.
Lemma lem5195351 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5195350 t) (@lem5195347 t h1)). Qed.
Lemma lem5195354 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (h1). Qed.
Lemma lem5195355 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term590 x c' t.
Proof. exact (fun h0 : term536 x c' t => @lem5195354 x c' t h1). Qed.
Lemma lem5195357 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195358 (x : type1021) (c' : real) (t : real -> Prop) : (term590 x c' t) = (term589 x c' t).
Proof. exact (@lem5195357 (term536 x c' t)). Qed.
Lemma lem5195359 (x : type1021) (c' : real) (t : real -> Prop) (h1 : term589 x c' t) : term589 x c' t.
Proof. exact (EQ_MP (@lem5195358 x c' t) (@lem5195355 x c' t h1)). Qed.
Lemma lem5195362 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (h1). Qed.
Lemma lem5195363 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term591 t c'.
Proof. exact (fun h0 : term108 t c' => @lem5195362 t c' h1). Qed.
Lemma lem5195365 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195366 (t : real -> Prop) (c' : real) : (term591 t c') = (term567 t c').
Proof. exact (@lem5195365 (term108 t c')). Qed.
Lemma lem5195367 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (EQ_MP (@lem5195366 t c') (@lem5195363 t c' h1)). Qed.
Lemma lem5195368 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term589 x c' t) (h2 : term567 t c') : term611 x t c'.
Proof. exact (conj (@lem5195359 x c' t h1) (@lem5195367 t c' h2)). Qed.
Lemma lem5195369 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term31 t) (h2 : term589 x c' t) (h3 : term567 t c') : term612 x t c'.
Proof. exact (conj (@lem5195351 t h1) (@lem5195368 x t c' h2 h3)). Qed.
Lemma lem5195371 (_67778 : real) (_67779 : real) (_67777 : real -> Prop) (x : type1021) (h1 : term444 x) : term610 _67778 x _67779 _67777.
Proof. exact (EQ_MP (@lem5195271 _67778 x _67779 _67777) (@lem5195254 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5195372 (c' : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term613 x c' t.
Proof. exact (@lem5195371 c' c' t x h1). Qed.
Lemma lem5195375 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term589 x c' t) (h4 : term567 t c') : term536 x c' t.
Proof. exact (@lem5195372 c' t x h1 (@lem5195369 x t c' h2 h3 h4)). Qed.
Lemma lem5195376 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') : term614 x c' t.
Proof. exact (fun h0 : term589 x c' t => @lem5195375 x t c' h1 h2 h0 h3). Qed.
Lemma lem5195378 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195379 (x : type1021) (c' : real) (t : real -> Prop) : (term614 x c' t) = (term536 x c' t).
Proof. exact (@lem5195378 (term536 x c' t)). Qed.
Lemma lem5195380 (x : type1021) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') : term536 x c' t.
Proof. exact (EQ_MP (@lem5195379 x c' t) (@lem5195376 x t c' h1 h2 h3)). Qed.
Lemma lem5195382 (_67781 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term53 t _67781 c'.
Proof. exact (EQ_MP (@lem5195325 t _67781 c') (@lem5195314 _67781 s t c' h1)). Qed.
Lemma lem5195383 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term624 x t c'.
Proof. exact (@lem5195382 (x t c') s t c' h1). Qed.
Lemma lem5195386 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term625 x t c'.
Proof. exact (@lem5195383 x s t c' h4 (@lem5195380 x t c' h1 h2 h3)). Qed.
Lemma lem5195387 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term626 x t c'.
Proof. exact (fun h0 : term537 x t c' => @lem5195386 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5195389 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195390 (x : type1021) (t : real -> Prop) (c' : real) : (term626 x t c') = (term625 x t c').
Proof. exact (@lem5195389 (term625 x t c')). Qed.
Lemma lem5195391 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term625 x t c'.
Proof. exact (EQ_MP (@lem5195390 x t c') (@lem5195387 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195394 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (h1). Qed.
Lemma lem5195395 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term591 t c'.
Proof. exact (fun h0 : term108 t c' => @lem5195394 t c' h1). Qed.
Lemma lem5195397 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195398 (t : real -> Prop) (c' : real) : (term591 t c') = (term567 t c').
Proof. exact (@lem5195397 (term108 t c')). Qed.
Lemma lem5195399 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term567 t c'.
Proof. exact (EQ_MP (@lem5195398 t c') (@lem5195395 t c' h1)). Qed.
Lemma lem5195427 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5195428 (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term546 x _67777 _67779) = (term627 x _67777 _67779).
Proof. exact (@lem5195427 (term108 _67777 _67779) (term537 x _67777 _67779)). Qed.
Lemma lem5195434 (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term628 x _67777 _67778) = (term628 x _67777 _67778).
Proof. exact (eq_refl (term628 x _67777 _67778)). Qed.
Lemma lem5195435 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term629 _67778 x _67777 _67779) = (term630 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195434 x _67777 _67778) (@lem5195428 x _67777 _67779)). Qed.
Lemma lem5195439 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195440 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term630 _67778 x _67777 _67779) = (term631 _67778 x _67777 _67779).
Proof. exact (@lem5195439 (term108 _67777 _67779) (term537 x _67777 _67778) (term537 x _67777 _67779)). Qed.
Lemma lem5195456 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term629 _67778 x _67777 _67779) = (term631 _67778 x _67777 _67779).
Proof. exact (TRANS (@lem5195435 _67778 x _67777 _67779) (@lem5195440 _67778 x _67777 _67779)). Qed.
Lemma lem5195457 (_67777 : real -> Prop) : (term289 _67777) = (term289 _67777).
Proof. exact (eq_refl (term289 _67777)). Qed.
Lemma lem5195458 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term580 _67778 x _67777 _67779) = (term632 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195457 _67777) (@lem5195456 _67778 x _67777 _67779)). Qed.
Lemma lem5195469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5195470 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term633 _67778 x _67777 _67779) = (term634 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195469) (@lem5195458 _67778 x _67777 _67779)). Qed.
Lemma lem5195474 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195475 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term635 x _67778 _67777 _67779) = (term636 x _67778 _67777 _67779).
Proof. exact (@lem5195474 (_67777 = (@EMPTY real)) (term537 x _67777 _67779) (term637 x _67778 _67777 _67779)). Qed.
Lemma lem5195491 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195492 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term638 x _67778 _67777 _67779) = (term629 _67778 x _67777 _67779).
Proof. exact (@lem5195491 (term537 x _67777 _67778) (term537 x _67777 _67779) (term108 _67777 _67779)). Qed.
Lemma lem5195506 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5195507 (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term546 x _67777 _67779) = (term627 x _67777 _67779).
Proof. exact (@lem5195506 (term108 _67777 _67779) (term537 x _67777 _67779)). Qed.
Lemma lem5195513 (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term628 x _67777 _67778) = (term628 x _67777 _67778).
Proof. exact (eq_refl (term628 x _67777 _67778)). Qed.
Lemma lem5195514 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term629 _67778 x _67777 _67779) = (term630 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195513 x _67777 _67778) (@lem5195507 x _67777 _67779)). Qed.
Lemma lem5195518 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195519 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term630 _67778 x _67777 _67779) = (term631 _67778 x _67777 _67779).
Proof. exact (@lem5195518 (term108 _67777 _67779) (term537 x _67777 _67778) (term537 x _67777 _67779)). Qed.
Lemma lem5195535 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term629 _67778 x _67777 _67779) = (term631 _67778 x _67777 _67779).
Proof. exact (TRANS (@lem5195514 _67778 x _67777 _67779) (@lem5195519 _67778 x _67777 _67779)). Qed.
Lemma lem5195536 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term638 x _67778 _67777 _67779) = (term631 _67778 x _67777 _67779).
Proof. exact (TRANS (@lem5195492 _67778 x _67777 _67779) (@lem5195535 _67778 x _67777 _67779)). Qed.
Lemma lem5195537 (_67777 : real -> Prop) : (term289 _67777) = (term289 _67777).
Proof. exact (eq_refl (term289 _67777)). Qed.
Lemma lem5195538 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term636 x _67778 _67777 _67779) = (term632 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195537 _67777) (@lem5195536 _67778 x _67777 _67779)). Qed.
Lemma lem5195549 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term635 x _67778 _67777 _67779) = (term632 _67778 x _67777 _67779).
Proof. exact (TRANS (@lem5195475 x _67778 _67777 _67779) (@lem5195538 _67778 x _67777 _67779)). Qed.
Lemma lem5195550 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : ((term580 _67778 x _67777 _67779) = (term635 x _67778 _67777 _67779)) = ((term632 _67778 x _67777 _67779) = (term632 _67778 x _67777 _67779)).
Proof. exact (MK_COMB (@lem5195470 _67778 x _67777 _67779) (@lem5195549 _67778 x _67777 _67779)). Qed.
Lemma lem5195552 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5195553 (x : Prop) : (x = x) = True.
Proof. exact (@lem5195552 Prop x). Qed.
Lemma lem5195554 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : ((term632 _67778 x _67777 _67779) = (term632 _67778 x _67777 _67779)) = True.
Proof. exact (@lem5195553 (term632 _67778 x _67777 _67779)). Qed.
Lemma lem5195555 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : ((term580 _67778 x _67777 _67779) = (term635 x _67778 _67777 _67779)) = True.
Proof. exact (TRANS (@lem5195550 _67778 x _67777 _67779) (@lem5195554 _67778 x _67777 _67779)). Qed.
Lemma lem5195556 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : True = ((term580 _67778 x _67777 _67779) = (term635 x _67778 _67777 _67779)).
Proof. exact (SYM (@lem5195555 x _67778 _67777 _67779)). Qed.
Lemma lem5195557 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term580 _67778 x _67777 _67779) = (term635 x _67778 _67777 _67779).
Proof. exact (EQ_MP (@lem5195556 x _67778 _67777 _67779) (@lem0)). Qed.
Lemma lem5195558 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term635 x _67778 _67777 _67779.
Proof. exact (EQ_MP (@lem5195557 x _67778 _67777 _67779) (@lem5193995 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5195560 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5195561 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term635 x _67778 _67777 _67779) = (term639 _67778 x _67777 _67779).
Proof. exact (@lem5195560 (term640 x _67778 _67777 _67779) (term537 x _67777 _67779)). Qed.
Lemma lem5195563 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195564 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term641 x _67778 _67777 _67779) = (term642 x _67778 _67777 _67779).
Proof. exact (@lem5195563 (_67777 = (@EMPTY real)) (term637 x _67778 _67777 _67779)). Qed.
Lemma lem5195566 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195567 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term643 x _67778 _67777 _67779) = (term644 x _67778 _67777 _67779).
Proof. exact (@lem5195566 (term537 x _67777 _67778) (term108 _67777 _67779)). Qed.
Lemma lem5195569 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5195570 (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term645 x _67777 _67778) = (term625 x _67777 _67778).
Proof. exact (@lem5195569 (term625 x _67777 _67778)). Qed.
Lemma lem5195571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5195572 (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term646 x _67777 _67778) = (term647 x _67777 _67778).
Proof. exact (MK_COMB (@lem5195571) (@lem5195570 x _67777 _67778)). Qed.
Lemma lem5195573 (_67777 : real -> Prop) (_67779 : real) : (term567 _67777 _67779) = (term567 _67777 _67779).
Proof. exact (eq_refl (term567 _67777 _67779)). Qed.
Lemma lem5195574 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term644 x _67778 _67777 _67779) = (term648 x _67778 _67777 _67779).
Proof. exact (MK_COMB (@lem5195572 x _67777 _67778) (@lem5195573 _67777 _67779)). Qed.
Lemma lem5195575 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term643 x _67778 _67777 _67779) = (term648 x _67778 _67777 _67779).
Proof. exact (TRANS (@lem5195567 x _67778 _67777 _67779) (@lem5195574 x _67778 _67777 _67779)). Qed.
Lemma lem5195576 (_67777 : real -> Prop) : (term118 _67777) = (term118 _67777).
Proof. exact (eq_refl (term118 _67777)). Qed.
Lemma lem5195577 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term642 x _67778 _67777 _67779) = (term649 x _67778 _67777 _67779).
Proof. exact (MK_COMB (@lem5195576 _67777) (@lem5195575 x _67778 _67777 _67779)). Qed.
Lemma lem5195578 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term641 x _67778 _67777 _67779) = (term649 x _67778 _67777 _67779).
Proof. exact (TRANS (@lem5195564 x _67778 _67777 _67779) (@lem5195577 x _67778 _67777 _67779)). Qed.
Lemma lem5195579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5195580 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term650 x _67778 _67777 _67779) = (term651 x _67778 _67777 _67779).
Proof. exact (MK_COMB (@lem5195579) (@lem5195578 x _67778 _67777 _67779)). Qed.
Lemma lem5195581 (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term537 x _67777 _67779) = (term537 x _67777 _67779).
Proof. exact (eq_refl (term537 x _67777 _67779)). Qed.
Lemma lem5195582 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term639 _67778 x _67777 _67779) = (term652 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195580 x _67778 _67777 _67779) (@lem5195581 x _67777 _67779)). Qed.
Lemma lem5195583 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term635 x _67778 _67777 _67779) = (term652 _67778 x _67777 _67779).
Proof. exact (TRANS (@lem5195561 _67778 x _67777 _67779) (@lem5195582 _67778 x _67777 _67779)). Qed.
Lemma lem5195585 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term653 x t c'.
Proof. exact (conj (@lem5195391 x s t c' h1 h2 h3 h4) (@lem5195399 t c' h3)). Qed.
Lemma lem5195586 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term654 x t c'.
Proof. exact (conj (@lem5195344 t h2) (@lem5195585 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195588 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term652 _67778 x _67777 _67779.
Proof. exact (EQ_MP (@lem5195583 _67778 x _67777 _67779) (@lem5195558 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5195589 (t : real -> Prop) (c' : real) (x : type1021) (h1 : term444 x) : term655 x t c'.
Proof. exact (@lem5195588 c' t c' x h1). Qed.
Lemma lem5195592 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term537 x t c'.
Proof. exact (@lem5195589 t c' x h1 (@lem5195586 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195593 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term656 x t c'.
Proof. exact (fun h0 : term625 x t c' => @lem5195592 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5195595 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195596 (x : type1021) (t : real -> Prop) (c' : real) : (term656 x t c') = (term537 x t c').
Proof. exact (@lem5195595 (term625 x t c')). Qed.
Lemma lem5195597 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term537 x t c'.
Proof. exact (EQ_MP (@lem5195596 x t c') (@lem5195593 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195599 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5195602 (c' : real) (_67781 : real) (t : real -> Prop) : (term130 t _67781 c') = (term657 c' _67781 t).
Proof. exact (@lem5195599 (real_le _67781 c') (term617 _67781 t)). Qed.
Lemma lem5195605 (_67781 : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term657 c' _67781 t.
Proof. exact (EQ_MP (@lem5195602 c' _67781 t) (@lem5193961 _67781 s t c' h1)). Qed.
Lemma lem5195606 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term160 s t c') : term658 x c' t.
Proof. exact (@lem5195605 (x t c') s t c' h1). Qed.
Lemma lem5195609 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term589 x c' t.
Proof. exact (@lem5195606 x s t c' h4 (@lem5195597 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195610 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term590 x c' t.
Proof. exact (fun h0 : term536 x c' t => @lem5195609 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5195612 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195613 (x : type1021) (c' : real) (t : real -> Prop) : (term590 x c' t) = (term589 x c' t).
Proof. exact (@lem5195612 (term536 x c' t)). Qed.
Lemma lem5195614 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term589 x c' t.
Proof. exact (EQ_MP (@lem5195613 x c' t) (@lem5195610 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195632 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195633 (x : type1021) (_67778 : real) (_67777 : real -> Prop) (_67779 : real) : (term659 _67778 x _67777 _67779) = (term660 x _67778 _67777 _67779).
Proof. exact (@lem5195632 (term536 x _67779 _67777) (term537 x _67777 _67778) (term108 _67777 _67779)). Qed.
Lemma lem5195647 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5195648 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term637 x _67778 _67777 _67779) = (term661 _67779 x _67777 _67778).
Proof. exact (@lem5195647 (term108 _67777 _67779) (term537 x _67777 _67778)). Qed.
Lemma lem5195654 (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term662 x _67779 _67777) = (term662 x _67779 _67777).
Proof. exact (eq_refl (term662 x _67779 _67777)). Qed.
Lemma lem5195655 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term660 x _67778 _67777 _67779) = (term663 _67779 x _67777 _67778).
Proof. exact (MK_COMB (@lem5195654 x _67779 _67777) (@lem5195648 _67779 x _67777 _67778)). Qed.
Lemma lem5195666 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term659 _67778 x _67777 _67779) = (term663 _67779 x _67777 _67778).
Proof. exact (TRANS (@lem5195633 x _67778 _67777 _67779) (@lem5195655 _67779 x _67777 _67778)). Qed.
Lemma lem5195667 (_67777 : real -> Prop) : (term289 _67777) = (term289 _67777).
Proof. exact (eq_refl (term289 _67777)). Qed.
Lemma lem5195668 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term582 _67778 x _67777 _67779) = (term664 _67779 x _67777 _67778).
Proof. exact (MK_COMB (@lem5195667 _67777) (@lem5195666 _67779 x _67777 _67778)). Qed.
Lemma lem5195679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5195680 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term665 _67778 x _67777 _67779) = (term666 _67779 x _67777 _67778).
Proof. exact (MK_COMB (@lem5195679) (@lem5195668 _67779 x _67777 _67778)). Qed.
Lemma lem5195684 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195685 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term667 _67778 x _67779 _67777) = (term668 _67778 x _67779 _67777).
Proof. exact (@lem5195684 (_67777 = (@EMPTY real)) (term108 _67777 _67779) (term669 _67778 x _67779 _67777)). Qed.
Lemma lem5195711 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5195712 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term669 _67778 x _67779 _67777) = (term670 _67779 x _67777 _67778).
Proof. exact (@lem5195711 (term536 x _67779 _67777) (term537 x _67777 _67778)). Qed.
Lemma lem5195718 (_67777 : real -> Prop) (_67779 : real) : (term671 _67777 _67779) = (term671 _67777 _67779).
Proof. exact (eq_refl (term671 _67777 _67779)). Qed.
Lemma lem5195719 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term672 _67778 x _67779 _67777) = (term673 _67779 x _67777 _67778).
Proof. exact (MK_COMB (@lem5195718 _67777 _67779) (@lem5195712 _67779 x _67777 _67778)). Qed.
Lemma lem5195723 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195724 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term673 _67779 x _67777 _67778) = (term663 _67779 x _67777 _67778).
Proof. exact (@lem5195723 (term536 x _67779 _67777) (term108 _67777 _67779) (term537 x _67777 _67778)). Qed.
Lemma lem5195740 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term672 _67778 x _67779 _67777) = (term663 _67779 x _67777 _67778).
Proof. exact (TRANS (@lem5195719 _67779 x _67777 _67778) (@lem5195724 _67779 x _67777 _67778)). Qed.
Lemma lem5195741 (_67777 : real -> Prop) : (term289 _67777) = (term289 _67777).
Proof. exact (eq_refl (term289 _67777)). Qed.
Lemma lem5195742 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term668 _67778 x _67779 _67777) = (term664 _67779 x _67777 _67778).
Proof. exact (MK_COMB (@lem5195741 _67777) (@lem5195740 _67779 x _67777 _67778)). Qed.
Lemma lem5195753 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term667 _67778 x _67779 _67777) = (term664 _67779 x _67777 _67778).
Proof. exact (TRANS (@lem5195685 _67778 x _67779 _67777) (@lem5195742 _67779 x _67777 _67778)). Qed.
Lemma lem5195754 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : ((term582 _67778 x _67777 _67779) = (term667 _67778 x _67779 _67777)) = ((term664 _67779 x _67777 _67778) = (term664 _67779 x _67777 _67778)).
Proof. exact (MK_COMB (@lem5195680 _67779 x _67777 _67778) (@lem5195753 _67779 x _67777 _67778)). Qed.
Lemma lem5195756 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5195757 (x : Prop) : (x = x) = True.
Proof. exact (@lem5195756 Prop x). Qed.
Lemma lem5195758 (_67779 : real) (x : type1021) (_67777 : real -> Prop) (_67778 : real) : ((term664 _67779 x _67777 _67778) = (term664 _67779 x _67777 _67778)) = True.
Proof. exact (@lem5195757 (term664 _67779 x _67777 _67778)). Qed.
Lemma lem5195759 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : ((term582 _67778 x _67777 _67779) = (term667 _67778 x _67779 _67777)) = True.
Proof. exact (TRANS (@lem5195754 _67779 x _67777 _67778) (@lem5195758 _67779 x _67777 _67778)). Qed.
Lemma lem5195760 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : True = ((term582 _67778 x _67777 _67779) = (term667 _67778 x _67779 _67777)).
Proof. exact (SYM (@lem5195759 _67778 x _67779 _67777)). Qed.
Lemma lem5195761 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term582 _67778 x _67777 _67779) = (term667 _67778 x _67779 _67777).
Proof. exact (EQ_MP (@lem5195760 _67778 x _67779 _67777) (@lem0)). Qed.
Lemma lem5195762 (_67778 : real) (_67779 : real) (_67777 : real -> Prop) (x : type1021) (h1 : term444 x) : term667 _67778 x _67779 _67777.
Proof. exact (EQ_MP (@lem5195761 _67778 x _67779 _67777) (@lem5194027 _67778 _67777 _67779 x h1)). Qed.
Lemma lem5195764 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5195765 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term667 _67778 x _67779 _67777) = (term674 _67778 x _67777 _67779).
Proof. exact (@lem5195764 (term675 _67778 x _67779 _67777) (term108 _67777 _67779)). Qed.
Lemma lem5195767 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195768 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term676 _67778 x _67779 _67777) = (term677 _67778 x _67779 _67777).
Proof. exact (@lem5195767 (_67777 = (@EMPTY real)) (term669 _67778 x _67779 _67777)). Qed.
Lemma lem5195770 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5195771 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term678 _67778 x _67779 _67777) = (term679 _67778 x _67779 _67777).
Proof. exact (@lem5195770 (term537 x _67777 _67778) (term536 x _67779 _67777)). Qed.
Lemma lem5195773 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5195774 (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term645 x _67777 _67778) = (term625 x _67777 _67778).
Proof. exact (@lem5195773 (term625 x _67777 _67778)). Qed.
Lemma lem5195775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5195776 (x : type1021) (_67777 : real -> Prop) (_67778 : real) : (term646 x _67777 _67778) = (term647 x _67777 _67778).
Proof. exact (MK_COMB (@lem5195775) (@lem5195774 x _67777 _67778)). Qed.
Lemma lem5195777 (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term589 x _67779 _67777) = (term589 x _67779 _67777).
Proof. exact (eq_refl (term589 x _67779 _67777)). Qed.
Lemma lem5195778 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term679 _67778 x _67779 _67777) = (term680 _67778 x _67779 _67777).
Proof. exact (MK_COMB (@lem5195776 x _67777 _67778) (@lem5195777 x _67779 _67777)). Qed.
Lemma lem5195779 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term678 _67778 x _67779 _67777) = (term680 _67778 x _67779 _67777).
Proof. exact (TRANS (@lem5195771 _67778 x _67779 _67777) (@lem5195778 _67778 x _67779 _67777)). Qed.
Lemma lem5195780 (_67777 : real -> Prop) : (term118 _67777) = (term118 _67777).
Proof. exact (eq_refl (term118 _67777)). Qed.
Lemma lem5195781 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term677 _67778 x _67779 _67777) = (term681 _67778 x _67779 _67777).
Proof. exact (MK_COMB (@lem5195780 _67777) (@lem5195779 _67778 x _67779 _67777)). Qed.
Lemma lem5195782 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term676 _67778 x _67779 _67777) = (term681 _67778 x _67779 _67777).
Proof. exact (TRANS (@lem5195768 _67778 x _67779 _67777) (@lem5195781 _67778 x _67779 _67777)). Qed.
Lemma lem5195783 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5195784 (_67778 : real) (x : type1021) (_67779 : real) (_67777 : real -> Prop) : (term682 _67778 x _67779 _67777) = (term683 _67778 x _67779 _67777).
Proof. exact (MK_COMB (@lem5195783) (@lem5195782 _67778 x _67779 _67777)). Qed.
Lemma lem5195785 (_67777 : real -> Prop) (_67779 : real) : (term108 _67777 _67779) = (term108 _67777 _67779).
Proof. exact (eq_refl (term108 _67777 _67779)). Qed.
Lemma lem5195786 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term674 _67778 x _67777 _67779) = (term684 _67778 x _67777 _67779).
Proof. exact (MK_COMB (@lem5195784 _67778 x _67779 _67777) (@lem5195785 _67777 _67779)). Qed.
Lemma lem5195787 (_67778 : real) (x : type1021) (_67777 : real -> Prop) (_67779 : real) : (term667 _67778 x _67779 _67777) = (term684 _67778 x _67777 _67779).
Proof. exact (TRANS (@lem5195765 _67778 x _67777 _67779) (@lem5195786 _67778 x _67777 _67779)). Qed.
Lemma lem5195789 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term685 x c' t.
Proof. exact (conj (@lem5195337 x s t c' h1 h2 h3 h4) (@lem5195614 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195790 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term686 x c' t.
Proof. exact (conj (@lem5195142 t h2) (@lem5195789 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195792 (_67778 : real) (_67777 : real -> Prop) (_67779 : real) (x : type1021) (h1 : term444 x) : term684 _67778 x _67777 _67779.
Proof. exact (EQ_MP (@lem5195787 _67778 x _67777 _67779) (@lem5195762 _67778 _67779 _67777 x h1)). Qed.
Lemma lem5195793 (t : real -> Prop) (c' : real) (x : type1021) (h1 : term444 x) : term687 x t c'.
Proof. exact (@lem5195792 c' t c' x h1). Qed.
Lemma lem5195796 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term108 t c'.
Proof. exact (@lem5195793 t c' x h1 (@lem5195790 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195797 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term160 s t c') : term688 t c'.
Proof. exact (fun h0 : term567 t c' => @lem5195796 x s t c' h1 h2 h0 h3). Qed.
Lemma lem5195799 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195800 (t : real -> Prop) (c' : real) : (term688 t c') = (term108 t c').
Proof. exact (@lem5195799 (term108 t c')). Qed.
Lemma lem5195801 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term160 s t c') : term108 t c'.
Proof. exact (EQ_MP (@lem5195800 t c') (@lem5195797 x s t c' h1 h2 h3)). Qed.
Lemma lem5195804 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5195806 (t : real -> Prop) (c' : real) : (term567 t c') = (term689 t c').
Proof. exact (@lem5195804 (term108 t c')). Qed.
Lemma lem5195809 (t : real -> Prop) (c' : real) (h1 : term567 t c') : term689 t c'.
Proof. exact (EQ_MP (@lem5195806 t c') (@lem5193963 t c' h1)). Qed.
Lemma lem5195812 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (@lem5195809 t c' h3 (@lem5195801 x s t c' h1 h2 h4)). Qed.
Lemma lem5195813 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : term690.
Proof. exact (fun h0 : ~ False => @lem5195812 x s t c' h1 h2 h3 h4). Qed.
Lemma lem5195815 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195816 : term690 = False.
Proof. exact (@lem5195815 False). Qed.
Lemma lem5195817 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5195816) (@lem5195813 x s t c' h1 h2 h3 h4)). Qed.
Lemma lem5195884 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5195885 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5195884 s h1). Qed.
Lemma lem5195887 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195888 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5195887 (s = (@EMPTY real))). Qed.
Lemma lem5195889 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5195888 s) (@lem5195885 s h1)). Qed.
Lemma lem5195891 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (h1). Qed.
Lemma lem5195892 (s : real -> Prop) (h1 : term31 s) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5195891 s h1). Qed.
Lemma lem5195894 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195895 (s : real -> Prop) : (term587 s) = (term31 s).
Proof. exact (@lem5195894 (s = (@EMPTY real))). Qed.
Lemma lem5195896 (s : real -> Prop) (h1 : term31 s) : term31 s.
Proof. exact (EQ_MP (@lem5195895 s) (@lem5195892 s h1)). Qed.
Lemma lem5195898 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : @IN real x' s.
Proof. exact (proj1 (@lem5192478 s x' c' h1)). Qed.
Lemma lem5195899 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : term691 x' s.
Proof. exact (fun h0 : term617 x' s => @lem5195898 s x' c' h1). Qed.
Lemma lem5195901 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5195902 (x' : real) (s : real -> Prop) : (term691 x' s) = (@IN real x' s).
Proof. exact (@lem5195901 (@IN real x' s)). Qed.
Lemma lem5195903 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : @IN real x' s.
Proof. exact (EQ_MP (@lem5195902 x' s) (@lem5195899 s x' c' h1)). Qed.
Lemma lem5195906 (x' : real) (s : real -> Prop) (h1 : term692 x' s) : term692 x' s.
Proof. exact (h1). Qed.
Lemma lem5195907 (x' : real) (s : real -> Prop) (h1 : term692 x' s) : term693 x' s.
Proof. exact (fun h0 : term294 x' s => @lem5195906 x' s h1). Qed.
Lemma lem5195909 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5195910 (x' : real) (s : real -> Prop) : (term693 x' s) = (term692 x' s).
Proof. exact (@lem5195909 (term294 x' s)). Qed.
Lemma lem5195911 (x' : real) (s : real -> Prop) (h1 : term692 x' s) : term692 x' s.
Proof. exact (EQ_MP (@lem5195910 x' s) (@lem5195907 x' s h1)). Qed.
Lemma lem5195939 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5195940 (_67789 : real) (_67787 : real -> Prop) : (term293 _67789 _67787) = (term694 _67789 _67787).
Proof. exact (@lem5195939 (term294 _67789 _67787) (term617 _67789 _67787)). Qed.
Lemma lem5195946 (x : type1021) (_67788 : real) (_67787 : real -> Prop) : (term662 x _67788 _67787) = (term662 x _67788 _67787).
Proof. exact (eq_refl (term662 x _67788 _67787)). Qed.
Lemma lem5195947 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term695 x _67788 _67789 _67787) = (term696 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5195946 x _67788 _67787) (@lem5195940 _67789 _67787)). Qed.
Lemma lem5195958 (_67787 : real -> Prop) : (term289 _67787) = (term289 _67787).
Proof. exact (eq_refl (term289 _67787)). Qed.
Lemma lem5195959 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term585 x _67788 _67789 _67787) = (term697 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5195958 _67787) (@lem5195947 x _67788 _67789 _67787)). Qed.
Lemma lem5195970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5195971 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term698 x _67788 _67789 _67787) = (term699 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5195970) (@lem5195959 x _67788 _67789 _67787)). Qed.
Lemma lem5195975 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5195976 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term700 x _67788 _67789 _67787) = (term585 x _67788 _67789 _67787).
Proof. exact (@lem5195975 (_67787 = (@EMPTY real)) (term536 x _67788 _67787) (term293 _67789 _67787)). Qed.
Lemma lem5196002 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196003 (_67789 : real) (_67787 : real -> Prop) : (term293 _67789 _67787) = (term694 _67789 _67787).
Proof. exact (@lem5196002 (term294 _67789 _67787) (term617 _67789 _67787)). Qed.
Lemma lem5196009 (x : type1021) (_67788 : real) (_67787 : real -> Prop) : (term662 x _67788 _67787) = (term662 x _67788 _67787).
Proof. exact (eq_refl (term662 x _67788 _67787)). Qed.
Lemma lem5196010 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term695 x _67788 _67789 _67787) = (term696 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5196009 x _67788 _67787) (@lem5196003 _67789 _67787)). Qed.
Lemma lem5196021 (_67787 : real -> Prop) : (term289 _67787) = (term289 _67787).
Proof. exact (eq_refl (term289 _67787)). Qed.
Lemma lem5196022 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term585 x _67788 _67789 _67787) = (term697 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5196021 _67787) (@lem5196010 x _67788 _67789 _67787)). Qed.
Lemma lem5196033 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term700 x _67788 _67789 _67787) = (term697 x _67788 _67789 _67787).
Proof. exact (TRANS (@lem5195976 x _67788 _67789 _67787) (@lem5196022 x _67788 _67789 _67787)). Qed.
Lemma lem5196034 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : ((term585 x _67788 _67789 _67787) = (term700 x _67788 _67789 _67787)) = ((term697 x _67788 _67789 _67787) = (term697 x _67788 _67789 _67787)).
Proof. exact (MK_COMB (@lem5195971 x _67788 _67789 _67787) (@lem5196033 x _67788 _67789 _67787)). Qed.
Lemma lem5196036 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5196037 (x : Prop) : (x = x) = True.
Proof. exact (@lem5196036 Prop x). Qed.
Lemma lem5196038 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : ((term697 x _67788 _67789 _67787) = (term697 x _67788 _67789 _67787)) = True.
Proof. exact (@lem5196037 (term697 x _67788 _67789 _67787)). Qed.
Lemma lem5196039 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : ((term585 x _67788 _67789 _67787) = (term700 x _67788 _67789 _67787)) = True.
Proof. exact (TRANS (@lem5196034 x _67788 _67789 _67787) (@lem5196038 x _67788 _67789 _67787)). Qed.
Lemma lem5196040 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : True = ((term585 x _67788 _67789 _67787) = (term700 x _67788 _67789 _67787)).
Proof. exact (SYM (@lem5196039 x _67788 _67789 _67787)). Qed.
Lemma lem5196041 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term585 x _67788 _67789 _67787) = (term700 x _67788 _67789 _67787).
Proof. exact (EQ_MP (@lem5196040 x _67788 _67789 _67787) (@lem0)). Qed.
Lemma lem5196042 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term700 x _67788 _67789 _67787.
Proof. exact (EQ_MP (@lem5196041 x _67788 _67789 _67787) (@lem5194175 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5196044 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5196045 (_67789 : real) (x : type1021) (_67788 : real) (_67787 : real -> Prop) : (term700 x _67788 _67789 _67787) = (term701 _67789 x _67788 _67787).
Proof. exact (@lem5196044 (term702 _67789 _67787) (term536 x _67788 _67787)). Qed.
Lemma lem5196047 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196048 (_67789 : real) (_67787 : real -> Prop) : (term703 _67789 _67787) = (term704 _67789 _67787).
Proof. exact (@lem5196047 (_67787 = (@EMPTY real)) (term293 _67789 _67787)). Qed.
Lemma lem5196050 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196051 (_67789 : real) (_67787 : real -> Prop) : (term705 _67789 _67787) = (term706 _67789 _67787).
Proof. exact (@lem5196050 (term617 _67789 _67787) (term294 _67789 _67787)). Qed.
Lemma lem5196053 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196054 (_67789 : real) (_67787 : real -> Prop) : (term622 _67789 _67787) = (@IN real _67789 _67787).
Proof. exact (@lem5196053 (@IN real _67789 _67787)). Qed.
Lemma lem5196055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5196056 (_67789 : real) (_67787 : real -> Prop) : (term707 _67789 _67787) = (term708 _67789 _67787).
Proof. exact (MK_COMB (@lem5196055) (@lem5196054 _67789 _67787)). Qed.
Lemma lem5196057 (_67789 : real) (_67787 : real -> Prop) : (term692 _67789 _67787) = (term692 _67789 _67787).
Proof. exact (eq_refl (term692 _67789 _67787)). Qed.
Lemma lem5196058 (_67789 : real) (_67787 : real -> Prop) : (term706 _67789 _67787) = (term709 _67789 _67787).
Proof. exact (MK_COMB (@lem5196056 _67789 _67787) (@lem5196057 _67789 _67787)). Qed.
Lemma lem5196059 (_67789 : real) (_67787 : real -> Prop) : (term705 _67789 _67787) = (term709 _67789 _67787).
Proof. exact (TRANS (@lem5196051 _67789 _67787) (@lem5196058 _67789 _67787)). Qed.
Lemma lem5196060 (_67787 : real -> Prop) : (term118 _67787) = (term118 _67787).
Proof. exact (eq_refl (term118 _67787)). Qed.
Lemma lem5196061 (_67789 : real) (_67787 : real -> Prop) : (term704 _67789 _67787) = (term710 _67789 _67787).
Proof. exact (MK_COMB (@lem5196060 _67787) (@lem5196059 _67789 _67787)). Qed.
Lemma lem5196062 (_67789 : real) (_67787 : real -> Prop) : (term703 _67789 _67787) = (term710 _67789 _67787).
Proof. exact (TRANS (@lem5196048 _67789 _67787) (@lem5196061 _67789 _67787)). Qed.
Lemma lem5196063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5196064 (_67789 : real) (_67787 : real -> Prop) : (term711 _67789 _67787) = (term712 _67789 _67787).
Proof. exact (MK_COMB (@lem5196063) (@lem5196062 _67789 _67787)). Qed.
Lemma lem5196065 (x : type1021) (_67788 : real) (_67787 : real -> Prop) : (term536 x _67788 _67787) = (term536 x _67788 _67787).
Proof. exact (eq_refl (term536 x _67788 _67787)). Qed.
Lemma lem5196066 (_67789 : real) (x : type1021) (_67788 : real) (_67787 : real -> Prop) : (term701 _67789 x _67788 _67787) = (term713 _67789 x _67788 _67787).
Proof. exact (MK_COMB (@lem5196064 _67789 _67787) (@lem5196065 x _67788 _67787)). Qed.
Lemma lem5196067 (_67789 : real) (x : type1021) (_67788 : real) (_67787 : real -> Prop) : (term700 x _67788 _67789 _67787) = (term713 _67789 x _67788 _67787).
Proof. exact (TRANS (@lem5196045 _67789 x _67788 _67787) (@lem5196066 _67789 x _67788 _67787)). Qed.
Lemma lem5196069 (s : real -> Prop) (x' : real) (c' : real) (h1 : term692 x' s) (h2 : term134 s x' c') : term709 x' s.
Proof. exact (conj (@lem5195903 s x' c' h2) (@lem5195911 x' s h1)). Qed.
Lemma lem5196070 (s : real -> Prop) (x' : real) (c' : real) (h1 : term31 s) (h2 : term692 x' s) (h3 : term134 s x' c') : term710 x' s.
Proof. exact (conj (@lem5195896 s h1) (@lem5196069 s x' c' h2 h3)). Qed.
Lemma lem5196072 (_67789 : real) (_67788 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term713 _67789 x _67788 _67787.
Proof. exact (EQ_MP (@lem5196067 _67789 x _67788 _67787) (@lem5196042 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5196073 (x' : real) (_67788 : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term713 x' x _67788 s.
Proof. exact (@lem5196072 x' _67788 s x h1). Qed.
Lemma lem5196076 (_67788 : real) (x : type1021) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 x' s) (h4 : term134 s x' c') : term536 x _67788 s.
Proof. exact (@lem5196073 x' _67788 s x h1 (@lem5196070 s x' c' h2 h3 h4)). Qed.
Lemma lem5196077 (b : real) (x : type1021) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 x' s) (h4 : term134 s x' c') : term536 x b s.
Proof. exact (@lem5196076 b x s x' c' h1 h2 h3 h4). Qed.
Lemma lem5196078 (b : real) (x : type1021) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 x' s) (h4 : term134 s x' c') : term614 x b s.
Proof. exact (fun h0 : term589 x b s => @lem5196077 b x s x' c' h1 h2 h3 h4). Qed.
Lemma lem5196080 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196081 (x : type1021) (b : real) (s : real -> Prop) : (term614 x b s) = (term536 x b s).
Proof. exact (@lem5196080 (term536 x b s)). Qed.
Lemma lem5196082 (b : real) (x : type1021) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term692 x' s) (h4 : term134 s x' c') : term536 x b s.
Proof. exact (EQ_MP (@lem5196081 x b s) (@lem5196078 b x s x' c' h1 h2 h3 h4)). Qed.
Lemma lem5196088 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196089 (b : real) (_67782 : real) (s : real -> Prop) : (term130 s _67782 b) = (term616 b _67782 s).
Proof. exact (@lem5196088 (real_le _67782 b) (term617 _67782 s)). Qed.
Lemma lem5196095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5196096 (b : real) (_67782 : real) (s : real -> Prop) : (term618 s _67782 b) = (term619 b _67782 s).
Proof. exact (MK_COMB (@lem5196095) (@lem5196089 b _67782 s)). Qed.
Lemma lem5196102 (b : real) (_67782 : real) (s : real -> Prop) : (term616 b _67782 s) = (term616 b _67782 s).
Proof. exact (eq_refl (term616 b _67782 s)). Qed.
Lemma lem5196103 (b : real) (_67782 : real) (s : real -> Prop) : ((term130 s _67782 b) = (term616 b _67782 s)) = ((term616 b _67782 s) = (term616 b _67782 s)).
Proof. exact (MK_COMB (@lem5196096 b _67782 s) (@lem5196102 b _67782 s)). Qed.
Lemma lem5196105 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5196106 (x : Prop) : (x = x) = True.
Proof. exact (@lem5196105 Prop x). Qed.
Lemma lem5196107 (b : real) (_67782 : real) (s : real -> Prop) : ((term616 b _67782 s) = (term616 b _67782 s)) = True.
Proof. exact (@lem5196106 (term616 b _67782 s)). Qed.
Lemma lem5196108 (b : real) (_67782 : real) (s : real -> Prop) : ((term130 s _67782 b) = (term616 b _67782 s)) = True.
Proof. exact (TRANS (@lem5196103 b _67782 s) (@lem5196107 b _67782 s)). Qed.
Lemma lem5196109 (b : real) (_67782 : real) (s : real -> Prop) : True = ((term130 s _67782 b) = (term616 b _67782 s)).
Proof. exact (SYM (@lem5196108 b _67782 s)). Qed.
Lemma lem5196110 (b : real) (_67782 : real) (s : real -> Prop) : (term130 s _67782 b) = (term616 b _67782 s).
Proof. exact (EQ_MP (@lem5196109 b _67782 s) (@lem0)). Qed.
Lemma lem5196111 (_67782 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term616 b _67782 s.
Proof. exact (EQ_MP (@lem5196110 b _67782 s) (@lem5194069 _67782 s b h1)). Qed.
Lemma lem5196113 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5196114 (s : real -> Prop) (_67782 : real) (b : real) : (term616 b _67782 s) = (term620 s _67782 b).
Proof. exact (@lem5196113 (term617 _67782 s) (real_le _67782 b)). Qed.
Lemma lem5196116 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196117 (_67782 : real) (s : real -> Prop) : (term622 _67782 s) = (@IN real _67782 s).
Proof. exact (@lem5196116 (@IN real _67782 s)). Qed.
Lemma lem5196118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5196119 (_67782 : real) (s : real -> Prop) : (term623 _67782 s) = (term51 _67782 s).
Proof. exact (MK_COMB (@lem5196118) (@lem5196117 _67782 s)). Qed.
Lemma lem5196120 (_67782 : real) (b : real) : (real_le _67782 b) = (real_le _67782 b).
Proof. exact (eq_refl (real_le _67782 b)). Qed.
Lemma lem5196121 (s : real -> Prop) (_67782 : real) (b : real) : (term620 s _67782 b) = (term53 s _67782 b).
Proof. exact (MK_COMB (@lem5196119 _67782 s) (@lem5196120 _67782 b)). Qed.
Lemma lem5196122 (s : real -> Prop) (_67782 : real) (b : real) : (term616 b _67782 s) = (term53 s _67782 b).
Proof. exact (TRANS (@lem5196114 s _67782 b) (@lem5196121 s _67782 b)). Qed.
Lemma lem5196125 (_67782 : real) (s : real -> Prop) (b : real) (h1 : term34 s b) : term53 s _67782 b.
Proof. exact (EQ_MP (@lem5196122 s _67782 b) (@lem5196111 _67782 s b h1)). Qed.
Lemma lem5196126 (x : type1021) (s : real -> Prop) (b : real) (h1 : term34 s b) : term624 x s b.
Proof. exact (@lem5196125 (x s b) s b h1). Qed.
Lemma lem5196129 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 x' s) (h5 : term134 s x' c') : term625 x s b.
Proof. exact (@lem5196126 x s b h2 (@lem5196082 b x s x' c' h1 h3 h4 h5)). Qed.
Lemma lem5196130 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 x' s) (h5 : term134 s x' c') : term626 x s b.
Proof. exact (fun h0 : term537 x s b => @lem5196129 x b s x' c' h1 h2 h3 h4 h5). Qed.
Lemma lem5196132 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196133 (x : type1021) (s : real -> Prop) (b : real) : (term626 x s b) = (term625 x s b).
Proof. exact (@lem5196132 (term625 x s b)). Qed.
Lemma lem5196134 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 x' s) (h5 : term134 s x' c') : term625 x s b.
Proof. exact (EQ_MP (@lem5196133 x s b) (@lem5196130 x b s x' c' h1 h2 h3 h4 h5)). Qed.
Lemma lem5196136 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : @IN real x' s.
Proof. exact (proj1 (@lem5192478 s x' c' h1)). Qed.
Lemma lem5196137 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : term691 x' s.
Proof. exact (fun h0 : term617 x' s => @lem5196136 s x' c' h1). Qed.
Lemma lem5196139 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196140 (x' : real) (s : real -> Prop) : (term691 x' s) = (@IN real x' s).
Proof. exact (@lem5196139 (@IN real x' s)). Qed.
Lemma lem5196141 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : @IN real x' s.
Proof. exact (EQ_MP (@lem5196140 x' s) (@lem5196137 s x' c' h1)). Qed.
Lemma lem5196159 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196160 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term714 x _67788 _67789 _67787) = (term715 x _67788 _67789 _67787).
Proof. exact (@lem5196159 (term617 _67789 _67787) (term537 x _67787 _67788) (term294 _67789 _67787)). Qed.
Lemma lem5196174 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196175 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term716 x _67788 _67789 _67787) = (term717 _67789 x _67787 _67788).
Proof. exact (@lem5196174 (term294 _67789 _67787) (term537 x _67787 _67788)). Qed.
Lemma lem5196181 (_67789 : real) (_67787 : real -> Prop) : (term718 _67789 _67787) = (term718 _67789 _67787).
Proof. exact (eq_refl (term718 _67789 _67787)). Qed.
Lemma lem5196182 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term715 x _67788 _67789 _67787) = (term719 _67789 x _67787 _67788).
Proof. exact (MK_COMB (@lem5196181 _67789 _67787) (@lem5196175 _67789 x _67787 _67788)). Qed.
Lemma lem5196186 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196187 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term719 _67789 x _67787 _67788) = (term720 _67789 x _67787 _67788).
Proof. exact (@lem5196186 (term294 _67789 _67787) (term617 _67789 _67787) (term537 x _67787 _67788)). Qed.
Lemma lem5196203 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term715 x _67788 _67789 _67787) = (term720 _67789 x _67787 _67788).
Proof. exact (TRANS (@lem5196182 _67789 x _67787 _67788) (@lem5196187 _67789 x _67787 _67788)). Qed.
Lemma lem5196204 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term714 x _67788 _67789 _67787) = (term720 _67789 x _67787 _67788).
Proof. exact (TRANS (@lem5196160 x _67788 _67789 _67787) (@lem5196203 _67789 x _67787 _67788)). Qed.
Lemma lem5196205 (_67787 : real -> Prop) : (term289 _67787) = (term289 _67787).
Proof. exact (eq_refl (term289 _67787)). Qed.
Lemma lem5196206 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term586 x _67788 _67789 _67787) = (term721 _67789 x _67787 _67788).
Proof. exact (MK_COMB (@lem5196205 _67787) (@lem5196204 _67789 x _67787 _67788)). Qed.
Lemma lem5196217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5196218 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term722 x _67788 _67789 _67787) = (term723 _67789 x _67787 _67788).
Proof. exact (MK_COMB (@lem5196217) (@lem5196206 _67789 x _67787 _67788)). Qed.
Lemma lem5196222 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196223 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term724 x _67788 _67789 _67787) = (term725 x _67788 _67789 _67787).
Proof. exact (@lem5196222 (_67787 = (@EMPTY real)) (term294 _67789 _67787) (term726 x _67788 _67789 _67787)). Qed.
Lemma lem5196249 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196250 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term726 x _67788 _67789 _67787) = (term727 _67789 x _67787 _67788).
Proof. exact (@lem5196249 (term617 _67789 _67787) (term537 x _67787 _67788)). Qed.
Lemma lem5196256 (_67789 : real) (_67787 : real -> Prop) : (term728 _67789 _67787) = (term728 _67789 _67787).
Proof. exact (eq_refl (term728 _67789 _67787)). Qed.
Lemma lem5196257 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term729 x _67788 _67789 _67787) = (term720 _67789 x _67787 _67788).
Proof. exact (MK_COMB (@lem5196256 _67789 _67787) (@lem5196250 _67789 x _67787 _67788)). Qed.
Lemma lem5196268 (_67787 : real -> Prop) : (term289 _67787) = (term289 _67787).
Proof. exact (eq_refl (term289 _67787)). Qed.
Lemma lem5196269 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term725 x _67788 _67789 _67787) = (term721 _67789 x _67787 _67788).
Proof. exact (MK_COMB (@lem5196268 _67787) (@lem5196257 _67789 x _67787 _67788)). Qed.
Lemma lem5196280 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term724 x _67788 _67789 _67787) = (term721 _67789 x _67787 _67788).
Proof. exact (TRANS (@lem5196223 x _67788 _67789 _67787) (@lem5196269 _67789 x _67787 _67788)). Qed.
Lemma lem5196281 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : ((term586 x _67788 _67789 _67787) = (term724 x _67788 _67789 _67787)) = ((term721 _67789 x _67787 _67788) = (term721 _67789 x _67787 _67788)).
Proof. exact (MK_COMB (@lem5196218 _67789 x _67787 _67788) (@lem5196280 _67789 x _67787 _67788)). Qed.
Lemma lem5196283 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5196284 (x : Prop) : (x = x) = True.
Proof. exact (@lem5196283 Prop x). Qed.
Lemma lem5196285 (_67789 : real) (x : type1021) (_67787 : real -> Prop) (_67788 : real) : ((term721 _67789 x _67787 _67788) = (term721 _67789 x _67787 _67788)) = True.
Proof. exact (@lem5196284 (term721 _67789 x _67787 _67788)). Qed.
Lemma lem5196286 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : ((term586 x _67788 _67789 _67787) = (term724 x _67788 _67789 _67787)) = True.
Proof. exact (TRANS (@lem5196281 _67789 x _67787 _67788) (@lem5196285 _67789 x _67787 _67788)). Qed.
Lemma lem5196287 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : True = ((term586 x _67788 _67789 _67787) = (term724 x _67788 _67789 _67787)).
Proof. exact (SYM (@lem5196286 x _67788 _67789 _67787)). Qed.
Lemma lem5196288 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term586 x _67788 _67789 _67787) = (term724 x _67788 _67789 _67787).
Proof. exact (EQ_MP (@lem5196287 x _67788 _67789 _67787) (@lem0)). Qed.
Lemma lem5196289 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term724 x _67788 _67789 _67787.
Proof. exact (EQ_MP (@lem5196288 x _67788 _67789 _67787) (@lem5194191 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5196291 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5196292 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term724 x _67788 _67789 _67787) = (term730 x _67788 _67789 _67787).
Proof. exact (@lem5196291 (term731 x _67788 _67789 _67787) (term294 _67789 _67787)). Qed.
Lemma lem5196294 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196295 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term732 x _67788 _67789 _67787) = (term733 x _67788 _67789 _67787).
Proof. exact (@lem5196294 (_67787 = (@EMPTY real)) (term726 x _67788 _67789 _67787)). Qed.
Lemma lem5196297 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196298 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term734 x _67788 _67789 _67787) = (term735 x _67788 _67789 _67787).
Proof. exact (@lem5196297 (term537 x _67787 _67788) (term617 _67789 _67787)). Qed.
Lemma lem5196300 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196301 (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term645 x _67787 _67788) = (term625 x _67787 _67788).
Proof. exact (@lem5196300 (term625 x _67787 _67788)). Qed.
Lemma lem5196302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5196303 (x : type1021) (_67787 : real -> Prop) (_67788 : real) : (term646 x _67787 _67788) = (term647 x _67787 _67788).
Proof. exact (MK_COMB (@lem5196302) (@lem5196301 x _67787 _67788)). Qed.
Lemma lem5196305 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196306 (_67789 : real) (_67787 : real -> Prop) : (term622 _67789 _67787) = (@IN real _67789 _67787).
Proof. exact (@lem5196305 (@IN real _67789 _67787)). Qed.
Lemma lem5196307 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term735 x _67788 _67789 _67787) = (term736 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5196303 x _67787 _67788) (@lem5196306 _67789 _67787)). Qed.
Lemma lem5196308 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term734 x _67788 _67789 _67787) = (term736 x _67788 _67789 _67787).
Proof. exact (TRANS (@lem5196298 x _67788 _67789 _67787) (@lem5196307 x _67788 _67789 _67787)). Qed.
Lemma lem5196309 (_67787 : real -> Prop) : (term118 _67787) = (term118 _67787).
Proof. exact (eq_refl (term118 _67787)). Qed.
Lemma lem5196310 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term733 x _67788 _67789 _67787) = (term737 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5196309 _67787) (@lem5196308 x _67788 _67789 _67787)). Qed.
Lemma lem5196311 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term732 x _67788 _67789 _67787) = (term737 x _67788 _67789 _67787).
Proof. exact (TRANS (@lem5196295 x _67788 _67789 _67787) (@lem5196310 x _67788 _67789 _67787)). Qed.
Lemma lem5196312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5196313 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term738 x _67788 _67789 _67787) = (term739 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5196312) (@lem5196311 x _67788 _67789 _67787)). Qed.
Lemma lem5196314 (_67789 : real) (_67787 : real -> Prop) : (term294 _67789 _67787) = (term294 _67789 _67787).
Proof. exact (eq_refl (term294 _67789 _67787)). Qed.
Lemma lem5196315 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term730 x _67788 _67789 _67787) = (term740 x _67788 _67789 _67787).
Proof. exact (MK_COMB (@lem5196313 x _67788 _67789 _67787) (@lem5196314 _67789 _67787)). Qed.
Lemma lem5196316 (x : type1021) (_67788 : real) (_67789 : real) (_67787 : real -> Prop) : (term724 x _67788 _67789 _67787) = (term740 x _67788 _67789 _67787).
Proof. exact (TRANS (@lem5196292 x _67788 _67789 _67787) (@lem5196315 x _67788 _67789 _67787)). Qed.
Lemma lem5196318 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 x' s) (h5 : term134 s x' c') : term736 x b x' s.
Proof. exact (conj (@lem5196134 x b s x' c' h1 h2 h3 h4 h5) (@lem5196141 s x' c' h5)). Qed.
Lemma lem5196319 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 x' s) (h5 : term134 s x' c') : term737 x b x' s.
Proof. exact (conj (@lem5195889 s h3) (@lem5196318 x b s x' c' h1 h2 h3 h4 h5)). Qed.
Lemma lem5196321 (_67788 : real) (_67789 : real) (_67787 : real -> Prop) (x : type1021) (h1 : term444 x) : term740 x _67788 _67789 _67787.
Proof. exact (EQ_MP (@lem5196316 x _67788 _67789 _67787) (@lem5196289 _67788 _67789 _67787 x h1)). Qed.
Lemma lem5196322 (b : real) (x' : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term740 x b x' s.
Proof. exact (@lem5196321 b x' s x h1). Qed.
Lemma lem5196325 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term692 x' s) (h5 : term134 s x' c') : term294 x' s.
Proof. exact (@lem5196322 b x' s x h1 (@lem5196319 x b s x' c' h1 h2 h3 h4 h5)). Qed.
Lemma lem5196326 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term134 s x' c') : term741 x' s.
Proof. exact (fun h0 : term692 x' s => @lem5196325 x b s x' c' h1 h2 h3 h0 h4). Qed.
Lemma lem5196328 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196329 (x' : real) (s : real -> Prop) : (term741 x' s) = (term294 x' s).
Proof. exact (@lem5196328 (term294 x' s)). Qed.
Lemma lem5196330 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term134 s x' c') : term294 x' s.
Proof. exact (EQ_MP (@lem5196329 x' s) (@lem5196326 x b s x' c' h1 h2 h3 h4)). Qed.
Lemma lem5196332 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term108 s c'.
Proof. exact (proj1 (@lem5192474 x' s t c' h1)). Qed.
Lemma lem5196333 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term688 s c'.
Proof. exact (fun h0 : term567 s c' => @lem5196332 x' s t c' h1). Qed.
Lemma lem5196335 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196336 (s : real -> Prop) (c' : real) : (term688 s c') = (term108 s c').
Proof. exact (@lem5196335 (term108 s c')). Qed.
Lemma lem5196337 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term108 s c'.
Proof. exact (EQ_MP (@lem5196336 s c') (@lem5196333 x' s t c' h1)). Qed.
Lemma lem5196353 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196354 (_67784 : real) (_67785 : real) (_67786 : real) : (term742 _67785 _67784 _67786) = (term743 _67784 _67785 _67786).
Proof. exact (@lem5196353 (real_le _67784 _67786) (term584 _67785 _67786)). Qed.
Lemma lem5196360 (_67784 : real) (_67785 : real) : (term744 _67784 _67785) = (term744 _67784 _67785).
Proof. exact (eq_refl (term744 _67784 _67785)). Qed.
Lemma lem5196361 (_67784 : real) (_67785 : real) (_67786 : real) : (term583 _67785 _67784 _67786) = (term745 _67784 _67785 _67786).
Proof. exact (MK_COMB (@lem5196360 _67784 _67785) (@lem5196354 _67784 _67785 _67786)). Qed.
Lemma lem5196365 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196366 (_67784 : real) (_67785 : real) (_67786 : real) : (term745 _67784 _67785 _67786) = (term746 _67784 _67785 _67786).
Proof. exact (@lem5196365 (real_le _67784 _67786) (term584 _67784 _67785) (term584 _67785 _67786)). Qed.
Lemma lem5196382 (_67784 : real) (_67785 : real) (_67786 : real) : (term583 _67785 _67784 _67786) = (term746 _67784 _67785 _67786).
Proof. exact (TRANS (@lem5196361 _67784 _67785 _67786) (@lem5196366 _67784 _67785 _67786)). Qed.
Lemma lem5196383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5196384 (_67784 : real) (_67785 : real) (_67786 : real) : (term747 _67785 _67784 _67786) = (term748 _67784 _67785 _67786).
Proof. exact (MK_COMB (@lem5196383) (@lem5196382 _67784 _67785 _67786)). Qed.
Lemma lem5196400 (_67784 : real) (_67785 : real) (_67786 : real) : (term746 _67784 _67785 _67786) = (term746 _67784 _67785 _67786).
Proof. exact (eq_refl (term746 _67784 _67785 _67786)). Qed.
Lemma lem5196401 (_67784 : real) (_67785 : real) (_67786 : real) : ((term583 _67785 _67784 _67786) = (term746 _67784 _67785 _67786)) = ((term746 _67784 _67785 _67786) = (term746 _67784 _67785 _67786)).
Proof. exact (MK_COMB (@lem5196384 _67784 _67785 _67786) (@lem5196400 _67784 _67785 _67786)). Qed.
Lemma lem5196403 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5196404 (x : Prop) : (x = x) = True.
Proof. exact (@lem5196403 Prop x). Qed.
Lemma lem5196405 (_67784 : real) (_67785 : real) (_67786 : real) : ((term746 _67784 _67785 _67786) = (term746 _67784 _67785 _67786)) = True.
Proof. exact (@lem5196404 (term746 _67784 _67785 _67786)). Qed.
Lemma lem5196406 (_67784 : real) (_67785 : real) (_67786 : real) : ((term583 _67785 _67784 _67786) = (term746 _67784 _67785 _67786)) = True.
Proof. exact (TRANS (@lem5196401 _67784 _67785 _67786) (@lem5196405 _67784 _67785 _67786)). Qed.
Lemma lem5196407 (_67784 : real) (_67785 : real) (_67786 : real) : True = ((term583 _67785 _67784 _67786) = (term746 _67784 _67785 _67786)).
Proof. exact (SYM (@lem5196406 _67784 _67785 _67786)). Qed.
Lemma lem5196408 (_67784 : real) (_67785 : real) (_67786 : real) : (term583 _67785 _67784 _67786) = (term746 _67784 _67785 _67786).
Proof. exact (EQ_MP (@lem5196407 _67784 _67785 _67786) (@lem0)). Qed.
Lemma lem5196409 (_67784 : real) (_67785 : real) (_67786 : real) (h1 : term129) : term746 _67784 _67785 _67786.
Proof. exact (EQ_MP (@lem5196408 _67784 _67785 _67786) (@lem5194087 _67785 _67784 _67786 h1)). Qed.
Lemma lem5196411 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5196412 (_67785 : real) (_67784 : real) (_67786 : real) : (term746 _67784 _67785 _67786) = (term749 _67785 _67784 _67786).
Proof. exact (@lem5196411 (term266 _67784 _67785 _67786) (real_le _67784 _67786)). Qed.
Lemma lem5196414 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196415 (_67784 : real) (_67785 : real) (_67786 : real) : (term750 _67784 _67785 _67786) = (term751 _67784 _67785 _67786).
Proof. exact (@lem5196414 (term584 _67784 _67785) (term584 _67785 _67786)). Qed.
Lemma lem5196417 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196418 (_67784 : real) (_67785 : real) : (term752 _67784 _67785) = (real_le _67784 _67785).
Proof. exact (@lem5196417 (real_le _67784 _67785)). Qed.
Lemma lem5196419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5196420 (_67784 : real) (_67785 : real) : (term753 _67784 _67785) = (term754 _67784 _67785).
Proof. exact (MK_COMB (@lem5196419) (@lem5196418 _67784 _67785)). Qed.
Lemma lem5196422 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196423 (_67785 : real) (_67786 : real) : (term752 _67785 _67786) = (real_le _67785 _67786).
Proof. exact (@lem5196422 (real_le _67785 _67786)). Qed.
Lemma lem5196424 (_67784 : real) (_67785 : real) (_67786 : real) : (term751 _67784 _67785 _67786) = (term271 _67784 _67785 _67786).
Proof. exact (MK_COMB (@lem5196420 _67784 _67785) (@lem5196423 _67785 _67786)). Qed.
Lemma lem5196425 (_67784 : real) (_67785 : real) (_67786 : real) : (term750 _67784 _67785 _67786) = (term271 _67784 _67785 _67786).
Proof. exact (TRANS (@lem5196415 _67784 _67785 _67786) (@lem5196424 _67784 _67785 _67786)). Qed.
Lemma lem5196426 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5196427 (_67784 : real) (_67785 : real) (_67786 : real) : (term755 _67784 _67785 _67786) = (term756 _67784 _67785 _67786).
Proof. exact (MK_COMB (@lem5196426) (@lem5196425 _67784 _67785 _67786)). Qed.
Lemma lem5196428 (_67784 : real) (_67786 : real) : (real_le _67784 _67786) = (real_le _67784 _67786).
Proof. exact (eq_refl (real_le _67784 _67786)). Qed.
Lemma lem5196429 (_67785 : real) (_67784 : real) (_67786 : real) : (term749 _67785 _67784 _67786) = (term123 _67785 _67784 _67786).
Proof. exact (MK_COMB (@lem5196427 _67784 _67785 _67786) (@lem5196428 _67784 _67786)). Qed.
Lemma lem5196430 (_67785 : real) (_67784 : real) (_67786 : real) : (term746 _67784 _67785 _67786) = (term123 _67785 _67784 _67786).
Proof. exact (TRANS (@lem5196412 _67785 _67784 _67786) (@lem5196429 _67785 _67784 _67786)). Qed.
Lemma lem5196432 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term34 s b) (h3 : term31 s) (h4 : term134 s x' c') (h5 : term228 x' s t c') : term757 x' s c'.
Proof. exact (conj (@lem5196330 x b s x' c' h1 h2 h3 h4) (@lem5196337 x' s t c' h5)). Qed.
Lemma lem5196434 (_67785 : real) (_67784 : real) (_67786 : real) (h1 : term129) : term123 _67785 _67784 _67786.
Proof. exact (EQ_MP (@lem5196430 _67785 _67784 _67786) (@lem5196409 _67784 _67785 _67786 h1)). Qed.
Lemma lem5196435 (s : real -> Prop) (x' : real) (c' : real) (h1 : term129) : term758 s x' c'.
Proof. exact (@lem5196434 (sup s) x' c' h1). Qed.
Lemma lem5196438 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : real_le x' c'.
Proof. exact (@lem5196435 s x' c' h2 (@lem5196432 x b x' s t c' h1 h3 h4 h5 h6)). Qed.
Lemma lem5196439 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : term759 x' c'.
Proof. exact (fun h0 : term584 x' c' => @lem5196438 x b x' s t c' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5196441 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196442 (x' : real) (c' : real) : (term759 x' c') = (real_le x' c').
Proof. exact (@lem5196441 (real_le x' c')). Qed.
Lemma lem5196443 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : real_le x' c'.
Proof. exact (EQ_MP (@lem5196442 x' c') (@lem5196439 x b x' s t c' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5196446 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5196448 (x' : real) (c' : real) : (term584 x' c') = (term760 x' c').
Proof. exact (@lem5196446 (real_le x' c')). Qed.
Lemma lem5196451 (s : real -> Prop) (x' : real) (c' : real) (h1 : term134 s x' c') : term760 x' c'.
Proof. exact (EQ_MP (@lem5196448 x' c') (@lem5194095 s x' c' h1)). Qed.
Lemma lem5196454 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : False.
Proof. exact (@lem5196451 s x' c' h5 (@lem5196443 x b x' s t c' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5196455 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : term690.
Proof. exact (fun h0 : ~ False => @lem5196454 x b x' s t c' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5196457 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196458 : term690 = False.
Proof. exact (@lem5196457 False). Qed.
Lemma lem5196459 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5196458) (@lem5196455 x b x' s t c' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5196526 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5196527 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5196526 t h1). Qed.
Lemma lem5196529 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5196530 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5196529 (t = (@EMPTY real))). Qed.
Lemma lem5196531 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5196530 t) (@lem5196527 t h1)). Qed.
Lemma lem5196533 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem5196534 (t : real -> Prop) (h1 : term31 t) : term587 t.
Proof. exact (fun h0 : t = (@EMPTY real) => @lem5196533 t h1). Qed.
Lemma lem5196536 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5196537 (t : real -> Prop) : (term587 t) = (term31 t).
Proof. exact (@lem5196536 (t = (@EMPTY real))). Qed.
Lemma lem5196538 (t : real -> Prop) (h1 : term31 t) : term31 t.
Proof. exact (EQ_MP (@lem5196537 t) (@lem5196534 t h1)). Qed.
Lemma lem5196540 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : @IN real x' t.
Proof. exact (proj1 (@lem5192479 t x' c' h1)). Qed.
Lemma lem5196541 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : term691 x' t.
Proof. exact (fun h0 : term617 x' t => @lem5196540 t x' c' h1). Qed.
Lemma lem5196543 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196544 (x' : real) (t : real -> Prop) : (term691 x' t) = (@IN real x' t).
Proof. exact (@lem5196543 (@IN real x' t)). Qed.
Lemma lem5196545 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : @IN real x' t.
Proof. exact (EQ_MP (@lem5196544 x' t) (@lem5196541 t x' c' h1)). Qed.
Lemma lem5196548 (x' : real) (t : real -> Prop) (h1 : term692 x' t) : term692 x' t.
Proof. exact (h1). Qed.
Lemma lem5196549 (x' : real) (t : real -> Prop) (h1 : term692 x' t) : term693 x' t.
Proof. exact (fun h0 : term294 x' t => @lem5196548 x' t h1). Qed.
Lemma lem5196551 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5196552 (x' : real) (t : real -> Prop) : (term693 x' t) = (term692 x' t).
Proof. exact (@lem5196551 (term294 x' t)). Qed.
Lemma lem5196553 (x' : real) (t : real -> Prop) (h1 : term692 x' t) : term692 x' t.
Proof. exact (EQ_MP (@lem5196552 x' t) (@lem5196549 x' t h1)). Qed.
Lemma lem5196581 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196582 (_67797 : real) (_67795 : real -> Prop) : (term293 _67797 _67795) = (term694 _67797 _67795).
Proof. exact (@lem5196581 (term294 _67797 _67795) (term617 _67797 _67795)). Qed.
Lemma lem5196588 (x : type1021) (_67796 : real) (_67795 : real -> Prop) : (term662 x _67796 _67795) = (term662 x _67796 _67795).
Proof. exact (eq_refl (term662 x _67796 _67795)). Qed.
Lemma lem5196589 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term695 x _67796 _67797 _67795) = (term696 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196588 x _67796 _67795) (@lem5196582 _67797 _67795)). Qed.
Lemma lem5196600 (_67795 : real -> Prop) : (term289 _67795) = (term289 _67795).
Proof. exact (eq_refl (term289 _67795)). Qed.
Lemma lem5196601 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term585 x _67796 _67797 _67795) = (term697 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196600 _67795) (@lem5196589 x _67796 _67797 _67795)). Qed.
Lemma lem5196612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5196613 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term698 x _67796 _67797 _67795) = (term699 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196612) (@lem5196601 x _67796 _67797 _67795)). Qed.
Lemma lem5196617 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196618 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term700 x _67796 _67797 _67795) = (term585 x _67796 _67797 _67795).
Proof. exact (@lem5196617 (_67795 = (@EMPTY real)) (term536 x _67796 _67795) (term293 _67797 _67795)). Qed.
Lemma lem5196644 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196645 (_67797 : real) (_67795 : real -> Prop) : (term293 _67797 _67795) = (term694 _67797 _67795).
Proof. exact (@lem5196644 (term294 _67797 _67795) (term617 _67797 _67795)). Qed.
Lemma lem5196651 (x : type1021) (_67796 : real) (_67795 : real -> Prop) : (term662 x _67796 _67795) = (term662 x _67796 _67795).
Proof. exact (eq_refl (term662 x _67796 _67795)). Qed.
Lemma lem5196652 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term695 x _67796 _67797 _67795) = (term696 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196651 x _67796 _67795) (@lem5196645 _67797 _67795)). Qed.
Lemma lem5196663 (_67795 : real -> Prop) : (term289 _67795) = (term289 _67795).
Proof. exact (eq_refl (term289 _67795)). Qed.
Lemma lem5196664 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term585 x _67796 _67797 _67795) = (term697 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196663 _67795) (@lem5196652 x _67796 _67797 _67795)). Qed.
Lemma lem5196675 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term700 x _67796 _67797 _67795) = (term697 x _67796 _67797 _67795).
Proof. exact (TRANS (@lem5196618 x _67796 _67797 _67795) (@lem5196664 x _67796 _67797 _67795)). Qed.
Lemma lem5196676 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : ((term585 x _67796 _67797 _67795) = (term700 x _67796 _67797 _67795)) = ((term697 x _67796 _67797 _67795) = (term697 x _67796 _67797 _67795)).
Proof. exact (MK_COMB (@lem5196613 x _67796 _67797 _67795) (@lem5196675 x _67796 _67797 _67795)). Qed.
Lemma lem5196678 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5196679 (x : Prop) : (x = x) = True.
Proof. exact (@lem5196678 Prop x). Qed.
Lemma lem5196680 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : ((term697 x _67796 _67797 _67795) = (term697 x _67796 _67797 _67795)) = True.
Proof. exact (@lem5196679 (term697 x _67796 _67797 _67795)). Qed.
Lemma lem5196681 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : ((term585 x _67796 _67797 _67795) = (term700 x _67796 _67797 _67795)) = True.
Proof. exact (TRANS (@lem5196676 x _67796 _67797 _67795) (@lem5196680 x _67796 _67797 _67795)). Qed.
Lemma lem5196682 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : True = ((term585 x _67796 _67797 _67795) = (term700 x _67796 _67797 _67795)).
Proof. exact (SYM (@lem5196681 x _67796 _67797 _67795)). Qed.
Lemma lem5196683 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term585 x _67796 _67797 _67795) = (term700 x _67796 _67797 _67795).
Proof. exact (EQ_MP (@lem5196682 x _67796 _67797 _67795) (@lem0)). Qed.
Lemma lem5196684 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term700 x _67796 _67797 _67795.
Proof. exact (EQ_MP (@lem5196683 x _67796 _67797 _67795) (@lem5194307 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5196686 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5196687 (_67797 : real) (x : type1021) (_67796 : real) (_67795 : real -> Prop) : (term700 x _67796 _67797 _67795) = (term701 _67797 x _67796 _67795).
Proof. exact (@lem5196686 (term702 _67797 _67795) (term536 x _67796 _67795)). Qed.
Lemma lem5196689 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196690 (_67797 : real) (_67795 : real -> Prop) : (term703 _67797 _67795) = (term704 _67797 _67795).
Proof. exact (@lem5196689 (_67795 = (@EMPTY real)) (term293 _67797 _67795)). Qed.
Lemma lem5196692 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196693 (_67797 : real) (_67795 : real -> Prop) : (term705 _67797 _67795) = (term706 _67797 _67795).
Proof. exact (@lem5196692 (term617 _67797 _67795) (term294 _67797 _67795)). Qed.
Lemma lem5196695 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196696 (_67797 : real) (_67795 : real -> Prop) : (term622 _67797 _67795) = (@IN real _67797 _67795).
Proof. exact (@lem5196695 (@IN real _67797 _67795)). Qed.
Lemma lem5196697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5196698 (_67797 : real) (_67795 : real -> Prop) : (term707 _67797 _67795) = (term708 _67797 _67795).
Proof. exact (MK_COMB (@lem5196697) (@lem5196696 _67797 _67795)). Qed.
Lemma lem5196699 (_67797 : real) (_67795 : real -> Prop) : (term692 _67797 _67795) = (term692 _67797 _67795).
Proof. exact (eq_refl (term692 _67797 _67795)). Qed.
Lemma lem5196700 (_67797 : real) (_67795 : real -> Prop) : (term706 _67797 _67795) = (term709 _67797 _67795).
Proof. exact (MK_COMB (@lem5196698 _67797 _67795) (@lem5196699 _67797 _67795)). Qed.
Lemma lem5196701 (_67797 : real) (_67795 : real -> Prop) : (term705 _67797 _67795) = (term709 _67797 _67795).
Proof. exact (TRANS (@lem5196693 _67797 _67795) (@lem5196700 _67797 _67795)). Qed.
Lemma lem5196702 (_67795 : real -> Prop) : (term118 _67795) = (term118 _67795).
Proof. exact (eq_refl (term118 _67795)). Qed.
Lemma lem5196703 (_67797 : real) (_67795 : real -> Prop) : (term704 _67797 _67795) = (term710 _67797 _67795).
Proof. exact (MK_COMB (@lem5196702 _67795) (@lem5196701 _67797 _67795)). Qed.
Lemma lem5196704 (_67797 : real) (_67795 : real -> Prop) : (term703 _67797 _67795) = (term710 _67797 _67795).
Proof. exact (TRANS (@lem5196690 _67797 _67795) (@lem5196703 _67797 _67795)). Qed.
Lemma lem5196705 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5196706 (_67797 : real) (_67795 : real -> Prop) : (term711 _67797 _67795) = (term712 _67797 _67795).
Proof. exact (MK_COMB (@lem5196705) (@lem5196704 _67797 _67795)). Qed.
Lemma lem5196707 (x : type1021) (_67796 : real) (_67795 : real -> Prop) : (term536 x _67796 _67795) = (term536 x _67796 _67795).
Proof. exact (eq_refl (term536 x _67796 _67795)). Qed.
Lemma lem5196708 (_67797 : real) (x : type1021) (_67796 : real) (_67795 : real -> Prop) : (term701 _67797 x _67796 _67795) = (term713 _67797 x _67796 _67795).
Proof. exact (MK_COMB (@lem5196706 _67797 _67795) (@lem5196707 x _67796 _67795)). Qed.
Lemma lem5196709 (_67797 : real) (x : type1021) (_67796 : real) (_67795 : real -> Prop) : (term700 x _67796 _67797 _67795) = (term713 _67797 x _67796 _67795).
Proof. exact (TRANS (@lem5196687 _67797 x _67796 _67795) (@lem5196708 _67797 x _67796 _67795)). Qed.
Lemma lem5196711 (t : real -> Prop) (x' : real) (c' : real) (h1 : term692 x' t) (h2 : term134 t x' c') : term709 x' t.
Proof. exact (conj (@lem5196545 t x' c' h2) (@lem5196553 x' t h1)). Qed.
Lemma lem5196712 (t : real -> Prop) (x' : real) (c' : real) (h1 : term31 t) (h2 : term692 x' t) (h3 : term134 t x' c') : term710 x' t.
Proof. exact (conj (@lem5196538 t h1) (@lem5196711 t x' c' h2 h3)). Qed.
Lemma lem5196714 (_67797 : real) (_67796 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term713 _67797 x _67796 _67795.
Proof. exact (EQ_MP (@lem5196709 _67797 x _67796 _67795) (@lem5196684 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5196715 (x' : real) (_67796 : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term713 x' x _67796 t.
Proof. exact (@lem5196714 x' _67796 t x h1). Qed.
Lemma lem5196718 (_67796 : real) (x : type1021) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 x' t) (h4 : term134 t x' c') : term536 x _67796 t.
Proof. exact (@lem5196715 x' _67796 t x h1 (@lem5196712 t x' c' h2 h3 h4)). Qed.
Lemma lem5196719 (c : real) (x : type1021) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 x' t) (h4 : term134 t x' c') : term536 x c t.
Proof. exact (@lem5196718 c x t x' c' h1 h2 h3 h4). Qed.
Lemma lem5196720 (c : real) (x : type1021) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 x' t) (h4 : term134 t x' c') : term614 x c t.
Proof. exact (fun h0 : term589 x c t => @lem5196719 c x t x' c' h1 h2 h3 h4). Qed.
Lemma lem5196722 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196723 (x : type1021) (c : real) (t : real -> Prop) : (term614 x c t) = (term536 x c t).
Proof. exact (@lem5196722 (term536 x c t)). Qed.
Lemma lem5196724 (c : real) (x : type1021) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term692 x' t) (h4 : term134 t x' c') : term536 x c t.
Proof. exact (EQ_MP (@lem5196723 x c t) (@lem5196720 c x t x' c' h1 h2 h3 h4)). Qed.
Lemma lem5196730 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196731 (c : real) (_67791 : real) (t : real -> Prop) : (term130 t _67791 c) = (term616 c _67791 t).
Proof. exact (@lem5196730 (real_le _67791 c) (term617 _67791 t)). Qed.
Lemma lem5196737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5196738 (c : real) (_67791 : real) (t : real -> Prop) : (term618 t _67791 c) = (term619 c _67791 t).
Proof. exact (MK_COMB (@lem5196737) (@lem5196731 c _67791 t)). Qed.
Lemma lem5196744 (c : real) (_67791 : real) (t : real -> Prop) : (term616 c _67791 t) = (term616 c _67791 t).
Proof. exact (eq_refl (term616 c _67791 t)). Qed.
Lemma lem5196745 (c : real) (_67791 : real) (t : real -> Prop) : ((term130 t _67791 c) = (term616 c _67791 t)) = ((term616 c _67791 t) = (term616 c _67791 t)).
Proof. exact (MK_COMB (@lem5196738 c _67791 t) (@lem5196744 c _67791 t)). Qed.
Lemma lem5196747 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5196748 (x : Prop) : (x = x) = True.
Proof. exact (@lem5196747 Prop x). Qed.
Lemma lem5196749 (c : real) (_67791 : real) (t : real -> Prop) : ((term616 c _67791 t) = (term616 c _67791 t)) = True.
Proof. exact (@lem5196748 (term616 c _67791 t)). Qed.
Lemma lem5196750 (c : real) (_67791 : real) (t : real -> Prop) : ((term130 t _67791 c) = (term616 c _67791 t)) = True.
Proof. exact (TRANS (@lem5196745 c _67791 t) (@lem5196749 c _67791 t)). Qed.
Lemma lem5196751 (c : real) (_67791 : real) (t : real -> Prop) : True = ((term130 t _67791 c) = (term616 c _67791 t)).
Proof. exact (SYM (@lem5196750 c _67791 t)). Qed.
Lemma lem5196752 (c : real) (_67791 : real) (t : real -> Prop) : (term130 t _67791 c) = (term616 c _67791 t).
Proof. exact (EQ_MP (@lem5196751 c _67791 t) (@lem0)). Qed.
Lemma lem5196753 (_67791 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term616 c _67791 t.
Proof. exact (EQ_MP (@lem5196752 c _67791 t) (@lem5194207 _67791 t c h1)). Qed.
Lemma lem5196755 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5196756 (t : real -> Prop) (_67791 : real) (c : real) : (term616 c _67791 t) = (term620 t _67791 c).
Proof. exact (@lem5196755 (term617 _67791 t) (real_le _67791 c)). Qed.
Lemma lem5196758 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196759 (_67791 : real) (t : real -> Prop) : (term622 _67791 t) = (@IN real _67791 t).
Proof. exact (@lem5196758 (@IN real _67791 t)). Qed.
Lemma lem5196760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5196761 (_67791 : real) (t : real -> Prop) : (term623 _67791 t) = (term51 _67791 t).
Proof. exact (MK_COMB (@lem5196760) (@lem5196759 _67791 t)). Qed.
Lemma lem5196762 (_67791 : real) (c : real) : (real_le _67791 c) = (real_le _67791 c).
Proof. exact (eq_refl (real_le _67791 c)). Qed.
Lemma lem5196763 (t : real -> Prop) (_67791 : real) (c : real) : (term620 t _67791 c) = (term53 t _67791 c).
Proof. exact (MK_COMB (@lem5196761 _67791 t) (@lem5196762 _67791 c)). Qed.
Lemma lem5196764 (t : real -> Prop) (_67791 : real) (c : real) : (term616 c _67791 t) = (term53 t _67791 c).
Proof. exact (TRANS (@lem5196756 t _67791 c) (@lem5196763 t _67791 c)). Qed.
Lemma lem5196767 (_67791 : real) (t : real -> Prop) (c : real) (h1 : term34 t c) : term53 t _67791 c.
Proof. exact (EQ_MP (@lem5196764 t _67791 c) (@lem5196753 _67791 t c h1)). Qed.
Lemma lem5196768 (x : type1021) (t : real -> Prop) (c : real) (h1 : term34 t c) : term624 x t c.
Proof. exact (@lem5196767 (x t c) t c h1). Qed.
Lemma lem5196771 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 x' t) (h5 : term134 t x' c') : term625 x t c.
Proof. exact (@lem5196768 x t c h2 (@lem5196724 c x t x' c' h1 h3 h4 h5)). Qed.
Lemma lem5196772 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 x' t) (h5 : term134 t x' c') : term626 x t c.
Proof. exact (fun h0 : term537 x t c => @lem5196771 x c t x' c' h1 h2 h3 h4 h5). Qed.
Lemma lem5196774 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196775 (x : type1021) (t : real -> Prop) (c : real) : (term626 x t c) = (term625 x t c).
Proof. exact (@lem5196774 (term625 x t c)). Qed.
Lemma lem5196776 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 x' t) (h5 : term134 t x' c') : term625 x t c.
Proof. exact (EQ_MP (@lem5196775 x t c) (@lem5196772 x c t x' c' h1 h2 h3 h4 h5)). Qed.
Lemma lem5196778 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : @IN real x' t.
Proof. exact (proj1 (@lem5192479 t x' c' h1)). Qed.
Lemma lem5196779 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : term691 x' t.
Proof. exact (fun h0 : term617 x' t => @lem5196778 t x' c' h1). Qed.
Lemma lem5196781 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196782 (x' : real) (t : real -> Prop) : (term691 x' t) = (@IN real x' t).
Proof. exact (@lem5196781 (@IN real x' t)). Qed.
Lemma lem5196783 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : @IN real x' t.
Proof. exact (EQ_MP (@lem5196782 x' t) (@lem5196779 t x' c' h1)). Qed.
Lemma lem5196801 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196802 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term714 x _67796 _67797 _67795) = (term715 x _67796 _67797 _67795).
Proof. exact (@lem5196801 (term617 _67797 _67795) (term537 x _67795 _67796) (term294 _67797 _67795)). Qed.
Lemma lem5196816 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196817 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term716 x _67796 _67797 _67795) = (term717 _67797 x _67795 _67796).
Proof. exact (@lem5196816 (term294 _67797 _67795) (term537 x _67795 _67796)). Qed.
Lemma lem5196823 (_67797 : real) (_67795 : real -> Prop) : (term718 _67797 _67795) = (term718 _67797 _67795).
Proof. exact (eq_refl (term718 _67797 _67795)). Qed.
Lemma lem5196824 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term715 x _67796 _67797 _67795) = (term719 _67797 x _67795 _67796).
Proof. exact (MK_COMB (@lem5196823 _67797 _67795) (@lem5196817 _67797 x _67795 _67796)). Qed.
Lemma lem5196828 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196829 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term719 _67797 x _67795 _67796) = (term720 _67797 x _67795 _67796).
Proof. exact (@lem5196828 (term294 _67797 _67795) (term617 _67797 _67795) (term537 x _67795 _67796)). Qed.
Lemma lem5196845 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term715 x _67796 _67797 _67795) = (term720 _67797 x _67795 _67796).
Proof. exact (TRANS (@lem5196824 _67797 x _67795 _67796) (@lem5196829 _67797 x _67795 _67796)). Qed.
Lemma lem5196846 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term714 x _67796 _67797 _67795) = (term720 _67797 x _67795 _67796).
Proof. exact (TRANS (@lem5196802 x _67796 _67797 _67795) (@lem5196845 _67797 x _67795 _67796)). Qed.
Lemma lem5196847 (_67795 : real -> Prop) : (term289 _67795) = (term289 _67795).
Proof. exact (eq_refl (term289 _67795)). Qed.
Lemma lem5196848 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term586 x _67796 _67797 _67795) = (term721 _67797 x _67795 _67796).
Proof. exact (MK_COMB (@lem5196847 _67795) (@lem5196846 _67797 x _67795 _67796)). Qed.
Lemma lem5196859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5196860 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term722 x _67796 _67797 _67795) = (term723 _67797 x _67795 _67796).
Proof. exact (MK_COMB (@lem5196859) (@lem5196848 _67797 x _67795 _67796)). Qed.
Lemma lem5196864 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5196865 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term724 x _67796 _67797 _67795) = (term725 x _67796 _67797 _67795).
Proof. exact (@lem5196864 (_67795 = (@EMPTY real)) (term294 _67797 _67795) (term726 x _67796 _67797 _67795)). Qed.
Lemma lem5196891 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196892 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term726 x _67796 _67797 _67795) = (term727 _67797 x _67795 _67796).
Proof. exact (@lem5196891 (term617 _67797 _67795) (term537 x _67795 _67796)). Qed.
Lemma lem5196898 (_67797 : real) (_67795 : real -> Prop) : (term728 _67797 _67795) = (term728 _67797 _67795).
Proof. exact (eq_refl (term728 _67797 _67795)). Qed.
Lemma lem5196899 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term729 x _67796 _67797 _67795) = (term720 _67797 x _67795 _67796).
Proof. exact (MK_COMB (@lem5196898 _67797 _67795) (@lem5196892 _67797 x _67795 _67796)). Qed.
Lemma lem5196910 (_67795 : real -> Prop) : (term289 _67795) = (term289 _67795).
Proof. exact (eq_refl (term289 _67795)). Qed.
Lemma lem5196911 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term725 x _67796 _67797 _67795) = (term721 _67797 x _67795 _67796).
Proof. exact (MK_COMB (@lem5196910 _67795) (@lem5196899 _67797 x _67795 _67796)). Qed.
Lemma lem5196922 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term724 x _67796 _67797 _67795) = (term721 _67797 x _67795 _67796).
Proof. exact (TRANS (@lem5196865 x _67796 _67797 _67795) (@lem5196911 _67797 x _67795 _67796)). Qed.
Lemma lem5196923 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : ((term586 x _67796 _67797 _67795) = (term724 x _67796 _67797 _67795)) = ((term721 _67797 x _67795 _67796) = (term721 _67797 x _67795 _67796)).
Proof. exact (MK_COMB (@lem5196860 _67797 x _67795 _67796) (@lem5196922 _67797 x _67795 _67796)). Qed.
Lemma lem5196925 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5196926 (x : Prop) : (x = x) = True.
Proof. exact (@lem5196925 Prop x). Qed.
Lemma lem5196927 (_67797 : real) (x : type1021) (_67795 : real -> Prop) (_67796 : real) : ((term721 _67797 x _67795 _67796) = (term721 _67797 x _67795 _67796)) = True.
Proof. exact (@lem5196926 (term721 _67797 x _67795 _67796)). Qed.
Lemma lem5196928 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : ((term586 x _67796 _67797 _67795) = (term724 x _67796 _67797 _67795)) = True.
Proof. exact (TRANS (@lem5196923 _67797 x _67795 _67796) (@lem5196927 _67797 x _67795 _67796)). Qed.
Lemma lem5196929 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : True = ((term586 x _67796 _67797 _67795) = (term724 x _67796 _67797 _67795)).
Proof. exact (SYM (@lem5196928 x _67796 _67797 _67795)). Qed.
Lemma lem5196930 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term586 x _67796 _67797 _67795) = (term724 x _67796 _67797 _67795).
Proof. exact (EQ_MP (@lem5196929 x _67796 _67797 _67795) (@lem0)). Qed.
Lemma lem5196931 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term724 x _67796 _67797 _67795.
Proof. exact (EQ_MP (@lem5196930 x _67796 _67797 _67795) (@lem5194323 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5196933 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5196934 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term724 x _67796 _67797 _67795) = (term730 x _67796 _67797 _67795).
Proof. exact (@lem5196933 (term731 x _67796 _67797 _67795) (term294 _67797 _67795)). Qed.
Lemma lem5196936 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196937 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term732 x _67796 _67797 _67795) = (term733 x _67796 _67797 _67795).
Proof. exact (@lem5196936 (_67795 = (@EMPTY real)) (term726 x _67796 _67797 _67795)). Qed.
Lemma lem5196939 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5196940 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term734 x _67796 _67797 _67795) = (term735 x _67796 _67797 _67795).
Proof. exact (@lem5196939 (term537 x _67795 _67796) (term617 _67797 _67795)). Qed.
Lemma lem5196942 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196943 (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term645 x _67795 _67796) = (term625 x _67795 _67796).
Proof. exact (@lem5196942 (term625 x _67795 _67796)). Qed.
Lemma lem5196944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5196945 (x : type1021) (_67795 : real -> Prop) (_67796 : real) : (term646 x _67795 _67796) = (term647 x _67795 _67796).
Proof. exact (MK_COMB (@lem5196944) (@lem5196943 x _67795 _67796)). Qed.
Lemma lem5196947 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5196948 (_67797 : real) (_67795 : real -> Prop) : (term622 _67797 _67795) = (@IN real _67797 _67795).
Proof. exact (@lem5196947 (@IN real _67797 _67795)). Qed.
Lemma lem5196949 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term735 x _67796 _67797 _67795) = (term736 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196945 x _67795 _67796) (@lem5196948 _67797 _67795)). Qed.
Lemma lem5196950 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term734 x _67796 _67797 _67795) = (term736 x _67796 _67797 _67795).
Proof. exact (TRANS (@lem5196940 x _67796 _67797 _67795) (@lem5196949 x _67796 _67797 _67795)). Qed.
Lemma lem5196951 (_67795 : real -> Prop) : (term118 _67795) = (term118 _67795).
Proof. exact (eq_refl (term118 _67795)). Qed.
Lemma lem5196952 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term733 x _67796 _67797 _67795) = (term737 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196951 _67795) (@lem5196950 x _67796 _67797 _67795)). Qed.
Lemma lem5196953 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term732 x _67796 _67797 _67795) = (term737 x _67796 _67797 _67795).
Proof. exact (TRANS (@lem5196937 x _67796 _67797 _67795) (@lem5196952 x _67796 _67797 _67795)). Qed.
Lemma lem5196954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5196955 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term738 x _67796 _67797 _67795) = (term739 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196954) (@lem5196953 x _67796 _67797 _67795)). Qed.
Lemma lem5196956 (_67797 : real) (_67795 : real -> Prop) : (term294 _67797 _67795) = (term294 _67797 _67795).
Proof. exact (eq_refl (term294 _67797 _67795)). Qed.
Lemma lem5196957 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term730 x _67796 _67797 _67795) = (term740 x _67796 _67797 _67795).
Proof. exact (MK_COMB (@lem5196955 x _67796 _67797 _67795) (@lem5196956 _67797 _67795)). Qed.
Lemma lem5196958 (x : type1021) (_67796 : real) (_67797 : real) (_67795 : real -> Prop) : (term724 x _67796 _67797 _67795) = (term740 x _67796 _67797 _67795).
Proof. exact (TRANS (@lem5196934 x _67796 _67797 _67795) (@lem5196957 x _67796 _67797 _67795)). Qed.
Lemma lem5196960 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 x' t) (h5 : term134 t x' c') : term736 x c x' t.
Proof. exact (conj (@lem5196776 x c t x' c' h1 h2 h3 h4 h5) (@lem5196783 t x' c' h5)). Qed.
Lemma lem5196961 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 x' t) (h5 : term134 t x' c') : term737 x c x' t.
Proof. exact (conj (@lem5196531 t h3) (@lem5196960 x c t x' c' h1 h2 h3 h4 h5)). Qed.
Lemma lem5196963 (_67796 : real) (_67797 : real) (_67795 : real -> Prop) (x : type1021) (h1 : term444 x) : term740 x _67796 _67797 _67795.
Proof. exact (EQ_MP (@lem5196958 x _67796 _67797 _67795) (@lem5196931 _67796 _67797 _67795 x h1)). Qed.
Lemma lem5196964 (c : real) (x' : real) (t : real -> Prop) (x : type1021) (h1 : term444 x) : term740 x c x' t.
Proof. exact (@lem5196963 c x' t x h1). Qed.
Lemma lem5196967 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term692 x' t) (h5 : term134 t x' c') : term294 x' t.
Proof. exact (@lem5196964 c x' t x h1 (@lem5196961 x c t x' c' h1 h2 h3 h4 h5)). Qed.
Lemma lem5196968 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term134 t x' c') : term741 x' t.
Proof. exact (fun h0 : term692 x' t => @lem5196967 x c t x' c' h1 h2 h3 h0 h4). Qed.
Lemma lem5196970 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196971 (x' : real) (t : real -> Prop) : (term741 x' t) = (term294 x' t).
Proof. exact (@lem5196970 (term294 x' t)). Qed.
Lemma lem5196972 (x : type1021) (c : real) (t : real -> Prop) (x' : real) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term134 t x' c') : term294 x' t.
Proof. exact (EQ_MP (@lem5196971 x' t) (@lem5196968 x c t x' c' h1 h2 h3 h4)). Qed.
Lemma lem5196974 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term108 t c'.
Proof. exact (proj2 (@lem5192474 x' s t c' h1)). Qed.
Lemma lem5196975 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term688 t c'.
Proof. exact (fun h0 : term567 t c' => @lem5196974 x' s t c' h1). Qed.
Lemma lem5196977 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5196978 (t : real -> Prop) (c' : real) : (term688 t c') = (term108 t c').
Proof. exact (@lem5196977 (term108 t c')). Qed.
Lemma lem5196979 (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term228 x' s t c') : term108 t c'.
Proof. exact (EQ_MP (@lem5196978 t c') (@lem5196975 x' s t c' h1)). Qed.
Lemma lem5196995 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5196996 (_67792 : real) (_67793 : real) (_67794 : real) : (term742 _67793 _67792 _67794) = (term743 _67792 _67793 _67794).
Proof. exact (@lem5196995 (real_le _67792 _67794) (term584 _67793 _67794)). Qed.
Lemma lem5197002 (_67792 : real) (_67793 : real) : (term744 _67792 _67793) = (term744 _67792 _67793).
Proof. exact (eq_refl (term744 _67792 _67793)). Qed.
Lemma lem5197003 (_67792 : real) (_67793 : real) (_67794 : real) : (term583 _67793 _67792 _67794) = (term745 _67792 _67793 _67794).
Proof. exact (MK_COMB (@lem5197002 _67792 _67793) (@lem5196996 _67792 _67793 _67794)). Qed.
Lemma lem5197007 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5197008 (_67792 : real) (_67793 : real) (_67794 : real) : (term745 _67792 _67793 _67794) = (term746 _67792 _67793 _67794).
Proof. exact (@lem5197007 (real_le _67792 _67794) (term584 _67792 _67793) (term584 _67793 _67794)). Qed.
Lemma lem5197024 (_67792 : real) (_67793 : real) (_67794 : real) : (term583 _67793 _67792 _67794) = (term746 _67792 _67793 _67794).
Proof. exact (TRANS (@lem5197003 _67792 _67793 _67794) (@lem5197008 _67792 _67793 _67794)). Qed.
Lemma lem5197025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5197026 (_67792 : real) (_67793 : real) (_67794 : real) : (term747 _67793 _67792 _67794) = (term748 _67792 _67793 _67794).
Proof. exact (MK_COMB (@lem5197025) (@lem5197024 _67792 _67793 _67794)). Qed.
Lemma lem5197042 (_67792 : real) (_67793 : real) (_67794 : real) : (term746 _67792 _67793 _67794) = (term746 _67792 _67793 _67794).
Proof. exact (eq_refl (term746 _67792 _67793 _67794)). Qed.
Lemma lem5197043 (_67792 : real) (_67793 : real) (_67794 : real) : ((term583 _67793 _67792 _67794) = (term746 _67792 _67793 _67794)) = ((term746 _67792 _67793 _67794) = (term746 _67792 _67793 _67794)).
Proof. exact (MK_COMB (@lem5197026 _67792 _67793 _67794) (@lem5197042 _67792 _67793 _67794)). Qed.
Lemma lem5197045 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5197046 (x : Prop) : (x = x) = True.
Proof. exact (@lem5197045 Prop x). Qed.
Lemma lem5197047 (_67792 : real) (_67793 : real) (_67794 : real) : ((term746 _67792 _67793 _67794) = (term746 _67792 _67793 _67794)) = True.
Proof. exact (@lem5197046 (term746 _67792 _67793 _67794)). Qed.
Lemma lem5197048 (_67792 : real) (_67793 : real) (_67794 : real) : ((term583 _67793 _67792 _67794) = (term746 _67792 _67793 _67794)) = True.
Proof. exact (TRANS (@lem5197043 _67792 _67793 _67794) (@lem5197047 _67792 _67793 _67794)). Qed.
Lemma lem5197049 (_67792 : real) (_67793 : real) (_67794 : real) : True = ((term583 _67793 _67792 _67794) = (term746 _67792 _67793 _67794)).
Proof. exact (SYM (@lem5197048 _67792 _67793 _67794)). Qed.
Lemma lem5197050 (_67792 : real) (_67793 : real) (_67794 : real) : (term583 _67793 _67792 _67794) = (term746 _67792 _67793 _67794).
Proof. exact (EQ_MP (@lem5197049 _67792 _67793 _67794) (@lem0)). Qed.
Lemma lem5197051 (_67792 : real) (_67793 : real) (_67794 : real) (h1 : term129) : term746 _67792 _67793 _67794.
Proof. exact (EQ_MP (@lem5197050 _67792 _67793 _67794) (@lem5194219 _67793 _67792 _67794 h1)). Qed.
Lemma lem5197053 (b : Prop) (a : Prop) : (a \/ b) = (term598 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5197054 (_67793 : real) (_67792 : real) (_67794 : real) : (term746 _67792 _67793 _67794) = (term749 _67793 _67792 _67794).
Proof. exact (@lem5197053 (term266 _67792 _67793 _67794) (real_le _67792 _67794)). Qed.
Lemma lem5197056 (a : Prop) (b : Prop) : (term601 a b) = (term602 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5197057 (_67792 : real) (_67793 : real) (_67794 : real) : (term750 _67792 _67793 _67794) = (term751 _67792 _67793 _67794).
Proof. exact (@lem5197056 (term584 _67792 _67793) (term584 _67793 _67794)). Qed.
Lemma lem5197059 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5197060 (_67792 : real) (_67793 : real) : (term752 _67792 _67793) = (real_le _67792 _67793).
Proof. exact (@lem5197059 (real_le _67792 _67793)). Qed.
Lemma lem5197061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197062 (_67792 : real) (_67793 : real) : (term753 _67792 _67793) = (term754 _67792 _67793).
Proof. exact (MK_COMB (@lem5197061) (@lem5197060 _67792 _67793)). Qed.
Lemma lem5197064 (a : Prop) : (term621 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5197065 (_67793 : real) (_67794 : real) : (term752 _67793 _67794) = (real_le _67793 _67794).
Proof. exact (@lem5197064 (real_le _67793 _67794)). Qed.
Lemma lem5197066 (_67792 : real) (_67793 : real) (_67794 : real) : (term751 _67792 _67793 _67794) = (term271 _67792 _67793 _67794).
Proof. exact (MK_COMB (@lem5197062 _67792 _67793) (@lem5197065 _67793 _67794)). Qed.
Lemma lem5197067 (_67792 : real) (_67793 : real) (_67794 : real) : (term750 _67792 _67793 _67794) = (term271 _67792 _67793 _67794).
Proof. exact (TRANS (@lem5197057 _67792 _67793 _67794) (@lem5197066 _67792 _67793 _67794)). Qed.
Lemma lem5197068 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5197069 (_67792 : real) (_67793 : real) (_67794 : real) : (term755 _67792 _67793 _67794) = (term756 _67792 _67793 _67794).
Proof. exact (MK_COMB (@lem5197068) (@lem5197067 _67792 _67793 _67794)). Qed.
Lemma lem5197070 (_67792 : real) (_67794 : real) : (real_le _67792 _67794) = (real_le _67792 _67794).
Proof. exact (eq_refl (real_le _67792 _67794)). Qed.
Lemma lem5197071 (_67793 : real) (_67792 : real) (_67794 : real) : (term749 _67793 _67792 _67794) = (term123 _67793 _67792 _67794).
Proof. exact (MK_COMB (@lem5197069 _67792 _67793 _67794) (@lem5197070 _67792 _67794)). Qed.
Lemma lem5197072 (_67793 : real) (_67792 : real) (_67794 : real) : (term746 _67792 _67793 _67794) = (term123 _67793 _67792 _67794).
Proof. exact (TRANS (@lem5197054 _67793 _67792 _67794) (@lem5197071 _67793 _67792 _67794)). Qed.
Lemma lem5197074 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term34 t c) (h3 : term31 t) (h4 : term134 t x' c') (h5 : term228 x' s t c') : term757 x' t c'.
Proof. exact (conj (@lem5196972 x c t x' c' h1 h2 h3 h4) (@lem5196979 x' s t c' h5)). Qed.
Lemma lem5197076 (_67793 : real) (_67792 : real) (_67794 : real) (h1 : term129) : term123 _67793 _67792 _67794.
Proof. exact (EQ_MP (@lem5197072 _67793 _67792 _67794) (@lem5197051 _67792 _67793 _67794 h1)). Qed.
Lemma lem5197077 (t : real -> Prop) (x' : real) (c' : real) (h1 : term129) : term758 t x' c'.
Proof. exact (@lem5197076 (sup t) x' c' h1). Qed.
Lemma lem5197080 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : real_le x' c'.
Proof. exact (@lem5197077 t x' c' h2 (@lem5197074 x c x' s t c' h1 h3 h4 h5 h6)). Qed.
Lemma lem5197081 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : term759 x' c'.
Proof. exact (fun h0 : term584 x' c' => @lem5197080 x c x' s t c' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5197083 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5197084 (x' : real) (c' : real) : (term759 x' c') = (real_le x' c').
Proof. exact (@lem5197083 (real_le x' c')). Qed.
Lemma lem5197085 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : real_le x' c'.
Proof. exact (EQ_MP (@lem5197084 x' c') (@lem5197081 x c x' s t c' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5197088 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5197090 (x' : real) (c' : real) : (term584 x' c') = (term760 x' c').
Proof. exact (@lem5197088 (real_le x' c')). Qed.
Lemma lem5197093 (t : real -> Prop) (x' : real) (c' : real) (h1 : term134 t x' c') : term760 x' c'.
Proof. exact (EQ_MP (@lem5197090 x' c') (@lem5194227 t x' c' h1)). Qed.
Lemma lem5197096 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : False.
Proof. exact (@lem5197093 t x' c' h5 (@lem5197085 x c x' s t c' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5197097 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : term690.
Proof. exact (fun h0 : ~ False => @lem5197096 x c x' s t c' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5197099 (p : Prop) : (term615 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5197100 : term690 = False.
Proof. exact (@lem5197099 False). Qed.
Lemma lem5197101 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197100) (@lem5197097 x c x' s t c' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5197102 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : (term31 t) = False.
Proof. exact (prop_ext (fun h7 : term31 t => @lem5197101 x c x' s t c' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5194195 t h4)). Qed.
Lemma lem5197103 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197102 x c x' s t c' h1 h2 h3 h4 h5 h6) (@lem5194195 t h4)). Qed.
Lemma lem5197104 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : (term31 s) = False.
Proof. exact (prop_ext (fun h7 : term31 s => @lem5196459 x b x' s t c' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5194061 s h4)). Qed.
Lemma lem5197105 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197104 x b x' s t c' h1 h2 h3 h4 h5 h6) (@lem5194061 s h4)). Qed.
Lemma lem5197106 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : (term567 t c') = False.
Proof. exact (prop_ext (fun h5 : term567 t c' => @lem5195817 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5193963 t c' h3)). Qed.
Lemma lem5197107 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197106 x s t c' h1 h2 h3 h4) (@lem5193963 t c' h3)). Qed.
Lemma lem5197108 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : (term31 t) = False.
Proof. exact (prop_ext (fun h5 : term31 t => @lem5197107 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5193925 t h2)). Qed.
Lemma lem5197109 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197108 x s t c' h1 h2 h3 h4) (@lem5193925 t h2)). Qed.
Lemma lem5197110 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : (term567 s c') = False.
Proof. exact (prop_ext (fun h5 : term567 s c' => @lem5195070 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5193825 s c' h3)). Qed.
Lemma lem5197111 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197110 x s t c' h1 h2 h3 h4) (@lem5193825 s c' h3)). Qed.
Lemma lem5197112 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : (term31 s) = False.
Proof. exact (prop_ext (fun h5 : term31 s => @lem5197111 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5193785 s h2)). Qed.
Lemma lem5197113 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197112 x s t c' h1 h2 h3 h4) (@lem5193785 s h2)). Qed.
Lemma lem5197114 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : (term31 t) = False.
Proof. exact (prop_ext (fun h7 : term31 t => @lem5197103 x c x' s t c' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5193362 t h4)). Qed.
Lemma lem5197115 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197114 x c x' s t c' h1 h2 h3 h4 h5 h6) (@lem5193362 t h4)). Qed.
Lemma lem5197116 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : (term31 s) = False.
Proof. exact (prop_ext (fun h7 : term31 s => @lem5197105 x b x' s t c' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5193077 s h4)). Qed.
Lemma lem5197117 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197116 x b x' s t c' h1 h2 h3 h4 h5 h6) (@lem5193077 s h4)). Qed.
Lemma lem5197118 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : (term567 t c') = False.
Proof. exact (prop_ext (fun h5 : term567 t c' => @lem5197109 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5193073 t c' h3)). Qed.
Lemma lem5197119 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197118 x s t c' h1 h2 h3 h4) (@lem5193073 t c' h3)). Qed.
Lemma lem5197120 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : (term31 t) = False.
Proof. exact (prop_ext (fun h5 : term31 t => @lem5197119 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5192786 t h2)). Qed.
Lemma lem5197121 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197120 x s t c' h1 h2 h3 h4) (@lem5192786 t h2)). Qed.
Lemma lem5197122 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : (term567 s c') = False.
Proof. exact (prop_ext (fun h5 : term567 s c' => @lem5197113 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5192778 s c' h3)). Qed.
Lemma lem5197123 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197122 x s t c' h1 h2 h3 h4) (@lem5192778 s c' h3)). Qed.
Lemma lem5197124 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : (term31 s) = False.
Proof. exact (prop_ext (fun h5 : term31 s => @lem5197123 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5192487 s h2)). Qed.
Lemma lem5197125 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197124 x s t c' h1 h2 h3 h4) (@lem5192487 s h2)). Qed.
Lemma lem5197126 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : (term31 t) = False.
Proof. exact (prop_ext (fun h7 : term31 t => @lem5197115 x c x' s t c' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5193362 t h4)). Qed.
Lemma lem5197127 (x : type1021) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 t c) (h4 : term31 t) (h5 : term134 t x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197126 x c x' s t c' h1 h2 h3 h4 h5 h6) (@lem5193362 t h4)). Qed.
Lemma lem5197128 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : (term31 s) = False.
Proof. exact (prop_ext (fun h7 : term31 s => @lem5197117 x b x' s t c' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5193077 s h4)). Qed.
Lemma lem5197129 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term31 s) (h5 : term134 s x' c') (h6 : term228 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197128 x b x' s t c' h1 h2 h3 h4 h5 h6) (@lem5193077 s h4)). Qed.
Lemma lem5197130 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : (term567 t c') = False.
Proof. exact (prop_ext (fun h5 : term567 t c' => @lem5197121 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5193073 t c' h3)). Qed.
Lemma lem5197131 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197130 x s t c' h1 h2 h3 h4) (@lem5193073 t c' h3)). Qed.
Lemma lem5197132 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : (term31 t) = False.
Proof. exact (prop_ext (fun h5 : term31 t => @lem5197131 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5192786 t h2)). Qed.
Lemma lem5197133 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 t) (h3 : term567 t c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197132 x s t c' h1 h2 h3 h4) (@lem5192786 t h2)). Qed.
Lemma lem5197134 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : (term567 s c') = False.
Proof. exact (prop_ext (fun h5 : term567 s c' => @lem5197125 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5192778 s c' h3)). Qed.
Lemma lem5197135 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197134 x s t c' h1 h2 h3 h4) (@lem5192778 s c' h3)). Qed.
Lemma lem5197136 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : (term31 s) = False.
Proof. exact (prop_ext (fun h5 : term31 s => @lem5197135 x s t c' h1 h2 h3 h4) (fun h5 : False => @lem5192487 s h2)). Qed.
Lemma lem5197137 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term567 s c') (h4 : term160 s t c') : False.
Proof. exact (EQ_MP (@lem5197136 x s t c' h1 h2 h3 h4) (@lem5192487 s h2)). Qed.
Lemma lem5197138 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term228 x' s t c') : False.
Proof. exact (or_elim (@lem5192475 x' s t c' h7) (fun h0 : term134 s x' c' => @lem5197129 x b x' s t c' h1 h2 h3 h5 h0 h7) (fun h0 : term134 t x' c' => @lem5197127 x c x' s t c' h1 h2 h4 h6 h0 h7)). Qed.
Lemma lem5197139 (x : type1021) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term31 s) (h3 : term31 t) (h4 : term160 s t c') : False.
Proof. exact (or_elim (@lem5192468 s t c' h4) (fun h0 : term567 s c' => @lem5197137 x s t c' h1 h2 h0 h4) (fun h0 : term567 t c' => @lem5197133 x s t c' h1 h3 h0 h4)). Qed.
Lemma lem5197140 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : False.
Proof. exact (or_elim (@lem5192465 x' s t c' h7) (fun h0 : term160 s t c' => @lem5197139 x s t c' h1 h5 h6 h0) (fun h0 : term228 x' s t c' => @lem5197138 x b c x' s t c' h1 h2 h3 h4 h5 h6 h0)). Qed.
Lemma lem5197141 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : (term259 x' s t c') = False.
Proof. exact (prop_ext (fun h8 : term259 x' s t c' => @lem5197140 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5192465 x' s t c' h7)). Qed.
Lemma lem5197142 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197141 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (@lem5192465 x' s t c' h7)). Qed.
Lemma lem5197143 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : (term444 x) = False.
Proof. exact (prop_ext (fun h8 : term444 x => @lem5197142 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5192345 x h1)). Qed.
Lemma lem5197144 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197143 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (@lem5192345 x h1)). Qed.
Lemma lem5197145 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : (term31 t) = False.
Proof. exact (prop_ext (fun h8 : term31 t => @lem5197144 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5192172 t h6)). Qed.
Lemma lem5197146 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197145 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (@lem5192172 t h6)). Qed.
Lemma lem5197147 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : (term31 s) = False.
Proof. exact (prop_ext (fun h8 : term31 s => @lem5197146 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5192164 s h5)). Qed.
Lemma lem5197148 (x : type1021) (b : real) (c : real) (x' : real) (s : real -> Prop) (t : real -> Prop) (c' : real) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term31 s) (h6 : term31 t) (h7 : term259 x' s t c') : False.
Proof. exact (EQ_MP (@lem5197147 x b c x' s t c' h1 h2 h3 h4 h5 h6 h7) (@lem5192164 s h5)). Qed.
Lemma lem5197149 (x : type1021) (b : real) (c : real) (c' : real) (s : real -> Prop) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term262 s t c') (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (ex_elim (@lem5192155 s t c' h5) (fun x' : real => fun h0 : term261 s t c' x' => @lem5197148 x b c x' s t c' h1 h2 h3 h4 h6 h7 h0)). Qed.
Lemma lem5197150 (x : type1021) (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term444 x) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (ex_elim (@lem5191541 s t h5) (fun c' : real => fun h0 : term263 s t c' => @lem5197149 x b c c' s t h1 h2 h3 h4 h0 h6 h7)). Qed.
Lemma lem5197151 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (ex_elim (@lem5192153 h1) (fun x : type1021 => fun h0 : term446 x => @lem5197150 x b c s t h0 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5197152 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : (term31 t) = False.
Proof. exact (prop_ext (fun h8 : term31 t => @lem5197151 b c s t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5190889 t h7)). Qed.
Lemma lem5197153 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (EQ_MP (@lem5197152 b c s t h1 h2 h3 h4 h5 h6 h7) (@lem5190889 t h7)). Qed.
Lemma lem5197154 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : (term31 s) = False.
Proof. exact (prop_ext (fun h8 : term31 s => @lem5197153 b c s t h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5190883 s h6)). Qed.
Lemma lem5197155 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term76) (h2 : term129) (h3 : term34 s b) (h4 : term34 t c) (h5 : term69 s t) (h6 : term31 s) (h7 : term31 t) : False.
Proof. exact (EQ_MP (@lem5197154 b c s t h1 h2 h3 h4 h5 h6 h7) (@lem5190883 s h6)). Qed.
Lemma lem5197156 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term129) (h2 : term34 s b) (h3 : term34 t c) (h4 : term69 s t) (h5 : term31 s) (h6 : term31 t) : term74.
Proof. exact (fun h0 : term76 => @lem5197155 b c s t h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5197157 : term74 = term75.
Proof. exact (@lem69 term76). Qed.
Lemma lem5197158 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term129) (h2 : term34 s b) (h3 : term34 t c) (h4 : term69 s t) (h5 : term31 s) (h6 : term31 t) : term75.
Proof. exact (EQ_MP (@lem5197157) (@lem5197156 b c s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5197159 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : term79.
Proof. exact (fun h0 : term129 => @lem5197158 b c s t h0 h1 h2 h3 h4 h5). Qed.
Lemma lem5197160 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term82 s t.
Proof. exact (fun h0 : term69 s t => @lem5197159 b c s t h1 h2 h0 h3 h4). Qed.
Lemma lem5197161 (c : real) (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term31 s) (h3 : term31 t) : term85 c s t.
Proof. exact (fun h0 : term34 t c => @lem5197160 b c s t h1 h0 h2 h3). Qed.
Lemma lem5197162 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) : term87 b c s t.
Proof. exact (fun h0 : term34 s b => @lem5197161 c b s t h0 h1 h2). Qed.
Lemma lem5197163 (b : real) (c : real) (t : real -> Prop) (s : real -> Prop) (h1 : term31 s) : term90 b c s t.
Proof. exact (fun h0 : term31 t => @lem5197162 b c s t h1 h0). Qed.
Lemma lem5197164 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term91 b c s t.
Proof. exact (fun h0 : term31 s => @lem5197163 b c t s h0). Qed.
Lemma lem5197169 (c : real) (s : real -> Prop) (t : real -> Prop) : term95 c s t.
Proof. exact (fun b : real => @lem5197164 b c s t). Qed.
Lemma lem5197174 (s : real -> Prop) (t : real -> Prop) : term99 s t.
Proof. exact (fun c : real => @lem5197169 c s t). Qed.
Lemma lem5197179 (t : real -> Prop) : term103 t.
Proof. exact (fun s : real -> Prop => @lem5197174 s t). Qed.
Lemma lem5197184 : term107.
Proof. exact (fun t : real -> Prop => @lem5197179 t). Qed.
Lemma lem5197185 : term106.
Proof. exact (EQ_MP (@lem5190870) (@lem5197184)). Qed.
Lemma lem5197186 (t : real -> Prop) : term761 t.
Proof. exact (@lem5197185 t). Qed.
Lemma lem5197187 (t : real -> Prop) : (term761 t) = (term102 t).
Proof. exact (eq_refl (term761 t)). Qed.
Lemma lem5197188 (t : real -> Prop) : term102 t.
Proof. exact (EQ_MP (@lem5197187 t) (@lem5197186 t)). Qed.
Lemma lem5197189 (t : real -> Prop) (s : real -> Prop) : term762 t s.
Proof. exact (@lem5197188 t s). Qed.
Lemma lem5197190 (s : real -> Prop) (t : real -> Prop) : (term762 t s) = (term98 s t).
Proof. exact (eq_refl (term762 t s)). Qed.
Lemma lem5197191 (s : real -> Prop) (t : real -> Prop) : term98 s t.
Proof. exact (EQ_MP (@lem5197190 s t) (@lem5197189 t s)). Qed.
Lemma lem5197192 (s : real -> Prop) (t : real -> Prop) (c : real) : term763 s t c.
Proof. exact (@lem5197191 s t c). Qed.
Lemma lem5197193 (c : real) (s : real -> Prop) (t : real -> Prop) : (term763 s t c) = (term94 c s t).
Proof. exact (eq_refl (term763 s t c)). Qed.
Lemma lem5197194 (c : real) (s : real -> Prop) (t : real -> Prop) : term94 c s t.
Proof. exact (EQ_MP (@lem5197193 c s t) (@lem5197192 s t c)). Qed.
Lemma lem5197195 (c : real) (s : real -> Prop) (t : real -> Prop) (b : real) : term764 c s t b.
Proof. exact (@lem5197194 c s t b). Qed.
Lemma lem5197196 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : (term764 c s t b) = (term70 b c s t).
Proof. exact (eq_refl (term764 c s t b)). Qed.
Lemma lem5197197 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term70 b c s t.
Proof. exact (EQ_MP (@lem5197196 b c s t) (@lem5197195 c s t b)). Qed.
Lemma lem5197199 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) : term70 b c s t.
Proof. exact (@lem5190390 b c s t (@lem5197197 b c s t)). Qed.
Lemma lem5197200 (b : real) (c : real) (t : real -> Prop) (s : real -> Prop) (h1 : term31 s) : term89 b c s t.
Proof. exact (@lem5197199 b c s t (@lem5190294 s h1)). Qed.
Lemma lem5197201 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) : term86 b c s t.
Proof. exact (@lem5197200 b c t s h1 (@lem5190296 t h2)). Qed.
Lemma lem5197202 (c : real) (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term31 s) (h3 : term31 t) : term84 c s t.
Proof. exact (@lem5197201 b c s t h2 h3 (@lem5190299 s b h1)). Qed.
Lemma lem5197203 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term81 s t.
Proof. exact (@lem5197202 c b s t h1 h3 h4 (@lem5190300 t c h2)). Qed.
Lemma lem5197204 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : term78.
Proof. exact (@lem5197203 b c s t h1 h2 h4 h5 (@lem5190375 s t h3)). Qed.
Lemma lem5197205 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : term74.
Proof. exact (@lem5197204 b c s t h1 h2 h3 h4 h5 (@lem1339577)). Qed.
Lemma lem5197206 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : False.
Proof. exact (@lem5197205 b c s t h1 h2 h3 h4 h5 (@lem5136700)). Qed.
Lemma lem5197207 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : (term69 s t) = False.
Proof. exact (prop_ext (fun h6 : term69 s t => @lem5197206 b c s t h1 h2 h3 h4 h5) (fun h6 : False => @lem5190375 s t h3)). Qed.
Lemma lem5197208 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term69 s t) (h4 : term31 s) (h5 : term31 t) : False.
Proof. exact (EQ_MP (@lem5197207 b c s t h1 h2 h3 h4 h5) (@lem5190375 s t h3)). Qed.
Lemma lem5197209 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term68 s t.
Proof. exact (fun h0 : term69 s t => @lem5197208 b c s t h1 h2 h0 h3 h4). Qed.
Lemma lem5197210 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term66 s t.
Proof. exact (EQ_MP (@lem5190374 s t) (@lem5197209 b c s t h1 h2 h3 h4)). Qed.
Lemma lem5197211 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : term65 s t.
Proof. exact (EQ_MP (@lem5190370 s t) (@lem5197210 b c s t h1 h2 h3 h4)). Qed.
Lemma lem5197212 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (@lem5190303 s t (@lem5197211 b c s t h1 h2 h3 h4)). Qed.
Lemma lem5197213 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : term30 s t.
Proof. exact (proj2 (@lem5190292 s t h1)). Qed.
Lemma lem5197214 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : term31 s.
Proof. exact (proj1 (@lem5190292 s t h1)). Qed.
Lemma lem5197215 (s : real -> Prop) (t : real -> Prop) (h1 : term30 s t) : term32 s t.
Proof. exact (proj2 (@lem5190293 s t h1)). Qed.
Lemma lem5197216 (s : real -> Prop) (t : real -> Prop) (h1 : term30 s t) : term31 t.
Proof. exact (proj1 (@lem5190293 s t h1)). Qed.
Lemma lem5197217 (s : real -> Prop) (t : real -> Prop) (h1 : term32 s t) : term33 t.
Proof. exact (proj2 (@lem5190295 s t h1)). Qed.
Lemma lem5197218 (s : real -> Prop) (t : real -> Prop) (h1 : term32 s t) : term33 s.
Proof. exact (proj1 (@lem5190295 s t h1)). Qed.
Lemma lem5197219 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : (term34 t c) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h5 : term34 t c => @lem5197212 b c s t h1 h2 h3 h4) (fun h5 : (term765 s t) = (term36 s t) => @lem5190300 t c h2)). Qed.
Lemma lem5197220 (b : real) (c : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term34 t c) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197219 b c s t h1 h2 h3 h4) (@lem5190300 t c h2)). Qed.
Lemma lem5197221 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (ex_elim (@lem5190297 t h2) (fun c : real => fun h0 : term117 t c => @lem5197220 b c s t h1 h0 h3 h4)). Qed.
Lemma lem5197222 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term34 s b) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h5 : term34 s b => @lem5197221 b s t h1 h2 h3 h4) (fun h5 : (term765 s t) = (term36 s t) => @lem5190299 s b h1)). Qed.
Lemma lem5197223 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term34 s b) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197222 b s t h1 h2 h3 h4) (@lem5190299 s b h1)). Qed.
Lemma lem5197224 (s : real -> Prop) (t : real -> Prop) (h1 : term33 s) (h2 : term33 t) (h3 : term31 s) (h4 : term31 t) : (term765 s t) = (term36 s t).
Proof. exact (ex_elim (@lem5190298 s h1) (fun b : real => fun h0 : term117 s b => @lem5197223 b s t h0 h2 h3 h4)). Qed.
Lemma lem5197225 (s : real -> Prop) (t : real -> Prop) (h1 : term33 s) (h2 : term31 s) (h3 : term31 t) (h4 : term32 s t) : (term33 t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h5 : term33 t => @lem5197224 s t h1 h5 h2 h3) (fun h5 : (term765 s t) = (term36 s t) => @lem5197217 s t h4)). Qed.
Lemma lem5197226 (s : real -> Prop) (t : real -> Prop) (h1 : term33 s) (h2 : term31 s) (h3 : term31 t) (h4 : term32 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197225 s t h1 h2 h3 h4) (@lem5197217 s t h4)). Qed.
Lemma lem5197227 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term33 s) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h4 : term33 s => @lem5197226 s t h4 h1 h2 h3) (fun h4 : (term765 s t) = (term36 s t) => @lem5197218 s t h3)). Qed.
Lemma lem5197228 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197227 s t h1 h2 h3) (@lem5197218 s t h3)). Qed.
Lemma lem5197229 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term31 t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h4 : term31 t => @lem5197228 s t h1 h2 h3) (fun h4 : (term765 s t) = (term36 s t) => @lem5190296 t h2)). Qed.
Lemma lem5197230 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term32 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197229 s t h1 h2 h3) (@lem5190296 t h2)). Qed.
Lemma lem5197231 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term30 s t) : (term32 s t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h4 : term32 s t => @lem5197230 s t h1 h2 h4) (fun h4 : (term765 s t) = (term36 s t) => @lem5197215 s t h3)). Qed.
Lemma lem5197232 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term31 t) (h3 : term30 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197231 s t h1 h2 h3) (@lem5197215 s t h3)). Qed.
Lemma lem5197233 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term31 t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h3 : term31 t => @lem5197232 s t h1 h3 h2) (fun h3 : (term765 s t) = (term36 s t) => @lem5197216 s t h2)). Qed.
Lemma lem5197234 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197233 s t h1 h2) (@lem5197216 s t h2)). Qed.
Lemma lem5197235 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term31 s) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h3 : term31 s => @lem5197234 s t h1 h2) (fun h3 : (term765 s t) = (term36 s t) => @lem5190294 s h1)). Qed.
Lemma lem5197236 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term30 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197235 s t h1 h2) (@lem5190294 s h1)). Qed.
Lemma lem5197237 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term29 s t) : (term30 s t) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h3 : term30 s t => @lem5197236 s t h1 h3) (fun h3 : (term765 s t) = (term36 s t) => @lem5197213 s t h2)). Qed.
Lemma lem5197238 (s : real -> Prop) (t : real -> Prop) (h1 : term31 s) (h2 : term29 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197237 s t h1 h2) (@lem5197213 s t h2)). Qed.
Lemma lem5197239 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : (term31 s) = ((term765 s t) = (term36 s t)).
Proof. exact (prop_ext (fun h2 : term31 s => @lem5197238 s t h2 h1) (fun h2 : (term765 s t) = (term36 s t) => @lem5197214 s t h1)). Qed.
Lemma lem5197240 (s : real -> Prop) (t : real -> Prop) (h1 : term29 s t) : (term765 s t) = (term36 s t).
Proof. exact (EQ_MP (@lem5197239 s t h1) (@lem5197214 s t h1)). Qed.
Lemma lem5197241 (s : real -> Prop) (t : real -> Prop) : term766 s t.
Proof. exact (fun h0 : term29 s t => @lem5197240 s t h0). Qed.
Lemma lem5197246 (s : real -> Prop) : term767 s.
Proof. exact (fun t : real -> Prop => @lem5197241 s t). Qed.
Lemma lem5197251 : term768.
Proof. exact (fun s : real -> Prop => @lem5197246 s). Qed.
