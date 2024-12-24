Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_RECURSION_DELETE_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_DELETE_IMP_spec.
Require Import FINITE_RECURSION_spec.
Require Import IN_DELETE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3816239 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3816240 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3816241 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3816240 A s) (@lem3816239 A s)). Qed.
Lemma lem3816242 {A : Type'} (s : A -> Prop) (x : A) : term2 A s x.
Proof. exact (@lem3816241 A s x). Qed.
Lemma lem3816243 {A : Type'} (s : A -> Prop) (x : A) : (term2 A s x) = (term3 A s x).
Proof. exact (eq_refl (term2 A s x)). Qed.
Lemma lem3816244 {A : Type'} (s : A -> Prop) (x : A) : term3 A s x.
Proof. exact (EQ_MP (@lem3816243 A s x) (@lem3816242 A s x)). Qed.
Lemma lem3816245 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term4 A s x y.
Proof. exact (@lem3816244 A s x y). Qed.
Lemma lem3816246 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term4 A s x y) = ((term5 A x s y) = (term6 A s x y)).
Proof. exact (eq_refl (term4 A s x y)). Qed.
Lemma lem3816248 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem3816249 {A : Type'} (s : A -> Prop) (h1 : term7 A) : term8 A s.
Proof. exact (@lem3816248 A h1 s). Qed.
Lemma lem3816250 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem3816251 {A : Type'} (s : A -> Prop) (h1 : term7 A) : term9 A s.
Proof. exact (EQ_MP (@lem3816250 A s) (@lem3816249 A s h1)). Qed.
Lemma lem3816252 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A) : term10 A s x.
Proof. exact (@lem3816251 A s h1 x). Qed.
Lemma lem3816253 {A : Type'} (s : A -> Prop) (x : A) : (term10 A s x) = (term11 A s x).
Proof. exact (eq_refl (term10 A s x)). Qed.
Lemma lem3816254 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A) : term11 A s x.
Proof. exact (EQ_MP (@lem3816253 A s x) (@lem3816252 A s x h1)). Qed.
Lemma lem3816255 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3816256 {A : Type'} (x : A) (s : A -> Prop) (h1 : term7 A) (h2 : @FINITE A s) : term12 A s x.
Proof. exact (@lem3816254 A s x h1 (@lem3816255 A s h2)). Qed.
Lemma lem3816257 {A : Type'} (s : A -> Prop) (h1 : term7 A) (h2 : @FINITE A s) : term13 A s.
Proof. exact (fun x : A => @lem3816256 A x s h1 h2). Qed.
Lemma lem3816258 {A : Type'} (s : A -> Prop) (h1 : term7 A) : term14 A s.
Proof. exact (fun h0 : @FINITE A s => @lem3816257 A s h1 h0). Qed.
Lemma lem3816259 {A : Type'} (h1 : term7 A) : term15 A.
Proof. exact (fun s : A -> Prop => @lem3816258 A s h1). Qed.
Lemma lem3816260 {A : Type'} : term16 A.
Proof. exact (fun h0 : term7 A => @lem3816259 A h0). Qed.
Lemma lem3816261 {A : Type'} : term15 A.
Proof. exact (@lem3816260 A (@lem3609207 A)). Qed.
Lemma lem3816262 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3816261 A s). Qed.
Lemma lem3816263 {A : Type'} (s : A -> Prop) : (term17 A s) = (term14 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem3816265 {A : Type'} (x : A) (s : A -> Prop) : term18 A x s.
Proof. exact (@lem9784 (@IN A x s)). Qed.
Lemma lem3816266 {A : Type'} (x : A) (s : A -> Prop) : (term18 A x s) = (term19 A x s).
Proof. exact (eq_refl (term18 A x s)). Qed.
Lemma lem3816267 {A : Type'} (x : A) (s : A -> Prop) : term19 A x s.
Proof. exact (EQ_MP (@lem3816266 A x s) (@lem3816265 A x s)). Qed.
Lemma lem3816268 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3816269 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : term20 A x s.
Proof. exact (h1). Qed.
Lemma lem3816270 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (h1). Qed.
Lemma lem3816271 {A B : Type'} (f : type1411 A B) (h1 : term21 A B) : term22 A B f.
Proof. exact (@lem3816270 A B h1 f). Qed.
Lemma lem3816272 {A B : Type'} (f : type1411 A B) : (term22 A B f) = (term23 A B f).
Proof. exact (eq_refl (term22 A B f)). Qed.
Lemma lem3816273 {A B : Type'} (f : type1411 A B) (h1 : term21 A B) : term23 A B f.
Proof. exact (EQ_MP (@lem3816272 A B f) (@lem3816271 A B f h1)). Qed.
Lemma lem3816274 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term21 A B) : term24 A B f b.
Proof. exact (@lem3816273 A B f h1 b). Qed.
Lemma lem3816275 {A B : Type'} (f : type1411 A B) (b : B) : (term24 A B f b) = (term25 A B f b).
Proof. exact (eq_refl (term24 A B f b)). Qed.
Lemma lem3816276 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term21 A B) : term25 A B f b.
Proof. exact (EQ_MP (@lem3816275 A B f b) (@lem3816274 A B f b h1)). Qed.
Lemma lem3816277 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term26 A B f.
Proof. exact (h1). Qed.
Lemma lem3816278 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) (h2 : term21 A B) : term27 A B f b.
Proof. exact (@lem3816276 A B f b h2 (@lem3816277 A B f h1)). Qed.
Lemma lem3816279 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) (h2 : term21 A B) : term28 A B f.
Proof. exact (fun b : B => @lem3816278 A B b f h1 h2). Qed.
Lemma lem3816280 {A B : Type'} (f : type1411 A B) (h1 : term21 A B) : term29 A B f.
Proof. exact (fun h0 : term26 A B f => @lem3816279 A B f h0 h1). Qed.
Lemma lem3816281 {A B : Type'} (h1 : term21 A B) : term30 A B.
Proof. exact (fun f : type1411 A B => @lem3816280 A B f h1). Qed.
Lemma lem3816282 {A B : Type'} : term31 A B.
Proof. exact (fun h0 : term21 A B => @lem3816281 A B h0). Qed.
Lemma lem3816283 {A B : Type'} : term30 A B.
Proof. exact (@lem3816282 A B (@lem3816218 A B)). Qed.
Lemma lem3816284 {A B : Type'} (f : type1411 A B) : term32 A B f.
Proof. exact (@lem3816283 A B f). Qed.
Lemma lem3816285 {A B : Type'} (f : type1411 A B) : (term32 A B f) = (term29 A B f).
Proof. exact (eq_refl (term32 A B f)). Qed.
Lemma lem3816287 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term26 A B f.
Proof. exact (h1). Qed.
Lemma lem3816289 {A B : Type'} (f : type1411 A B) : term29 A B f.
Proof. exact (EQ_MP (@lem3816285 A B f) (@lem3816284 A B f)). Qed.
Lemma lem3816290 {A B : Type'} (f : type1411 A B) : term29 A B f.
Proof. exact (@lem3816289 A B f). Qed.
Lemma lem3816291 {A B : Type'} (f : type1411 A B) (h1 : term26 A B f) : term28 A B f.
Proof. exact (@lem3816290 A B f (@lem3816287 A B f h1)). Qed.
Lemma lem3816292 {A B : Type'} (f : type1411 A B) (h1 : term28 A B f) : term28 A B f.
Proof. exact (h1). Qed.
Lemma lem3816293 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term28 A B f) : term33 A B f b.
Proof. exact (@lem3816292 A B f h1 b). Qed.
Lemma lem3816294 {A B : Type'} (f : type1411 A B) (b : B) : (term33 A B f b) = (term27 A B f b).
Proof. exact (eq_refl (term33 A B f b)). Qed.
Lemma lem3816295 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term28 A B f) : term27 A B f b.
Proof. exact (EQ_MP (@lem3816294 A B f b) (@lem3816293 A B b f h1)). Qed.
Lemma lem3816296 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term34 A B f b.
Proof. exact (h1). Qed.
Lemma lem3816297 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : (@ITSET B A f (@EMPTY A) b) = b.
Proof. exact (h1). Qed.
Lemma lem3816311 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : (@ITSET B A f (@EMPTY A) b) = b.
Proof. exact (h1). Qed.
Lemma lem3816312 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3816313 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : (term35 A B f b) = (@eq B b).
Proof. exact (MK_COMB (@lem3816312 B) (@lem3816311 A B f b h1)). Qed.
Lemma lem3816314 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3816315 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : ((@ITSET B A f (@EMPTY A) b) = b) = (b = b).
Proof. exact (MK_COMB (@lem3816313 A B f b h1) (@lem3816314 B b)). Qed.
Lemma lem3816317 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3816318 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3816317 B x). Qed.
Lemma lem3816319 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem3816318 B b). Qed.
Lemma lem3816320 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : ((@ITSET B A f (@EMPTY A) b) = b) = True.
Proof. exact (TRANS (@lem3816315 A B f b h1) (@lem3816319 B b)). Qed.
Lemma lem3816321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3816322 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : (term36 A B f b) = (and True).
Proof. exact (MK_COMB (@lem3816321) (@lem3816320 A B f b h1)). Qed.
Lemma lem3816335 {A B : Type'} (f : type1411 A B) (b : B) : (term37 A B f b) = (term37 A B f b).
Proof. exact (eq_refl (term37 A B f b)). Qed.
Lemma lem3816336 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : (term38 A B f b) = (term39 A B f b).
Proof. exact (MK_COMB (@lem3816322 A B f b h1) (@lem3816335 A B f b)). Qed.
Lemma lem3816338 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3816339 {A B : Type'} (f : type1411 A B) (b : B) : (term39 A B f b) = (term37 A B f b).
Proof. exact (@lem3816338 (term37 A B f b)). Qed.
Lemma lem3816352 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : (term38 A B f b) = (term37 A B f b).
Proof. exact (TRANS (@lem3816336 A B f b h1) (@lem3816339 A B f b)). Qed.
Lemma lem3816353 {A B : Type'} (f : type1411 A B) (b : B) (h1 : (@ITSET B A f (@EMPTY A) b) = b) : (term37 A B f b) = (term38 A B f b).
Proof. exact (SYM (@lem3816352 A B f b h1)). Qed.
Lemma lem3816362 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem3816369 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem3816362 A x s) (@lem3816268 A x s h1)). Qed.
Lemma lem3816370 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem3816371 {A B : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term40 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem3816370 B) (@lem3816369 A x s h1)). Qed.
Lemma lem3816372 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term41 A B f s x b) = (term41 A B f s x b).
Proof. exact (eq_refl (term41 A B f s x b)). Qed.
Lemma lem3816373 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term42 A B f s x b) = (term43 A B f s x b).
Proof. exact (MK_COMB (@lem3816371 A B x s h1) (@lem3816372 A B f s x b)). Qed.
Lemma lem3816374 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term44 A B f s x b) = (term44 A B f s x b).
Proof. exact (eq_refl (term44 A B f s x b)). Qed.
Lemma lem3816375 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term45 A B f s x b) = (term46 A B f s x b).
Proof. exact (MK_COMB (@lem3816373 A B f b x s h1) (@lem3816374 A B f s x b)). Qed.
Lemma lem3816377 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3816378 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem3816377 B t2 t1). Qed.
Lemma lem3816379 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term46 A B f s x b) = (term41 A B f s x b).
Proof. exact (@lem3816378 B (term44 A B f s x b) (term41 A B f s x b)). Qed.
Lemma lem3816380 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term45 A B f s x b) = (term41 A B f s x b).
Proof. exact (TRANS (@lem3816375 A B f b x s h1) (@lem3816379 A B f s x b)). Qed.
Lemma lem3816381 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) : (term47 A B f s b) = (term47 A B f s b).
Proof. exact (eq_refl (term47 A B f s b)). Qed.
Lemma lem3816382 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : ((@ITSET B A f s b) = (term45 A B f s x b)) = ((@ITSET B A f s b) = (term41 A B f s x b)).
Proof. exact (MK_COMB (@lem3816381 A B f s b) (@lem3816380 A B f b x s h1)). Qed.
Lemma lem3816385 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem3816386 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term49 A B f s x b) = (term50 A B f s x b).
Proof. exact (MK_COMB (@lem3816385 A s) (@lem3816382 A B f b x s h1)). Qed.
Lemma lem3816389 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term50 A B f s x b) = (term49 A B f s x b).
Proof. exact (SYM (@lem3816386 A B f b x s h1)). Qed.
Lemma lem3816398 {A : Type'} (x : A) (s : A -> Prop) : term51 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3816405 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : (@IN A x s) = False.
Proof. exact (@lem3816398 A x s (@lem3816269 A x s h1)). Qed.
Lemma lem3816406 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem3816407 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : (term40 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem3816406 B) (@lem3816405 A x s h1)). Qed.
Lemma lem3816408 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term41 A B f s x b) = (term41 A B f s x b).
Proof. exact (eq_refl (term41 A B f s x b)). Qed.
Lemma lem3816409 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : (term42 A B f s x b) = (term52 A B f s x b).
Proof. exact (MK_COMB (@lem3816407 A B x s h1) (@lem3816408 A B f s x b)). Qed.
Lemma lem3816410 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term44 A B f s x b) = (term44 A B f s x b).
Proof. exact (eq_refl (term44 A B f s x b)). Qed.
Lemma lem3816411 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : (term45 A B f s x b) = (term53 A B f s x b).
Proof. exact (MK_COMB (@lem3816409 A B f b x s h1) (@lem3816410 A B f s x b)). Qed.
Lemma lem3816413 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3816414 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem3816413 B t1 t2). Qed.
Lemma lem3816415 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term53 A B f s x b) = (term44 A B f s x b).
Proof. exact (@lem3816414 B (term41 A B f s x b) (term44 A B f s x b)). Qed.
Lemma lem3816416 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : (term45 A B f s x b) = (term44 A B f s x b).
Proof. exact (TRANS (@lem3816411 A B f b x s h1) (@lem3816415 A B f s x b)). Qed.
Lemma lem3816417 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) : (term47 A B f s b) = (term47 A B f s b).
Proof. exact (eq_refl (term47 A B f s b)). Qed.
Lemma lem3816418 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : ((@ITSET B A f s b) = (term45 A B f s x b)) = ((@ITSET B A f s b) = (term44 A B f s x b)).
Proof. exact (MK_COMB (@lem3816417 A B f s b) (@lem3816416 A B f b x s h1)). Qed.
Lemma lem3816421 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem3816422 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : (term49 A B f s x b) = (term54 A B f s x b).
Proof. exact (MK_COMB (@lem3816421 A s) (@lem3816418 A B f b x s h1)). Qed.
Lemma lem3816425 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : (term54 A B f s x b) = (term49 A B f s x b).
Proof. exact (SYM (@lem3816422 A B f b x s h1)). Qed.
Lemma lem3816426 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3816428 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem3816263 A s) (@lem3816262 A s)). Qed.
Lemma lem3816429 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3816428 A s). Qed.
Lemma lem3816430 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term13 A s.
Proof. exact (@lem3816429 A s (@lem3816426 A s h1)). Qed.
Lemma lem3816431 {A : Type'} (s : A -> Prop) (h1 : term13 A s) : term13 A s.
Proof. exact (h1). Qed.
Lemma lem3816432 {A : Type'} (x : A) (s : A -> Prop) (h1 : term13 A s) : term55 A s x.
Proof. exact (@lem3816431 A s h1 x). Qed.
Lemma lem3816433 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (term12 A s x).
Proof. exact (eq_refl (term55 A s x)). Qed.
Lemma lem3816434 {A : Type'} (x : A) (s : A -> Prop) (h1 : term13 A s) : term12 A s x.
Proof. exact (EQ_MP (@lem3816433 A s x) (@lem3816432 A x s h1)). Qed.
Lemma lem3816435 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term34 A B f b.
Proof. exact (h1). Qed.
Lemma lem3816436 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term56 A B f b x.
Proof. exact (@lem3816435 A B f b h1 x). Qed.
Lemma lem3816437 {A B : Type'} (x : A) (f : type1411 A B) (b : B) : (term56 A B f b x) = (term57 A B x f b).
Proof. exact (eq_refl (term56 A B f b x)). Qed.
Lemma lem3816438 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term57 A B x f b.
Proof. exact (EQ_MP (@lem3816437 A B x f b) (@lem3816436 A B x f b h1)). Qed.
Lemma lem3816439 {A B : Type'} (x : A) (s : A -> Prop) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term58 A B x f b s.
Proof. exact (@lem3816438 A B x f b h1 s). Qed.
Lemma lem3816440 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) : (term58 A B x f b s) = (term59 A B x f s b).
Proof. exact (eq_refl (term58 A B x f b s)). Qed.
Lemma lem3816441 {A B : Type'} (x : A) (s : A -> Prop) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term59 A B x f s b.
Proof. exact (EQ_MP (@lem3816440 A B x f s b) (@lem3816439 A B x s f b h1)). Qed.
Lemma lem3816442 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3816443 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (h1 : term34 A B f b) (h2 : @FINITE A s) : (term60 A B f x s b) = (term61 A B x f s b).
Proof. exact (@lem3816441 A B x s f b h1 (@lem3816442 A s h2)). Qed.
Lemma lem3816444 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (h1 : term34 A B f b) (h2 : @FINITE A s) : term62 A B f s b.
Proof. exact (fun x : A => @lem3816443 A B x f b s h1 h2). Qed.
Lemma lem3816445 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term63 A B f s b.
Proof. exact (fun h0 : @FINITE A s => @lem3816444 A B f b s h1 h0). Qed.
Lemma lem3816446 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term64 A B f b.
Proof. exact (fun s : A -> Prop => @lem3816445 A B s f b h1). Qed.
Lemma lem3816447 {A B : Type'} (f : type1411 A B) (b : B) : term65 A B f b.
Proof. exact (fun h0 : term34 A B f b => @lem3816446 A B f b h0). Qed.
Lemma lem3816448 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term64 A B f b.
Proof. exact (@lem3816447 A B f b (@lem3816296 A B f b h1)). Qed.
Lemma lem3816449 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term66 A B f b s.
Proof. exact (@lem3816448 A B f b h1 s). Qed.
Lemma lem3816450 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) : (term66 A B f b s) = (term63 A B f s b).
Proof. exact (eq_refl (term66 A B f b s)). Qed.
Lemma lem3816453 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term63 A B f s b.
Proof. exact (EQ_MP (@lem3816450 A B f s b) (@lem3816449 A B s f b h1)). Qed.
Lemma lem3816454 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term63 A B f s b.
Proof. exact (@lem3816453 A B s f b h1). Qed.
Lemma lem3816455 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term67 A B f s x b.
Proof. exact (@lem3816454 A B (@DELETE A s x) f b h1). Qed.
Lemma lem3816456 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (h1 : term34 A B f b) (h2 : term13 A s) : term68 A B f s x b.
Proof. exact (@lem3816455 A B s x f b h1 (@lem3816434 A x s h2)). Qed.
Lemma lem3816457 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : term68 A B f s x b) : term68 A B f s x b.
Proof. exact (h1). Qed.
Lemma lem3816458 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : term68 A B f s x b) : term69 A B f s b x.
Proof. exact (@lem3816457 A B f s x b h1 x). Qed.
Lemma lem3816459 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term69 A B f s b x) = ((term70 A B f s x b) = (term71 A B f s x b)).
Proof. exact (eq_refl (term69 A B f s b x)). Qed.
Lemma lem3816460 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : term68 A B f s x b) : (term70 A B f s x b) = (term71 A B f s x b).
Proof. exact (EQ_MP (@lem3816459 A B f s x b) (@lem3816458 A B f s x b h1)). Qed.
Lemma lem3816468 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (EQ_MP (@lem3816246 A s x y) (@lem3816245 A s x y)). Qed.
Lemma lem3816469 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (@lem3816468 A s x y). Qed.
Lemma lem3816470 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term73 A s x).
Proof. exact (@lem3816469 A s x x). Qed.
Lemma lem3816474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3816475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3816474 A x). Qed.
Lemma lem3816476 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3816477 {A : Type'} (x : A) : (term74 A x) = (~ True).
Proof. exact (MK_COMB (@lem3816476) (@lem3816475 A x)). Qed.
Lemma lem3816479 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3816480 {A : Type'} (x : A) : (term74 A x) = False.
Proof. exact (TRANS (@lem3816477 A x) (@lem3816479)). Qed.
Lemma lem3816481 {A : Type'} (x : A) (s : A -> Prop) : (term75 A x s) = (term75 A x s).
Proof. exact (eq_refl (term75 A x s)). Qed.
Lemma lem3816482 {A : Type'} (x : A) (s : A -> Prop) : (term73 A s x) = (term76 A x s).
Proof. exact (MK_COMB (@lem3816481 A x s) (@lem3816480 A x)). Qed.
Lemma lem3816484 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3816485 {A : Type'} (x : A) (s : A -> Prop) : (term76 A x s) = False.
Proof. exact (@lem3816484 (@IN A x s)). Qed.
Lemma lem3816486 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = False.
Proof. exact (TRANS (@lem3816482 A x s) (@lem3816485 A x s)). Qed.
Lemma lem3816487 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = False.
Proof. exact (TRANS (@lem3816470 A s x) (@lem3816486 A s x)). Qed.
Lemma lem3816488 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem3816489 {A B : Type'} (s : A -> Prop) (x : A) : (term77 A B s x) = (@COND B False).
Proof. exact (MK_COMB (@lem3816488 B) (@lem3816487 A s x)). Qed.
Lemma lem3816490 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term44 A B f s x b) = (term44 A B f s x b).
Proof. exact (eq_refl (term44 A B f s x b)). Qed.
Lemma lem3816491 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term78 A B f s x b) = (term79 A B f s x b).
Proof. exact (MK_COMB (@lem3816489 A B s x) (@lem3816490 A B f s x b)). Qed.
Lemma lem3816492 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term41 A B f s x b) = (term41 A B f s x b).
Proof. exact (eq_refl (term41 A B f s x b)). Qed.
Lemma lem3816493 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term71 A B f s x b) = (term80 A B f s x b).
Proof. exact (MK_COMB (@lem3816491 A B f s x b) (@lem3816492 A B f s x b)). Qed.
Lemma lem3816495 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3816496 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem3816495 B t1 t2). Qed.
Lemma lem3816497 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term80 A B f s x b) = (term41 A B f s x b).
Proof. exact (@lem3816496 B (term44 A B f s x b) (term41 A B f s x b)). Qed.
Lemma lem3816498 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term71 A B f s x b) = (term41 A B f s x b).
Proof. exact (TRANS (@lem3816493 A B f s x b) (@lem3816497 A B f s x b)). Qed.
Lemma lem3816499 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term81 A B f s x b) = (term81 A B f s x b).
Proof. exact (eq_refl (term81 A B f s x b)). Qed.
Lemma lem3816500 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : ((term70 A B f s x b) = (term71 A B f s x b)) = ((term70 A B f s x b) = (term41 A B f s x b)).
Proof. exact (MK_COMB (@lem3816499 A B f s x b) (@lem3816498 A B f s x b)). Qed.
Lemma lem3816503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3816504 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term82 A B f s x b) = (term83 A B f s x b).
Proof. exact (MK_COMB (@lem3816503) (@lem3816500 A B f s x b)). Qed.
Lemma lem3816507 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : ((@ITSET B A f s b) = (term41 A B f s x b)) = ((@ITSET B A f s b) = (term41 A B f s x b)).
Proof. exact (eq_refl ((@ITSET B A f s b) = (term41 A B f s x b))). Qed.
Lemma lem3816508 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term84 A B f s x b) = (term85 A B f s x b).
Proof. exact (MK_COMB (@lem3816504 A B f s x b) (@lem3816507 A B f s x b)). Qed.
Lemma lem3816513 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term85 A B f s x b) = (term84 A B f s x b).
Proof. exact (SYM (@lem3816508 A B f s x b)). Qed.
Lemma lem3816514 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : (term70 A B f s x b) = (term41 A B f s x b)) : (term70 A B f s x b) = (term41 A B f s x b).
Proof. exact (h1). Qed.
Lemma lem3816515 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : (term70 A B f s x b) = (term41 A B f s x b)) : (term41 A B f s x b) = (term70 A B f s x b).
Proof. exact (SYM (@lem3816514 A B f s x b h1)). Qed.
Lemma lem3816516 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) : (term86 A B f s b) = (term86 A B f s b).
Proof. exact (eq_refl (term86 A B f s b)). Qed.
Lemma lem3816517 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : (term70 A B f s x b) = (term41 A B f s x b)) : (term87 A B f s x b) = (term88 A B f s x b).
Proof. exact (MK_COMB (@lem3816516 A B f s b) (@lem3816515 A B f s x b h1)). Qed.
Lemma lem3816518 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term88 A B f s x b) = ((@ITSET B A f s b) = (term70 A B f s x b)).
Proof. exact (eq_refl (term88 A B f s x b)). Qed.
Lemma lem3816519 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term89 A B f s x b) = (term89 A B f s x b).
Proof. exact (eq_refl (term89 A B f s x b)). Qed.
Lemma lem3816520 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : ((term87 A B f s x b) = (term88 A B f s x b)) = ((term87 A B f s x b) = ((@ITSET B A f s b) = (term70 A B f s x b))).
Proof. exact (MK_COMB (@lem3816519 A B f s x b) (@lem3816518 A B f s x b)). Qed.
Lemma lem3816521 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term87 A B f s x b) = ((@ITSET B A f s b) = (term41 A B f s x b)).
Proof. exact (eq_refl (term87 A B f s x b)). Qed.
Lemma lem3816522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3816523 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : (term89 A B f s x b) = (term90 A B f s x b).
Proof. exact (MK_COMB (@lem3816522) (@lem3816521 A B f s x b)). Qed.
Lemma lem3816524 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : ((@ITSET B A f s b) = (term70 A B f s x b)) = ((@ITSET B A f s b) = (term70 A B f s x b)).
Proof. exact (eq_refl ((@ITSET B A f s b) = (term70 A B f s x b))). Qed.
Lemma lem3816525 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : ((term87 A B f s x b) = ((@ITSET B A f s b) = (term70 A B f s x b))) = (((@ITSET B A f s b) = (term41 A B f s x b)) = ((@ITSET B A f s b) = (term70 A B f s x b))).
Proof. exact (MK_COMB (@lem3816523 A B f s x b) (@lem3816524 A B f s x b)). Qed.
Lemma lem3816526 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) : ((term87 A B f s x b) = (term88 A B f s x b)) = (((@ITSET B A f s b) = (term41 A B f s x b)) = ((@ITSET B A f s b) = (term70 A B f s x b))).
Proof. exact (TRANS (@lem3816520 A B f s x b) (@lem3816525 A B f s x b)). Qed.
Lemma lem3816527 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : (term70 A B f s x b) = (term41 A B f s x b)) : ((@ITSET B A f s b) = (term41 A B f s x b)) = ((@ITSET B A f s b) = (term70 A B f s x b)).
Proof. exact (EQ_MP (@lem3816526 A B f s x b) (@lem3816517 A B f s x b h1)). Qed.
Lemma lem3816528 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (b : B) (h1 : (term70 A B f s x b) = (term41 A B f s x b)) : ((@ITSET B A f s b) = (term70 A B f s x b)) = ((@ITSET B A f s b) = (term41 A B f s x b)).
Proof. exact (SYM (@lem3816527 A B f s x b h1)). Qed.
Lemma lem3816529 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3816530 {A B : Type'} (f : type1411 A B) : (@ITSET B A f) = (@ITSET B A f).
Proof. exact (eq_refl (@ITSET B A f)). Qed.
Lemma lem3816536 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term91 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3816537 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term91 A s t).
Proof. exact (@lem3816536 A s t). Qed.
Lemma lem3816538 {A : Type'} (s : A -> Prop) (x : A) : (s = (term92 A s x)) = (term93 A s x).
Proof. exact (@lem3816537 A s (term92 A s x)). Qed.
Lemma lem3816547 {A : Type'} (x : A) (s : A -> Prop) : (term94 A x s) = (term94 A x s).
Proof. exact (eq_refl (term94 A x s)). Qed.
Lemma lem3816548 {A : Type'} (s : A -> Prop) (x : A) : (term95 A s x) = (term96 A s x).
Proof. exact (MK_COMB (@lem3816547 A x s) (@lem3816538 A s x)). Qed.
Lemma lem3816551 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term95 A s x).
Proof. exact (SYM (@lem3816548 A s x)). Qed.
Lemma lem3816555 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3816556 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3816555 A P x). Qed.
Lemma lem3816557 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3816556 A s x). Qed.
Lemma lem3816558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3816559 {A : Type'} (s : A -> Prop) (x : A) : (term94 A x s) = (term97 A s x).
Proof. exact (MK_COMB (@lem3816558) (@lem3816557 A s x)). Qed.
Lemma lem3816567 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3816568 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3816567 A P x). Qed.
Lemma lem3816569 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3816568 A s x'). Qed.
Lemma lem3816570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3816571 {A : Type'} (s : A -> Prop) (x' : A) : (term98 A x' s) = (term99 A s x').
Proof. exact (MK_COMB (@lem3816570) (@lem3816569 A s x')). Qed.
Lemma lem3816573 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term100 A x y s) = (term101 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3816574 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term100 A x y s) = (term101 A y x s).
Proof. exact (@lem3816573 A y x s). Qed.
Lemma lem3816575 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term102 A x' s x) = (term103 A x' s x).
Proof. exact (@lem3816574 A x x' (@DELETE A s x)). Qed.
Lemma lem3816581 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3816582 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (@lem3816581 A s x y). Qed.
Lemma lem3816583 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term5 A x' s x) = (term6 A s x' x).
Proof. exact (@lem3816582 A s x' x). Qed.
Lemma lem3816587 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3816588 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3816587 A P x). Qed.
Lemma lem3816589 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3816588 A s x'). Qed.
Lemma lem3816590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3816591 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A x' s) = (term104 A s x').
Proof. exact (MK_COMB (@lem3816590) (@lem3816589 A s x')). Qed.
Lemma lem3816594 {A : Type'} (x' : A) (x : A) : (term105 A x' x) = (term105 A x' x).
Proof. exact (eq_refl (term105 A x' x)). Qed.
Lemma lem3816595 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term6 A s x' x) = (term106 A s x' x).
Proof. exact (MK_COMB (@lem3816591 A s x') (@lem3816594 A x' x)). Qed.
Lemma lem3816598 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term5 A x' s x) = (term106 A s x' x).
Proof. exact (TRANS (@lem3816583 A s x' x) (@lem3816595 A s x' x)). Qed.
Lemma lem3816599 {A : Type'} (x' : A) (x : A) : (term107 A x' x) = (term107 A x' x).
Proof. exact (eq_refl (term107 A x' x)). Qed.
Lemma lem3816600 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term103 A x' s x) = (term108 A s x' x).
Proof. exact (MK_COMB (@lem3816599 A x' x) (@lem3816598 A s x' x)). Qed.
Lemma lem3816603 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term102 A x' s x) = (term108 A s x' x).
Proof. exact (TRANS (@lem3816575 A x' s x) (@lem3816600 A s x' x)). Qed.
Lemma lem3816604 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((@IN A x' s) = (term102 A x' s x)) = ((s x') = (term108 A s x' x)).
Proof. exact (MK_COMB (@lem3816571 A s x') (@lem3816603 A s x' x)). Qed.
Lemma lem3816607 {A : Type'} (s : A -> Prop) (x : A) : (term109 A s x) = (term110 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3816604 A s x' x)). Qed.
Lemma lem3816608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3816609 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term111 A s x).
Proof. exact (MK_COMB (@lem3816608 A) (@lem3816607 A s x)). Qed.
Lemma lem3816614 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term112 A s x).
Proof. exact (MK_COMB (@lem3816559 A s x) (@lem3816609 A s x)). Qed.
Lemma lem3816617 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term96 A s x).
Proof. exact (SYM (@lem3816614 A s x)). Qed.
Lemma lem3816619 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3816620 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term114 A s x).
Proof. exact (@lem3816619 (term112 A s x)). Qed.
Lemma lem3816621 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term112 A s x).
Proof. exact (SYM (@lem3816620 A s x)). Qed.
Lemma lem3816622 {A : Type'} (s : A -> Prop) (x : A) (h1 : term115 A s x) : term115 A s x.
Proof. exact (h1). Qed.
Lemma lem3816625 {A : Type'} (s : A -> Prop) (x : A) (h1 : term114 A s x) : term114 A s x.
Proof. exact (h1). Qed.
Lemma lem3816626 {A : Type'} (s : A -> Prop) (x : A) : term116 A s x.
Proof. exact (fun h0 : term114 A s x => @lem3816625 A s x h0). Qed.
Lemma lem3816627 {A : Type'} (s : A -> Prop) (x : A) (h1 : term116 A s x) : term116 A s x.
Proof. exact (h1). Qed.
Lemma lem3816628 {A : Type'} (s : A -> Prop) (x : A) (h1 : term114 A s x) : term114 A s x.
Proof. exact (h1). Qed.
Lemma lem3816629 {A : Type'} (s : A -> Prop) (x : A) (h1 : term114 A s x) (h2 : term116 A s x) : term114 A s x.
Proof. exact (@lem3816627 A s x h2 (@lem3816628 A s x h1)). Qed.
Lemma lem3816630 {A : Type'} (s : A -> Prop) (x : A) (h1 : term114 A s x) : term117 A s x.
Proof. exact (fun h0 : term116 A s x => @lem3816629 A s x h1 h0). Qed.
Lemma lem3816631 {A : Type'} (s : A -> Prop) (x : A) (h1 : term116 A s x) : term116 A s x.
Proof. exact (h1). Qed.
Lemma lem3816632 {A : Type'} (s : A -> Prop) (x : A) (h1 : term114 A s x) (h2 : term116 A s x) : term114 A s x.
Proof. exact (@lem3816630 A s x h1 (@lem3816631 A s x h2)). Qed.
Lemma lem3816633 {A : Type'} (s : A -> Prop) (x : A) (h1 : term116 A s x) : term116 A s x.
Proof. exact (fun h0 : term114 A s x => @lem3816632 A s x h0 h1). Qed.
Lemma lem3816634 {A : Type'} (s : A -> Prop) (x : A) : term118 A s x.
Proof. exact (fun h0 : term116 A s x => @lem3816633 A s x h0). Qed.
Lemma lem3816637 {A : Type'} (s : A -> Prop) (x : A) : term116 A s x.
Proof. exact (@lem3816634 A s x (@lem3816626 A s x)). Qed.
Lemma lem3816638 {A : Type'} (s : A -> Prop) (x : A) : term116 A s x.
Proof. exact (@lem3816637 A s x). Qed.
Lemma lem3816648 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3816649 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term119 A s x).
Proof. exact (@lem3816648 (term115 A s x)). Qed.
Lemma lem3816651 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3816652 {A : Type'} (s : A -> Prop) (x : A) : (term119 A s x) = (term112 A s x).
Proof. exact (@lem3816651 (term112 A s x)). Qed.
Lemma lem3816655 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term112 A s x).
Proof. exact (TRANS (@lem3816649 A s x) (@lem3816652 A s x)). Qed.
Lemma lem3816664 {A : Type'} (x : A) : (term121 A x) = (term122 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3816655 A s x)). Qed.
Lemma lem3816665 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3816666 {A : Type'} (x : A) : (term123 A x) = (term124 A x).
Proof. exact (MK_COMB (@lem3816665 A) (@lem3816664 A x)). Qed.
Lemma lem3816671 {A : Type'} : (term125 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3816666 A x)). Qed.
Lemma lem3816672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3816681 {A : Type'} : (term127 A) = (term128 A).
Proof. exact (MK_COMB (@lem3816672 A) (@lem3816671 A)). Qed.
Lemma lem3816696 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term108 A s x' x)) = ((s x') = (term108 A s x' x)).
Proof. exact (eq_refl ((s x') = (term108 A s x' x))). Qed.
Lemma lem3816697 {A : Type'} (s : A -> Prop) (x : A) : (term110 A s x) = (term110 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3816696 A s x' x)). Qed.
Lemma lem3816698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3816699 {A : Type'} (s : A -> Prop) (x : A) : (term111 A s x) = (term111 A s x).
Proof. exact (MK_COMB (@lem3816698 A) (@lem3816697 A s x)). Qed.
Lemma lem3816702 {A : Type'} (s : A -> Prop) (x : A) : (term97 A s x) = (term97 A s x).
Proof. exact (eq_refl (term97 A s x)). Qed.
Lemma lem3816703 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (MK_COMB (@lem3816702 A s x) (@lem3816699 A s x)). Qed.
Lemma lem3816704 {A : Type'} (x : A) : (term122 A x) = (term122 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3816703 A s x)). Qed.
Lemma lem3816705 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3816706 {A : Type'} (x : A) : (term124 A x) = (term124 A x).
Proof. exact (MK_COMB (@lem3816705 A) (@lem3816704 A x)). Qed.
Lemma lem3816707 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3816706 A x)). Qed.
Lemma lem3816708 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3816709 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (MK_COMB (@lem3816708 A) (@lem3816707 A)). Qed.
Lemma lem3816736 {A : Type'} : (term127 A) = (term128 A).
Proof. exact (TRANS (@lem3816681 A) (@lem3816709 A)). Qed.
Lemma lem3816737 {A : Type'} : (term128 A) = (term127 A).
Proof. exact (SYM (@lem3816736 A)). Qed.
Lemma lem3816740 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3816741 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term108 A s x' x)) = (term129 A s x' x).
Proof. exact (@lem3816740 ((s x') = (term108 A s x' x))). Qed.
Lemma lem3816742 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term129 A s x' x) = ((s x') = (term108 A s x' x)).
Proof. exact (SYM (@lem3816741 A s x' x)). Qed.
Lemma lem3816743 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term130 A s x' x) : term130 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3816749 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3816759 {A : Type'} (x' : A) (x : A) : (term131 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3816761 {A : Type'} (s : A -> Prop) (x' : A) : (term132 A s x') = (term132 A s x').
Proof. exact (eq_refl (term132 A s x')). Qed.
Lemma lem3816762 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term133 A s x' x) = (term134 A s x' x).
Proof. exact (MK_COMB (@lem3816761 A s x') (@lem3816759 A x' x)). Qed.
Lemma lem3816763 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term135 A s x' x) = (term133 A s x' x).
Proof. exact (@lem17045 (s x') (term105 A x' x)). Qed.
Lemma lem3816764 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term135 A s x' x) = (term134 A s x' x).
Proof. exact (TRANS (@lem3816763 A s x' x) (@lem3816762 A s x' x)). Qed.
Lemma lem3816769 {A : Type'} (x' : A) (x : A) : (term136 A x' x) = (term136 A x' x).
Proof. exact (eq_refl (term136 A x' x)). Qed.
Lemma lem3816770 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term137 A s x' x) = (term138 A s x' x).
Proof. exact (MK_COMB (@lem3816769 A x' x) (@lem3816764 A s x' x)). Qed.
Lemma lem3816771 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term139 A s x' x) = (term137 A s x' x).
Proof. exact (@lem17160 (x' = x) (term106 A s x' x)). Qed.
Lemma lem3816772 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term139 A s x' x) = (term138 A s x' x).
Proof. exact (TRANS (@lem3816771 A s x' x) (@lem3816770 A s x' x)). Qed.
Lemma lem3816778 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term140 A s x' x) = (term140 A s x' x).
Proof. exact (eq_refl (term140 A s x' x)). Qed.
Lemma lem3816780 {A : Type'} (s : A -> Prop) (x' : A) : (term104 A s x') = (term104 A s x').
Proof. exact (eq_refl (term104 A s x')). Qed.
Lemma lem3816781 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term141 A s x' x) = (term142 A s x' x).
Proof. exact (MK_COMB (@lem3816780 A s x') (@lem3816772 A s x' x)). Qed.
Lemma lem3816782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3816783 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term143 A s x' x) = (term144 A s x' x).
Proof. exact (MK_COMB (@lem3816782) (@lem3816781 A s x' x)). Qed.
Lemma lem3816784 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term145 A s x' x) = (term146 A s x' x).
Proof. exact (MK_COMB (@lem3816783 A s x' x) (@lem3816778 A s x' x)). Qed.
Lemma lem3816785 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term130 A s x' x) = (term145 A s x' x).
Proof. exact (@lem17646 (s x') (term108 A s x' x)). Qed.
Lemma lem3816790 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term130 A s x' x) = (term146 A s x' x).
Proof. exact (TRANS (@lem3816785 A s x' x) (@lem3816784 A s x' x)). Qed.
Lemma lem3816795 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3816857 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term130 A s x' x) : term146 A s x' x.
Proof. exact (EQ_MP (@lem3816790 A s x' x) (@lem3816743 A s x' x h1)). Qed.
Lemma lem3816858 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : term142 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3816859 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) : term140 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3816860 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : term138 A s x' x.
Proof. exact (proj2 (@lem3816858 A s x' x h1)). Qed.
Lemma lem3816862 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : term134 A s x' x.
Proof. exact (proj2 (@lem3816860 A s x' x h1)). Qed.
Lemma lem3816866 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) : term108 A s x' x.
Proof. exact (proj2 (@lem3816859 A s x' x h1)). Qed.
Lemma lem3816869 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term106 A s x' x) : term106 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3816887 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term147 A s x') : term147 A s x'.
Proof. exact (h1). Qed.
Lemma lem3816903 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3816907 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3816915 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3816939 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term147 A s x') : term147 A s x'.
Proof. exact (h1). Qed.
Lemma lem3816945 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : term105 A x' x.
Proof. exact (proj1 (@lem3816860 A s x' x h1)). Qed.
Lemma lem3816947 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3816949 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3816951 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) : term147 A s x'.
Proof. exact (proj1 (@lem3816859 A s x' x h1)). Qed.
Lemma lem3816953 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3816957 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) : term147 A s x'.
Proof. exact (proj1 (@lem3816859 A s x' x h1)). Qed.
Lemma lem3817003 {A : Type'} (x : A) : (term148 A x) = (term148 A x).
Proof. exact (eq_refl (term148 A x)). Qed.
Lemma lem3817004 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term149 A x x') = (term150 A x).
Proof. exact (MK_COMB (@lem3817003 A x) (@lem3816947 A x' x h1)). Qed.
Lemma lem3817005 {A : Type'} (x : A) : (term150 A x) = (term74 A x).
Proof. exact (eq_refl (term150 A x)). Qed.
Lemma lem3817006 {A : Type'} (x : A) (x' : A) : (term151 A x x') = (term151 A x x').
Proof. exact (eq_refl (term151 A x x')). Qed.
Lemma lem3817007 {A : Type'} (x' : A) (x : A) : ((term149 A x x') = (term150 A x)) = ((term149 A x x') = (term74 A x)).
Proof. exact (MK_COMB (@lem3817006 A x x') (@lem3817005 A x)). Qed.
Lemma lem3817008 {A : Type'} (x' : A) (x : A) : (term149 A x x') = (term105 A x' x).
Proof. exact (eq_refl (term149 A x x')). Qed.
Lemma lem3817009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3817010 {A : Type'} (x' : A) (x : A) : (term151 A x x') = (term152 A x' x).
Proof. exact (MK_COMB (@lem3817009) (@lem3817008 A x' x)). Qed.
Lemma lem3817011 {A : Type'} (x : A) : (term74 A x) = (term74 A x).
Proof. exact (eq_refl (term74 A x)). Qed.
Lemma lem3817012 {A : Type'} (x' : A) (x : A) : ((term149 A x x') = (term74 A x)) = ((term105 A x' x) = (term74 A x)).
Proof. exact (MK_COMB (@lem3817010 A x' x) (@lem3817011 A x)). Qed.
Lemma lem3817013 {A : Type'} (x' : A) (x : A) : ((term149 A x x') = (term150 A x)) = ((term105 A x' x) = (term74 A x)).
Proof. exact (TRANS (@lem3817007 A x' x) (@lem3817012 A x' x)). Qed.
Lemma lem3817014 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term105 A x' x) = (term74 A x).
Proof. exact (EQ_MP (@lem3817013 A x' x) (@lem3817004 A x' x h1)). Qed.
Lemma lem3817015 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : term74 A x.
Proof. exact (EQ_MP (@lem3817014 A x' x h2) (@lem3816945 A s x' x h1)). Qed.
Lemma lem3817043 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3817044 {A : Type'} (s : A -> Prop) : (term153 A s) = (term153 A s).
Proof. exact (eq_refl (term153 A s)). Qed.
Lemma lem3817045 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term154 A s x') = (term154 A s x).
Proof. exact (MK_COMB (@lem3817044 A s) (@lem3816953 A x' x h1)). Qed.
Lemma lem3817046 {A : Type'} (s : A -> Prop) (x : A) : (term154 A s x) = (term147 A s x).
Proof. exact (eq_refl (term154 A s x)). Qed.
Lemma lem3817047 {A : Type'} (s : A -> Prop) (x' : A) : (term155 A s x') = (term155 A s x').
Proof. exact (eq_refl (term155 A s x')). Qed.
Lemma lem3817048 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term154 A s x') = (term154 A s x)) = ((term154 A s x') = (term147 A s x)).
Proof. exact (MK_COMB (@lem3817047 A s x') (@lem3817046 A s x)). Qed.
Lemma lem3817049 {A : Type'} (s : A -> Prop) (x' : A) : (term154 A s x') = (term147 A s x').
Proof. exact (eq_refl (term154 A s x')). Qed.
Lemma lem3817050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3817051 {A : Type'} (s : A -> Prop) (x' : A) : (term155 A s x') = (term156 A s x').
Proof. exact (MK_COMB (@lem3817050) (@lem3817049 A s x')). Qed.
Lemma lem3817052 {A : Type'} (s : A -> Prop) (x : A) : (term147 A s x) = (term147 A s x).
Proof. exact (eq_refl (term147 A s x)). Qed.
Lemma lem3817053 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term154 A s x') = (term147 A s x)) = ((term147 A s x') = (term147 A s x)).
Proof. exact (MK_COMB (@lem3817051 A s x') (@lem3817052 A s x)). Qed.
Lemma lem3817054 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term154 A s x') = (term154 A s x)) = ((term147 A s x') = (term147 A s x)).
Proof. exact (TRANS (@lem3817048 A x' s x) (@lem3817053 A x' s x)). Qed.
Lemma lem3817055 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term147 A s x') = (term147 A s x).
Proof. exact (EQ_MP (@lem3817054 A x' s x) (@lem3817045 A s x' x h1)). Qed.
Lemma lem3817056 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) (h2 : x' = x) : term147 A s x.
Proof. exact (EQ_MP (@lem3817055 A s x' x h2) (@lem3816951 A s x' x h1)). Qed.
Lemma lem3817072 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : s x'.
Proof. exact (proj1 (@lem3816858 A s x' x h1)). Qed.
Lemma lem3817073 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : term157 A s x'.
Proof. exact (fun h0 : term147 A s x' => @lem3817072 A s x' x h1). Qed.
Lemma lem3817075 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817076 {A : Type'} (s : A -> Prop) (x' : A) : (term157 A s x') = (s x').
Proof. exact (@lem3817075 (s x')). Qed.
Lemma lem3817077 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3817076 A s x') (@lem3817073 A s x' x h1)). Qed.
Lemma lem3817080 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3817082 {A : Type'} (s : A -> Prop) (x' : A) : (term147 A s x') = (term159 A s x').
Proof. exact (@lem3817080 (s x')). Qed.
Lemma lem3817085 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term147 A s x') : term159 A s x'.
Proof. exact (EQ_MP (@lem3817082 A s x') (@lem3816939 A s x' h1)). Qed.
Lemma lem3817088 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : False.
Proof. exact (@lem3817085 A s x' h1 (@lem3817077 A s x' x h2)). Qed.
Lemma lem3817089 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : term160.
Proof. exact (fun h0 : ~ False => @lem3817088 A s x' x h1 h2). Qed.
Lemma lem3817091 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817092 : term160 = False.
Proof. exact (@lem3817091 False). Qed.
Lemma lem3817093 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817092) (@lem3817089 A s x' x h1 h2)). Qed.
Lemma lem3817109 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3817110 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3817109 A x). Qed.
Lemma lem3817111 {A : Type'} (x : A) : term161 A x.
Proof. exact (fun h0 : term74 A x => @lem3817110 A x). Qed.
Lemma lem3817113 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817114 {A : Type'} (x : A) : (term161 A x) = (x = x).
Proof. exact (@lem3817113 (x = x)). Qed.
Lemma lem3817115 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3817114 A x) (@lem3817111 A x)). Qed.
Lemma lem3817118 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3817120 {A : Type'} (x : A) : (term74 A x) = (term162 A x).
Proof. exact (@lem3817118 (x = x)). Qed.
Lemma lem3817123 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : term162 A x.
Proof. exact (EQ_MP (@lem3817120 A x) (@lem3817015 A s x' x h1 h2)). Qed.
Lemma lem3817126 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3817123 A s x' x h1 h2 (@lem3817115 A x)). Qed.
Lemma lem3817127 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : term160.
Proof. exact (fun h0 : ~ False => @lem3817126 A s x' x h1 h2). Qed.
Lemma lem3817129 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817130 : term160 = False.
Proof. exact (@lem3817129 False). Qed.
Lemma lem3817133 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3817134 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term157 A s x.
Proof. exact (fun h0 : term147 A s x => @lem3817133 A s x h1). Qed.
Lemma lem3817136 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817137 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (s x).
Proof. exact (@lem3817136 (s x)). Qed.
Lemma lem3817138 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3817137 A s x) (@lem3817134 A s x h1)). Qed.
Lemma lem3817141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3817143 {A : Type'} (s : A -> Prop) (x : A) : (term147 A s x) = (term159 A s x).
Proof. exact (@lem3817141 (s x)). Qed.
Lemma lem3817146 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) (h2 : x' = x) : term159 A s x.
Proof. exact (EQ_MP (@lem3817143 A s x) (@lem3817056 A s x' x h1 h2)). Qed.
Lemma lem3817149 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (@lem3817146 A s x' x h2 h3 (@lem3817138 A s x h1)). Qed.
Lemma lem3817150 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : term160.
Proof. exact (fun h0 : ~ False => @lem3817149 A s x' x h1 h2 h3). Qed.
Lemma lem3817152 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817153 : term160 = False.
Proof. exact (@lem3817152 False). Qed.
Lemma lem3817154 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817153) (@lem3817150 A s x' x h1 h2 h3)). Qed.
Lemma lem3817170 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term106 A s x' x) : s x'.
Proof. exact (proj1 (@lem3816869 A s x' x h1)). Qed.
Lemma lem3817171 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term106 A s x' x) : term157 A s x'.
Proof. exact (fun h0 : term147 A s x' => @lem3817170 A s x' x h1). Qed.
Lemma lem3817173 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817174 {A : Type'} (s : A -> Prop) (x' : A) : (term157 A s x') = (s x').
Proof. exact (@lem3817173 (s x')). Qed.
Lemma lem3817175 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term106 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3817174 A s x') (@lem3817171 A s x' x h1)). Qed.
Lemma lem3817178 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3817180 {A : Type'} (s : A -> Prop) (x' : A) : (term147 A s x') = (term159 A s x').
Proof. exact (@lem3817178 (s x')). Qed.
Lemma lem3817183 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) : term159 A s x'.
Proof. exact (EQ_MP (@lem3817180 A s x') (@lem3816957 A s x' x h1)). Qed.
Lemma lem3817186 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) (h2 : term106 A s x' x) : False.
Proof. exact (@lem3817183 A s x' x h1 (@lem3817175 A s x' x h2)). Qed.
Lemma lem3817187 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) (h2 : term106 A s x' x) : term160.
Proof. exact (fun h0 : ~ False => @lem3817186 A s x' x h1 h2). Qed.
Lemma lem3817189 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817190 : term160 = False.
Proof. exact (@lem3817189 False). Qed.
Lemma lem3817191 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term140 A s x' x) (h2 : term106 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817190) (@lem3817187 A s x' x h1 h2)). Qed.
Lemma lem3817192 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3817154 A s x' x h1 h2 h3) (fun h4 : False => @lem3817043 A s x h1)). Qed.
Lemma lem3817194 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817192 A s x' x h1 h2 h3) (@lem3817043 A s x h1)). Qed.
Lemma lem3817195 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817130) (@lem3817127 A s x' x h1 h2)). Qed.
Lemma lem3817196 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3817194 A s x' x h1 h2 h3) (fun h4 : False => @lem3816953 A x' x h3)). Qed.
Lemma lem3817197 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817196 A s x' x h1 h2 h3) (@lem3816953 A x' x h3)). Qed.
Lemma lem3817198 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3817197 A s x' x h1 h2 h3) (fun h4 : False => @lem3816949 A s x h1)). Qed.
Lemma lem3817199 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817198 A s x' x h1 h2 h3) (@lem3816949 A s x h1)). Qed.
Lemma lem3817200 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3817195 A s x' x h1 h2) (fun h3 : False => @lem3816947 A x' x h2)). Qed.
Lemma lem3817201 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817200 A s x' x h1 h2) (@lem3816947 A x' x h2)). Qed.
Lemma lem3817202 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : (term147 A s x') = False.
Proof. exact (prop_ext (fun h3 : term147 A s x' => @lem3817093 A s x' x h1 h2) (fun h3 : False => @lem3816939 A s x' h1)). Qed.
Lemma lem3817203 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817202 A s x' x h1 h2) (@lem3816939 A s x' h1)). Qed.
Lemma lem3817204 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3817199 A s x' x h1 h2 h3) (fun h4 : False => @lem3816915 A x' x h3)). Qed.
Lemma lem3817205 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817204 A s x' x h1 h2 h3) (@lem3816915 A x' x h3)). Qed.
Lemma lem3817206 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3817205 A s x' x h1 h2 h3) (fun h4 : False => @lem3816907 A s x h1)). Qed.
Lemma lem3817207 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817206 A s x' x h1 h2 h3) (@lem3816907 A s x h1)). Qed.
Lemma lem3817208 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3817201 A s x' x h1 h2) (fun h3 : False => @lem3816903 A x' x h2)). Qed.
Lemma lem3817209 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817208 A s x' x h1 h2) (@lem3816903 A x' x h2)). Qed.
Lemma lem3817210 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : (term147 A s x') = False.
Proof. exact (prop_ext (fun h3 : term147 A s x' => @lem3817203 A s x' x h1 h2) (fun h3 : False => @lem3816887 A s x' h1)). Qed.
Lemma lem3817211 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817210 A s x' x h1 h2) (@lem3816887 A s x' h1)). Qed.
Lemma lem3817212 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3817207 A s x' x h1 h2 h3) (fun h4 : False => @lem3816915 A x' x h3)). Qed.
Lemma lem3817213 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817212 A s x' x h1 h2 h3) (@lem3816915 A x' x h3)). Qed.
Lemma lem3817214 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3817213 A s x' x h1 h2 h3) (fun h4 : False => @lem3816907 A s x h1)). Qed.
Lemma lem3817215 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817214 A s x' x h1 h2 h3) (@lem3816907 A s x h1)). Qed.
Lemma lem3817216 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3817209 A s x' x h1 h2) (fun h3 : False => @lem3816903 A x' x h2)). Qed.
Lemma lem3817217 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817216 A s x' x h1 h2) (@lem3816903 A x' x h2)). Qed.
Lemma lem3817218 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : (term147 A s x') = False.
Proof. exact (prop_ext (fun h3 : term147 A s x' => @lem3817211 A s x' x h1 h2) (fun h3 : False => @lem3816887 A s x' h1)). Qed.
Lemma lem3817219 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term142 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817218 A s x' x h1 h2) (@lem3816887 A s x' h1)). Qed.
Lemma lem3817220 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term140 A s x' x) : False.
Proof. exact (or_elim (@lem3816866 A s x' x h2) (fun h0 : x' = x => @lem3817215 A s x' x h1 h2 h0) (fun h0 : term106 A s x' x => @lem3817191 A s x' x h2 h0)). Qed.
Lemma lem3817221 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term142 A s x' x) : False.
Proof. exact (or_elim (@lem3816862 A s x' x h1) (fun h0 : term147 A s x' => @lem3817219 A s x' x h0 h1) (fun h0 : x' = x => @lem3817217 A s x' x h1 h0)). Qed.
Lemma lem3817222 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A s x' x) (h2 : s x) : False.
Proof. exact (or_elim (@lem3816857 A s x' x h1) (fun h0 : term142 A s x' x => @lem3817221 A s x' x h0) (fun h0 : term140 A s x' x => @lem3817220 A s x' x h2 h0)). Qed.
Lemma lem3817223 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3817222 A x' s x h1 h2) (fun h3 : False => @lem3816795 A s x h2)). Qed.
Lemma lem3817224 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3817223 A x' s x h1 h2) (@lem3816795 A s x h2)). Qed.
Lemma lem3817225 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3817224 A x' s x h1 h2) (fun h3 : False => @lem3816749 A s x h2)). Qed.
Lemma lem3817226 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3817225 A x' s x h1 h2) (@lem3816749 A s x h2)). Qed.
Lemma lem3817227 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A s x' x) (h2 : s x) : (term130 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term130 A s x' x => @lem3817226 A x' s x h1 h2) (fun h3 : False => @lem3816743 A s x' x h1)). Qed.
Lemma lem3817228 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3817227 A x' s x h1 h2) (@lem3816743 A s x' x h1)). Qed.
Lemma lem3817229 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : term129 A s x' x.
Proof. exact (fun h0 : term130 A s x' x => @lem3817228 A x' s x h0 h1). Qed.
Lemma lem3817230 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : (s x') = (term108 A s x' x).
Proof. exact (EQ_MP (@lem3816742 A s x' x) (@lem3817229 A x' s x h1)). Qed.
Lemma lem3817235 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term111 A s x.
Proof. exact (fun x' : A => @lem3817230 A x' s x h1). Qed.
Lemma lem3817236 {A : Type'} (s : A -> Prop) (x : A) : term112 A s x.
Proof. exact (fun h0 : s x => @lem3817235 A s x h0). Qed.
Lemma lem3817241 {A : Type'} (x : A) : term124 A x.
Proof. exact (fun s : A -> Prop => @lem3817236 A s x). Qed.
Lemma lem3817246 {A : Type'} : term128 A.
Proof. exact (fun x : A => @lem3817241 A x). Qed.
Lemma lem3817247 {A : Type'} : term127 A.
Proof. exact (EQ_MP (@lem3816737 A) (@lem3817246 A)). Qed.
Lemma lem3817248 {A : Type'} (x : A) : term163 A x.
Proof. exact (@lem3817247 A x). Qed.
Lemma lem3817249 {A : Type'} (x : A) : (term163 A x) = (term123 A x).
Proof. exact (eq_refl (term163 A x)). Qed.
Lemma lem3817250 {A : Type'} (x : A) : term123 A x.
Proof. exact (EQ_MP (@lem3817249 A x) (@lem3817248 A x)). Qed.
Lemma lem3817251 {A : Type'} (x : A) (s : A -> Prop) : term164 A x s.
Proof. exact (@lem3817250 A x s). Qed.
Lemma lem3817252 {A : Type'} (s : A -> Prop) (x : A) : (term164 A x s) = (term114 A s x).
Proof. exact (eq_refl (term164 A x s)). Qed.
Lemma lem3817253 {A : Type'} (s : A -> Prop) (x : A) : term114 A s x.
Proof. exact (EQ_MP (@lem3817252 A s x) (@lem3817251 A x s)). Qed.
Lemma lem3817255 {A : Type'} (s : A -> Prop) (x : A) : term114 A s x.
Proof. exact (@lem3816638 A s x (@lem3817253 A s x)). Qed.
Lemma lem3817256 {A : Type'} (s : A -> Prop) (x : A) (h1 : term115 A s x) : False.
Proof. exact (@lem3817255 A s x (@lem3816622 A s x h1)). Qed.
Lemma lem3817257 {A : Type'} (s : A -> Prop) (x : A) (h1 : term115 A s x) : (term115 A s x) = False.
Proof. exact (prop_ext (fun h2 : term115 A s x => @lem3817256 A s x h1) (fun h2 : False => @lem3816622 A s x h1)). Qed.
Lemma lem3817258 {A : Type'} (s : A -> Prop) (x : A) (h1 : term115 A s x) : False.
Proof. exact (EQ_MP (@lem3817257 A s x h1) (@lem3816622 A s x h1)). Qed.
Lemma lem3817259 {A : Type'} (s : A -> Prop) (x : A) : term114 A s x.
Proof. exact (fun h0 : term115 A s x => @lem3817258 A s x h0). Qed.
Lemma lem3817260 {A : Type'} (s : A -> Prop) (x : A) : term112 A s x.
Proof. exact (EQ_MP (@lem3816621 A s x) (@lem3817259 A s x)). Qed.
Lemma lem3817261 {A : Type'} (s : A -> Prop) (x : A) : term96 A s x.
Proof. exact (EQ_MP (@lem3816617 A s x) (@lem3817260 A s x)). Qed.
Lemma lem3817262 {A : Type'} (s : A -> Prop) (x : A) : term95 A s x.
Proof. exact (EQ_MP (@lem3816551 A s x) (@lem3817261 A s x)). Qed.
Lemma lem3817263 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : s = (term92 A s x).
Proof. exact (@lem3817262 A s x (@lem3816268 A x s h1)). Qed.
Lemma lem3817264 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@ITSET B A f s) = (term165 A B f s x).
Proof. exact (MK_COMB (@lem3816530 A B f) (@lem3817263 A x s h1)). Qed.
Lemma lem3817265 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@ITSET B A f s b) = (term70 A B f s x b).
Proof. exact (MK_COMB (@lem3817264 A B f x s h1) (@lem3816529 B b)). Qed.
Lemma lem3817266 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : (term70 A B f s x b) = (term41 A B f s x b)) (h2 : @IN A x s) : (@ITSET B A f s b) = (term41 A B f s x b).
Proof. exact (EQ_MP (@lem3816528 A B f s x b h1) (@lem3817265 A B f b x s h2)). Qed.
Lemma lem3817267 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term85 A B f s x b.
Proof. exact (fun h0 : (term70 A B f s x b) = (term41 A B f s x b) => @lem3817266 A B f b x s h0 h1). Qed.
Lemma lem3817268 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term84 A B f s x b.
Proof. exact (EQ_MP (@lem3816513 A B f s x b) (@lem3817267 A B f b x s h1)). Qed.
Lemma lem3817269 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term68 A B f s x b) (h2 : @IN A x s) : (@ITSET B A f s b) = (term41 A B f s x b).
Proof. exact (@lem3817268 A B f b x s h2 (@lem3816460 A B f s x b h1)). Qed.
Lemma lem3817270 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term166 A B f s x b.
Proof. exact (fun h0 : term68 A B f s x b => @lem3817269 A B f b x s h0 h1). Qed.
Lemma lem3817271 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term34 A B f b) (h2 : term13 A s) (h3 : @IN A x s) : (@ITSET B A f s b) = (term41 A B f s x b).
Proof. exact (@lem3817270 A B f b x s h3 (@lem3816456 A B x f b s h1 h2)). Qed.
Lemma lem3817272 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term34 A B f b) (h2 : @IN A x s) : term167 A B f s x b.
Proof. exact (fun h0 : term13 A s => @lem3817271 A B f b x s h1 h0 h2). Qed.
Lemma lem3817273 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term34 A B f b) (h2 : @FINITE A s) (h3 : @IN A x s) : (@ITSET B A f s b) = (term41 A B f s x b).
Proof. exact (@lem3817272 A B f b x s h1 h3 (@lem3816430 A s h2)). Qed.
Lemma lem3817274 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term34 A B f b) (h2 : @IN A x s) : term50 A B f s x b.
Proof. exact (fun h0 : @FINITE A s => @lem3817273 A B f b x s h1 h0 h2). Qed.
Lemma lem3817276 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3817277 {A B : Type'} (f : type1411 A B) : (@ITSET B A f) = (@ITSET B A f).
Proof. exact (eq_refl (@ITSET B A f)). Qed.
Lemma lem3817283 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term91 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3817284 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term91 A s t).
Proof. exact (@lem3817283 A s t). Qed.
Lemma lem3817285 {A : Type'} (s : A -> Prop) (x : A) : (s = (@DELETE A s x)) = (term168 A s x).
Proof. exact (@lem3817284 A s (@DELETE A s x)). Qed.
Lemma lem3817294 {A : Type'} (x : A) (s : A -> Prop) : (term169 A x s) = (term169 A x s).
Proof. exact (eq_refl (term169 A x s)). Qed.
Lemma lem3817295 {A : Type'} (s : A -> Prop) (x : A) : (term170 A s x) = (term171 A s x).
Proof. exact (MK_COMB (@lem3817294 A x s) (@lem3817285 A s x)). Qed.
Lemma lem3817298 {A : Type'} (s : A -> Prop) (x : A) : (term171 A s x) = (term170 A s x).
Proof. exact (SYM (@lem3817295 A s x)). Qed.
Lemma lem3817302 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3817303 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3817302 A P x). Qed.
Lemma lem3817304 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3817303 A s x). Qed.
Lemma lem3817305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3817306 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term147 A s x).
Proof. exact (MK_COMB (@lem3817305) (@lem3817304 A s x)). Qed.
Lemma lem3817307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3817308 {A : Type'} (s : A -> Prop) (x : A) : (term169 A x s) = (term172 A s x).
Proof. exact (MK_COMB (@lem3817307) (@lem3817306 A s x)). Qed.
Lemma lem3817316 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3817317 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3817316 A P x). Qed.
Lemma lem3817318 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3817317 A s x'). Qed.
Lemma lem3817319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3817320 {A : Type'} (s : A -> Prop) (x' : A) : (term98 A x' s) = (term99 A s x').
Proof. exact (MK_COMB (@lem3817319) (@lem3817318 A s x')). Qed.
Lemma lem3817322 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3817323 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term5 A x s y) = (term6 A s x y).
Proof. exact (@lem3817322 A s x y). Qed.
Lemma lem3817324 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term5 A x' s x) = (term6 A s x' x).
Proof. exact (@lem3817323 A s x' x). Qed.
Lemma lem3817328 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3817329 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3817328 A P x). Qed.
Lemma lem3817330 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3817329 A s x'). Qed.
Lemma lem3817331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3817332 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A x' s) = (term104 A s x').
Proof. exact (MK_COMB (@lem3817331) (@lem3817330 A s x')). Qed.
Lemma lem3817335 {A : Type'} (x' : A) (x : A) : (term105 A x' x) = (term105 A x' x).
Proof. exact (eq_refl (term105 A x' x)). Qed.
Lemma lem3817336 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term6 A s x' x) = (term106 A s x' x).
Proof. exact (MK_COMB (@lem3817332 A s x') (@lem3817335 A x' x)). Qed.
Lemma lem3817339 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term5 A x' s x) = (term106 A s x' x).
Proof. exact (TRANS (@lem3817324 A s x' x) (@lem3817336 A s x' x)). Qed.
Lemma lem3817340 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((@IN A x' s) = (term5 A x' s x)) = ((s x') = (term106 A s x' x)).
Proof. exact (MK_COMB (@lem3817320 A s x') (@lem3817339 A s x' x)). Qed.
Lemma lem3817343 {A : Type'} (s : A -> Prop) (x : A) : (term173 A s x) = (term174 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3817340 A s x' x)). Qed.
Lemma lem3817344 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3817345 {A : Type'} (s : A -> Prop) (x : A) : (term168 A s x) = (term175 A s x).
Proof. exact (MK_COMB (@lem3817344 A) (@lem3817343 A s x)). Qed.
Lemma lem3817350 {A : Type'} (s : A -> Prop) (x : A) : (term171 A s x) = (term176 A s x).
Proof. exact (MK_COMB (@lem3817308 A s x) (@lem3817345 A s x)). Qed.
Lemma lem3817353 {A : Type'} (s : A -> Prop) (x : A) : (term176 A s x) = (term171 A s x).
Proof. exact (SYM (@lem3817350 A s x)). Qed.
Lemma lem3817355 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3817356 {A : Type'} (s : A -> Prop) (x : A) : (term176 A s x) = (term177 A s x).
Proof. exact (@lem3817355 (term176 A s x)). Qed.
Lemma lem3817357 {A : Type'} (s : A -> Prop) (x : A) : (term177 A s x) = (term176 A s x).
Proof. exact (SYM (@lem3817356 A s x)). Qed.
Lemma lem3817358 {A : Type'} (s : A -> Prop) (x : A) (h1 : term178 A s x) : term178 A s x.
Proof. exact (h1). Qed.
Lemma lem3817361 {A : Type'} (s : A -> Prop) (x : A) (h1 : term177 A s x) : term177 A s x.
Proof. exact (h1). Qed.
Lemma lem3817362 {A : Type'} (s : A -> Prop) (x : A) : term179 A s x.
Proof. exact (fun h0 : term177 A s x => @lem3817361 A s x h0). Qed.
Lemma lem3817363 {A : Type'} (s : A -> Prop) (x : A) (h1 : term179 A s x) : term179 A s x.
Proof. exact (h1). Qed.
Lemma lem3817364 {A : Type'} (s : A -> Prop) (x : A) (h1 : term177 A s x) : term177 A s x.
Proof. exact (h1). Qed.
Lemma lem3817365 {A : Type'} (s : A -> Prop) (x : A) (h1 : term177 A s x) (h2 : term179 A s x) : term177 A s x.
Proof. exact (@lem3817363 A s x h2 (@lem3817364 A s x h1)). Qed.
Lemma lem3817366 {A : Type'} (s : A -> Prop) (x : A) (h1 : term177 A s x) : term180 A s x.
Proof. exact (fun h0 : term179 A s x => @lem3817365 A s x h1 h0). Qed.
Lemma lem3817367 {A : Type'} (s : A -> Prop) (x : A) (h1 : term179 A s x) : term179 A s x.
Proof. exact (h1). Qed.
Lemma lem3817368 {A : Type'} (s : A -> Prop) (x : A) (h1 : term177 A s x) (h2 : term179 A s x) : term177 A s x.
Proof. exact (@lem3817366 A s x h1 (@lem3817367 A s x h2)). Qed.
Lemma lem3817369 {A : Type'} (s : A -> Prop) (x : A) (h1 : term179 A s x) : term179 A s x.
Proof. exact (fun h0 : term177 A s x => @lem3817368 A s x h0 h1). Qed.
Lemma lem3817370 {A : Type'} (s : A -> Prop) (x : A) : term181 A s x.
Proof. exact (fun h0 : term179 A s x => @lem3817369 A s x h0). Qed.
Lemma lem3817373 {A : Type'} (s : A -> Prop) (x : A) : term179 A s x.
Proof. exact (@lem3817370 A s x (@lem3817362 A s x)). Qed.
Lemma lem3817374 {A : Type'} (s : A -> Prop) (x : A) : term179 A s x.
Proof. exact (@lem3817373 A s x). Qed.
Lemma lem3817384 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3817385 {A : Type'} (s : A -> Prop) (x : A) : (term177 A s x) = (term182 A s x).
Proof. exact (@lem3817384 (term178 A s x)). Qed.
Lemma lem3817387 (t : Prop) : (term120 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3817388 {A : Type'} (s : A -> Prop) (x : A) : (term182 A s x) = (term176 A s x).
Proof. exact (@lem3817387 (term176 A s x)). Qed.
Lemma lem3817391 {A : Type'} (s : A -> Prop) (x : A) : (term177 A s x) = (term176 A s x).
Proof. exact (TRANS (@lem3817385 A s x) (@lem3817388 A s x)). Qed.
Lemma lem3817398 {A : Type'} (x : A) : (term183 A x) = (term184 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3817391 A s x)). Qed.
Lemma lem3817399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3817400 {A : Type'} (x : A) : (term185 A x) = (term186 A x).
Proof. exact (MK_COMB (@lem3817399 A) (@lem3817398 A x)). Qed.
Lemma lem3817405 {A : Type'} : (term187 A) = (term188 A).
Proof. exact (fun_ext (fun x : A => @lem3817400 A x)). Qed.
Lemma lem3817406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3817415 {A : Type'} : (term189 A) = (term190 A).
Proof. exact (MK_COMB (@lem3817406 A) (@lem3817405 A)). Qed.
Lemma lem3817426 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term106 A s x' x)) = ((s x') = (term106 A s x' x)).
Proof. exact (eq_refl ((s x') = (term106 A s x' x))). Qed.
Lemma lem3817427 {A : Type'} (s : A -> Prop) (x : A) : (term174 A s x) = (term174 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3817426 A s x' x)). Qed.
Lemma lem3817428 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3817429 {A : Type'} (s : A -> Prop) (x : A) : (term175 A s x) = (term175 A s x).
Proof. exact (MK_COMB (@lem3817428 A) (@lem3817427 A s x)). Qed.
Lemma lem3817434 {A : Type'} (s : A -> Prop) (x : A) : (term172 A s x) = (term172 A s x).
Proof. exact (eq_refl (term172 A s x)). Qed.
Lemma lem3817435 {A : Type'} (s : A -> Prop) (x : A) : (term176 A s x) = (term176 A s x).
Proof. exact (MK_COMB (@lem3817434 A s x) (@lem3817429 A s x)). Qed.
Lemma lem3817436 {A : Type'} (x : A) : (term184 A x) = (term184 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3817435 A s x)). Qed.
Lemma lem3817437 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3817438 {A : Type'} (x : A) : (term186 A x) = (term186 A x).
Proof. exact (MK_COMB (@lem3817437 A) (@lem3817436 A x)). Qed.
Lemma lem3817439 {A : Type'} : (term188 A) = (term188 A).
Proof. exact (fun_ext (fun x : A => @lem3817438 A x)). Qed.
Lemma lem3817440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3817441 {A : Type'} : (term190 A) = (term190 A).
Proof. exact (MK_COMB (@lem3817440 A) (@lem3817439 A)). Qed.
Lemma lem3817466 {A : Type'} : (term189 A) = (term190 A).
Proof. exact (TRANS (@lem3817415 A) (@lem3817441 A)). Qed.
Lemma lem3817467 {A : Type'} : (term190 A) = (term189 A).
Proof. exact (SYM (@lem3817466 A)). Qed.
Lemma lem3817470 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3817471 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term106 A s x' x)) = (term191 A s x' x).
Proof. exact (@lem3817470 ((s x') = (term106 A s x' x))). Qed.
Lemma lem3817472 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term191 A s x' x) = ((s x') = (term106 A s x' x)).
Proof. exact (SYM (@lem3817471 A s x' x)). Qed.
Lemma lem3817473 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term192 A s x' x) : term192 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3817479 {A : Type'} (s : A -> Prop) (x : A) (h1 : term147 A s x) : term147 A s x.
Proof. exact (h1). Qed.
Lemma lem3817487 {A : Type'} (x' : A) (x : A) : (term131 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3817489 {A : Type'} (s : A -> Prop) (x' : A) : (term132 A s x') = (term132 A s x').
Proof. exact (eq_refl (term132 A s x')). Qed.
Lemma lem3817490 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term133 A s x' x) = (term134 A s x' x).
Proof. exact (MK_COMB (@lem3817489 A s x') (@lem3817487 A x' x)). Qed.
Lemma lem3817491 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term135 A s x' x) = (term133 A s x' x).
Proof. exact (@lem17045 (s x') (term105 A x' x)). Qed.
Lemma lem3817492 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term135 A s x' x) = (term134 A s x' x).
Proof. exact (TRANS (@lem3817491 A s x' x) (@lem3817490 A s x' x)). Qed.
Lemma lem3817498 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term193 A s x' x) = (term193 A s x' x).
Proof. exact (eq_refl (term193 A s x' x)). Qed.
Lemma lem3817500 {A : Type'} (s : A -> Prop) (x' : A) : (term104 A s x') = (term104 A s x').
Proof. exact (eq_refl (term104 A s x')). Qed.
Lemma lem3817501 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term194 A s x' x) = (term195 A s x' x).
Proof. exact (MK_COMB (@lem3817500 A s x') (@lem3817492 A s x' x)). Qed.
Lemma lem3817502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3817503 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term196 A s x' x) = (term197 A s x' x).
Proof. exact (MK_COMB (@lem3817502) (@lem3817501 A s x' x)). Qed.
Lemma lem3817504 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term198 A s x' x) = (term199 A s x' x).
Proof. exact (MK_COMB (@lem3817503 A s x' x) (@lem3817498 A s x' x)). Qed.
Lemma lem3817505 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term192 A s x' x) = (term198 A s x' x).
Proof. exact (@lem17646 (s x') (term106 A s x' x)). Qed.
Lemma lem3817510 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term192 A s x' x) = (term199 A s x' x).
Proof. exact (TRANS (@lem3817505 A s x' x) (@lem3817504 A s x' x)). Qed.
Lemma lem3817517 {A : Type'} (s : A -> Prop) (x : A) (h1 : term147 A s x) : term147 A s x.
Proof. exact (h1). Qed.
Lemma lem3817561 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term192 A s x' x) : term199 A s x' x.
Proof. exact (EQ_MP (@lem3817510 A s x' x) (@lem3817473 A s x' x h1)). Qed.
Lemma lem3817562 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) : term195 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3817563 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : term193 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3817564 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) : term134 A s x' x.
Proof. exact (proj2 (@lem3817562 A s x' x h1)). Qed.
Lemma lem3817568 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : term106 A s x' x.
Proof. exact (proj2 (@lem3817563 A s x' x h1)). Qed.
Lemma lem3817583 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term147 A s x') : term147 A s x'.
Proof. exact (h1). Qed.
Lemma lem3817587 {A : Type'} (s : A -> Prop) (x : A) (h1 : term147 A s x) : term147 A s x.
Proof. exact (h1). Qed.
Lemma lem3817595 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3817617 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term147 A s x') : term147 A s x'.
Proof. exact (h1). Qed.
Lemma lem3817619 {A : Type'} (s : A -> Prop) (x : A) (h1 : term147 A s x) : term147 A s x.
Proof. exact (h1). Qed.
Lemma lem3817621 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) : s x'.
Proof. exact (proj1 (@lem3817562 A s x' x h1)). Qed.
Lemma lem3817623 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3817627 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : term147 A s x'.
Proof. exact (proj1 (@lem3817563 A s x' x h1)). Qed.
Lemma lem3817659 {A : Type'} (s : A -> Prop) (x : A) (h1 : term147 A s x) : term147 A s x.
Proof. exact (h1). Qed.
Lemma lem3817660 {A : Type'} (s : A -> Prop) : (term200 A s) = (term200 A s).
Proof. exact (eq_refl (term200 A s)). Qed.
Lemma lem3817661 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term201 A s x') = (term201 A s x).
Proof. exact (MK_COMB (@lem3817660 A s) (@lem3817623 A x' x h1)). Qed.
Lemma lem3817662 {A : Type'} (s : A -> Prop) (x : A) : (term201 A s x) = (s x).
Proof. exact (eq_refl (term201 A s x)). Qed.
Lemma lem3817663 {A : Type'} (s : A -> Prop) (x' : A) : (term202 A s x') = (term202 A s x').
Proof. exact (eq_refl (term202 A s x')). Qed.
Lemma lem3817664 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term201 A s x') = (term201 A s x)) = ((term201 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3817663 A s x') (@lem3817662 A s x)). Qed.
Lemma lem3817665 {A : Type'} (s : A -> Prop) (x' : A) : (term201 A s x') = (s x').
Proof. exact (eq_refl (term201 A s x')). Qed.
Lemma lem3817666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3817667 {A : Type'} (s : A -> Prop) (x' : A) : (term202 A s x') = (term99 A s x').
Proof. exact (MK_COMB (@lem3817666) (@lem3817665 A s x')). Qed.
Lemma lem3817668 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3817669 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term201 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3817667 A s x') (@lem3817668 A s x)). Qed.
Lemma lem3817670 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term201 A s x') = (term201 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3817664 A x' s x) (@lem3817669 A x' s x)). Qed.
Lemma lem3817671 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3817670 A x' s x) (@lem3817661 A s x' x h1)). Qed.
Lemma lem3817674 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) : s x'.
Proof. exact (proj1 (@lem3817562 A s x' x h1)). Qed.
Lemma lem3817675 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) : term157 A s x'.
Proof. exact (fun h0 : term147 A s x' => @lem3817674 A s x' x h1). Qed.
Lemma lem3817677 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817678 {A : Type'} (s : A -> Prop) (x' : A) : (term157 A s x') = (s x').
Proof. exact (@lem3817677 (s x')). Qed.
Lemma lem3817679 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3817678 A s x') (@lem3817675 A s x' x h1)). Qed.
Lemma lem3817682 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3817684 {A : Type'} (s : A -> Prop) (x' : A) : (term147 A s x') = (term159 A s x').
Proof. exact (@lem3817682 (s x')). Qed.
Lemma lem3817687 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term147 A s x') : term159 A s x'.
Proof. exact (EQ_MP (@lem3817684 A s x') (@lem3817617 A s x' h1)). Qed.
Lemma lem3817690 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : False.
Proof. exact (@lem3817687 A s x' h1 (@lem3817679 A s x' x h2)). Qed.
Lemma lem3817691 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : term160.
Proof. exact (fun h0 : ~ False => @lem3817690 A s x' x h1 h2). Qed.
Lemma lem3817693 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817694 : term160 = False.
Proof. exact (@lem3817693 False). Qed.
Lemma lem3817695 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817694) (@lem3817691 A s x' x h1 h2)). Qed.
Lemma lem3817697 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3817671 A s x' x h2) (@lem3817621 A s x' x h1)). Qed.
Lemma lem3817698 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) (h2 : x' = x) : term157 A s x.
Proof. exact (fun h0 : term147 A s x => @lem3817697 A s x' x h1 h2). Qed.
Lemma lem3817700 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817701 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (s x).
Proof. exact (@lem3817700 (s x)). Qed.
Lemma lem3817702 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term195 A s x' x) (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3817701 A s x) (@lem3817698 A s x' x h1 h2)). Qed.
Lemma lem3817705 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3817707 {A : Type'} (s : A -> Prop) (x : A) : (term147 A s x) = (term159 A s x).
Proof. exact (@lem3817705 (s x)). Qed.
Lemma lem3817710 {A : Type'} (s : A -> Prop) (x : A) (h1 : term147 A s x) : term159 A s x.
Proof. exact (EQ_MP (@lem3817707 A s x) (@lem3817659 A s x h1)). Qed.
Lemma lem3817713 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (@lem3817710 A s x h1 (@lem3817702 A s x' x h2 h3)). Qed.
Lemma lem3817714 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : term160.
Proof. exact (fun h0 : ~ False => @lem3817713 A s x' x h1 h2 h3). Qed.
Lemma lem3817716 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817717 : term160 = False.
Proof. exact (@lem3817716 False). Qed.
Lemma lem3817718 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817717) (@lem3817714 A s x' x h1 h2 h3)). Qed.
Lemma lem3817734 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : s x'.
Proof. exact (proj1 (@lem3817568 A s x' x h1)). Qed.
Lemma lem3817735 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : term157 A s x'.
Proof. exact (fun h0 : term147 A s x' => @lem3817734 A s x' x h1). Qed.
Lemma lem3817737 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817738 {A : Type'} (s : A -> Prop) (x' : A) : (term157 A s x') = (s x').
Proof. exact (@lem3817737 (s x')). Qed.
Lemma lem3817739 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3817738 A s x') (@lem3817735 A s x' x h1)). Qed.
Lemma lem3817742 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3817744 {A : Type'} (s : A -> Prop) (x' : A) : (term147 A s x') = (term159 A s x').
Proof. exact (@lem3817742 (s x')). Qed.
Lemma lem3817747 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : term159 A s x'.
Proof. exact (EQ_MP (@lem3817744 A s x') (@lem3817627 A s x' x h1)). Qed.
Lemma lem3817750 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : False.
Proof. exact (@lem3817747 A s x' x h1 (@lem3817739 A s x' x h1)). Qed.
Lemma lem3817751 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : term160.
Proof. exact (fun h0 : ~ False => @lem3817750 A s x' x h1). Qed.
Lemma lem3817753 (p : Prop) : (term158 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3817754 : term160 = False.
Proof. exact (@lem3817753 False). Qed.
Lemma lem3817755 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term193 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817754) (@lem3817751 A s x' x h1)). Qed.
Lemma lem3817756 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : (term147 A s x) = False.
Proof. exact (prop_ext (fun h4 : term147 A s x => @lem3817718 A s x' x h1 h2 h3) (fun h4 : False => @lem3817659 A s x h1)). Qed.
Lemma lem3817758 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817756 A s x' x h1 h2 h3) (@lem3817659 A s x h1)). Qed.
Lemma lem3817759 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3817758 A s x' x h1 h2 h3) (fun h4 : False => @lem3817623 A x' x h3)). Qed.
Lemma lem3817760 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817759 A s x' x h1 h2 h3) (@lem3817623 A x' x h3)). Qed.
Lemma lem3817761 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : (term147 A s x) = False.
Proof. exact (prop_ext (fun h4 : term147 A s x => @lem3817760 A s x' x h1 h2 h3) (fun h4 : False => @lem3817619 A s x h1)). Qed.
Lemma lem3817762 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817761 A s x' x h1 h2 h3) (@lem3817619 A s x h1)). Qed.
Lemma lem3817763 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : (term147 A s x') = False.
Proof. exact (prop_ext (fun h3 : term147 A s x' => @lem3817695 A s x' x h1 h2) (fun h3 : False => @lem3817617 A s x' h1)). Qed.
Lemma lem3817764 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817763 A s x' x h1 h2) (@lem3817617 A s x' h1)). Qed.
Lemma lem3817765 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3817762 A s x' x h1 h2 h3) (fun h4 : False => @lem3817595 A x' x h3)). Qed.
Lemma lem3817766 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817765 A s x' x h1 h2 h3) (@lem3817595 A x' x h3)). Qed.
Lemma lem3817767 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : (term147 A s x) = False.
Proof. exact (prop_ext (fun h4 : term147 A s x => @lem3817766 A s x' x h1 h2 h3) (fun h4 : False => @lem3817587 A s x h1)). Qed.
Lemma lem3817768 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817767 A s x' x h1 h2 h3) (@lem3817587 A s x h1)). Qed.
Lemma lem3817769 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : (term147 A s x') = False.
Proof. exact (prop_ext (fun h3 : term147 A s x' => @lem3817764 A s x' x h1 h2) (fun h3 : False => @lem3817583 A s x' h1)). Qed.
Lemma lem3817770 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817769 A s x' x h1 h2) (@lem3817583 A s x' h1)). Qed.
Lemma lem3817771 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3817768 A s x' x h1 h2 h3) (fun h4 : False => @lem3817595 A x' x h3)). Qed.
Lemma lem3817772 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817771 A s x' x h1 h2 h3) (@lem3817595 A x' x h3)). Qed.
Lemma lem3817773 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : (term147 A s x) = False.
Proof. exact (prop_ext (fun h4 : term147 A s x => @lem3817772 A s x' x h1 h2 h3) (fun h4 : False => @lem3817587 A s x h1)). Qed.
Lemma lem3817774 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3817773 A s x' x h1 h2 h3) (@lem3817587 A s x h1)). Qed.
Lemma lem3817775 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : (term147 A s x') = False.
Proof. exact (prop_ext (fun h3 : term147 A s x' => @lem3817770 A s x' x h1 h2) (fun h3 : False => @lem3817583 A s x' h1)). Qed.
Lemma lem3817776 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x') (h2 : term195 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817775 A s x' x h1 h2) (@lem3817583 A s x' h1)). Qed.
Lemma lem3817777 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term195 A s x' x) : False.
Proof. exact (or_elim (@lem3817564 A s x' x h2) (fun h0 : term147 A s x' => @lem3817776 A s x' x h0 h2) (fun h0 : x' = x => @lem3817774 A s x' x h1 h2 h0)). Qed.
Lemma lem3817778 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term192 A s x' x) : False.
Proof. exact (or_elim (@lem3817561 A s x' x h2) (fun h0 : term195 A s x' x => @lem3817777 A s x' x h1 h0) (fun h0 : term193 A s x' x => @lem3817755 A s x' x h0)). Qed.
Lemma lem3817779 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term192 A s x' x) : (term147 A s x) = False.
Proof. exact (prop_ext (fun h3 : term147 A s x => @lem3817778 A s x' x h1 h2) (fun h3 : False => @lem3817517 A s x h1)). Qed.
Lemma lem3817780 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term192 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817779 A s x' x h1 h2) (@lem3817517 A s x h1)). Qed.
Lemma lem3817781 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term192 A s x' x) : (term147 A s x) = False.
Proof. exact (prop_ext (fun h3 : term147 A s x => @lem3817780 A s x' x h1 h2) (fun h3 : False => @lem3817479 A s x h1)). Qed.
Lemma lem3817782 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term192 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817781 A s x' x h1 h2) (@lem3817479 A s x h1)). Qed.
Lemma lem3817783 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term192 A s x' x) : (term192 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term192 A s x' x => @lem3817782 A s x' x h1 h2) (fun h3 : False => @lem3817473 A s x' x h2)). Qed.
Lemma lem3817784 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term147 A s x) (h2 : term192 A s x' x) : False.
Proof. exact (EQ_MP (@lem3817783 A s x' x h1 h2) (@lem3817473 A s x' x h2)). Qed.
Lemma lem3817785 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term147 A s x) : term191 A s x' x.
Proof. exact (fun h0 : term192 A s x' x => @lem3817784 A s x' x h1 h0). Qed.
Lemma lem3817786 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term147 A s x) : (s x') = (term106 A s x' x).
Proof. exact (EQ_MP (@lem3817472 A s x' x) (@lem3817785 A x' s x h1)). Qed.
Lemma lem3817791 {A : Type'} (s : A -> Prop) (x : A) (h1 : term147 A s x) : term175 A s x.
Proof. exact (fun x' : A => @lem3817786 A x' s x h1). Qed.
Lemma lem3817792 {A : Type'} (s : A -> Prop) (x : A) : term176 A s x.
Proof. exact (fun h0 : term147 A s x => @lem3817791 A s x h0). Qed.
Lemma lem3817797 {A : Type'} (x : A) : term186 A x.
Proof. exact (fun s : A -> Prop => @lem3817792 A s x). Qed.
Lemma lem3817802 {A : Type'} : term190 A.
Proof. exact (fun x : A => @lem3817797 A x). Qed.
Lemma lem3817803 {A : Type'} : term189 A.
Proof. exact (EQ_MP (@lem3817467 A) (@lem3817802 A)). Qed.
Lemma lem3817804 {A : Type'} (x : A) : term203 A x.
Proof. exact (@lem3817803 A x). Qed.
Lemma lem3817805 {A : Type'} (x : A) : (term203 A x) = (term185 A x).
Proof. exact (eq_refl (term203 A x)). Qed.
Lemma lem3817806 {A : Type'} (x : A) : term185 A x.
Proof. exact (EQ_MP (@lem3817805 A x) (@lem3817804 A x)). Qed.
Lemma lem3817807 {A : Type'} (x : A) (s : A -> Prop) : term204 A x s.
Proof. exact (@lem3817806 A x s). Qed.
Lemma lem3817808 {A : Type'} (s : A -> Prop) (x : A) : (term204 A x s) = (term177 A s x).
Proof. exact (eq_refl (term204 A x s)). Qed.
Lemma lem3817809 {A : Type'} (s : A -> Prop) (x : A) : term177 A s x.
Proof. exact (EQ_MP (@lem3817808 A s x) (@lem3817807 A x s)). Qed.
Lemma lem3817811 {A : Type'} (s : A -> Prop) (x : A) : term177 A s x.
Proof. exact (@lem3817374 A s x (@lem3817809 A s x)). Qed.
Lemma lem3817812 {A : Type'} (s : A -> Prop) (x : A) (h1 : term178 A s x) : False.
Proof. exact (@lem3817811 A s x (@lem3817358 A s x h1)). Qed.
Lemma lem3817813 {A : Type'} (s : A -> Prop) (x : A) (h1 : term178 A s x) : (term178 A s x) = False.
Proof. exact (prop_ext (fun h2 : term178 A s x => @lem3817812 A s x h1) (fun h2 : False => @lem3817358 A s x h1)). Qed.
Lemma lem3817814 {A : Type'} (s : A -> Prop) (x : A) (h1 : term178 A s x) : False.
Proof. exact (EQ_MP (@lem3817813 A s x h1) (@lem3817358 A s x h1)). Qed.
Lemma lem3817815 {A : Type'} (s : A -> Prop) (x : A) : term177 A s x.
Proof. exact (fun h0 : term178 A s x => @lem3817814 A s x h0). Qed.
Lemma lem3817816 {A : Type'} (s : A -> Prop) (x : A) : term176 A s x.
Proof. exact (EQ_MP (@lem3817357 A s x) (@lem3817815 A s x)). Qed.
Lemma lem3817817 {A : Type'} (s : A -> Prop) (x : A) : term171 A s x.
Proof. exact (EQ_MP (@lem3817353 A s x) (@lem3817816 A s x)). Qed.
Lemma lem3817818 {A : Type'} (s : A -> Prop) (x : A) : term170 A s x.
Proof. exact (EQ_MP (@lem3817298 A s x) (@lem3817817 A s x)). Qed.
Lemma lem3817819 {A : Type'} (x : A) (s : A -> Prop) (h1 : term20 A x s) : s = (@DELETE A s x).
Proof. exact (@lem3817818 A s x (@lem3816269 A x s h1)). Qed.
Lemma lem3817820 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : (@ITSET B A f s) = (term205 A B f s x).
Proof. exact (MK_COMB (@lem3817277 A B f) (@lem3817819 A x s h1)). Qed.
Lemma lem3817821 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : (@ITSET B A f s b) = (term44 A B f s x b).
Proof. exact (MK_COMB (@lem3817820 A B f x s h1) (@lem3817276 B b)). Qed.
Lemma lem3817822 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : term54 A B f s x b.
Proof. exact (fun h0 : @FINITE A s => @lem3817821 A B f b x s h1). Qed.
Lemma lem3817823 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term20 A x s) : term49 A B f s x b.
Proof. exact (EQ_MP (@lem3816425 A B f b x s h1) (@lem3817822 A B f b x s h1)). Qed.
Lemma lem3817824 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term34 A B f b) (h2 : @IN A x s) : term49 A B f s x b.
Proof. exact (EQ_MP (@lem3816389 A B f b x s h2) (@lem3817274 A B f b x s h1 h2)). Qed.
Lemma lem3817825 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term49 A B f s x b.
Proof. exact (or_elim (@lem3816267 A x s) (fun h0 : @IN A x s => @lem3817824 A B f b x s h1 h0) (fun h0 : term20 A x s => @lem3817823 A B f b x s h0)). Qed.
Lemma lem3817830 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term206 A B f x b.
Proof. exact (fun s : A -> Prop => @lem3817825 A B s x f b h1). Qed.
Lemma lem3817835 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) : term37 A B f b.
Proof. exact (fun x : A => @lem3817830 A B x f b h1). Qed.
Lemma lem3817836 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) (h2 : (@ITSET B A f (@EMPTY A) b) = b) : term38 A B f b.
Proof. exact (EQ_MP (@lem3816353 A B f b h2) (@lem3817835 A B f b h1)). Qed.
Lemma lem3817837 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term28 A B f) : term34 A B f b.
Proof. exact (proj2 (@lem3816295 A B b f h1)). Qed.
Lemma lem3817838 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term28 A B f) : (@ITSET B A f (@EMPTY A) b) = b.
Proof. exact (proj1 (@lem3816295 A B b f h1)). Qed.
Lemma lem3817839 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) (h2 : (@ITSET B A f (@EMPTY A) b) = b) : (term34 A B f b) = (term38 A B f b).
Proof. exact (prop_ext (fun h3 : term34 A B f b => @lem3817836 A B f b h1 h2) (fun h3 : term38 A B f b => @lem3816296 A B f b h1)). Qed.
Lemma lem3817840 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) (h2 : (@ITSET B A f (@EMPTY A) b) = b) : term38 A B f b.
Proof. exact (EQ_MP (@lem3817839 A B f b h1 h2) (@lem3816296 A B f b h1)). Qed.
Lemma lem3817841 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) (h2 : (@ITSET B A f (@EMPTY A) b) = b) : ((@ITSET B A f (@EMPTY A) b) = b) = (term38 A B f b).
Proof. exact (prop_ext (fun h3 : (@ITSET B A f (@EMPTY A) b) = b => @lem3817840 A B f b h1 h2) (fun h3 : term38 A B f b => @lem3816297 A B f b h2)). Qed.
Lemma lem3817842 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term34 A B f b) (h2 : (@ITSET B A f (@EMPTY A) b) = b) : term38 A B f b.
Proof. exact (EQ_MP (@lem3817841 A B f b h1 h2) (@lem3816297 A B f b h2)). Qed.
Lemma lem3817843 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term28 A B f) (h2 : (@ITSET B A f (@EMPTY A) b) = b) : (term34 A B f b) = (term38 A B f b).
Proof. exact (prop_ext (fun h3 : term34 A B f b => @lem3817842 A B f b h3 h2) (fun h3 : term38 A B f b => @lem3817837 A B b f h1)). Qed.
Lemma lem3817844 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term28 A B f) (h2 : (@ITSET B A f (@EMPTY A) b) = b) : term38 A B f b.
Proof. exact (EQ_MP (@lem3817843 A B f b h1 h2) (@lem3817837 A B b f h1)). Qed.
Lemma lem3817845 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term28 A B f) : ((@ITSET B A f (@EMPTY A) b) = b) = (term38 A B f b).
Proof. exact (prop_ext (fun h2 : (@ITSET B A f (@EMPTY A) b) = b => @lem3817844 A B f b h1 h2) (fun h2 : term38 A B f b => @lem3817838 A B b f h1)). Qed.
Lemma lem3817846 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term28 A B f) : term38 A B f b.
Proof. exact (EQ_MP (@lem3817845 A B b f h1) (@lem3817838 A B b f h1)). Qed.
Lemma lem3817847 {A B : Type'} (f : type1411 A B) (b : B) : term207 A B f b.
Proof. exact (fun h0 : term28 A B f => @lem3817846 A B b f h0). Qed.
Lemma lem3817848 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term26 A B f) : term38 A B f b.
Proof. exact (@lem3817847 A B f b (@lem3816291 A B f h1)). Qed.
Lemma lem3817849 {A B : Type'} (f : type1411 A B) (b : B) : term208 A B f b.
Proof. exact (fun h0 : term26 A B f => @lem3817848 A B b f h0). Qed.
Lemma lem3817854 {A B : Type'} (f : type1411 A B) : term209 A B f.
Proof. exact (fun b : B => @lem3817849 A B f b). Qed.
Lemma lem3817859 {A B : Type'} : term210 A B.
Proof. exact (fun f : type1411 A B => @lem3817854 A B f). Qed.
