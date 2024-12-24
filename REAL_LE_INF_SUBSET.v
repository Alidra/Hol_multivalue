Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_INF_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INF_spec.
Require Import REAL_LE_INF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem5238254 (s : real -> Prop) : term0 s.
Proof. exact (@lem5214027 s). Qed.
Lemma lem5238255 (s : real -> Prop) : (term0 s) = (term1 s).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5238256 (s : real -> Prop) : term1 s.
Proof. exact (EQ_MP (@lem5238255 s) (@lem5238254 s)). Qed.
Lemma lem5238257 (s : real -> Prop) (h1 : term2 s) : term2 s.
Proof. exact (h1). Qed.
Lemma lem5238258 (b : real) (s : real -> Prop) (h1 : term2 s) : term3 s b.
Proof. exact (@lem5238257 s h1 b). Qed.
Lemma lem5238259 (b : real) (s : real -> Prop) : (term3 s b) = (term4 b s).
Proof. exact (eq_refl (term3 s b)). Qed.
Lemma lem5238260 (b : real) (s : real -> Prop) (h1 : term2 s) : term4 b s.
Proof. exact (EQ_MP (@lem5238259 b s) (@lem5238258 b s h1)). Qed.
Lemma lem5238261 (s : real -> Prop) (b : real) (h1 : term5 s b) : term5 s b.
Proof. exact (h1). Qed.
Lemma lem5238262 (s : real -> Prop) (b : real) (h1 : term2 s) (h2 : term5 s b) : term6 b s.
Proof. exact (@lem5238260 b s h1 (@lem5238261 s b h2)). Qed.
Lemma lem5238263 (s : real -> Prop) (b : real) (h1 : term5 s b) : term7 b s.
Proof. exact (fun h0 : term2 s => @lem5238262 s b h0 h1). Qed.
Lemma lem5238264 (s : real -> Prop) (h1 : term2 s) : term2 s.
Proof. exact (h1). Qed.
Lemma lem5238265 (s : real -> Prop) (b : real) (h1 : term2 s) (h2 : term5 s b) : term6 b s.
Proof. exact (@lem5238263 s b h2 (@lem5238264 s h1)). Qed.
Lemma lem5238266 (b : real) (s : real -> Prop) (h1 : term2 s) : term4 b s.
Proof. exact (fun h0 : term5 s b => @lem5238265 s b h1 h0). Qed.
Lemma lem5238267 (s : real -> Prop) (h1 : term2 s) : term2 s.
Proof. exact (fun b : real => @lem5238266 b s h1). Qed.
Lemma lem5238268 (s : real -> Prop) : term8 s.
Proof. exact (fun h0 : term2 s => @lem5238267 s h0). Qed.
Lemma lem5238269 (s : real -> Prop) : term2 s.
Proof. exact (@lem5238268 s (@lem5238253 s)). Qed.
Lemma lem5238270 (s : real -> Prop) (b : real) : term3 s b.
Proof. exact (@lem5238269 s b). Qed.
Lemma lem5238271 (b : real) (s : real -> Prop) : (term3 s b) = (term4 b s).
Proof. exact (eq_refl (term3 s b)). Qed.
Lemma lem5238273 (t : real -> Prop) (s : real -> Prop) (h1 : term9 t s) : term9 t s.
Proof. exact (h1). Qed.
Lemma lem5238274 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term10 t s.
Proof. exact (h1). Qed.
Lemma lem5238275 (t : real -> Prop) (h1 : term11 t) : term11 t.
Proof. exact (h1). Qed.
Lemma lem5238276 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem5238277 (t : real -> Prop) (s : real -> Prop) (h1 : @SUBSET real t s) : @SUBSET real t s.
Proof. exact (h1). Qed.
Lemma lem5238278 (s : real -> Prop) (b : real) (h1 : term13 s b) : term13 s b.
Proof. exact (h1). Qed.
Lemma lem5238280 (b : real) (s : real -> Prop) : term4 b s.
Proof. exact (EQ_MP (@lem5238271 b s) (@lem5238270 s b)). Qed.
Lemma lem5238281 (s : real -> Prop) (t : real -> Prop) : term14 s t.
Proof. exact (@lem5238280 (inf s) t). Qed.
Lemma lem5238292 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : @SUBSET real t s) : term15 s t.
Proof. exact (conj (@lem5238277 t s h2) (@lem5238275 t h1)). Qed.
Lemma lem5238293 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term13 s b) (h2 : term11 t) (h3 : @SUBSET real t s) : term16 b s t.
Proof. exact (conj (@lem5238278 s b h1) (@lem5238292 t s h2 h3)). Qed.
Lemma lem5238307 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5238308 (s : real -> Prop) (t : real -> Prop) : (@SUBSET real s t) = (term18 s t).
Proof. exact (@lem5238307 real s t). Qed.
Lemma lem5238309 (t : real -> Prop) (s : real -> Prop) : (@SUBSET real t s) = (term18 t s).
Proof. exact (@lem5238308 t s). Qed.
Lemma lem5238316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238317 (t : real -> Prop) (s : real -> Prop) : (term19 t s) = (term20 t s).
Proof. exact (MK_COMB (@lem5238316) (@lem5238309 t s)). Qed.
Lemma lem5238321 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5238322 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term22 s t).
Proof. exact (@lem5238321 real s t). Qed.
Lemma lem5238323 (t : real -> Prop) : (t = (@EMPTY real)) = (term23 t).
Proof. exact (@lem5238322 t (@EMPTY real)). Qed.
Lemma lem5238332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238333 (t : real -> Prop) : (term11 t) = (term24 t).
Proof. exact (MK_COMB (@lem5238332) (@lem5238323 t)). Qed.
Lemma lem5238334 (s : real -> Prop) (t : real -> Prop) : (term15 s t) = (term25 s t).
Proof. exact (MK_COMB (@lem5238317 t s) (@lem5238333 t)). Qed.
Lemma lem5238337 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (eq_refl (term26 s b)). Qed.
Lemma lem5238338 (b : real) (s : real -> Prop) (t : real -> Prop) : (term16 b s t) = (term27 b s t).
Proof. exact (MK_COMB (@lem5238337 s b) (@lem5238334 s t)). Qed.
Lemma lem5238341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238342 (b : real) (s : real -> Prop) (t : real -> Prop) : (term28 b s t) = (term29 b s t).
Proof. exact (MK_COMB (@lem5238341) (@lem5238338 b s t)). Qed.
Lemma lem5238352 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5238353 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term22 s t).
Proof. exact (@lem5238352 real s t). Qed.
Lemma lem5238354 (s : real -> Prop) : (s = (@EMPTY real)) = (term23 s).
Proof. exact (@lem5238353 s (@EMPTY real)). Qed.
Lemma lem5238363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238364 (s : real -> Prop) : (term11 s) = (term24 s).
Proof. exact (MK_COMB (@lem5238363) (@lem5238354 s)). Qed.
Lemma lem5238365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238366 (s : real -> Prop) : (term30 s) = (term31 s).
Proof. exact (MK_COMB (@lem5238365) (@lem5238364 s)). Qed.
Lemma lem5238377 (s : real -> Prop) : (term12 s) = (term12 s).
Proof. exact (eq_refl (term12 s)). Qed.
Lemma lem5238378 (s : real -> Prop) : (term32 s) = (term33 s).
Proof. exact (MK_COMB (@lem5238366 s) (@lem5238377 s)). Qed.
Lemma lem5238381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238382 (s : real -> Prop) : (term34 s) = (term35 s).
Proof. exact (MK_COMB (@lem5238381) (@lem5238378 s)). Qed.
Lemma lem5238403 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (eq_refl (term36 s)). Qed.
Lemma lem5238404 (s : real -> Prop) : (term1 s) = (term37 s).
Proof. exact (MK_COMB (@lem5238382 s) (@lem5238403 s)). Qed.
Lemma lem5238407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238408 (s : real -> Prop) : (term38 s) = (term39 s).
Proof. exact (MK_COMB (@lem5238407) (@lem5238404 s)). Qed.
Lemma lem5238414 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5238415 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term22 s t).
Proof. exact (@lem5238414 real s t). Qed.
Lemma lem5238416 (t : real -> Prop) : (t = (@EMPTY real)) = (term23 t).
Proof. exact (@lem5238415 t (@EMPTY real)). Qed.
Lemma lem5238425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238426 (t : real -> Prop) : (term11 t) = (term24 t).
Proof. exact (MK_COMB (@lem5238425) (@lem5238416 t)). Qed.
Lemma lem5238427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238428 (t : real -> Prop) : (term30 t) = (term31 t).
Proof. exact (MK_COMB (@lem5238427) (@lem5238426 t)). Qed.
Lemma lem5238435 (t : real -> Prop) (s : real -> Prop) : (term40 t s) = (term40 t s).
Proof. exact (eq_refl (term40 t s)). Qed.
Lemma lem5238436 (t : real -> Prop) (s : real -> Prop) : (term41 t s) = (term42 t s).
Proof. exact (MK_COMB (@lem5238428 t) (@lem5238435 t s)). Qed.
Lemma lem5238439 (t : real -> Prop) (s : real -> Prop) : (term43 t s) = (term44 t s).
Proof. exact (MK_COMB (@lem5238408 s) (@lem5238436 t s)). Qed.
Lemma lem5238442 (b : real) (t : real -> Prop) (s : real -> Prop) : (term45 b t s) = (term46 b t s).
Proof. exact (MK_COMB (@lem5238342 b s t) (@lem5238439 t s)). Qed.
Lemma lem5238445 (b : real) (t : real -> Prop) (s : real -> Prop) : (term46 b t s) = (term45 b t s).
Proof. exact (SYM (@lem5238442 b t s)). Qed.
Lemma lem5238457 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238458 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238457 real P x). Qed.
Lemma lem5238459 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5238458 s x). Qed.
Lemma lem5238460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238461 (s : real -> Prop) (x : real) : (term47 x s) = (term48 s x).
Proof. exact (MK_COMB (@lem5238460) (@lem5238459 s x)). Qed.
Lemma lem5238462 (b : real) (x : real) : (real_le b x) = (real_le b x).
Proof. exact (eq_refl (real_le b x)). Qed.
Lemma lem5238463 (s : real -> Prop) (b : real) (x : real) : (term49 s b x) = (term50 s b x).
Proof. exact (MK_COMB (@lem5238461 s x) (@lem5238462 b x)). Qed.
Lemma lem5238466 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5238463 s b x)). Qed.
Lemma lem5238467 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238468 (s : real -> Prop) (b : real) : (term13 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5238467) (@lem5238466 s b)). Qed.
Lemma lem5238473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238474 (s : real -> Prop) (b : real) : (term26 s b) = (term54 s b).
Proof. exact (MK_COMB (@lem5238473) (@lem5238468 s b)). Qed.
Lemma lem5238484 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238485 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238484 real P x). Qed.
Lemma lem5238486 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5238485 t x). Qed.
Lemma lem5238487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238488 (t : real -> Prop) (x : real) : (term47 x t) = (term48 t x).
Proof. exact (MK_COMB (@lem5238487) (@lem5238486 t x)). Qed.
Lemma lem5238490 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238491 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238490 real P x). Qed.
Lemma lem5238492 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5238491 s x). Qed.
Lemma lem5238493 (t : real -> Prop) (s : real -> Prop) (x : real) : (term55 t x s) = (term56 t s x).
Proof. exact (MK_COMB (@lem5238488 t x) (@lem5238492 s x)). Qed.
Lemma lem5238496 (t : real -> Prop) (s : real -> Prop) : (term57 t s) = (term58 t s).
Proof. exact (fun_ext (fun x : real => @lem5238493 t s x)). Qed.
Lemma lem5238497 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238498 (t : real -> Prop) (s : real -> Prop) : (term18 t s) = (term59 t s).
Proof. exact (MK_COMB (@lem5238497) (@lem5238496 t s)). Qed.
Lemma lem5238503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238504 (t : real -> Prop) (s : real -> Prop) : (term20 t s) = (term60 t s).
Proof. exact (MK_COMB (@lem5238503) (@lem5238498 t s)). Qed.
Lemma lem5238512 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238513 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238512 real P x). Qed.
Lemma lem5238514 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5238513 t x). Qed.
Lemma lem5238515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5238516 (t : real -> Prop) (x : real) : (term61 x t) = (term62 t x).
Proof. exact (MK_COMB (@lem5238515) (@lem5238514 t x)). Qed.
Lemma lem5238518 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5238519 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5238518 real x). Qed.
Lemma lem5238520 (t : real -> Prop) (x : real) : ((@IN real x t) = (@IN real x (@EMPTY real))) = ((t x) = False).
Proof. exact (MK_COMB (@lem5238516 t x) (@lem5238519 x)). Qed.
Lemma lem5238522 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5238523 (t : real -> Prop) (x : real) : ((t x) = False) = (term63 t x).
Proof. exact (@lem5238522 (t x)). Qed.
Lemma lem5238524 (t : real -> Prop) (x : real) : ((@IN real x t) = (@IN real x (@EMPTY real))) = (term63 t x).
Proof. exact (TRANS (@lem5238520 t x) (@lem5238523 t x)). Qed.
Lemma lem5238525 (t : real -> Prop) : (term64 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5238524 t x)). Qed.
Lemma lem5238526 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238527 (t : real -> Prop) : (term23 t) = (term66 t).
Proof. exact (MK_COMB (@lem5238526) (@lem5238525 t)). Qed.
Lemma lem5238532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238533 (t : real -> Prop) : (term24 t) = (term67 t).
Proof. exact (MK_COMB (@lem5238532) (@lem5238527 t)). Qed.
Lemma lem5238534 (s : real -> Prop) (t : real -> Prop) : (term25 s t) = (term68 s t).
Proof. exact (MK_COMB (@lem5238504 t s) (@lem5238533 t)). Qed.
Lemma lem5238537 (b : real) (s : real -> Prop) (t : real -> Prop) : (term27 b s t) = (term69 b s t).
Proof. exact (MK_COMB (@lem5238474 s b) (@lem5238534 s t)). Qed.
Lemma lem5238540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238541 (b : real) (s : real -> Prop) (t : real -> Prop) : (term29 b s t) = (term70 b s t).
Proof. exact (MK_COMB (@lem5238540) (@lem5238537 b s t)). Qed.
Lemma lem5238555 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238556 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238555 real P x). Qed.
Lemma lem5238557 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5238556 s x). Qed.
Lemma lem5238558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5238559 (s : real -> Prop) (x : real) : (term61 x s) = (term62 s x).
Proof. exact (MK_COMB (@lem5238558) (@lem5238557 s x)). Qed.
Lemma lem5238561 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5238562 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5238561 real x). Qed.
Lemma lem5238563 (s : real -> Prop) (x : real) : ((@IN real x s) = (@IN real x (@EMPTY real))) = ((s x) = False).
Proof. exact (MK_COMB (@lem5238559 s x) (@lem5238562 x)). Qed.
Lemma lem5238565 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5238566 (s : real -> Prop) (x : real) : ((s x) = False) = (term63 s x).
Proof. exact (@lem5238565 (s x)). Qed.
Lemma lem5238567 (s : real -> Prop) (x : real) : ((@IN real x s) = (@IN real x (@EMPTY real))) = (term63 s x).
Proof. exact (TRANS (@lem5238563 s x) (@lem5238566 s x)). Qed.
Lemma lem5238568 (s : real -> Prop) : (term64 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5238567 s x)). Qed.
Lemma lem5238569 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238570 (s : real -> Prop) : (term23 s) = (term66 s).
Proof. exact (MK_COMB (@lem5238569) (@lem5238568 s)). Qed.
Lemma lem5238575 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238576 (s : real -> Prop) : (term24 s) = (term67 s).
Proof. exact (MK_COMB (@lem5238575) (@lem5238570 s)). Qed.
Lemma lem5238577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238578 (s : real -> Prop) : (term31 s) = (term71 s).
Proof. exact (MK_COMB (@lem5238577) (@lem5238576 s)). Qed.
Lemma lem5238590 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238591 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238590 real P x). Qed.
Lemma lem5238592 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5238591 s x). Qed.
Lemma lem5238593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238594 (s : real -> Prop) (x : real) : (term47 x s) = (term48 s x).
Proof. exact (MK_COMB (@lem5238593) (@lem5238592 s x)). Qed.
Lemma lem5238595 (b : real) (x : real) : (real_le b x) = (real_le b x).
Proof. exact (eq_refl (real_le b x)). Qed.
Lemma lem5238596 (s : real -> Prop) (b : real) (x : real) : (term49 s b x) = (term50 s b x).
Proof. exact (MK_COMB (@lem5238594 s x) (@lem5238595 b x)). Qed.
Lemma lem5238599 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5238596 s b x)). Qed.
Lemma lem5238600 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238601 (s : real -> Prop) (b : real) : (term13 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5238600) (@lem5238599 s b)). Qed.
Lemma lem5238606 (s : real -> Prop) : (term72 s) = (term73 s).
Proof. exact (fun_ext (fun b : real => @lem5238601 s b)). Qed.
Lemma lem5238607 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5238608 (s : real -> Prop) : (term12 s) = (term74 s).
Proof. exact (MK_COMB (@lem5238607) (@lem5238606 s)). Qed.
Lemma lem5238613 (s : real -> Prop) : (term33 s) = (term75 s).
Proof. exact (MK_COMB (@lem5238578 s) (@lem5238608 s)). Qed.
Lemma lem5238616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238617 (s : real -> Prop) : (term35 s) = (term76 s).
Proof. exact (MK_COMB (@lem5238616) (@lem5238613 s)). Qed.
Lemma lem5238627 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238628 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238627 real P x). Qed.
Lemma lem5238629 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5238628 s x). Qed.
Lemma lem5238630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238631 (s : real -> Prop) (x : real) : (term47 x s) = (term48 s x).
Proof. exact (MK_COMB (@lem5238630) (@lem5238629 s x)). Qed.
Lemma lem5238632 (s : real -> Prop) (x : real) : (term77 s x) = (term77 s x).
Proof. exact (eq_refl (term77 s x)). Qed.
Lemma lem5238633 (s : real -> Prop) (x : real) : (term78 s x) = (term79 s x).
Proof. exact (MK_COMB (@lem5238631 s x) (@lem5238632 s x)). Qed.
Lemma lem5238636 (s : real -> Prop) : (term80 s) = (term81 s).
Proof. exact (fun_ext (fun x : real => @lem5238633 s x)). Qed.
Lemma lem5238637 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238638 (s : real -> Prop) : (term82 s) = (term83 s).
Proof. exact (MK_COMB (@lem5238637) (@lem5238636 s)). Qed.
Lemma lem5238643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238644 (s : real -> Prop) : (term84 s) = (term85 s).
Proof. exact (MK_COMB (@lem5238643) (@lem5238638 s)). Qed.
Lemma lem5238658 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238659 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238658 real P x). Qed.
Lemma lem5238660 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5238659 s x). Qed.
Lemma lem5238661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238662 (s : real -> Prop) (x : real) : (term47 x s) = (term48 s x).
Proof. exact (MK_COMB (@lem5238661) (@lem5238660 s x)). Qed.
Lemma lem5238663 (b : real) (x : real) : (real_le b x) = (real_le b x).
Proof. exact (eq_refl (real_le b x)). Qed.
Lemma lem5238664 (s : real -> Prop) (b : real) (x : real) : (term49 s b x) = (term50 s b x).
Proof. exact (MK_COMB (@lem5238662 s x) (@lem5238663 b x)). Qed.
Lemma lem5238667 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5238664 s b x)). Qed.
Lemma lem5238668 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238669 (s : real -> Prop) (b : real) : (term13 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5238668) (@lem5238667 s b)). Qed.
Lemma lem5238674 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238675 (s : real -> Prop) (b : real) : (term86 s b) = (term87 s b).
Proof. exact (MK_COMB (@lem5238674) (@lem5238669 s b)). Qed.
Lemma lem5238676 (b : real) (s : real -> Prop) : (term6 b s) = (term6 b s).
Proof. exact (eq_refl (term6 b s)). Qed.
Lemma lem5238677 (b : real) (s : real -> Prop) : (term88 b s) = (term89 b s).
Proof. exact (MK_COMB (@lem5238675 s b) (@lem5238676 b s)). Qed.
Lemma lem5238680 (s : real -> Prop) : (term90 s) = (term91 s).
Proof. exact (fun_ext (fun b : real => @lem5238677 b s)). Qed.
Lemma lem5238681 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238682 (s : real -> Prop) : (term92 s) = (term93 s).
Proof. exact (MK_COMB (@lem5238681) (@lem5238680 s)). Qed.
Lemma lem5238687 (s : real -> Prop) : (term36 s) = (term94 s).
Proof. exact (MK_COMB (@lem5238644 s) (@lem5238682 s)). Qed.
Lemma lem5238690 (s : real -> Prop) : (term37 s) = (term95 s).
Proof. exact (MK_COMB (@lem5238617 s) (@lem5238687 s)). Qed.
Lemma lem5238693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238694 (s : real -> Prop) : (term39 s) = (term96 s).
Proof. exact (MK_COMB (@lem5238693) (@lem5238690 s)). Qed.
Lemma lem5238704 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238705 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238704 real P x). Qed.
Lemma lem5238706 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5238705 t x). Qed.
Lemma lem5238707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5238708 (t : real -> Prop) (x : real) : (term61 x t) = (term62 t x).
Proof. exact (MK_COMB (@lem5238707) (@lem5238706 t x)). Qed.
Lemma lem5238710 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5238711 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5238710 real x). Qed.
Lemma lem5238712 (t : real -> Prop) (x : real) : ((@IN real x t) = (@IN real x (@EMPTY real))) = ((t x) = False).
Proof. exact (MK_COMB (@lem5238708 t x) (@lem5238711 x)). Qed.
Lemma lem5238714 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5238715 (t : real -> Prop) (x : real) : ((t x) = False) = (term63 t x).
Proof. exact (@lem5238714 (t x)). Qed.
Lemma lem5238716 (t : real -> Prop) (x : real) : ((@IN real x t) = (@IN real x (@EMPTY real))) = (term63 t x).
Proof. exact (TRANS (@lem5238712 t x) (@lem5238715 t x)). Qed.
Lemma lem5238717 (t : real -> Prop) : (term64 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5238716 t x)). Qed.
Lemma lem5238718 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238719 (t : real -> Prop) : (term23 t) = (term66 t).
Proof. exact (MK_COMB (@lem5238718) (@lem5238717 t)). Qed.
Lemma lem5238724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238725 (t : real -> Prop) : (term24 t) = (term67 t).
Proof. exact (MK_COMB (@lem5238724) (@lem5238719 t)). Qed.
Lemma lem5238726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238727 (t : real -> Prop) : (term31 t) = (term71 t).
Proof. exact (MK_COMB (@lem5238726) (@lem5238725 t)). Qed.
Lemma lem5238735 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5238736 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5238735 real P x). Qed.
Lemma lem5238737 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5238736 t x). Qed.
Lemma lem5238738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238739 (t : real -> Prop) (x : real) : (term47 x t) = (term48 t x).
Proof. exact (MK_COMB (@lem5238738) (@lem5238737 t x)). Qed.
Lemma lem5238740 (s : real -> Prop) (x : real) : (term77 s x) = (term77 s x).
Proof. exact (eq_refl (term77 s x)). Qed.
Lemma lem5238741 (t : real -> Prop) (s : real -> Prop) (x : real) : (term97 t s x) = (term98 t s x).
Proof. exact (MK_COMB (@lem5238739 t x) (@lem5238740 s x)). Qed.
Lemma lem5238744 (t : real -> Prop) (s : real -> Prop) : (term99 t s) = (term100 t s).
Proof. exact (fun_ext (fun x : real => @lem5238741 t s x)). Qed.
Lemma lem5238745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238746 (t : real -> Prop) (s : real -> Prop) : (term40 t s) = (term101 t s).
Proof. exact (MK_COMB (@lem5238745) (@lem5238744 t s)). Qed.
Lemma lem5238751 (t : real -> Prop) (s : real -> Prop) : (term42 t s) = (term102 t s).
Proof. exact (MK_COMB (@lem5238727 t) (@lem5238746 t s)). Qed.
Lemma lem5238754 (t : real -> Prop) (s : real -> Prop) : (term44 t s) = (term103 t s).
Proof. exact (MK_COMB (@lem5238694 s) (@lem5238751 t s)). Qed.
Lemma lem5238757 (b : real) (t : real -> Prop) (s : real -> Prop) : (term46 b t s) = (term104 b t s).
Proof. exact (MK_COMB (@lem5238541 b s t) (@lem5238754 t s)). Qed.
Lemma lem5238760 (b : real) (t : real -> Prop) (s : real -> Prop) : (term104 b t s) = (term46 b t s).
Proof. exact (SYM (@lem5238757 b t s)). Qed.
Lemma lem5238762 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5238763 (b : real) (t : real -> Prop) (s : real -> Prop) : (term104 b t s) = (term106 b t s).
Proof. exact (@lem5238762 (term104 b t s)). Qed.
Lemma lem5238764 (b : real) (t : real -> Prop) (s : real -> Prop) : (term106 b t s) = (term104 b t s).
Proof. exact (SYM (@lem5238763 b t s)). Qed.
Lemma lem5238765 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term107 b t s) : term107 b t s.
Proof. exact (h1). Qed.
Lemma lem5238768 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term106 b t s) : term106 b t s.
Proof. exact (h1). Qed.
Lemma lem5238769 (b : real) (t : real -> Prop) (s : real -> Prop) : term108 b t s.
Proof. exact (fun h0 : term106 b t s => @lem5238768 b t s h0). Qed.
Lemma lem5238770 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term108 b t s) : term108 b t s.
Proof. exact (h1). Qed.
Lemma lem5238771 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term106 b t s) : term106 b t s.
Proof. exact (h1). Qed.
Lemma lem5238772 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term106 b t s) (h2 : term108 b t s) : term106 b t s.
Proof. exact (@lem5238770 b t s h2 (@lem5238771 b t s h1)). Qed.
Lemma lem5238773 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term106 b t s) : term109 b t s.
Proof. exact (fun h0 : term108 b t s => @lem5238772 b t s h1 h0). Qed.
Lemma lem5238774 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term108 b t s) : term108 b t s.
Proof. exact (h1). Qed.
Lemma lem5238775 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term106 b t s) (h2 : term108 b t s) : term106 b t s.
Proof. exact (@lem5238773 b t s h1 (@lem5238774 b t s h2)). Qed.
Lemma lem5238776 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term108 b t s) : term108 b t s.
Proof. exact (fun h0 : term106 b t s => @lem5238775 b t s h0 h1). Qed.
Lemma lem5238777 (b : real) (t : real -> Prop) (s : real -> Prop) : term110 b t s.
Proof. exact (fun h0 : term108 b t s => @lem5238776 b t s h0). Qed.
Lemma lem5238780 (b : real) (t : real -> Prop) (s : real -> Prop) : term108 b t s.
Proof. exact (@lem5238777 b t s (@lem5238769 b t s)). Qed.
Lemma lem5238794 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5238795 (b : real) (t : real -> Prop) (s : real -> Prop) : (term106 b t s) = (term111 b t s).
Proof. exact (@lem5238794 (term107 b t s)). Qed.
Lemma lem5238797 (t : Prop) : (term112 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5238798 (b : real) (t : real -> Prop) (s : real -> Prop) : (term111 b t s) = (term104 b t s).
Proof. exact (@lem5238797 (term104 b t s)). Qed.
Lemma lem5238801 (b : real) (t : real -> Prop) (s : real -> Prop) : (term106 b t s) = (term104 b t s).
Proof. exact (TRANS (@lem5238795 b t s) (@lem5238798 b t s)). Qed.
Lemma lem5238874 (t : real -> Prop) (s : real -> Prop) : (term113 t s) = (term114 t s).
Proof. exact (fun_ext (fun b : real => @lem5238801 b t s)). Qed.
Lemma lem5238875 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238876 (t : real -> Prop) (s : real -> Prop) : (term115 t s) = (term116 t s).
Proof. exact (MK_COMB (@lem5238875) (@lem5238874 t s)). Qed.
Lemma lem5238881 (s : real -> Prop) : (term117 s) = (term118 s).
Proof. exact (fun_ext (fun t : real -> Prop => @lem5238876 t s)). Qed.
Lemma lem5238882 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5238883 (s : real -> Prop) : (term119 s) = (term120 s).
Proof. exact (MK_COMB (@lem5238882) (@lem5238881 s)). Qed.
Lemma lem5238888 : term121 = term122.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5238883 s)). Qed.
Lemma lem5238889 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5238898 : term123 = term124.
Proof. exact (MK_COMB (@lem5238889) (@lem5238888)). Qed.
Lemma lem5238903 (t : real -> Prop) (s : real -> Prop) (x : real) : (term98 t s x) = (term98 t s x).
Proof. exact (eq_refl (term98 t s x)). Qed.
Lemma lem5238904 (t : real -> Prop) (s : real -> Prop) : (term100 t s) = (term100 t s).
Proof. exact (fun_ext (fun x : real => @lem5238903 t s x)). Qed.
Lemma lem5238905 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238906 (t : real -> Prop) (s : real -> Prop) : (term101 t s) = (term101 t s).
Proof. exact (MK_COMB (@lem5238905) (@lem5238904 t s)). Qed.
Lemma lem5238909 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5238910 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5238909 t x)). Qed.
Lemma lem5238911 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238912 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5238911) (@lem5238910 t)). Qed.
Lemma lem5238913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238914 (t : real -> Prop) : (term67 t) = (term67 t).
Proof. exact (MK_COMB (@lem5238913) (@lem5238912 t)). Qed.
Lemma lem5238915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238916 (t : real -> Prop) : (term71 t) = (term71 t).
Proof. exact (MK_COMB (@lem5238915) (@lem5238914 t)). Qed.
Lemma lem5238917 (t : real -> Prop) (s : real -> Prop) : (term102 t s) = (term102 t s).
Proof. exact (MK_COMB (@lem5238916 t) (@lem5238906 t s)). Qed.
Lemma lem5238918 (b : real) (s : real -> Prop) : (term6 b s) = (term6 b s).
Proof. exact (eq_refl (term6 b s)). Qed.
Lemma lem5238923 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term50 s b x).
Proof. exact (eq_refl (term50 s b x)). Qed.
Lemma lem5238924 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5238923 s b x)). Qed.
Lemma lem5238925 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238926 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5238925) (@lem5238924 s b)). Qed.
Lemma lem5238927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238928 (s : real -> Prop) (b : real) : (term87 s b) = (term87 s b).
Proof. exact (MK_COMB (@lem5238927) (@lem5238926 s b)). Qed.
Lemma lem5238929 (b : real) (s : real -> Prop) : (term89 b s) = (term89 b s).
Proof. exact (MK_COMB (@lem5238928 s b) (@lem5238918 b s)). Qed.
Lemma lem5238930 (s : real -> Prop) : (term91 s) = (term91 s).
Proof. exact (fun_ext (fun b : real => @lem5238929 b s)). Qed.
Lemma lem5238931 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238932 (s : real -> Prop) : (term93 s) = (term93 s).
Proof. exact (MK_COMB (@lem5238931) (@lem5238930 s)). Qed.
Lemma lem5238937 (s : real -> Prop) (x : real) : (term79 s x) = (term79 s x).
Proof. exact (eq_refl (term79 s x)). Qed.
Lemma lem5238938 (s : real -> Prop) : (term81 s) = (term81 s).
Proof. exact (fun_ext (fun x : real => @lem5238937 s x)). Qed.
Lemma lem5238939 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238940 (s : real -> Prop) : (term83 s) = (term83 s).
Proof. exact (MK_COMB (@lem5238939) (@lem5238938 s)). Qed.
Lemma lem5238941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238942 (s : real -> Prop) : (term85 s) = (term85 s).
Proof. exact (MK_COMB (@lem5238941) (@lem5238940 s)). Qed.
Lemma lem5238943 (s : real -> Prop) : (term94 s) = (term94 s).
Proof. exact (MK_COMB (@lem5238942 s) (@lem5238932 s)). Qed.
Lemma lem5238948 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term50 s b x).
Proof. exact (eq_refl (term50 s b x)). Qed.
Lemma lem5238949 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5238948 s b x)). Qed.
Lemma lem5238950 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238951 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5238950) (@lem5238949 s b)). Qed.
Lemma lem5238952 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (fun_ext (fun b : real => @lem5238951 s b)). Qed.
Lemma lem5238953 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5238954 (s : real -> Prop) : (term74 s) = (term74 s).
Proof. exact (MK_COMB (@lem5238953) (@lem5238952 s)). Qed.
Lemma lem5238957 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5238958 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5238957 s x)). Qed.
Lemma lem5238959 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238960 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5238959) (@lem5238958 s)). Qed.
Lemma lem5238961 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238962 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (MK_COMB (@lem5238961) (@lem5238960 s)). Qed.
Lemma lem5238963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238964 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (MK_COMB (@lem5238963) (@lem5238962 s)). Qed.
Lemma lem5238965 (s : real -> Prop) : (term75 s) = (term75 s).
Proof. exact (MK_COMB (@lem5238964 s) (@lem5238954 s)). Qed.
Lemma lem5238966 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238967 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (MK_COMB (@lem5238966) (@lem5238965 s)). Qed.
Lemma lem5238968 (s : real -> Prop) : (term95 s) = (term95 s).
Proof. exact (MK_COMB (@lem5238967 s) (@lem5238943 s)). Qed.
Lemma lem5238969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238970 (s : real -> Prop) : (term96 s) = (term96 s).
Proof. exact (MK_COMB (@lem5238969) (@lem5238968 s)). Qed.
Lemma lem5238971 (t : real -> Prop) (s : real -> Prop) : (term103 t s) = (term103 t s).
Proof. exact (MK_COMB (@lem5238970 s) (@lem5238917 t s)). Qed.
Lemma lem5238974 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5238975 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5238974 t x)). Qed.
Lemma lem5238976 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238977 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5238976) (@lem5238975 t)). Qed.
Lemma lem5238978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5238979 (t : real -> Prop) : (term67 t) = (term67 t).
Proof. exact (MK_COMB (@lem5238978) (@lem5238977 t)). Qed.
Lemma lem5238984 (t : real -> Prop) (s : real -> Prop) (x : real) : (term56 t s x) = (term56 t s x).
Proof. exact (eq_refl (term56 t s x)). Qed.
Lemma lem5238985 (t : real -> Prop) (s : real -> Prop) : (term58 t s) = (term58 t s).
Proof. exact (fun_ext (fun x : real => @lem5238984 t s x)). Qed.
Lemma lem5238986 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238987 (t : real -> Prop) (s : real -> Prop) : (term59 t s) = (term59 t s).
Proof. exact (MK_COMB (@lem5238986) (@lem5238985 t s)). Qed.
Lemma lem5238988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238989 (t : real -> Prop) (s : real -> Prop) : (term60 t s) = (term60 t s).
Proof. exact (MK_COMB (@lem5238988) (@lem5238987 t s)). Qed.
Lemma lem5238990 (s : real -> Prop) (t : real -> Prop) : (term68 s t) = (term68 s t).
Proof. exact (MK_COMB (@lem5238989 t s) (@lem5238979 t)). Qed.
Lemma lem5238995 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term50 s b x).
Proof. exact (eq_refl (term50 s b x)). Qed.
Lemma lem5238996 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5238995 s b x)). Qed.
Lemma lem5238997 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5238998 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5238997) (@lem5238996 s b)). Qed.
Lemma lem5238999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239000 (s : real -> Prop) (b : real) : (term54 s b) = (term54 s b).
Proof. exact (MK_COMB (@lem5238999) (@lem5238998 s b)). Qed.
Lemma lem5239001 (b : real) (s : real -> Prop) (t : real -> Prop) : (term69 b s t) = (term69 b s t).
Proof. exact (MK_COMB (@lem5239000 s b) (@lem5238990 s t)). Qed.
Lemma lem5239002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5239003 (b : real) (s : real -> Prop) (t : real -> Prop) : (term70 b s t) = (term70 b s t).
Proof. exact (MK_COMB (@lem5239002) (@lem5239001 b s t)). Qed.
Lemma lem5239004 (b : real) (t : real -> Prop) (s : real -> Prop) : (term104 b t s) = (term104 b t s).
Proof. exact (MK_COMB (@lem5239003 b s t) (@lem5238971 t s)). Qed.
Lemma lem5239005 (t : real -> Prop) (s : real -> Prop) : (term114 t s) = (term114 t s).
Proof. exact (fun_ext (fun b : real => @lem5239004 b t s)). Qed.
Lemma lem5239006 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239007 (t : real -> Prop) (s : real -> Prop) : (term116 t s) = (term116 t s).
Proof. exact (MK_COMB (@lem5239006) (@lem5239005 t s)). Qed.
Lemma lem5239008 (s : real -> Prop) : (term118 s) = (term118 s).
Proof. exact (fun_ext (fun t : real -> Prop => @lem5239007 t s)). Qed.
Lemma lem5239009 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5239010 (s : real -> Prop) : (term120 s) = (term120 s).
Proof. exact (MK_COMB (@lem5239009) (@lem5239008 s)). Qed.
Lemma lem5239011 : term122 = term122.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5239010 s)). Qed.
Lemma lem5239012 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5239013 : term124 = term124.
Proof. exact (MK_COMB (@lem5239012) (@lem5239011)). Qed.
Lemma lem5239130 : term123 = term124.
Proof. exact (TRANS (@lem5238898) (@lem5239013)). Qed.
Lemma lem5239131 : term124 = term123.
Proof. exact (SYM (@lem5239130)). Qed.
Lemma lem5239132 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term69 b s t) : term69 b s t.
Proof. exact (h1). Qed.
Lemma lem5239133 (s : real -> Prop) (h1 : term95 s) : term95 s.
Proof. exact (h1). Qed.
Lemma lem5239135 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5239136 (t : real -> Prop) (s : real -> Prop) : (term102 t s) = (term125 t s).
Proof. exact (@lem5239135 (term102 t s)). Qed.
Lemma lem5239137 (t : real -> Prop) (s : real -> Prop) : (term125 t s) = (term102 t s).
Proof. exact (SYM (@lem5239136 t s)). Qed.
Lemma lem5239138 (t : real -> Prop) (s : real -> Prop) (h1 : term126 t s) : term126 t s.
Proof. exact (h1). Qed.
Lemma lem5239145 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term127 s b x).
Proof. exact (@lem17265 (s x) (real_le b x)). Qed.
Lemma lem5239146 (s : real -> Prop) (b : real) : (term52 s b) = (term128 s b).
Proof. exact (fun_ext (fun x : real => @lem5239145 s b x)). Qed.
Lemma lem5239147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239148 (s : real -> Prop) (b : real) : (term53 s b) = (term129 s b).
Proof. exact (MK_COMB (@lem5239147) (@lem5239146 s b)). Qed.
Lemma lem5239155 (t : real -> Prop) (s : real -> Prop) (x : real) : (term56 t s x) = (term130 t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem5239156 (t : real -> Prop) (s : real -> Prop) : (term58 t s) = (term131 t s).
Proof. exact (fun_ext (fun x : real => @lem5239155 t s x)). Qed.
Lemma lem5239157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239158 (t : real -> Prop) (s : real -> Prop) : (term59 t s) = (term132 t s).
Proof. exact (MK_COMB (@lem5239157) (@lem5239156 t s)). Qed.
Lemma lem5239161 (t : real -> Prop) (x : real) : (term133 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem5239162 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5239163 (t : real -> Prop) : (term67 t) = (term136 t).
Proof. exact (@lem5239162 (term65 t)). Qed.
Lemma lem5239164 (t : real -> Prop) (x : real) : (term137 t x) = (term63 t x).
Proof. exact (eq_refl (term137 t x)). Qed.
Lemma lem5239165 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239166 (t : real -> Prop) (x : real) : (term138 t x) = (term133 t x).
Proof. exact (MK_COMB (@lem5239165) (@lem5239164 t x)). Qed.
Lemma lem5239167 (t : real -> Prop) (x : real) : (term138 t x) = (t x).
Proof. exact (TRANS (@lem5239166 t x) (@lem5239161 t x)). Qed.
Lemma lem5239168 (t : real -> Prop) : (term139 t) = (term140 t).
Proof. exact (fun_ext (fun x : real => @lem5239167 t x)). Qed.
Lemma lem5239169 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239170 (t : real -> Prop) : (term136 t) = (term141 t).
Proof. exact (MK_COMB (@lem5239169) (@lem5239168 t)). Qed.
Lemma lem5239171 (t : real -> Prop) : (term67 t) = (term141 t).
Proof. exact (TRANS (@lem5239163 t) (@lem5239170 t)). Qed.
Lemma lem5239172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239173 (t : real -> Prop) (s : real -> Prop) : (term60 t s) = (term142 t s).
Proof. exact (MK_COMB (@lem5239172) (@lem5239158 t s)). Qed.
Lemma lem5239174 (s : real -> Prop) (t : real -> Prop) : (term68 s t) = (term143 s t).
Proof. exact (MK_COMB (@lem5239173 t s) (@lem5239171 t)). Qed.
Lemma lem5239175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239176 (s : real -> Prop) (b : real) : (term54 s b) = (term144 s b).
Proof. exact (MK_COMB (@lem5239175) (@lem5239148 s b)). Qed.
Lemma lem5239177 (b : real) (s : real -> Prop) (t : real -> Prop) : (term69 b s t) = (term145 b s t).
Proof. exact (MK_COMB (@lem5239176 s b) (@lem5239174 s t)). Qed.
Lemma lem5239264 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5239265 (P : Prop) (Q : real -> Prop) : (term148 P Q) = (term149 P Q).
Proof. exact (@lem5239264 real P Q). Qed.
Lemma lem5239266 (s : real -> Prop) (t : real -> Prop) : (term143 s t) = (term150 s t).
Proof. exact (@lem5239265 (term132 t s) t). Qed.
Lemma lem5239267 (s : real -> Prop) (b : real) : (term144 s b) = (term144 s b).
Proof. exact (eq_refl (term144 s b)). Qed.
Lemma lem5239268 (b : real) (s : real -> Prop) (t : real -> Prop) : (term145 b s t) = (term151 b s t).
Proof. exact (MK_COMB (@lem5239267 s b) (@lem5239266 s t)). Qed.
Lemma lem5239270 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5239271 (P : Prop) (Q : real -> Prop) : (term148 P Q) = (term149 P Q).
Proof. exact (@lem5239270 real P Q). Qed.
Lemma lem5239272 (b : real) (s : real -> Prop) (t : real -> Prop) : (term152 b s t) = (term153 b s t).
Proof. exact (@lem5239271 (term129 s b) (term154 s t)). Qed.
Lemma lem5239273 (s : real -> Prop) (t : real -> Prop) (x : real) : (term155 s t x) = (term156 s t x).
Proof. exact (eq_refl (term155 s t x)). Qed.
Lemma lem5239274 (s : real -> Prop) (t : real -> Prop) : (term157 s t) = (term154 s t).
Proof. exact (fun_ext (fun x : real => @lem5239273 s t x)). Qed.
Lemma lem5239275 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239276 (s : real -> Prop) (t : real -> Prop) : (term158 s t) = (term150 s t).
Proof. exact (MK_COMB (@lem5239275) (@lem5239274 s t)). Qed.
Lemma lem5239277 (s : real -> Prop) (b : real) : (term144 s b) = (term144 s b).
Proof. exact (eq_refl (term144 s b)). Qed.
Lemma lem5239278 (b : real) (s : real -> Prop) (t : real -> Prop) : (term152 b s t) = (term151 b s t).
Proof. exact (MK_COMB (@lem5239277 s b) (@lem5239276 s t)). Qed.
Lemma lem5239279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239280 (b : real) (s : real -> Prop) (t : real -> Prop) : (term159 b s t) = (term160 b s t).
Proof. exact (MK_COMB (@lem5239279) (@lem5239278 b s t)). Qed.
Lemma lem5239281 (s : real -> Prop) (t : real -> Prop) (x : real) : (term155 s t x) = (term156 s t x).
Proof. exact (eq_refl (term155 s t x)). Qed.
Lemma lem5239282 (s : real -> Prop) (b : real) : (term144 s b) = (term144 s b).
Proof. exact (eq_refl (term144 s b)). Qed.
Lemma lem5239283 (b : real) (s : real -> Prop) (t : real -> Prop) (x : real) : (term161 b s t x) = (term162 b s t x).
Proof. exact (MK_COMB (@lem5239282 s b) (@lem5239281 s t x)). Qed.
Lemma lem5239284 (b : real) (s : real -> Prop) (t : real -> Prop) : (term163 b s t) = (term164 b s t).
Proof. exact (fun_ext (fun x : real => @lem5239283 b s t x)). Qed.
Lemma lem5239285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239286 (b : real) (s : real -> Prop) (t : real -> Prop) : (term153 b s t) = (term165 b s t).
Proof. exact (MK_COMB (@lem5239285) (@lem5239284 b s t)). Qed.
Lemma lem5239287 (b : real) (s : real -> Prop) (t : real -> Prop) : ((term152 b s t) = (term153 b s t)) = ((term151 b s t) = (term165 b s t)).
Proof. exact (MK_COMB (@lem5239280 b s t) (@lem5239286 b s t)). Qed.
Lemma lem5239288 (b : real) (s : real -> Prop) (t : real -> Prop) : (term151 b s t) = (term165 b s t).
Proof. exact (EQ_MP (@lem5239287 b s t) (@lem5239272 b s t)). Qed.
Lemma lem5239290 (b : real) (s : real -> Prop) (t : real -> Prop) : (term145 b s t) = (term165 b s t).
Proof. exact (TRANS (@lem5239268 b s t) (@lem5239288 b s t)). Qed.
Lemma lem5239291 (b : real) (s : real -> Prop) (t : real -> Prop) : (term69 b s t) = (term165 b s t).
Proof. exact (TRANS (@lem5239177 b s t) (@lem5239290 b s t)). Qed.
Lemma lem5239292 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term69 b s t) : term165 b s t.
Proof. exact (EQ_MP (@lem5239291 b s t) (@lem5239132 b s t h1)). Qed.
Lemma lem5239293 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5239294 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5239293 s x)). Qed.
Lemma lem5239295 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239296 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5239295) (@lem5239294 s)). Qed.
Lemma lem5239297 (s : real -> Prop) : (term166 s) = (term66 s).
Proof. exact (@lem16933 (term66 s)). Qed.
Lemma lem5239298 (s : real -> Prop) : (term166 s) = (term66 s).
Proof. exact (TRANS (@lem5239297 s) (@lem5239296 s)). Qed.
Lemma lem5239305 (s : real -> Prop) (b : real) (x : real) : (term167 s b x) = (term168 s b x).
Proof. exact (@lem17362 (s x) (real_le b x)). Qed.
Lemma lem5239306 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5239307 (s : real -> Prop) (b : real) : (term169 s b) = (term170 s b).
Proof. exact (@lem5239306 (term52 s b)). Qed.
Lemma lem5239308 (s : real -> Prop) (b : real) (x : real) : (term171 s b x) = (term50 s b x).
Proof. exact (eq_refl (term171 s b x)). Qed.
Lemma lem5239309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239310 (s : real -> Prop) (b : real) (x : real) : (term172 s b x) = (term167 s b x).
Proof. exact (MK_COMB (@lem5239309) (@lem5239308 s b x)). Qed.
Lemma lem5239311 (s : real -> Prop) (b : real) (x : real) : (term172 s b x) = (term168 s b x).
Proof. exact (TRANS (@lem5239310 s b x) (@lem5239305 s b x)). Qed.
Lemma lem5239312 (s : real -> Prop) (b : real) : (term173 s b) = (term174 s b).
Proof. exact (fun_ext (fun x : real => @lem5239311 s b x)). Qed.
Lemma lem5239313 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239314 (s : real -> Prop) (b : real) : (term170 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5239313) (@lem5239312 s b)). Qed.
Lemma lem5239315 (s : real -> Prop) (b : real) : (term169 s b) = (term175 s b).
Proof. exact (TRANS (@lem5239307 s b) (@lem5239314 s b)). Qed.
Lemma lem5239316 (P : real -> Prop) : (term176 P) = (term66 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5239317 (s : real -> Prop) : (term177 s) = (term178 s).
Proof. exact (@lem5239316 (term73 s)). Qed.
Lemma lem5239318 (s : real -> Prop) (b : real) : (term179 s b) = (term53 s b).
Proof. exact (eq_refl (term179 s b)). Qed.
Lemma lem5239319 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239320 (s : real -> Prop) (b : real) : (term180 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5239319) (@lem5239318 s b)). Qed.
Lemma lem5239321 (s : real -> Prop) (b : real) : (term180 s b) = (term175 s b).
Proof. exact (TRANS (@lem5239320 s b) (@lem5239315 s b)). Qed.
Lemma lem5239322 (s : real -> Prop) : (term181 s) = (term182 s).
Proof. exact (fun_ext (fun b : real => @lem5239321 s b)). Qed.
Lemma lem5239323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239324 (s : real -> Prop) : (term178 s) = (term183 s).
Proof. exact (MK_COMB (@lem5239323) (@lem5239322 s)). Qed.
Lemma lem5239325 (s : real -> Prop) : (term177 s) = (term183 s).
Proof. exact (TRANS (@lem5239317 s) (@lem5239324 s)). Qed.
Lemma lem5239326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239327 (s : real -> Prop) : (term184 s) = (term185 s).
Proof. exact (MK_COMB (@lem5239326) (@lem5239298 s)). Qed.
Lemma lem5239328 (s : real -> Prop) : (term186 s) = (term187 s).
Proof. exact (MK_COMB (@lem5239327 s) (@lem5239325 s)). Qed.
Lemma lem5239329 (s : real -> Prop) : (term188 s) = (term186 s).
Proof. exact (@lem17045 (term67 s) (term74 s)). Qed.
Lemma lem5239330 (s : real -> Prop) : (term188 s) = (term187 s).
Proof. exact (TRANS (@lem5239329 s) (@lem5239328 s)). Qed.
Lemma lem5239337 (s : real -> Prop) (x : real) : (term79 s x) = (term189 s x).
Proof. exact (@lem17265 (s x) (term77 s x)). Qed.
Lemma lem5239338 (s : real -> Prop) : (term81 s) = (term190 s).
Proof. exact (fun_ext (fun x : real => @lem5239337 s x)). Qed.
Lemma lem5239339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239340 (s : real -> Prop) : (term83 s) = (term191 s).
Proof. exact (MK_COMB (@lem5239339) (@lem5239338 s)). Qed.
Lemma lem5239347 (s : real -> Prop) (b : real) (x : real) : (term167 s b x) = (term168 s b x).
Proof. exact (@lem17362 (s x) (real_le b x)). Qed.
Lemma lem5239348 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5239349 (s : real -> Prop) (b : real) : (term169 s b) = (term170 s b).
Proof. exact (@lem5239348 (term52 s b)). Qed.
Lemma lem5239350 (s : real -> Prop) (b : real) (x : real) : (term171 s b x) = (term50 s b x).
Proof. exact (eq_refl (term171 s b x)). Qed.
Lemma lem5239351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239352 (s : real -> Prop) (b : real) (x : real) : (term172 s b x) = (term167 s b x).
Proof. exact (MK_COMB (@lem5239351) (@lem5239350 s b x)). Qed.
Lemma lem5239353 (s : real -> Prop) (b : real) (x : real) : (term172 s b x) = (term168 s b x).
Proof. exact (TRANS (@lem5239352 s b x) (@lem5239347 s b x)). Qed.
Lemma lem5239354 (s : real -> Prop) (b : real) : (term173 s b) = (term174 s b).
Proof. exact (fun_ext (fun x : real => @lem5239353 s b x)). Qed.
Lemma lem5239355 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239356 (s : real -> Prop) (b : real) : (term170 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5239355) (@lem5239354 s b)). Qed.
Lemma lem5239357 (s : real -> Prop) (b : real) : (term169 s b) = (term175 s b).
Proof. exact (TRANS (@lem5239349 s b) (@lem5239356 s b)). Qed.
Lemma lem5239358 (b : real) (s : real -> Prop) : (term6 b s) = (term6 b s).
Proof. exact (eq_refl (term6 b s)). Qed.
Lemma lem5239359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239360 (s : real -> Prop) (b : real) : (term192 s b) = (term193 s b).
Proof. exact (MK_COMB (@lem5239359) (@lem5239357 s b)). Qed.
Lemma lem5239361 (b : real) (s : real -> Prop) : (term194 b s) = (term195 b s).
Proof. exact (MK_COMB (@lem5239360 s b) (@lem5239358 b s)). Qed.
Lemma lem5239362 (b : real) (s : real -> Prop) : (term89 b s) = (term194 b s).
Proof. exact (@lem17265 (term53 s b) (term6 b s)). Qed.
Lemma lem5239363 (b : real) (s : real -> Prop) : (term89 b s) = (term195 b s).
Proof. exact (TRANS (@lem5239362 b s) (@lem5239361 b s)). Qed.
Lemma lem5239364 (s : real -> Prop) : (term91 s) = (term196 s).
Proof. exact (fun_ext (fun b : real => @lem5239363 b s)). Qed.
Lemma lem5239365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239366 (s : real -> Prop) : (term93 s) = (term197 s).
Proof. exact (MK_COMB (@lem5239365) (@lem5239364 s)). Qed.
Lemma lem5239367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239368 (s : real -> Prop) : (term85 s) = (term198 s).
Proof. exact (MK_COMB (@lem5239367) (@lem5239340 s)). Qed.
Lemma lem5239369 (s : real -> Prop) : (term94 s) = (term199 s).
Proof. exact (MK_COMB (@lem5239368 s) (@lem5239366 s)). Qed.
Lemma lem5239370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239371 (s : real -> Prop) : (term200 s) = (term201 s).
Proof. exact (MK_COMB (@lem5239370) (@lem5239330 s)). Qed.
Lemma lem5239372 (s : real -> Prop) : (term202 s) = (term203 s).
Proof. exact (MK_COMB (@lem5239371 s) (@lem5239369 s)). Qed.
Lemma lem5239373 (s : real -> Prop) : (term95 s) = (term202 s).
Proof. exact (@lem17265 (term75 s) (term94 s)). Qed.
Lemma lem5239374 (s : real -> Prop) : (term95 s) = (term203 s).
Proof. exact (TRANS (@lem5239373 s) (@lem5239372 s)). Qed.
Lemma lem5239537 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5239538 (P : type1626) : (term206 P) = (term207 P).
Proof. exact (@lem5239537 real real P). Qed.
Lemma lem5239539 (s : real -> Prop) : (term208 s) = (term209 s).
Proof. exact (@lem5239538 (term210 s)). Qed.
Lemma lem5239540 (s : real -> Prop) (b : real) : (term211 s b) = (term174 s b).
Proof. exact (eq_refl (term211 s b)). Qed.
Lemma lem5239541 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5239542 (s : real -> Prop) (b : real) (x : real) : (term212 s b x) = (term213 s b x).
Proof. exact (MK_COMB (@lem5239540 s b) (@lem5239541 x)). Qed.
Lemma lem5239543 (s : real -> Prop) (b : real) (x : real) : (term213 s b x) = (term168 s b x).
Proof. exact (eq_refl (term213 s b x)). Qed.
Lemma lem5239544 (s : real -> Prop) (b : real) (x : real) : (term212 s b x) = (term168 s b x).
Proof. exact (TRANS (@lem5239542 s b x) (@lem5239543 s b x)). Qed.
Lemma lem5239545 (s : real -> Prop) (b : real) : (term214 s b) = (term174 s b).
Proof. exact (fun_ext (fun x : real => @lem5239544 s b x)). Qed.
Lemma lem5239546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239547 (s : real -> Prop) (b : real) : (term215 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5239546) (@lem5239545 s b)). Qed.
Lemma lem5239548 (s : real -> Prop) : (term216 s) = (term182 s).
Proof. exact (fun_ext (fun b : real => @lem5239547 s b)). Qed.
Lemma lem5239549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239550 (s : real -> Prop) : (term208 s) = (term183 s).
Proof. exact (MK_COMB (@lem5239549) (@lem5239548 s)). Qed.
Lemma lem5239551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239552 (s : real -> Prop) : (term217 s) = (term218 s).
Proof. exact (MK_COMB (@lem5239551) (@lem5239550 s)). Qed.
Lemma lem5239553 (s : real -> Prop) (b : real) : (term211 s b) = (term174 s b).
Proof. exact (eq_refl (term211 s b)). Qed.
Lemma lem5239554 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5239555 (s : real -> Prop) (x : real -> real) (b : real) : (term219 s x b) = (term220 s x b).
Proof. exact (MK_COMB (@lem5239553 s b) (@lem5239554 x b)). Qed.
Lemma lem5239556 (s : real -> Prop) (x : real -> real) (b : real) : (term220 s x b) = (term221 s x b).
Proof. exact (eq_refl (term220 s x b)). Qed.
Lemma lem5239557 (s : real -> Prop) (x : real -> real) (b : real) : (term219 s x b) = (term221 s x b).
Proof. exact (TRANS (@lem5239555 s x b) (@lem5239556 s x b)). Qed.
Lemma lem5239558 (s : real -> Prop) (x : real -> real) : (term222 s x) = (term223 s x).
Proof. exact (fun_ext (fun b : real => @lem5239557 s x b)). Qed.
Lemma lem5239559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239560 (s : real -> Prop) (x : real -> real) : (term224 s x) = (term225 s x).
Proof. exact (MK_COMB (@lem5239559) (@lem5239558 s x)). Qed.
Lemma lem5239561 (s : real -> Prop) : (term226 s) = (term227 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239560 s x)). Qed.
Lemma lem5239562 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239563 (s : real -> Prop) : (term209 s) = (term228 s).
Proof. exact (MK_COMB (@lem5239562) (@lem5239561 s)). Qed.
Lemma lem5239564 (s : real -> Prop) : ((term208 s) = (term209 s)) = ((term183 s) = (term228 s)).
Proof. exact (MK_COMB (@lem5239552 s) (@lem5239563 s)). Qed.
Lemma lem5239565 (s : real -> Prop) : (term183 s) = (term228 s).
Proof. exact (EQ_MP (@lem5239564 s) (@lem5239539 s)). Qed.
Lemma lem5239566 (s : real -> Prop) : (term185 s) = (term185 s).
Proof. exact (eq_refl (term185 s)). Qed.
Lemma lem5239567 (s : real -> Prop) : (term187 s) = (term229 s).
Proof. exact (MK_COMB (@lem5239566 s) (@lem5239565 s)). Qed.
Lemma lem5239569 {A : Type'} (P : Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5239570 (P : Prop) (Q : type1028) : (term232 P Q) = (term233 P Q).
Proof. exact (@lem5239569 (real -> real) P Q). Qed.
Lemma lem5239571 (s : real -> Prop) : (term234 s) = (term235 s).
Proof. exact (@lem5239570 (term66 s) (term227 s)). Qed.
Lemma lem5239572 (s : real -> Prop) (x : real -> real) : (term236 s x) = (term225 s x).
Proof. exact (eq_refl (term236 s x)). Qed.
Lemma lem5239573 (s : real -> Prop) : (term237 s) = (term227 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239572 s x)). Qed.
Lemma lem5239574 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239575 (s : real -> Prop) : (term238 s) = (term228 s).
Proof. exact (MK_COMB (@lem5239574) (@lem5239573 s)). Qed.
Lemma lem5239576 (s : real -> Prop) : (term185 s) = (term185 s).
Proof. exact (eq_refl (term185 s)). Qed.
Lemma lem5239577 (s : real -> Prop) : (term234 s) = (term229 s).
Proof. exact (MK_COMB (@lem5239576 s) (@lem5239575 s)). Qed.
Lemma lem5239578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239579 (s : real -> Prop) : (term239 s) = (term240 s).
Proof. exact (MK_COMB (@lem5239578) (@lem5239577 s)). Qed.
Lemma lem5239580 (s : real -> Prop) (x : real -> real) : (term236 s x) = (term225 s x).
Proof. exact (eq_refl (term236 s x)). Qed.
Lemma lem5239581 (s : real -> Prop) : (term185 s) = (term185 s).
Proof. exact (eq_refl (term185 s)). Qed.
Lemma lem5239582 (s : real -> Prop) (x : real -> real) : (term241 s x) = (term242 s x).
Proof. exact (MK_COMB (@lem5239581 s) (@lem5239580 s x)). Qed.
Lemma lem5239583 (s : real -> Prop) : (term243 s) = (term244 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239582 s x)). Qed.
Lemma lem5239584 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239585 (s : real -> Prop) : (term235 s) = (term245 s).
Proof. exact (MK_COMB (@lem5239584) (@lem5239583 s)). Qed.
Lemma lem5239586 (s : real -> Prop) : ((term234 s) = (term235 s)) = ((term229 s) = (term245 s)).
Proof. exact (MK_COMB (@lem5239579 s) (@lem5239585 s)). Qed.
Lemma lem5239587 (s : real -> Prop) : (term229 s) = (term245 s).
Proof. exact (EQ_MP (@lem5239586 s) (@lem5239571 s)). Qed.
Lemma lem5239588 (s : real -> Prop) : (term187 s) = (term245 s).
Proof. exact (TRANS (@lem5239567 s) (@lem5239587 s)). Qed.
Lemma lem5239589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239590 (s : real -> Prop) : (term201 s) = (term246 s).
Proof. exact (MK_COMB (@lem5239589) (@lem5239588 s)). Qed.
Lemma lem5239592 {A : Type'} (P : A -> Prop) (Q : Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5239593 (P : real -> Prop) (Q : Prop) : (term249 P Q) = (term250 P Q).
Proof. exact (@lem5239592 real P Q). Qed.
Lemma lem5239594 (b : real) (s : real -> Prop) : (term251 b s) = (term252 b s).
Proof. exact (@lem5239593 (term174 s b) (term6 b s)). Qed.
Lemma lem5239595 (s : real -> Prop) (b : real) (x : real) : (term213 s b x) = (term168 s b x).
Proof. exact (eq_refl (term213 s b x)). Qed.
Lemma lem5239596 (s : real -> Prop) (b : real) : (term253 s b) = (term174 s b).
Proof. exact (fun_ext (fun x : real => @lem5239595 s b x)). Qed.
Lemma lem5239597 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239598 (s : real -> Prop) (b : real) : (term254 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5239597) (@lem5239596 s b)). Qed.
Lemma lem5239599 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239600 (s : real -> Prop) (b : real) : (term255 s b) = (term193 s b).
Proof. exact (MK_COMB (@lem5239599) (@lem5239598 s b)). Qed.
Lemma lem5239601 (b : real) (s : real -> Prop) : (term6 b s) = (term6 b s).
Proof. exact (eq_refl (term6 b s)). Qed.
Lemma lem5239602 (b : real) (s : real -> Prop) : (term251 b s) = (term195 b s).
Proof. exact (MK_COMB (@lem5239600 s b) (@lem5239601 b s)). Qed.
Lemma lem5239603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239604 (b : real) (s : real -> Prop) : (term256 b s) = (term257 b s).
Proof. exact (MK_COMB (@lem5239603) (@lem5239602 b s)). Qed.
Lemma lem5239605 (s : real -> Prop) (b : real) (x : real) : (term213 s b x) = (term168 s b x).
Proof. exact (eq_refl (term213 s b x)). Qed.
Lemma lem5239606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239607 (s : real -> Prop) (b : real) (x : real) : (term258 s b x) = (term259 s b x).
Proof. exact (MK_COMB (@lem5239606) (@lem5239605 s b x)). Qed.
Lemma lem5239608 (b : real) (s : real -> Prop) : (term6 b s) = (term6 b s).
Proof. exact (eq_refl (term6 b s)). Qed.
Lemma lem5239609 (x : real) (b : real) (s : real -> Prop) : (term260 x b s) = (term261 x b s).
Proof. exact (MK_COMB (@lem5239607 s b x) (@lem5239608 b s)). Qed.
Lemma lem5239610 (b : real) (s : real -> Prop) : (term262 b s) = (term263 b s).
Proof. exact (fun_ext (fun x : real => @lem5239609 x b s)). Qed.
Lemma lem5239611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239612 (b : real) (s : real -> Prop) : (term252 b s) = (term264 b s).
Proof. exact (MK_COMB (@lem5239611) (@lem5239610 b s)). Qed.
Lemma lem5239613 (b : real) (s : real -> Prop) : ((term251 b s) = (term252 b s)) = ((term195 b s) = (term264 b s)).
Proof. exact (MK_COMB (@lem5239604 b s) (@lem5239612 b s)). Qed.
Lemma lem5239614 (b : real) (s : real -> Prop) : (term195 b s) = (term264 b s).
Proof. exact (EQ_MP (@lem5239613 b s) (@lem5239594 b s)). Qed.
Lemma lem5239615 (s : real -> Prop) : (term196 s) = (term265 s).
Proof. exact (fun_ext (fun b : real => @lem5239614 b s)). Qed.
Lemma lem5239616 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239617 (s : real -> Prop) : (term197 s) = (term266 s).
Proof. exact (MK_COMB (@lem5239616) (@lem5239615 s)). Qed.
Lemma lem5239619 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5239620 (P : type1626) : (term206 P) = (term207 P).
Proof. exact (@lem5239619 real real P). Qed.
Lemma lem5239621 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (@lem5239620 (term269 s)). Qed.
Lemma lem5239622 (b : real) (s : real -> Prop) : (term270 s b) = (term263 b s).
Proof. exact (eq_refl (term270 s b)). Qed.
Lemma lem5239623 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5239624 (b : real) (s : real -> Prop) (x : real) : (term271 s b x) = (term272 b s x).
Proof. exact (MK_COMB (@lem5239622 b s) (@lem5239623 x)). Qed.
Lemma lem5239625 (x : real) (b : real) (s : real -> Prop) : (term272 b s x) = (term261 x b s).
Proof. exact (eq_refl (term272 b s x)). Qed.
Lemma lem5239626 (x : real) (b : real) (s : real -> Prop) : (term271 s b x) = (term261 x b s).
Proof. exact (TRANS (@lem5239624 b s x) (@lem5239625 x b s)). Qed.
Lemma lem5239627 (b : real) (s : real -> Prop) : (term273 s b) = (term263 b s).
Proof. exact (fun_ext (fun x : real => @lem5239626 x b s)). Qed.
Lemma lem5239628 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239629 (b : real) (s : real -> Prop) : (term274 s b) = (term264 b s).
Proof. exact (MK_COMB (@lem5239628) (@lem5239627 b s)). Qed.
Lemma lem5239630 (s : real -> Prop) : (term275 s) = (term265 s).
Proof. exact (fun_ext (fun b : real => @lem5239629 b s)). Qed.
Lemma lem5239631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239632 (s : real -> Prop) : (term267 s) = (term266 s).
Proof. exact (MK_COMB (@lem5239631) (@lem5239630 s)). Qed.
Lemma lem5239633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239634 (s : real -> Prop) : (term276 s) = (term277 s).
Proof. exact (MK_COMB (@lem5239633) (@lem5239632 s)). Qed.
Lemma lem5239635 (b : real) (s : real -> Prop) : (term270 s b) = (term263 b s).
Proof. exact (eq_refl (term270 s b)). Qed.
Lemma lem5239636 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5239637 (s : real -> Prop) (x : real -> real) (b : real) : (term278 s x b) = (term279 s x b).
Proof. exact (MK_COMB (@lem5239635 b s) (@lem5239636 x b)). Qed.
Lemma lem5239638 (x : real -> real) (b : real) (s : real -> Prop) : (term279 s x b) = (term280 x b s).
Proof. exact (eq_refl (term279 s x b)). Qed.
Lemma lem5239639 (x : real -> real) (b : real) (s : real -> Prop) : (term278 s x b) = (term280 x b s).
Proof. exact (TRANS (@lem5239637 s x b) (@lem5239638 x b s)). Qed.
Lemma lem5239640 (x : real -> real) (s : real -> Prop) : (term281 s x) = (term282 x s).
Proof. exact (fun_ext (fun b : real => @lem5239639 x b s)). Qed.
Lemma lem5239641 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239642 (x : real -> real) (s : real -> Prop) : (term283 s x) = (term284 x s).
Proof. exact (MK_COMB (@lem5239641) (@lem5239640 x s)). Qed.
Lemma lem5239643 (s : real -> Prop) : (term285 s) = (term286 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239642 x s)). Qed.
Lemma lem5239644 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239645 (s : real -> Prop) : (term268 s) = (term287 s).
Proof. exact (MK_COMB (@lem5239644) (@lem5239643 s)). Qed.
Lemma lem5239646 (s : real -> Prop) : ((term267 s) = (term268 s)) = ((term266 s) = (term287 s)).
Proof. exact (MK_COMB (@lem5239634 s) (@lem5239645 s)). Qed.
Lemma lem5239647 (s : real -> Prop) : (term266 s) = (term287 s).
Proof. exact (EQ_MP (@lem5239646 s) (@lem5239621 s)). Qed.
Lemma lem5239648 (s : real -> Prop) : (term197 s) = (term287 s).
Proof. exact (TRANS (@lem5239617 s) (@lem5239647 s)). Qed.
Lemma lem5239649 (s : real -> Prop) : (term198 s) = (term198 s).
Proof. exact (eq_refl (term198 s)). Qed.
Lemma lem5239650 (s : real -> Prop) : (term199 s) = (term288 s).
Proof. exact (MK_COMB (@lem5239649 s) (@lem5239648 s)). Qed.
Lemma lem5239652 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5239653 (P : Prop) (Q : type1028) : (term289 P Q) = (term290 P Q).
Proof. exact (@lem5239652 (real -> real) P Q). Qed.
Lemma lem5239654 (s : real -> Prop) : (term291 s) = (term292 s).
Proof. exact (@lem5239653 (term191 s) (term286 s)). Qed.
Lemma lem5239655 (x : real -> real) (s : real -> Prop) : (term293 s x) = (term284 x s).
Proof. exact (eq_refl (term293 s x)). Qed.
Lemma lem5239656 (s : real -> Prop) : (term294 s) = (term286 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239655 x s)). Qed.
Lemma lem5239657 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239658 (s : real -> Prop) : (term295 s) = (term287 s).
Proof. exact (MK_COMB (@lem5239657) (@lem5239656 s)). Qed.
Lemma lem5239659 (s : real -> Prop) : (term198 s) = (term198 s).
Proof. exact (eq_refl (term198 s)). Qed.
Lemma lem5239660 (s : real -> Prop) : (term291 s) = (term288 s).
Proof. exact (MK_COMB (@lem5239659 s) (@lem5239658 s)). Qed.
Lemma lem5239661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239662 (s : real -> Prop) : (term296 s) = (term297 s).
Proof. exact (MK_COMB (@lem5239661) (@lem5239660 s)). Qed.
Lemma lem5239663 (x : real -> real) (s : real -> Prop) : (term293 s x) = (term284 x s).
Proof. exact (eq_refl (term293 s x)). Qed.
Lemma lem5239664 (s : real -> Prop) : (term198 s) = (term198 s).
Proof. exact (eq_refl (term198 s)). Qed.
Lemma lem5239665 (x : real -> real) (s : real -> Prop) : (term298 s x) = (term299 x s).
Proof. exact (MK_COMB (@lem5239664 s) (@lem5239663 x s)). Qed.
Lemma lem5239666 (s : real -> Prop) : (term300 s) = (term301 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239665 x s)). Qed.
Lemma lem5239667 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239668 (s : real -> Prop) : (term292 s) = (term302 s).
Proof. exact (MK_COMB (@lem5239667) (@lem5239666 s)). Qed.
Lemma lem5239669 (s : real -> Prop) : ((term291 s) = (term292 s)) = ((term288 s) = (term302 s)).
Proof. exact (MK_COMB (@lem5239662 s) (@lem5239668 s)). Qed.
Lemma lem5239670 (s : real -> Prop) : (term288 s) = (term302 s).
Proof. exact (EQ_MP (@lem5239669 s) (@lem5239654 s)). Qed.
Lemma lem5239671 (s : real -> Prop) : (term199 s) = (term302 s).
Proof. exact (TRANS (@lem5239650 s) (@lem5239670 s)). Qed.
Lemma lem5239672 (s : real -> Prop) : (term203 s) = (term303 s).
Proof. exact (MK_COMB (@lem5239590 s) (@lem5239671 s)). Qed.
Lemma lem5239674 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5239675 (P : type1028) (Q : type1028) : (term306 P Q) = (term307 P Q).
Proof. exact (@lem5239674 (real -> real) P Q). Qed.
Lemma lem5239676 (s : real -> Prop) : (term308 s) = (term309 s).
Proof. exact (@lem5239675 (term244 s) (term301 s)). Qed.
Lemma lem5239677 (s : real -> Prop) (x : real -> real) : (term310 s x) = (term242 s x).
Proof. exact (eq_refl (term310 s x)). Qed.
Lemma lem5239678 (s : real -> Prop) : (term311 s) = (term244 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239677 s x)). Qed.
Lemma lem5239679 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239680 (s : real -> Prop) : (term312 s) = (term245 s).
Proof. exact (MK_COMB (@lem5239679) (@lem5239678 s)). Qed.
Lemma lem5239681 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239682 (s : real -> Prop) : (term313 s) = (term246 s).
Proof. exact (MK_COMB (@lem5239681) (@lem5239680 s)). Qed.
Lemma lem5239683 (x : real -> real) (s : real -> Prop) : (term314 s x) = (term299 x s).
Proof. exact (eq_refl (term314 s x)). Qed.
Lemma lem5239684 (s : real -> Prop) : (term315 s) = (term301 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239683 x s)). Qed.
Lemma lem5239685 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239686 (s : real -> Prop) : (term316 s) = (term302 s).
Proof. exact (MK_COMB (@lem5239685) (@lem5239684 s)). Qed.
Lemma lem5239687 (s : real -> Prop) : (term308 s) = (term303 s).
Proof. exact (MK_COMB (@lem5239682 s) (@lem5239686 s)). Qed.
Lemma lem5239688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239689 (s : real -> Prop) : (term317 s) = (term318 s).
Proof. exact (MK_COMB (@lem5239688) (@lem5239687 s)). Qed.
Lemma lem5239690 (s : real -> Prop) (x : real -> real) : (term310 s x) = (term242 s x).
Proof. exact (eq_refl (term310 s x)). Qed.
Lemma lem5239691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239692 (s : real -> Prop) (x : real -> real) : (term319 s x) = (term320 s x).
Proof. exact (MK_COMB (@lem5239691) (@lem5239690 s x)). Qed.
Lemma lem5239693 (x : real -> real) (s : real -> Prop) : (term314 s x) = (term299 x s).
Proof. exact (eq_refl (term314 s x)). Qed.
Lemma lem5239694 (x : real -> real) (s : real -> Prop) : (term321 s x) = (term322 x s).
Proof. exact (MK_COMB (@lem5239692 s x) (@lem5239693 x s)). Qed.
Lemma lem5239695 (s : real -> Prop) : (term323 s) = (term324 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5239694 x s)). Qed.
Lemma lem5239696 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5239697 (s : real -> Prop) : (term309 s) = (term325 s).
Proof. exact (MK_COMB (@lem5239696) (@lem5239695 s)). Qed.
Lemma lem5239698 (s : real -> Prop) : ((term308 s) = (term309 s)) = ((term303 s) = (term325 s)).
Proof. exact (MK_COMB (@lem5239689 s) (@lem5239697 s)). Qed.
Lemma lem5239699 (s : real -> Prop) : (term303 s) = (term325 s).
Proof. exact (EQ_MP (@lem5239698 s) (@lem5239676 s)). Qed.
Lemma lem5239701 (s : real -> Prop) : (term203 s) = (term325 s).
Proof. exact (TRANS (@lem5239672 s) (@lem5239699 s)). Qed.
Lemma lem5239702 (s : real -> Prop) : (term95 s) = (term325 s).
Proof. exact (TRANS (@lem5239374 s) (@lem5239701 s)). Qed.
Lemma lem5239703 (s : real -> Prop) (h1 : term95 s) : term325 s.
Proof. exact (EQ_MP (@lem5239702 s) (@lem5239133 s h1)). Qed.
Lemma lem5239704 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5239705 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5239704 t x)). Qed.
Lemma lem5239706 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239707 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5239706) (@lem5239705 t)). Qed.
Lemma lem5239708 (t : real -> Prop) : (term166 t) = (term66 t).
Proof. exact (@lem16933 (term66 t)). Qed.
Lemma lem5239709 (t : real -> Prop) : (term166 t) = (term66 t).
Proof. exact (TRANS (@lem5239708 t) (@lem5239707 t)). Qed.
Lemma lem5239716 (t : real -> Prop) (s : real -> Prop) (x : real) : (term326 t s x) = (term327 t s x).
Proof. exact (@lem17362 (t x) (term77 s x)). Qed.
Lemma lem5239717 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5239718 (t : real -> Prop) (s : real -> Prop) : (term328 t s) = (term329 t s).
Proof. exact (@lem5239717 (term100 t s)). Qed.
Lemma lem5239719 (t : real -> Prop) (s : real -> Prop) (x : real) : (term330 t s x) = (term98 t s x).
Proof. exact (eq_refl (term330 t s x)). Qed.
Lemma lem5239720 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239721 (t : real -> Prop) (s : real -> Prop) (x : real) : (term331 t s x) = (term326 t s x).
Proof. exact (MK_COMB (@lem5239720) (@lem5239719 t s x)). Qed.
Lemma lem5239722 (t : real -> Prop) (s : real -> Prop) (x : real) : (term331 t s x) = (term327 t s x).
Proof. exact (TRANS (@lem5239721 t s x) (@lem5239716 t s x)). Qed.
Lemma lem5239723 (t : real -> Prop) (s : real -> Prop) : (term332 t s) = (term333 t s).
Proof. exact (fun_ext (fun x : real => @lem5239722 t s x)). Qed.
Lemma lem5239724 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239725 (t : real -> Prop) (s : real -> Prop) : (term329 t s) = (term334 t s).
Proof. exact (MK_COMB (@lem5239724) (@lem5239723 t s)). Qed.
Lemma lem5239726 (t : real -> Prop) (s : real -> Prop) : (term328 t s) = (term334 t s).
Proof. exact (TRANS (@lem5239718 t s) (@lem5239725 t s)). Qed.
Lemma lem5239727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239728 (t : real -> Prop) : (term184 t) = (term185 t).
Proof. exact (MK_COMB (@lem5239727) (@lem5239709 t)). Qed.
Lemma lem5239729 (t : real -> Prop) (s : real -> Prop) : (term335 t s) = (term336 t s).
Proof. exact (MK_COMB (@lem5239728 t) (@lem5239726 t s)). Qed.
Lemma lem5239730 (t : real -> Prop) (s : real -> Prop) : (term126 t s) = (term335 t s).
Proof. exact (@lem17045 (term67 t) (term101 t s)). Qed.
Lemma lem5239731 (t : real -> Prop) (s : real -> Prop) : (term126 t s) = (term336 t s).
Proof. exact (TRANS (@lem5239730 t s) (@lem5239729 t s)). Qed.
Lemma lem5239766 {A : Type'} (P : Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5239767 (P : Prop) (Q : real -> Prop) : (term337 P Q) = (term338 P Q).
Proof. exact (@lem5239766 real P Q). Qed.
Lemma lem5239768 (t : real -> Prop) (s : real -> Prop) : (term339 t s) = (term340 t s).
Proof. exact (@lem5239767 (term66 t) (term333 t s)). Qed.
Lemma lem5239769 (t : real -> Prop) (s : real -> Prop) (x : real) : (term341 t s x) = (term327 t s x).
Proof. exact (eq_refl (term341 t s x)). Qed.
Lemma lem5239770 (t : real -> Prop) (s : real -> Prop) : (term342 t s) = (term333 t s).
Proof. exact (fun_ext (fun x : real => @lem5239769 t s x)). Qed.
Lemma lem5239771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239772 (t : real -> Prop) (s : real -> Prop) : (term343 t s) = (term334 t s).
Proof. exact (MK_COMB (@lem5239771) (@lem5239770 t s)). Qed.
Lemma lem5239773 (t : real -> Prop) : (term185 t) = (term185 t).
Proof. exact (eq_refl (term185 t)). Qed.
Lemma lem5239774 (t : real -> Prop) (s : real -> Prop) : (term339 t s) = (term336 t s).
Proof. exact (MK_COMB (@lem5239773 t) (@lem5239772 t s)). Qed.
Lemma lem5239775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5239776 (t : real -> Prop) (s : real -> Prop) : (term344 t s) = (term345 t s).
Proof. exact (MK_COMB (@lem5239775) (@lem5239774 t s)). Qed.
Lemma lem5239777 (t : real -> Prop) (s : real -> Prop) (x : real) : (term341 t s x) = (term327 t s x).
Proof. exact (eq_refl (term341 t s x)). Qed.
Lemma lem5239778 (t : real -> Prop) : (term185 t) = (term185 t).
Proof. exact (eq_refl (term185 t)). Qed.
Lemma lem5239779 (t : real -> Prop) (s : real -> Prop) (x : real) : (term346 t s x) = (term347 t s x).
Proof. exact (MK_COMB (@lem5239778 t) (@lem5239777 t s x)). Qed.
Lemma lem5239780 (t : real -> Prop) (s : real -> Prop) : (term348 t s) = (term349 t s).
Proof. exact (fun_ext (fun x : real => @lem5239779 t s x)). Qed.
Lemma lem5239781 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5239782 (t : real -> Prop) (s : real -> Prop) : (term340 t s) = (term350 t s).
Proof. exact (MK_COMB (@lem5239781) (@lem5239780 t s)). Qed.
Lemma lem5239783 (t : real -> Prop) (s : real -> Prop) : ((term339 t s) = (term340 t s)) = ((term336 t s) = (term350 t s)).
Proof. exact (MK_COMB (@lem5239776 t s) (@lem5239782 t s)). Qed.
Lemma lem5239785 (t : real -> Prop) (s : real -> Prop) : (term336 t s) = (term350 t s).
Proof. exact (EQ_MP (@lem5239783 t s) (@lem5239768 t s)). Qed.
Lemma lem5239786 (t : real -> Prop) (s : real -> Prop) : (term126 t s) = (term350 t s).
Proof. exact (TRANS (@lem5239731 t s) (@lem5239785 t s)). Qed.
Lemma lem5239787 (t : real -> Prop) (s : real -> Prop) (h1 : term126 t s) : term350 t s.
Proof. exact (EQ_MP (@lem5239786 t s) (@lem5239138 t s h1)). Qed.
Lemma lem5239788 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term347 t s x) : term347 t s x.
Proof. exact (h1). Qed.
Lemma lem5239789 (x' : real -> real) (s : real -> Prop) (h1 : term322 x' s) : term322 x' s.
Proof. exact (h1). Qed.
Lemma lem5239790 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term162 b s t x''.
Proof. exact (h1). Qed.
Lemma lem5239805 (t : real -> Prop) (s : real -> Prop) (x : real) : (term327 t s x) = (term327 t s x).
Proof. exact (eq_refl (term327 t s x)). Qed.
Lemma lem5239810 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5239811 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5239810 t x)). Qed.
Lemma lem5239812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239813 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5239812) (@lem5239811 t)). Qed.
Lemma lem5239814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239815 (t : real -> Prop) : (term185 t) = (term185 t).
Proof. exact (MK_COMB (@lem5239814) (@lem5239813 t)). Qed.
Lemma lem5239816 (t : real -> Prop) (s : real -> Prop) (x : real) : (term347 t s x) = (term347 t s x).
Proof. exact (MK_COMB (@lem5239815 t) (@lem5239805 t s x)). Qed.
Lemma lem5239817 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term347 t s x) : term347 t s x.
Proof. exact (EQ_MP (@lem5239816 t s x) (@lem5239788 t s x h1)). Qed.
Lemma lem5239824 (b : real) (s : real -> Prop) : (term6 b s) = (term6 b s).
Proof. exact (eq_refl (term6 b s)). Qed.
Lemma lem5239833 (x' : real -> real) (b : real) : (term351 x' b) = (term351 x' b).
Proof. exact (eq_refl (term351 x' b)). Qed.
Lemma lem5239840 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5239841 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5239840 real Prop f x). Qed.
Lemma lem5239843 (s : real -> Prop) (x' : real -> real) (b : real) : (term352 s x' b) = (term353 s x' b).
Proof. exact (@lem5239841 s (x' b)). Qed.
Lemma lem5239844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239845 (s : real -> Prop) (x' : real -> real) (b : real) : (term354 s x' b) = (term355 s x' b).
Proof. exact (MK_COMB (@lem5239844) (@lem5239843 s x' b)). Qed.
Lemma lem5239846 (s : real -> Prop) (x' : real -> real) (b : real) : (term221 s x' b) = (term356 s x' b).
Proof. exact (MK_COMB (@lem5239845 s x' b) (@lem5239833 x' b)). Qed.
Lemma lem5239847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239848 (s : real -> Prop) (x' : real -> real) (b : real) : (term357 s x' b) = (term358 s x' b).
Proof. exact (MK_COMB (@lem5239847) (@lem5239846 s x' b)). Qed.
Lemma lem5239849 (x' : real -> real) (b : real) (s : real -> Prop) : (term280 x' b s) = (term359 x' b s).
Proof. exact (MK_COMB (@lem5239848 s x' b) (@lem5239824 b s)). Qed.
Lemma lem5239850 (x' : real -> real) (s : real -> Prop) : (term282 x' s) = (term360 x' s).
Proof. exact (fun_ext (fun b : real => @lem5239849 x' b s)). Qed.
Lemma lem5239851 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239852 (x' : real -> real) (s : real -> Prop) : (term284 x' s) = (term361 x' s).
Proof. exact (MK_COMB (@lem5239851) (@lem5239850 x' s)). Qed.
Lemma lem5239859 (s : real -> Prop) (x : real) : (term77 s x) = (term77 s x).
Proof. exact (eq_refl (term77 s x)). Qed.
Lemma lem5239860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239865 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5239866 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5239865 real Prop f x). Qed.
Lemma lem5239868 (s : real -> Prop) (x : real) : (s x) = (@I (real -> Prop) s x).
Proof. exact (@lem5239866 s x). Qed.
Lemma lem5239869 (s : real -> Prop) (x : real) : (term63 s x) = (term362 s x).
Proof. exact (MK_COMB (@lem5239860) (@lem5239868 s x)). Qed.
Lemma lem5239870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239871 (s : real -> Prop) (x : real) : (term363 s x) = (term364 s x).
Proof. exact (MK_COMB (@lem5239870) (@lem5239869 s x)). Qed.
Lemma lem5239872 (s : real -> Prop) (x : real) : (term189 s x) = (term365 s x).
Proof. exact (MK_COMB (@lem5239871 s x) (@lem5239859 s x)). Qed.
Lemma lem5239873 (s : real -> Prop) : (term190 s) = (term366 s).
Proof. exact (fun_ext (fun x : real => @lem5239872 s x)). Qed.
Lemma lem5239874 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239875 (s : real -> Prop) : (term191 s) = (term367 s).
Proof. exact (MK_COMB (@lem5239874) (@lem5239873 s)). Qed.
Lemma lem5239876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239877 (s : real -> Prop) : (term198 s) = (term368 s).
Proof. exact (MK_COMB (@lem5239876) (@lem5239875 s)). Qed.
Lemma lem5239878 (x' : real -> real) (s : real -> Prop) : (term299 x' s) = (term369 x' s).
Proof. exact (MK_COMB (@lem5239877 s) (@lem5239852 x' s)). Qed.
Lemma lem5239887 (x' : real -> real) (b : real) : (term351 x' b) = (term351 x' b).
Proof. exact (eq_refl (term351 x' b)). Qed.
Lemma lem5239894 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5239895 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5239894 real Prop f x). Qed.
Lemma lem5239897 (s : real -> Prop) (x' : real -> real) (b : real) : (term352 s x' b) = (term353 s x' b).
Proof. exact (@lem5239895 s (x' b)). Qed.
Lemma lem5239898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239899 (s : real -> Prop) (x' : real -> real) (b : real) : (term354 s x' b) = (term355 s x' b).
Proof. exact (MK_COMB (@lem5239898) (@lem5239897 s x' b)). Qed.
Lemma lem5239900 (s : real -> Prop) (x' : real -> real) (b : real) : (term221 s x' b) = (term356 s x' b).
Proof. exact (MK_COMB (@lem5239899 s x' b) (@lem5239887 x' b)). Qed.
Lemma lem5239901 (s : real -> Prop) (x' : real -> real) : (term223 s x') = (term370 s x').
Proof. exact (fun_ext (fun b : real => @lem5239900 s x' b)). Qed.
Lemma lem5239902 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239903 (s : real -> Prop) (x' : real -> real) : (term225 s x') = (term371 s x').
Proof. exact (MK_COMB (@lem5239902) (@lem5239901 s x')). Qed.
Lemma lem5239904 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5239910 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5239909 real Prop f x). Qed.
Lemma lem5239912 (s : real -> Prop) (x : real) : (s x) = (@I (real -> Prop) s x).
Proof. exact (@lem5239910 s x). Qed.
Lemma lem5239913 (s : real -> Prop) (x : real) : (term63 s x) = (term362 s x).
Proof. exact (MK_COMB (@lem5239904) (@lem5239912 s x)). Qed.
Lemma lem5239914 (s : real -> Prop) : (term65 s) = (term372 s).
Proof. exact (fun_ext (fun x : real => @lem5239913 s x)). Qed.
Lemma lem5239915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239916 (s : real -> Prop) : (term66 s) = (term373 s).
Proof. exact (MK_COMB (@lem5239915) (@lem5239914 s)). Qed.
Lemma lem5239917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239918 (s : real -> Prop) : (term185 s) = (term374 s).
Proof. exact (MK_COMB (@lem5239917) (@lem5239916 s)). Qed.
Lemma lem5239919 (s : real -> Prop) (x' : real -> real) : (term242 s x') = (term375 s x').
Proof. exact (MK_COMB (@lem5239918 s) (@lem5239903 s x')). Qed.
Lemma lem5239920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239921 (s : real -> Prop) (x' : real -> real) : (term320 s x') = (term376 s x').
Proof. exact (MK_COMB (@lem5239920) (@lem5239919 s x')). Qed.
Lemma lem5239922 (x' : real -> real) (s : real -> Prop) : (term322 x' s) = (term377 x' s).
Proof. exact (MK_COMB (@lem5239921 s x') (@lem5239878 x' s)). Qed.
Lemma lem5239923 (x' : real -> real) (s : real -> Prop) (h1 : term322 x' s) : term377 x' s.
Proof. exact (EQ_MP (@lem5239922 x' s) (@lem5239789 x' s h1)). Qed.
Lemma lem5239926 (t : real -> Prop) (x'' : real) : (t x'') = (t x'').
Proof. exact (eq_refl (t x'')). Qed.
Lemma lem5239931 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5239932 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5239931 real Prop f x). Qed.
Lemma lem5239934 (s : real -> Prop) (x : real) : (s x) = (@I (real -> Prop) s x).
Proof. exact (@lem5239932 s x). Qed.
Lemma lem5239941 (t : real -> Prop) (x : real) : (term363 t x) = (term363 t x).
Proof. exact (eq_refl (term363 t x)). Qed.
Lemma lem5239942 (t : real -> Prop) (s : real -> Prop) (x : real) : (term130 t s x) = (term378 t s x).
Proof. exact (MK_COMB (@lem5239941 t x) (@lem5239934 s x)). Qed.
Lemma lem5239943 (t : real -> Prop) (s : real -> Prop) : (term131 t s) = (term379 t s).
Proof. exact (fun_ext (fun x : real => @lem5239942 t s x)). Qed.
Lemma lem5239944 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239945 (t : real -> Prop) (s : real -> Prop) : (term132 t s) = (term380 t s).
Proof. exact (MK_COMB (@lem5239944) (@lem5239943 t s)). Qed.
Lemma lem5239946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239947 (t : real -> Prop) (s : real -> Prop) : (term142 t s) = (term381 t s).
Proof. exact (MK_COMB (@lem5239946) (@lem5239945 t s)). Qed.
Lemma lem5239948 (s : real -> Prop) (t : real -> Prop) (x'' : real) : (term156 s t x'') = (term382 s t x'').
Proof. exact (MK_COMB (@lem5239947 t s) (@lem5239926 t x'')). Qed.
Lemma lem5239953 (b : real) (x : real) : (real_le b x) = (real_le b x).
Proof. exact (eq_refl (real_le b x)). Qed.
Lemma lem5239954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5239959 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5239960 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5239959 real Prop f x). Qed.
Lemma lem5239962 (s : real -> Prop) (x : real) : (s x) = (@I (real -> Prop) s x).
Proof. exact (@lem5239960 s x). Qed.
Lemma lem5239963 (s : real -> Prop) (x : real) : (term63 s x) = (term362 s x).
Proof. exact (MK_COMB (@lem5239954) (@lem5239962 s x)). Qed.
Lemma lem5239964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5239965 (s : real -> Prop) (x : real) : (term363 s x) = (term364 s x).
Proof. exact (MK_COMB (@lem5239964) (@lem5239963 s x)). Qed.
Lemma lem5239966 (s : real -> Prop) (b : real) (x : real) : (term127 s b x) = (term383 s b x).
Proof. exact (MK_COMB (@lem5239965 s x) (@lem5239953 b x)). Qed.
Lemma lem5239967 (s : real -> Prop) (b : real) : (term128 s b) = (term384 s b).
Proof. exact (fun_ext (fun x : real => @lem5239966 s b x)). Qed.
Lemma lem5239968 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5239969 (s : real -> Prop) (b : real) : (term129 s b) = (term385 s b).
Proof. exact (MK_COMB (@lem5239968) (@lem5239967 s b)). Qed.
Lemma lem5239970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5239971 (s : real -> Prop) (b : real) : (term144 s b) = (term386 s b).
Proof. exact (MK_COMB (@lem5239970) (@lem5239969 s b)). Qed.
Lemma lem5239972 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) : (term162 b s t x'') = (term387 b s t x'').
Proof. exact (MK_COMB (@lem5239971 s b) (@lem5239948 s t x'')). Qed.
Lemma lem5239973 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term387 b s t x''.
Proof. exact (EQ_MP (@lem5239972 b s t x'') (@lem5239790 b s t x'' h1)). Qed.
Lemma lem5239974 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term382 s t x''.
Proof. exact (proj2 (@lem5239973 b s t x'' h1)). Qed.
Lemma lem5239975 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term385 s b.
Proof. exact (proj1 (@lem5239973 b s t x'' h1)). Qed.
Lemma lem5239977 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term380 t s.
Proof. exact (proj1 (@lem5239974 b s t x'' h1)). Qed.
Lemma lem5239978 (s : real -> Prop) (x' : real -> real) (h1 : term375 s x') : term375 s x'.
Proof. exact (h1). Qed.
Lemma lem5239979 (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term369 x' s.
Proof. exact (h1). Qed.
Lemma lem5239980 (s : real -> Prop) (h1 : term373 s) : term373 s.
Proof. exact (h1). Qed.
Lemma lem5239981 (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term371 s x'.
Proof. exact (h1). Qed.
Lemma lem5239982 (t : real -> Prop) (h1 : term66 t) : term66 t.
Proof. exact (h1). Qed.
Lemma lem5239983 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : term327 t s x.
Proof. exact (h1). Qed.
Lemma lem5239986 (t : real -> Prop) (h1 : term66 t) : term66 t.
Proof. exact (h1). Qed.
Lemma lem5239991 (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term367 s.
Proof. exact (proj1 (@lem5239979 x' s h1)). Qed.
Lemma lem5239992 (t : real -> Prop) (h1 : term66 t) : term66 t.
Proof. exact (h1). Qed.
Lemma lem5239993 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : term327 t s x.
Proof. exact (h1). Qed.
Lemma lem5240034 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5240035 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5240034 t x)). Qed.
Lemma lem5240036 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240038 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5240036) (@lem5240035 t)). Qed.
Lemma lem5240039 (t : real -> Prop) (h1 : term66 t) : term66 t.
Proof. exact (EQ_MP (@lem5240038 t) (@lem5239982 t h1)). Qed.
Lemma lem5240060 (t : real -> Prop) (s : real -> Prop) (x : real) : (term378 t s x) = (term378 t s x).
Proof. exact (eq_refl (term378 t s x)). Qed.
Lemma lem5240061 (t : real -> Prop) (s : real -> Prop) : (term379 t s) = (term379 t s).
Proof. exact (fun_ext (fun x : real => @lem5240060 t s x)). Qed.
Lemma lem5240062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240064 (t : real -> Prop) (s : real -> Prop) : (term380 t s) = (term380 t s).
Proof. exact (MK_COMB (@lem5240062) (@lem5240061 t s)). Qed.
Lemma lem5240065 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term380 t s.
Proof. exact (EQ_MP (@lem5240064 t s) (@lem5239977 b s t x'' h1)). Qed.
Lemma lem5240071 (s : real -> Prop) (x : real) : (term362 s x) = (term362 s x).
Proof. exact (eq_refl (term362 s x)). Qed.
Lemma lem5240072 (s : real -> Prop) : (term372 s) = (term372 s).
Proof. exact (fun_ext (fun x : real => @lem5240071 s x)). Qed.
Lemma lem5240073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240075 (s : real -> Prop) : (term373 s) = (term373 s).
Proof. exact (MK_COMB (@lem5240073) (@lem5240072 s)). Qed.
Lemma lem5240076 (s : real -> Prop) (h1 : term373 s) : term373 s.
Proof. exact (EQ_MP (@lem5240075 s) (@lem5239980 s h1)). Qed.
Lemma lem5240127 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5240128 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5240127 t x)). Qed.
Lemma lem5240129 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240131 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5240129) (@lem5240128 t)). Qed.
Lemma lem5240132 (t : real -> Prop) (h1 : term66 t) : term66 t.
Proof. exact (EQ_MP (@lem5240131 t) (@lem5239986 t h1)). Qed.
Lemma lem5240140 (s : real -> Prop) (b : real) (x : real) : (term383 s b x) = (term383 s b x).
Proof. exact (eq_refl (term383 s b x)). Qed.
Lemma lem5240141 (s : real -> Prop) (b : real) : (term384 s b) = (term384 s b).
Proof. exact (fun_ext (fun x : real => @lem5240140 s b x)). Qed.
Lemma lem5240142 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240144 (s : real -> Prop) (b : real) : (term385 s b) = (term385 s b).
Proof. exact (MK_COMB (@lem5240142) (@lem5240141 s b)). Qed.
Lemma lem5240145 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term385 s b.
Proof. exact (EQ_MP (@lem5240144 s b) (@lem5239975 b s t x'' h1)). Qed.
Lemma lem5240168 (s : real -> Prop) (x' : real -> real) (b : real) : (term356 s x' b) = (term356 s x' b).
Proof. exact (eq_refl (term356 s x' b)). Qed.
Lemma lem5240169 (s : real -> Prop) (x' : real -> real) : (term370 s x') = (term370 s x').
Proof. exact (fun_ext (fun b : real => @lem5240168 s x' b)). Qed.
Lemma lem5240170 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240172 (s : real -> Prop) (x' : real -> real) : (term371 s x') = (term371 s x').
Proof. exact (MK_COMB (@lem5240170) (@lem5240169 s x')). Qed.
Lemma lem5240173 (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term371 s x'.
Proof. exact (EQ_MP (@lem5240172 s x') (@lem5239981 s x' h1)). Qed.
Lemma lem5240249 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5240250 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5240249 t x)). Qed.
Lemma lem5240251 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240253 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5240251) (@lem5240250 t)). Qed.
Lemma lem5240254 (t : real -> Prop) (h1 : term66 t) : term66 t.
Proof. exact (EQ_MP (@lem5240253 t) (@lem5239992 t h1)). Qed.
Lemma lem5240275 (t : real -> Prop) (s : real -> Prop) (x : real) : (term378 t s x) = (term378 t s x).
Proof. exact (eq_refl (term378 t s x)). Qed.
Lemma lem5240276 (t : real -> Prop) (s : real -> Prop) : (term379 t s) = (term379 t s).
Proof. exact (fun_ext (fun x : real => @lem5240275 t s x)). Qed.
Lemma lem5240277 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240279 (t : real -> Prop) (s : real -> Prop) : (term380 t s) = (term380 t s).
Proof. exact (MK_COMB (@lem5240277) (@lem5240276 t s)). Qed.
Lemma lem5240280 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term380 t s.
Proof. exact (EQ_MP (@lem5240279 t s) (@lem5239977 b s t x'' h1)). Qed.
Lemma lem5240292 (s : real -> Prop) (x : real) : (term365 s x) = (term365 s x).
Proof. exact (eq_refl (term365 s x)). Qed.
Lemma lem5240293 (s : real -> Prop) : (term366 s) = (term366 s).
Proof. exact (fun_ext (fun x : real => @lem5240292 s x)). Qed.
Lemma lem5240294 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5240296 (s : real -> Prop) : (term367 s) = (term367 s).
Proof. exact (MK_COMB (@lem5240294) (@lem5240293 s)). Qed.
Lemma lem5240297 (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term367 s.
Proof. exact (EQ_MP (@lem5240296 s) (@lem5239991 x' s h1)). Qed.
Lemma lem5240338 (_68664 : real) (t : real -> Prop) (h1 : term66 t) : term137 t _68664.
Proof. exact (@lem5240039 t h1 _68664). Qed.
Lemma lem5240339 (t : real -> Prop) (_68664 : real) : (term137 t _68664) = (term63 t _68664).
Proof. exact (eq_refl (term137 t _68664)). Qed.
Lemma lem5240344 (_68666 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term388 t s _68666.
Proof. exact (@lem5240065 b s t x'' h1 _68666). Qed.
Lemma lem5240345 (t : real -> Prop) (s : real -> Prop) (_68666 : real) : (term388 t s _68666) = (term378 t s _68666).
Proof. exact (eq_refl (term388 t s _68666)). Qed.
Lemma lem5240347 (_68667 : real) (s : real -> Prop) (h1 : term373 s) : term389 s _68667.
Proof. exact (@lem5240076 s h1 _68667). Qed.
Lemma lem5240348 (s : real -> Prop) (_68667 : real) : (term389 s _68667) = (term362 s _68667).
Proof. exact (eq_refl (term389 s _68667)). Qed.
Lemma lem5240359 (_68671 : real) (t : real -> Prop) (h1 : term66 t) : term137 t _68671.
Proof. exact (@lem5240132 t h1 _68671). Qed.
Lemma lem5240360 (t : real -> Prop) (_68671 : real) : (term137 t _68671) = (term63 t _68671).
Proof. exact (eq_refl (term137 t _68671)). Qed.
Lemma lem5240362 (_68672 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term390 s b _68672.
Proof. exact (@lem5240145 b s t x'' h1 _68672). Qed.
Lemma lem5240363 (s : real -> Prop) (b : real) (_68672 : real) : (term390 s b _68672) = (term383 s b _68672).
Proof. exact (eq_refl (term390 s b _68672)). Qed.
Lemma lem5240368 (_68674 : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term391 s x' _68674.
Proof. exact (@lem5240173 s x' h1 _68674). Qed.
Lemma lem5240369 (s : real -> Prop) (x' : real -> real) (_68674 : real) : (term391 s x' _68674) = (term356 s x' _68674).
Proof. exact (eq_refl (term391 s x' _68674)). Qed.
Lemma lem5240370 (_68674 : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term356 s x' _68674.
Proof. exact (EQ_MP (@lem5240369 s x' _68674) (@lem5240368 _68674 s x' h1)). Qed.
Lemma lem5240383 (_68679 : real) (t : real -> Prop) (h1 : term66 t) : term137 t _68679.
Proof. exact (@lem5240254 t h1 _68679). Qed.
Lemma lem5240384 (t : real -> Prop) (_68679 : real) : (term137 t _68679) = (term63 t _68679).
Proof. exact (eq_refl (term137 t _68679)). Qed.
Lemma lem5240389 (_68681 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term388 t s _68681.
Proof. exact (@lem5240280 b s t x'' h1 _68681). Qed.
Lemma lem5240390 (t : real -> Prop) (s : real -> Prop) (_68681 : real) : (term388 t s _68681) = (term378 t s _68681).
Proof. exact (eq_refl (term388 t s _68681)). Qed.
Lemma lem5240392 (_68682 : real) (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term392 s _68682.
Proof. exact (@lem5240297 x' s h1 _68682). Qed.
Lemma lem5240393 (s : real -> Prop) (_68682 : real) : (term392 s _68682) = (term365 s _68682).
Proof. exact (eq_refl (term392 s _68682)). Qed.
Lemma lem5240423 (_68664 : real) (t : real -> Prop) (h1 : term66 t) : term63 t _68664.
Proof. exact (EQ_MP (@lem5240339 t _68664) (@lem5240338 _68664 t h1)). Qed.
Lemma lem5240435 (_68666 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term378 t s _68666.
Proof. exact (EQ_MP (@lem5240345 t s _68666) (@lem5240344 _68666 b s t x'' h1)). Qed.
Lemma lem5240439 (_68667 : real) (s : real -> Prop) (h1 : term373 s) : term362 s _68667.
Proof. exact (EQ_MP (@lem5240348 s _68667) (@lem5240347 _68667 s h1)). Qed.
Lemma lem5240459 (_68671 : real) (t : real -> Prop) (h1 : term66 t) : term63 t _68671.
Proof. exact (EQ_MP (@lem5240360 t _68671) (@lem5240359 _68671 t h1)). Qed.
Lemma lem5240469 (_68672 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term383 s b _68672.
Proof. exact (EQ_MP (@lem5240363 s b _68672) (@lem5240362 _68672 b s t x'' h1)). Qed.
Lemma lem5240485 (_68674 : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term351 x' _68674.
Proof. exact (proj2 (@lem5240370 _68674 s x' h1)). Qed.
Lemma lem5240507 (_68679 : real) (t : real -> Prop) (h1 : term66 t) : term63 t _68679.
Proof. exact (EQ_MP (@lem5240384 t _68679) (@lem5240383 _68679 t h1)). Qed.
Lemma lem5240531 (_68681 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term378 t s _68681.
Proof. exact (EQ_MP (@lem5240390 t s _68681) (@lem5240389 _68681 b s t x'' h1)). Qed.
Lemma lem5240539 (_68682 : real) (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term365 s _68682.
Proof. exact (EQ_MP (@lem5240393 s _68682) (@lem5240392 _68682 x' s h1)). Qed.
Lemma lem5240543 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : term393 s x.
Proof. exact (proj2 (@lem5239993 t s x h1)). Qed.
Lemma lem5240557 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : t x''.
Proof. exact (proj2 (@lem5239974 b s t x'' h1)). Qed.
Lemma lem5240558 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term394 t x''.
Proof. exact (fun h0 : term63 t x'' => @lem5240557 b s t x'' h1). Qed.
Lemma lem5240560 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240561 (t : real -> Prop) (x'' : real) : (term394 t x'') = (t x'').
Proof. exact (@lem5240560 (t x'')). Qed.
Lemma lem5240562 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : t x''.
Proof. exact (EQ_MP (@lem5240561 t x'') (@lem5240558 b s t x'' h1)). Qed.
Lemma lem5240565 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5240567 (t : real -> Prop) (_68664 : real) : (term63 t _68664) = (term396 t _68664).
Proof. exact (@lem5240565 (t _68664)). Qed.
Lemma lem5240570 (_68664 : real) (t : real -> Prop) (h1 : term66 t) : term396 t _68664.
Proof. exact (EQ_MP (@lem5240567 t _68664) (@lem5240423 _68664 t h1)). Qed.
Lemma lem5240571 (x'' : real) (t : real -> Prop) (h1 : term66 t) : term396 t x''.
Proof. exact (@lem5240570 x'' t h1). Qed.
Lemma lem5240574 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (@lem5240571 x'' t h1 (@lem5240562 b s t x'' h2)). Qed.
Lemma lem5240575 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5240574 b s t x'' h1 h2). Qed.
Lemma lem5240577 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240578 : term397 = False.
Proof. exact (@lem5240577 False). Qed.
Lemma lem5240579 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240578) (@lem5240575 b s t x'' h1 h2)). Qed.
Lemma lem5240581 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : t x.
Proof. exact (proj1 (@lem5239983 t s x h1)). Qed.
Lemma lem5240582 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : term394 t x.
Proof. exact (fun h0 : term63 t x => @lem5240581 t s x h1). Qed.
Lemma lem5240584 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240585 (t : real -> Prop) (x : real) : (term394 t x) = (t x).
Proof. exact (@lem5240584 (t x)). Qed.
Lemma lem5240586 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : t x.
Proof. exact (EQ_MP (@lem5240585 t x) (@lem5240582 t s x h1)). Qed.
Lemma lem5240592 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5240593 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : (term378 t s _68666) = (term398 s t _68666).
Proof. exact (@lem5240592 (@I (real -> Prop) s _68666) (term63 t _68666)). Qed.
Lemma lem5240599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5240600 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : (term399 t s _68666) = (term400 s t _68666).
Proof. exact (MK_COMB (@lem5240599) (@lem5240593 s t _68666)). Qed.
Lemma lem5240606 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : (term398 s t _68666) = (term398 s t _68666).
Proof. exact (eq_refl (term398 s t _68666)). Qed.
Lemma lem5240607 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : ((term378 t s _68666) = (term398 s t _68666)) = ((term398 s t _68666) = (term398 s t _68666)).
Proof. exact (MK_COMB (@lem5240600 s t _68666) (@lem5240606 s t _68666)). Qed.
Lemma lem5240609 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5240610 (x : Prop) : (x = x) = True.
Proof. exact (@lem5240609 Prop x). Qed.
Lemma lem5240611 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : ((term398 s t _68666) = (term398 s t _68666)) = True.
Proof. exact (@lem5240610 (term398 s t _68666)). Qed.
Lemma lem5240612 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : ((term378 t s _68666) = (term398 s t _68666)) = True.
Proof. exact (TRANS (@lem5240607 s t _68666) (@lem5240611 s t _68666)). Qed.
Lemma lem5240613 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : True = ((term378 t s _68666) = (term398 s t _68666)).
Proof. exact (SYM (@lem5240612 s t _68666)). Qed.
Lemma lem5240614 (s : real -> Prop) (t : real -> Prop) (_68666 : real) : (term378 t s _68666) = (term398 s t _68666).
Proof. exact (EQ_MP (@lem5240613 s t _68666) (@lem0)). Qed.
Lemma lem5240615 (_68666 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term398 s t _68666.
Proof. exact (EQ_MP (@lem5240614 s t _68666) (@lem5240435 _68666 b s t x'' h1)). Qed.
Lemma lem5240617 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5240618 (t : real -> Prop) (s : real -> Prop) (_68666 : real) : (term398 s t _68666) = (term402 t s _68666).
Proof. exact (@lem5240617 (term63 t _68666) (@I (real -> Prop) s _68666)). Qed.
Lemma lem5240620 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5240621 (t : real -> Prop) (_68666 : real) : (term133 t _68666) = (t _68666).
Proof. exact (@lem5240620 (t _68666)). Qed.
Lemma lem5240622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5240623 (t : real -> Prop) (_68666 : real) : (term403 t _68666) = (term48 t _68666).
Proof. exact (MK_COMB (@lem5240622) (@lem5240621 t _68666)). Qed.
Lemma lem5240624 (s : real -> Prop) (_68666 : real) : (@I (real -> Prop) s _68666) = (@I (real -> Prop) s _68666).
Proof. exact (eq_refl (@I (real -> Prop) s _68666)). Qed.
Lemma lem5240625 (t : real -> Prop) (s : real -> Prop) (_68666 : real) : (term402 t s _68666) = (term404 t s _68666).
Proof. exact (MK_COMB (@lem5240623 t _68666) (@lem5240624 s _68666)). Qed.
Lemma lem5240626 (t : real -> Prop) (s : real -> Prop) (_68666 : real) : (term398 s t _68666) = (term404 t s _68666).
Proof. exact (TRANS (@lem5240618 t s _68666) (@lem5240625 t s _68666)). Qed.
Lemma lem5240629 (_68666 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term404 t s _68666.
Proof. exact (EQ_MP (@lem5240626 t s _68666) (@lem5240615 _68666 b s t x'' h1)). Qed.
Lemma lem5240630 (x : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term404 t s x.
Proof. exact (@lem5240629 x b s t x'' h1). Qed.
Lemma lem5240633 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term327 t s x) : @I (real -> Prop) s x.
Proof. exact (@lem5240630 x b s t x'' h1 (@lem5240586 t s x h2)). Qed.
Lemma lem5240634 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term327 t s x) : term405 s x.
Proof. exact (fun h0 : term362 s x => @lem5240633 b x'' t s x h1 h2). Qed.
Lemma lem5240636 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240637 (s : real -> Prop) (x : real) : (term405 s x) = (@I (real -> Prop) s x).
Proof. exact (@lem5240636 (@I (real -> Prop) s x)). Qed.
Lemma lem5240638 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term327 t s x) : @I (real -> Prop) s x.
Proof. exact (EQ_MP (@lem5240637 s x) (@lem5240634 b x'' t s x h1 h2)). Qed.
Lemma lem5240641 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5240643 (s : real -> Prop) (_68667 : real) : (term362 s _68667) = (term406 s _68667).
Proof. exact (@lem5240641 (@I (real -> Prop) s _68667)). Qed.
Lemma lem5240646 (_68667 : real) (s : real -> Prop) (h1 : term373 s) : term406 s _68667.
Proof. exact (EQ_MP (@lem5240643 s _68667) (@lem5240439 _68667 s h1)). Qed.
Lemma lem5240647 (x : real) (s : real -> Prop) (h1 : term373 s) : term406 s x.
Proof. exact (@lem5240646 x s h1). Qed.
Lemma lem5240650 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term373 s) (h2 : term162 b s t x'') (h3 : term327 t s x) : False.
Proof. exact (@lem5240647 x s h1 (@lem5240638 b x'' t s x h2 h3)). Qed.
Lemma lem5240651 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term373 s) (h2 : term162 b s t x'') (h3 : term327 t s x) : term397.
Proof. exact (fun h0 : ~ False => @lem5240650 b x'' t s x h1 h2 h3). Qed.
Lemma lem5240653 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240654 : term397 = False.
Proof. exact (@lem5240653 False). Qed.
Lemma lem5240655 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term373 s) (h2 : term162 b s t x'') (h3 : term327 t s x) : False.
Proof. exact (EQ_MP (@lem5240654) (@lem5240651 b x'' t s x h1 h2 h3)). Qed.
Lemma lem5240657 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : t x''.
Proof. exact (proj2 (@lem5239974 b s t x'' h1)). Qed.
Lemma lem5240658 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term394 t x''.
Proof. exact (fun h0 : term63 t x'' => @lem5240657 b s t x'' h1). Qed.
Lemma lem5240660 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240661 (t : real -> Prop) (x'' : real) : (term394 t x'') = (t x'').
Proof. exact (@lem5240660 (t x'')). Qed.
Lemma lem5240662 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : t x''.
Proof. exact (EQ_MP (@lem5240661 t x'') (@lem5240658 b s t x'' h1)). Qed.
Lemma lem5240665 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5240667 (t : real -> Prop) (_68671 : real) : (term63 t _68671) = (term396 t _68671).
Proof. exact (@lem5240665 (t _68671)). Qed.
Lemma lem5240670 (_68671 : real) (t : real -> Prop) (h1 : term66 t) : term396 t _68671.
Proof. exact (EQ_MP (@lem5240667 t _68671) (@lem5240459 _68671 t h1)). Qed.
Lemma lem5240671 (x'' : real) (t : real -> Prop) (h1 : term66 t) : term396 t x''.
Proof. exact (@lem5240670 x'' t h1). Qed.
Lemma lem5240674 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (@lem5240671 x'' t h1 (@lem5240662 b s t x'' h2)). Qed.
Lemma lem5240675 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5240674 b s t x'' h1 h2). Qed.
Lemma lem5240677 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240678 : term397 = False.
Proof. exact (@lem5240677 False). Qed.
Lemma lem5240679 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240678) (@lem5240675 b s t x'' h1 h2)). Qed.
Lemma lem5240681 (_68674 : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term353 s x' _68674.
Proof. exact (proj1 (@lem5240370 _68674 s x' h1)). Qed.
Lemma lem5240682 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term353 s x' b.
Proof. exact (@lem5240681 b s x' h1). Qed.
Lemma lem5240683 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term407 s x' b.
Proof. exact (fun h0 : term408 s x' b => @lem5240682 b s x' h1). Qed.
Lemma lem5240685 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240686 (s : real -> Prop) (x' : real -> real) (b : real) : (term407 s x' b) = (term353 s x' b).
Proof. exact (@lem5240685 (term353 s x' b)). Qed.
Lemma lem5240687 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term353 s x' b.
Proof. exact (EQ_MP (@lem5240686 s x' b) (@lem5240683 b s x' h1)). Qed.
Lemma lem5240693 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5240694 (b : real) (s : real -> Prop) (_68672 : real) : (term383 s b _68672) = (term409 b s _68672).
Proof. exact (@lem5240693 (real_le b _68672) (term362 s _68672)). Qed.
Lemma lem5240700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5240701 (b : real) (s : real -> Prop) (_68672 : real) : (term410 s b _68672) = (term411 b s _68672).
Proof. exact (MK_COMB (@lem5240700) (@lem5240694 b s _68672)). Qed.
Lemma lem5240707 (b : real) (s : real -> Prop) (_68672 : real) : (term409 b s _68672) = (term409 b s _68672).
Proof. exact (eq_refl (term409 b s _68672)). Qed.
Lemma lem5240708 (b : real) (s : real -> Prop) (_68672 : real) : ((term383 s b _68672) = (term409 b s _68672)) = ((term409 b s _68672) = (term409 b s _68672)).
Proof. exact (MK_COMB (@lem5240701 b s _68672) (@lem5240707 b s _68672)). Qed.
Lemma lem5240710 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5240711 (x : Prop) : (x = x) = True.
Proof. exact (@lem5240710 Prop x). Qed.
Lemma lem5240712 (b : real) (s : real -> Prop) (_68672 : real) : ((term409 b s _68672) = (term409 b s _68672)) = True.
Proof. exact (@lem5240711 (term409 b s _68672)). Qed.
Lemma lem5240713 (b : real) (s : real -> Prop) (_68672 : real) : ((term383 s b _68672) = (term409 b s _68672)) = True.
Proof. exact (TRANS (@lem5240708 b s _68672) (@lem5240712 b s _68672)). Qed.
Lemma lem5240714 (b : real) (s : real -> Prop) (_68672 : real) : True = ((term383 s b _68672) = (term409 b s _68672)).
Proof. exact (SYM (@lem5240713 b s _68672)). Qed.
Lemma lem5240715 (b : real) (s : real -> Prop) (_68672 : real) : (term383 s b _68672) = (term409 b s _68672).
Proof. exact (EQ_MP (@lem5240714 b s _68672) (@lem0)). Qed.
Lemma lem5240716 (_68672 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term409 b s _68672.
Proof. exact (EQ_MP (@lem5240715 b s _68672) (@lem5240469 _68672 b s t x'' h1)). Qed.
Lemma lem5240718 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5240719 (s : real -> Prop) (b : real) (_68672 : real) : (term409 b s _68672) = (term412 s b _68672).
Proof. exact (@lem5240718 (term362 s _68672) (real_le b _68672)). Qed.
Lemma lem5240721 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5240722 (s : real -> Prop) (_68672 : real) : (term413 s _68672) = (@I (real -> Prop) s _68672).
Proof. exact (@lem5240721 (@I (real -> Prop) s _68672)). Qed.
Lemma lem5240723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5240724 (s : real -> Prop) (_68672 : real) : (term414 s _68672) = (term415 s _68672).
Proof. exact (MK_COMB (@lem5240723) (@lem5240722 s _68672)). Qed.
Lemma lem5240725 (b : real) (_68672 : real) : (real_le b _68672) = (real_le b _68672).
Proof. exact (eq_refl (real_le b _68672)). Qed.
Lemma lem5240726 (s : real -> Prop) (b : real) (_68672 : real) : (term412 s b _68672) = (term416 s b _68672).
Proof. exact (MK_COMB (@lem5240724 s _68672) (@lem5240725 b _68672)). Qed.
Lemma lem5240727 (s : real -> Prop) (b : real) (_68672 : real) : (term409 b s _68672) = (term416 s b _68672).
Proof. exact (TRANS (@lem5240719 s b _68672) (@lem5240726 s b _68672)). Qed.
Lemma lem5240730 (_68672 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term416 s b _68672.
Proof. exact (EQ_MP (@lem5240727 s b _68672) (@lem5240716 _68672 b s t x'' h1)). Qed.
Lemma lem5240731 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term417 s x' b.
Proof. exact (@lem5240730 (x' b) b s t x'' h1). Qed.
Lemma lem5240734 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : term418 x' b.
Proof. exact (@lem5240731 x' b s t x'' h2 (@lem5240687 b s x' h1)). Qed.
Lemma lem5240735 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : term419 x' b.
Proof. exact (fun h0 : term351 x' b => @lem5240734 x' b s t x'' h1 h2). Qed.
Lemma lem5240737 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240738 (x' : real -> real) (b : real) : (term419 x' b) = (term418 x' b).
Proof. exact (@lem5240737 (term418 x' b)). Qed.
Lemma lem5240739 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : term418 x' b.
Proof. exact (EQ_MP (@lem5240738 x' b) (@lem5240735 x' b s t x'' h1 h2)). Qed.
Lemma lem5240742 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5240744 (x' : real -> real) (_68674 : real) : (term351 x' _68674) = (term420 x' _68674).
Proof. exact (@lem5240742 (term418 x' _68674)). Qed.
Lemma lem5240747 (_68674 : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term420 x' _68674.
Proof. exact (EQ_MP (@lem5240744 x' _68674) (@lem5240485 _68674 s x' h1)). Qed.
Lemma lem5240748 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term371 s x') : term420 x' b.
Proof. exact (@lem5240747 b s x' h1). Qed.
Lemma lem5240751 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : False.
Proof. exact (@lem5240748 b s x' h1 (@lem5240739 x' b s t x'' h1 h2)). Qed.
Lemma lem5240752 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5240751 x' b s t x'' h1 h2). Qed.
Lemma lem5240754 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240755 : term397 = False.
Proof. exact (@lem5240754 False). Qed.
Lemma lem5240756 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240755) (@lem5240752 x' b s t x'' h1 h2)). Qed.
Lemma lem5240758 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : t x''.
Proof. exact (proj2 (@lem5239974 b s t x'' h1)). Qed.
Lemma lem5240759 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term394 t x''.
Proof. exact (fun h0 : term63 t x'' => @lem5240758 b s t x'' h1). Qed.
Lemma lem5240761 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240762 (t : real -> Prop) (x'' : real) : (term394 t x'') = (t x'').
Proof. exact (@lem5240761 (t x'')). Qed.
Lemma lem5240763 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : t x''.
Proof. exact (EQ_MP (@lem5240762 t x'') (@lem5240759 b s t x'' h1)). Qed.
Lemma lem5240766 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5240768 (t : real -> Prop) (_68679 : real) : (term63 t _68679) = (term396 t _68679).
Proof. exact (@lem5240766 (t _68679)). Qed.
Lemma lem5240771 (_68679 : real) (t : real -> Prop) (h1 : term66 t) : term396 t _68679.
Proof. exact (EQ_MP (@lem5240768 t _68679) (@lem5240507 _68679 t h1)). Qed.
Lemma lem5240772 (x'' : real) (t : real -> Prop) (h1 : term66 t) : term396 t x''.
Proof. exact (@lem5240771 x'' t h1). Qed.
Lemma lem5240775 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (@lem5240772 x'' t h1 (@lem5240763 b s t x'' h2)). Qed.
Lemma lem5240776 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5240775 b s t x'' h1 h2). Qed.
Lemma lem5240778 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240779 : term397 = False.
Proof. exact (@lem5240778 False). Qed.
Lemma lem5240780 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240779) (@lem5240776 b s t x'' h1 h2)). Qed.
Lemma lem5240782 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : t x.
Proof. exact (proj1 (@lem5239993 t s x h1)). Qed.
Lemma lem5240783 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : term394 t x.
Proof. exact (fun h0 : term63 t x => @lem5240782 t s x h1). Qed.
Lemma lem5240785 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240786 (t : real -> Prop) (x : real) : (term394 t x) = (t x).
Proof. exact (@lem5240785 (t x)). Qed.
Lemma lem5240787 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : t x.
Proof. exact (EQ_MP (@lem5240786 t x) (@lem5240783 t s x h1)). Qed.
Lemma lem5240793 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5240794 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : (term378 t s _68681) = (term398 s t _68681).
Proof. exact (@lem5240793 (@I (real -> Prop) s _68681) (term63 t _68681)). Qed.
Lemma lem5240800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5240801 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : (term399 t s _68681) = (term400 s t _68681).
Proof. exact (MK_COMB (@lem5240800) (@lem5240794 s t _68681)). Qed.
Lemma lem5240807 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : (term398 s t _68681) = (term398 s t _68681).
Proof. exact (eq_refl (term398 s t _68681)). Qed.
Lemma lem5240808 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : ((term378 t s _68681) = (term398 s t _68681)) = ((term398 s t _68681) = (term398 s t _68681)).
Proof. exact (MK_COMB (@lem5240801 s t _68681) (@lem5240807 s t _68681)). Qed.
Lemma lem5240810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5240811 (x : Prop) : (x = x) = True.
Proof. exact (@lem5240810 Prop x). Qed.
Lemma lem5240812 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : ((term398 s t _68681) = (term398 s t _68681)) = True.
Proof. exact (@lem5240811 (term398 s t _68681)). Qed.
Lemma lem5240813 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : ((term378 t s _68681) = (term398 s t _68681)) = True.
Proof. exact (TRANS (@lem5240808 s t _68681) (@lem5240812 s t _68681)). Qed.
Lemma lem5240814 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : True = ((term378 t s _68681) = (term398 s t _68681)).
Proof. exact (SYM (@lem5240813 s t _68681)). Qed.
Lemma lem5240815 (s : real -> Prop) (t : real -> Prop) (_68681 : real) : (term378 t s _68681) = (term398 s t _68681).
Proof. exact (EQ_MP (@lem5240814 s t _68681) (@lem0)). Qed.
Lemma lem5240816 (_68681 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term398 s t _68681.
Proof. exact (EQ_MP (@lem5240815 s t _68681) (@lem5240531 _68681 b s t x'' h1)). Qed.
Lemma lem5240818 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5240819 (t : real -> Prop) (s : real -> Prop) (_68681 : real) : (term398 s t _68681) = (term402 t s _68681).
Proof. exact (@lem5240818 (term63 t _68681) (@I (real -> Prop) s _68681)). Qed.
Lemma lem5240821 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5240822 (t : real -> Prop) (_68681 : real) : (term133 t _68681) = (t _68681).
Proof. exact (@lem5240821 (t _68681)). Qed.
Lemma lem5240823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5240824 (t : real -> Prop) (_68681 : real) : (term403 t _68681) = (term48 t _68681).
Proof. exact (MK_COMB (@lem5240823) (@lem5240822 t _68681)). Qed.
Lemma lem5240825 (s : real -> Prop) (_68681 : real) : (@I (real -> Prop) s _68681) = (@I (real -> Prop) s _68681).
Proof. exact (eq_refl (@I (real -> Prop) s _68681)). Qed.
Lemma lem5240826 (t : real -> Prop) (s : real -> Prop) (_68681 : real) : (term402 t s _68681) = (term404 t s _68681).
Proof. exact (MK_COMB (@lem5240824 t _68681) (@lem5240825 s _68681)). Qed.
Lemma lem5240827 (t : real -> Prop) (s : real -> Prop) (_68681 : real) : (term398 s t _68681) = (term404 t s _68681).
Proof. exact (TRANS (@lem5240819 t s _68681) (@lem5240826 t s _68681)). Qed.
Lemma lem5240830 (_68681 : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term404 t s _68681.
Proof. exact (EQ_MP (@lem5240827 t s _68681) (@lem5240816 _68681 b s t x'' h1)). Qed.
Lemma lem5240831 (x : real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term162 b s t x'') : term404 t s x.
Proof. exact (@lem5240830 x b s t x'' h1). Qed.
Lemma lem5240834 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term327 t s x) : @I (real -> Prop) s x.
Proof. exact (@lem5240831 x b s t x'' h1 (@lem5240787 t s x h2)). Qed.
Lemma lem5240835 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term327 t s x) : term405 s x.
Proof. exact (fun h0 : term362 s x => @lem5240834 b x'' t s x h1 h2). Qed.
Lemma lem5240837 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240838 (s : real -> Prop) (x : real) : (term405 s x) = (@I (real -> Prop) s x).
Proof. exact (@lem5240837 (@I (real -> Prop) s x)). Qed.
Lemma lem5240839 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term327 t s x) : @I (real -> Prop) s x.
Proof. exact (EQ_MP (@lem5240838 s x) (@lem5240835 b x'' t s x h1 h2)). Qed.
Lemma lem5240845 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5240846 (s : real -> Prop) (_68682 : real) : (term365 s _68682) = (term421 s _68682).
Proof. exact (@lem5240845 (term77 s _68682) (term362 s _68682)). Qed.
Lemma lem5240852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5240853 (s : real -> Prop) (_68682 : real) : (term422 s _68682) = (term423 s _68682).
Proof. exact (MK_COMB (@lem5240852) (@lem5240846 s _68682)). Qed.
Lemma lem5240859 (s : real -> Prop) (_68682 : real) : (term421 s _68682) = (term421 s _68682).
Proof. exact (eq_refl (term421 s _68682)). Qed.
Lemma lem5240860 (s : real -> Prop) (_68682 : real) : ((term365 s _68682) = (term421 s _68682)) = ((term421 s _68682) = (term421 s _68682)).
Proof. exact (MK_COMB (@lem5240853 s _68682) (@lem5240859 s _68682)). Qed.
Lemma lem5240862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5240863 (x : Prop) : (x = x) = True.
Proof. exact (@lem5240862 Prop x). Qed.
Lemma lem5240864 (s : real -> Prop) (_68682 : real) : ((term421 s _68682) = (term421 s _68682)) = True.
Proof. exact (@lem5240863 (term421 s _68682)). Qed.
Lemma lem5240865 (s : real -> Prop) (_68682 : real) : ((term365 s _68682) = (term421 s _68682)) = True.
Proof. exact (TRANS (@lem5240860 s _68682) (@lem5240864 s _68682)). Qed.
Lemma lem5240866 (s : real -> Prop) (_68682 : real) : True = ((term365 s _68682) = (term421 s _68682)).
Proof. exact (SYM (@lem5240865 s _68682)). Qed.
Lemma lem5240867 (s : real -> Prop) (_68682 : real) : (term365 s _68682) = (term421 s _68682).
Proof. exact (EQ_MP (@lem5240866 s _68682) (@lem0)). Qed.
Lemma lem5240868 (_68682 : real) (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term421 s _68682.
Proof. exact (EQ_MP (@lem5240867 s _68682) (@lem5240539 _68682 x' s h1)). Qed.
Lemma lem5240870 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5240871 (s : real -> Prop) (_68682 : real) : (term421 s _68682) = (term424 s _68682).
Proof. exact (@lem5240870 (term362 s _68682) (term77 s _68682)). Qed.
Lemma lem5240873 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5240874 (s : real -> Prop) (_68682 : real) : (term413 s _68682) = (@I (real -> Prop) s _68682).
Proof. exact (@lem5240873 (@I (real -> Prop) s _68682)). Qed.
Lemma lem5240875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5240876 (s : real -> Prop) (_68682 : real) : (term414 s _68682) = (term415 s _68682).
Proof. exact (MK_COMB (@lem5240875) (@lem5240874 s _68682)). Qed.
Lemma lem5240877 (s : real -> Prop) (_68682 : real) : (term77 s _68682) = (term77 s _68682).
Proof. exact (eq_refl (term77 s _68682)). Qed.
Lemma lem5240878 (s : real -> Prop) (_68682 : real) : (term424 s _68682) = (term425 s _68682).
Proof. exact (MK_COMB (@lem5240876 s _68682) (@lem5240877 s _68682)). Qed.
Lemma lem5240879 (s : real -> Prop) (_68682 : real) : (term421 s _68682) = (term425 s _68682).
Proof. exact (TRANS (@lem5240871 s _68682) (@lem5240878 s _68682)). Qed.
Lemma lem5240882 (_68682 : real) (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term425 s _68682.
Proof. exact (EQ_MP (@lem5240879 s _68682) (@lem5240868 _68682 x' s h1)). Qed.
Lemma lem5240883 (x : real) (x' : real -> real) (s : real -> Prop) (h1 : term369 x' s) : term425 s x.
Proof. exact (@lem5240882 x x' s h1). Qed.
Lemma lem5240886 (b : real) (x'' : real) (x' : real -> real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term369 x' s) (h3 : term327 t s x) : term77 s x.
Proof. exact (@lem5240883 x x' s h2 (@lem5240839 b x'' t s x h1 h3)). Qed.
Lemma lem5240887 (b : real) (x'' : real) (x' : real -> real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term369 x' s) (h3 : term327 t s x) : term426 s x.
Proof. exact (fun h0 : term393 s x => @lem5240886 b x'' x' t s x h1 h2 h3). Qed.
Lemma lem5240889 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240890 (s : real -> Prop) (x : real) : (term426 s x) = (term77 s x).
Proof. exact (@lem5240889 (term77 s x)). Qed.
Lemma lem5240891 (b : real) (x'' : real) (x' : real -> real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term369 x' s) (h3 : term327 t s x) : term77 s x.
Proof. exact (EQ_MP (@lem5240890 s x) (@lem5240887 b x'' x' t s x h1 h2 h3)). Qed.
Lemma lem5240894 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5240896 (s : real -> Prop) (x : real) : (term393 s x) = (term427 s x).
Proof. exact (@lem5240894 (term77 s x)). Qed.
Lemma lem5240899 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term327 t s x) : term427 s x.
Proof. exact (EQ_MP (@lem5240896 s x) (@lem5240543 t s x h1)). Qed.
Lemma lem5240902 (b : real) (x'' : real) (x' : real -> real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term369 x' s) (h3 : term327 t s x) : False.
Proof. exact (@lem5240899 t s x h3 (@lem5240891 b x'' x' t s x h1 h2 h3)). Qed.
Lemma lem5240903 (b : real) (x'' : real) (x' : real -> real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term369 x' s) (h3 : term327 t s x) : term397.
Proof. exact (fun h0 : ~ False => @lem5240902 b x'' x' t s x h1 h2 h3). Qed.
Lemma lem5240905 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5240906 : term397 = False.
Proof. exact (@lem5240905 False). Qed.
Lemma lem5240907 (b : real) (x'' : real) (x' : real -> real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term369 x' s) (h3 : term327 t s x) : False.
Proof. exact (EQ_MP (@lem5240906) (@lem5240903 b x'' x' t s x h1 h2 h3)). Qed.
Lemma lem5240908 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : (term66 t) = False.
Proof. exact (prop_ext (fun h3 : term66 t => @lem5240780 b s t x'' h1 h2) (fun h3 : False => @lem5240254 t h1)). Qed.
Lemma lem5240909 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240908 b s t x'' h1 h2) (@lem5240254 t h1)). Qed.
Lemma lem5240910 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : (term371 s x') = False.
Proof. exact (prop_ext (fun h3 : term371 s x' => @lem5240756 x' b s t x'' h1 h2) (fun h3 : False => @lem5240173 s x' h1)). Qed.
Lemma lem5240911 (x' : real -> real) (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term371 s x') (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240910 x' b s t x'' h1 h2) (@lem5240173 s x' h1)). Qed.
Lemma lem5240912 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : (term66 t) = False.
Proof. exact (prop_ext (fun h3 : term66 t => @lem5240679 b s t x'' h1 h2) (fun h3 : False => @lem5240132 t h1)). Qed.
Lemma lem5240913 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240912 b s t x'' h1 h2) (@lem5240132 t h1)). Qed.
Lemma lem5240914 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term373 s) (h2 : term162 b s t x'') (h3 : term327 t s x) : (term373 s) = False.
Proof. exact (prop_ext (fun h4 : term373 s => @lem5240655 b x'' t s x h1 h2 h3) (fun h4 : False => @lem5240076 s h1)). Qed.
Lemma lem5240915 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term373 s) (h2 : term162 b s t x'') (h3 : term327 t s x) : False.
Proof. exact (EQ_MP (@lem5240914 b x'' t s x h1 h2 h3) (@lem5240076 s h1)). Qed.
Lemma lem5240916 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : (term66 t) = False.
Proof. exact (prop_ext (fun h3 : term66 t => @lem5240579 b s t x'' h1 h2) (fun h3 : False => @lem5240039 t h1)). Qed.
Lemma lem5240917 (b : real) (s : real -> Prop) (t : real -> Prop) (x'' : real) (h1 : term66 t) (h2 : term162 b s t x'') : False.
Proof. exact (EQ_MP (@lem5240916 b s t x'' h1 h2) (@lem5240039 t h1)). Qed.
Lemma lem5240918 (b : real) (x'' : real) (x' : real -> real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term162 b s t x'') (h2 : term369 x' s) (h3 : term347 t s x) : False.
Proof. exact (or_elim (@lem5239817 t s x h3) (fun h0 : term66 t => @lem5240909 b s t x'' h0 h1) (fun h0 : term327 t s x => @lem5240907 b x'' x' t s x h1 h2 h0)). Qed.
Lemma lem5240919 (x' : real -> real) (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term371 s x') (h2 : term162 b s t x'') (h3 : term347 t s x) : False.
Proof. exact (or_elim (@lem5239817 t s x h3) (fun h0 : term66 t => @lem5240913 b s t x'' h0 h2) (fun h0 : term327 t s x => @lem5240911 x' b s t x'' h1 h2)). Qed.
Lemma lem5240920 (b : real) (x'' : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term373 s) (h2 : term162 b s t x'') (h3 : term347 t s x) : False.
Proof. exact (or_elim (@lem5239817 t s x h3) (fun h0 : term66 t => @lem5240917 b s t x'' h0 h2) (fun h0 : term327 t s x => @lem5240915 b x'' t s x h1 h2 h0)). Qed.
Lemma lem5240921 (b : real) (x'' : real) (t : real -> Prop) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term162 b s t x'') (h2 : term347 t s x) (h3 : term375 s x') : False.
Proof. exact (or_elim (@lem5239978 s x' h3) (fun h0 : term373 s => @lem5240920 b x'' t s x h0 h1 h2) (fun h0 : term371 s x' => @lem5240919 x' b x'' t s x h0 h1 h2)). Qed.
Lemma lem5240922 (b : real) (x'' : real) (t : real -> Prop) (x : real) (x' : real -> real) (s : real -> Prop) (h1 : term162 b s t x'') (h2 : term347 t s x) (h3 : term322 x' s) : False.
Proof. exact (or_elim (@lem5239923 x' s h3) (fun h0 : term375 s x' => @lem5240921 b x'' t x s x' h1 h2 h0) (fun h0 : term369 x' s => @lem5240918 b x'' x' t s x h1 h0 h2)). Qed.
Lemma lem5240923 (b : real) (x'' : real) (t : real -> Prop) (x : real) (x' : real -> real) (s : real -> Prop) (h1 : term162 b s t x'') (h2 : term347 t s x) (h3 : term322 x' s) : (term347 t s x) = False.
Proof. exact (prop_ext (fun h4 : term347 t s x => @lem5240922 b x'' t x x' s h1 h2 h3) (fun h4 : False => @lem5239817 t s x h2)). Qed.
Lemma lem5240924 (b : real) (x'' : real) (t : real -> Prop) (x : real) (x' : real -> real) (s : real -> Prop) (h1 : term162 b s t x'') (h2 : term347 t s x) (h3 : term322 x' s) : False.
Proof. exact (EQ_MP (@lem5240923 b x'' t x x' s h1 h2 h3) (@lem5239817 t s x h2)). Qed.
Lemma lem5240925 (b : real) (t : real -> Prop) (x : real) (x' : real -> real) (s : real -> Prop) (h1 : term69 b s t) (h2 : term347 t s x) (h3 : term322 x' s) : False.
Proof. exact (ex_elim (@lem5239292 b s t h1) (fun x'' : real => fun h0 : term164 b s t x'' => @lem5240924 b x'' t x x' s h0 h2 h3)). Qed.
Lemma lem5240926 (b : real) (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term69 b s t) (h2 : term95 s) (h3 : term347 t s x) : False.
Proof. exact (ex_elim (@lem5239703 s h2) (fun x' : real -> real => fun h0 : term324 s x' => @lem5240925 b t x x' s h1 h3 h0)). Qed.
Lemma lem5240927 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term126 t s) (h2 : term69 b s t) (h3 : term95 s) : False.
Proof. exact (ex_elim (@lem5239787 t s h1) (fun x : real => fun h0 : term349 t s x => @lem5240926 b t s x h2 h3 h0)). Qed.
Lemma lem5240928 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term126 t s) (h2 : term69 b s t) (h3 : term95 s) : (term126 t s) = False.
Proof. exact (prop_ext (fun h4 : term126 t s => @lem5240927 b t s h1 h2 h3) (fun h4 : False => @lem5239138 t s h1)). Qed.
Lemma lem5240929 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term126 t s) (h2 : term69 b s t) (h3 : term95 s) : False.
Proof. exact (EQ_MP (@lem5240928 b t s h1 h2 h3) (@lem5239138 t s h1)). Qed.
Lemma lem5240930 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term69 b s t) (h2 : term95 s) : term125 t s.
Proof. exact (fun h0 : term126 t s => @lem5240929 b t s h0 h1 h2). Qed.
Lemma lem5240931 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term69 b s t) (h2 : term95 s) : term102 t s.
Proof. exact (EQ_MP (@lem5239137 t s) (@lem5240930 b t s h1 h2)). Qed.
Lemma lem5240932 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term69 b s t) : term103 t s.
Proof. exact (fun h0 : term95 s => @lem5240931 b t s h1 h0). Qed.
Lemma lem5240933 (b : real) (t : real -> Prop) (s : real -> Prop) : term104 b t s.
Proof. exact (fun h0 : term69 b s t => @lem5240932 b s t h0). Qed.
Lemma lem5240938 (t : real -> Prop) (s : real -> Prop) : term116 t s.
Proof. exact (fun b : real => @lem5240933 b t s). Qed.
Lemma lem5240943 (s : real -> Prop) : term120 s.
Proof. exact (fun t : real -> Prop => @lem5240938 t s). Qed.
Lemma lem5240948 : term124.
Proof. exact (fun s : real -> Prop => @lem5240943 s). Qed.
Lemma lem5240949 : term123.
Proof. exact (EQ_MP (@lem5239131) (@lem5240948)). Qed.
Lemma lem5240950 (s : real -> Prop) : term428 s.
Proof. exact (@lem5240949 s). Qed.
Lemma lem5240951 (s : real -> Prop) : (term428 s) = (term119 s).
Proof. exact (eq_refl (term428 s)). Qed.
Lemma lem5240952 (s : real -> Prop) : term119 s.
Proof. exact (EQ_MP (@lem5240951 s) (@lem5240950 s)). Qed.
Lemma lem5240953 (s : real -> Prop) (t : real -> Prop) : term429 s t.
Proof. exact (@lem5240952 s t). Qed.
Lemma lem5240954 (t : real -> Prop) (s : real -> Prop) : (term429 s t) = (term115 t s).
Proof. exact (eq_refl (term429 s t)). Qed.
Lemma lem5240955 (t : real -> Prop) (s : real -> Prop) : term115 t s.
Proof. exact (EQ_MP (@lem5240954 t s) (@lem5240953 s t)). Qed.
Lemma lem5240956 (t : real -> Prop) (s : real -> Prop) (b : real) : term430 t s b.
Proof. exact (@lem5240955 t s b). Qed.
Lemma lem5240957 (b : real) (t : real -> Prop) (s : real -> Prop) : (term430 t s b) = (term106 b t s).
Proof. exact (eq_refl (term430 t s b)). Qed.
Lemma lem5240958 (b : real) (t : real -> Prop) (s : real -> Prop) : term106 b t s.
Proof. exact (EQ_MP (@lem5240957 b t s) (@lem5240956 t s b)). Qed.
Lemma lem5240960 (b : real) (t : real -> Prop) (s : real -> Prop) : term106 b t s.
Proof. exact (@lem5238780 b t s (@lem5240958 b t s)). Qed.
Lemma lem5240961 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term107 b t s) : False.
Proof. exact (@lem5240960 b t s (@lem5238765 b t s h1)). Qed.
Lemma lem5240962 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term107 b t s) : (term107 b t s) = False.
Proof. exact (prop_ext (fun h2 : term107 b t s => @lem5240961 b t s h1) (fun h2 : False => @lem5238765 b t s h1)). Qed.
Lemma lem5240963 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term107 b t s) : False.
Proof. exact (EQ_MP (@lem5240962 b t s h1) (@lem5238765 b t s h1)). Qed.
Lemma lem5240964 (b : real) (t : real -> Prop) (s : real -> Prop) : term106 b t s.
Proof. exact (fun h0 : term107 b t s => @lem5240963 b t s h0). Qed.
Lemma lem5240965 (b : real) (t : real -> Prop) (s : real -> Prop) : term104 b t s.
Proof. exact (EQ_MP (@lem5238764 b t s) (@lem5240964 b t s)). Qed.
Lemma lem5240966 (b : real) (t : real -> Prop) (s : real -> Prop) : term46 b t s.
Proof. exact (EQ_MP (@lem5238760 b t s) (@lem5240965 b t s)). Qed.
Lemma lem5240967 (b : real) (t : real -> Prop) (s : real -> Prop) : term45 b t s.
Proof. exact (EQ_MP (@lem5238445 b t s) (@lem5240966 b t s)). Qed.
Lemma lem5240968 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term13 s b) (h2 : term11 t) (h3 : @SUBSET real t s) : term43 t s.
Proof. exact (@lem5240967 b t s (@lem5238293 b t s h1 h2 h3)). Qed.
Lemma lem5240969 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term13 s b) (h2 : term11 t) (h3 : @SUBSET real t s) : term41 t s.
Proof. exact (@lem5240968 b t s h1 h2 h3 (@lem5238256 s)). Qed.
Lemma lem5240970 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term13 s b) (h2 : term11 t) (h3 : @SUBSET real t s) : term431 s t.
Proof. exact (@lem5238281 s t (@lem5240969 b t s h1 h2 h3)). Qed.
Lemma lem5240971 (t : real -> Prop) (s : real -> Prop) (h1 : term9 t s) : term10 t s.
Proof. exact (proj2 (@lem5238273 t s h1)). Qed.
Lemma lem5240972 (t : real -> Prop) (s : real -> Prop) (h1 : term9 t s) : term11 t.
Proof. exact (proj1 (@lem5238273 t s h1)). Qed.
Lemma lem5240973 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term12 s.
Proof. exact (proj2 (@lem5238274 t s h1)). Qed.
Lemma lem5240974 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : @SUBSET real t s.
Proof. exact (proj1 (@lem5238274 t s h1)). Qed.
Lemma lem5240975 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term13 s b) (h2 : term11 t) (h3 : @SUBSET real t s) : (term13 s b) = (term431 s t).
Proof. exact (prop_ext (fun h4 : term13 s b => @lem5240970 b t s h1 h2 h3) (fun h4 : term431 s t => @lem5238278 s b h1)). Qed.
Lemma lem5240976 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term13 s b) (h2 : term11 t) (h3 : @SUBSET real t s) : term431 s t.
Proof. exact (EQ_MP (@lem5240975 b t s h1 h2 h3) (@lem5238278 s b h1)). Qed.
Lemma lem5240977 (t : real -> Prop) (s : real -> Prop) (h1 : term12 s) (h2 : term11 t) (h3 : @SUBSET real t s) : term431 s t.
Proof. exact (ex_elim (@lem5238276 s h1) (fun b : real => fun h0 : term72 s b => @lem5240976 b t s h0 h2 h3)). Qed.
Lemma lem5240978 (t : real -> Prop) (s : real -> Prop) (h1 : term12 s) (h2 : term11 t) (h3 : @SUBSET real t s) : (@SUBSET real t s) = (term431 s t).
Proof. exact (prop_ext (fun h4 : @SUBSET real t s => @lem5240977 t s h1 h2 h3) (fun h4 : term431 s t => @lem5238277 t s h3)). Qed.
Lemma lem5240979 (t : real -> Prop) (s : real -> Prop) (h1 : term12 s) (h2 : term11 t) (h3 : @SUBSET real t s) : term431 s t.
Proof. exact (EQ_MP (@lem5240978 t s h1 h2 h3) (@lem5238277 t s h3)). Qed.
Lemma lem5240980 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term10 t s) (h3 : @SUBSET real t s) : (term12 s) = (term431 s t).
Proof. exact (prop_ext (fun h4 : term12 s => @lem5240979 t s h4 h1 h3) (fun h4 : term431 s t => @lem5240973 t s h2)). Qed.
Lemma lem5240981 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term10 t s) (h3 : @SUBSET real t s) : term431 s t.
Proof. exact (EQ_MP (@lem5240980 t s h1 h2 h3) (@lem5240973 t s h2)). Qed.
Lemma lem5240982 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term10 t s) : (@SUBSET real t s) = (term431 s t).
Proof. exact (prop_ext (fun h3 : @SUBSET real t s => @lem5240981 t s h1 h2 h3) (fun h3 : term431 s t => @lem5240974 t s h2)). Qed.
Lemma lem5240983 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term10 t s) : term431 s t.
Proof. exact (EQ_MP (@lem5240982 t s h1 h2) (@lem5240974 t s h2)). Qed.
Lemma lem5240984 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term10 t s) : (term11 t) = (term431 s t).
Proof. exact (prop_ext (fun h3 : term11 t => @lem5240983 t s h1 h2) (fun h3 : term431 s t => @lem5238275 t h1)). Qed.
Lemma lem5240985 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term10 t s) : term431 s t.
Proof. exact (EQ_MP (@lem5240984 t s h1 h2) (@lem5238275 t h1)). Qed.
Lemma lem5240986 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term9 t s) : (term10 t s) = (term431 s t).
Proof. exact (prop_ext (fun h3 : term10 t s => @lem5240985 t s h1 h3) (fun h3 : term431 s t => @lem5240971 t s h2)). Qed.
Lemma lem5240987 (t : real -> Prop) (s : real -> Prop) (h1 : term11 t) (h2 : term9 t s) : term431 s t.
Proof. exact (EQ_MP (@lem5240986 t s h1 h2) (@lem5240971 t s h2)). Qed.
Lemma lem5240988 (t : real -> Prop) (s : real -> Prop) (h1 : term9 t s) : (term11 t) = (term431 s t).
Proof. exact (prop_ext (fun h2 : term11 t => @lem5240987 t s h2 h1) (fun h2 : term431 s t => @lem5240972 t s h1)). Qed.
Lemma lem5240989 (t : real -> Prop) (s : real -> Prop) (h1 : term9 t s) : term431 s t.
Proof. exact (EQ_MP (@lem5240988 t s h1) (@lem5240972 t s h1)). Qed.
Lemma lem5240990 (s : real -> Prop) (t : real -> Prop) : term432 s t.
Proof. exact (fun h0 : term9 t s => @lem5240989 t s h0). Qed.
Lemma lem5240995 (s : real -> Prop) : term433 s.
Proof. exact (fun t : real -> Prop => @lem5240990 s t). Qed.
Lemma lem5241000 : term434.
Proof. exact (fun s : real -> Prop => @lem5240995 s). Qed.
