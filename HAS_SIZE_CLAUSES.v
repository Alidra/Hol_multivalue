Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_CLAUSES_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_INSERT_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_0_spec.
Require Import HAS_SIZE_SUC_spec.
Require Import IN_DELETE_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3884249 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3884250 {_100455 : Type'} (s : _100455 -> Prop) (t : _100455 -> Prop) : (s = t) = (term0 _100455 s t).
Proof. exact (@lem3884249 _100455 s t). Qed.
Lemma lem3884251 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (s = (term1 _100455 s a)) = (term2 _100455 s a).
Proof. exact (@lem3884250 _100455 s (term1 _100455 s a)). Qed.
Lemma lem3884260 {_100455 : Type'} (a : _100455) (s : _100455 -> Prop) : (term3 _100455 a s) = (term3 _100455 a s).
Proof. exact (eq_refl (term3 _100455 a s)). Qed.
Lemma lem3884261 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term4 _100455 s a) = (term5 _100455 s a).
Proof. exact (MK_COMB (@lem3884260 _100455 a s) (@lem3884251 _100455 s a)). Qed.
Lemma lem3884264 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term5 _100455 s a) = (term4 _100455 s a).
Proof. exact (SYM (@lem3884261 _100455 s a)). Qed.
Lemma lem3884268 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3884269 {_100455 : Type'} (P : _100455 -> Prop) (x : _100455) : (@IN _100455 x P) = (P x).
Proof. exact (@lem3884268 _100455 P x). Qed.
Lemma lem3884270 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (@IN _100455 a s) = (s a).
Proof. exact (@lem3884269 _100455 s a). Qed.
Lemma lem3884271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3884272 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term3 _100455 a s) = (term6 _100455 s a).
Proof. exact (MK_COMB (@lem3884271) (@lem3884270 _100455 s a)). Qed.
Lemma lem3884280 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3884281 {_100455 : Type'} (P : _100455 -> Prop) (x : _100455) : (@IN _100455 x P) = (P x).
Proof. exact (@lem3884280 _100455 P x). Qed.
Lemma lem3884282 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (@IN _100455 x s) = (s x).
Proof. exact (@lem3884281 _100455 s x). Qed.
Lemma lem3884283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3884284 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term7 _100455 x s) = (term8 _100455 s x).
Proof. exact (MK_COMB (@lem3884283) (@lem3884282 _100455 s x)). Qed.
Lemma lem3884286 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term9 A x y s) = (term10 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3884287 {_100455 : Type'} (y : _100455) (x : _100455) (s : _100455 -> Prop) : (term9 _100455 x y s) = (term10 _100455 y x s).
Proof. exact (@lem3884286 _100455 y x s). Qed.
Lemma lem3884288 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) : (term11 _100455 x s a) = (term12 _100455 x s a).
Proof. exact (@lem3884287 _100455 a x (@DELETE _100455 s a)). Qed.
Lemma lem3884294 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term13 A x s y) = (term14 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3884295 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (y : _100455) : (term13 _100455 x s y) = (term14 _100455 s x y).
Proof. exact (@lem3884294 _100455 s x y). Qed.
Lemma lem3884296 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term13 _100455 x s a) = (term14 _100455 s x a).
Proof. exact (@lem3884295 _100455 s x a). Qed.
Lemma lem3884300 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3884301 {_100455 : Type'} (P : _100455 -> Prop) (x : _100455) : (@IN _100455 x P) = (P x).
Proof. exact (@lem3884300 _100455 P x). Qed.
Lemma lem3884302 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (@IN _100455 x s) = (s x).
Proof. exact (@lem3884301 _100455 s x). Qed.
Lemma lem3884303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3884304 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term15 _100455 x s) = (term16 _100455 s x).
Proof. exact (MK_COMB (@lem3884303) (@lem3884302 _100455 s x)). Qed.
Lemma lem3884307 {_100455 : Type'} (x : _100455) (a : _100455) : (term17 _100455 x a) = (term17 _100455 x a).
Proof. exact (eq_refl (term17 _100455 x a)). Qed.
Lemma lem3884308 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term14 _100455 s x a) = (term18 _100455 s x a).
Proof. exact (MK_COMB (@lem3884304 _100455 s x) (@lem3884307 _100455 x a)). Qed.
Lemma lem3884311 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term13 _100455 x s a) = (term18 _100455 s x a).
Proof. exact (TRANS (@lem3884296 _100455 s x a) (@lem3884308 _100455 s x a)). Qed.
Lemma lem3884312 {_100455 : Type'} (x : _100455) (a : _100455) : (term19 _100455 x a) = (term19 _100455 x a).
Proof. exact (eq_refl (term19 _100455 x a)). Qed.
Lemma lem3884313 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term12 _100455 x s a) = (term20 _100455 s x a).
Proof. exact (MK_COMB (@lem3884312 _100455 x a) (@lem3884311 _100455 s x a)). Qed.
Lemma lem3884316 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term11 _100455 x s a) = (term20 _100455 s x a).
Proof. exact (TRANS (@lem3884288 _100455 x s a) (@lem3884313 _100455 s x a)). Qed.
Lemma lem3884317 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : ((@IN _100455 x s) = (term11 _100455 x s a)) = ((s x) = (term20 _100455 s x a)).
Proof. exact (MK_COMB (@lem3884284 _100455 s x) (@lem3884316 _100455 s x a)). Qed.
Lemma lem3884320 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term21 _100455 s a) = (term22 _100455 s a).
Proof. exact (fun_ext (fun x : _100455 => @lem3884317 _100455 s x a)). Qed.
Lemma lem3884321 {_100455 : Type'} : (@all _100455) = (@all _100455).
Proof. exact (eq_refl (@all _100455)). Qed.
Lemma lem3884322 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term2 _100455 s a) = (term23 _100455 s a).
Proof. exact (MK_COMB (@lem3884321 _100455) (@lem3884320 _100455 s a)). Qed.
Lemma lem3884327 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term5 _100455 s a) = (term24 _100455 s a).
Proof. exact (MK_COMB (@lem3884272 _100455 s a) (@lem3884322 _100455 s a)). Qed.
Lemma lem3884330 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term24 _100455 s a) = (term5 _100455 s a).
Proof. exact (SYM (@lem3884327 _100455 s a)). Qed.
Lemma lem3884332 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3884333 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term24 _100455 s a) = (term26 _100455 s a).
Proof. exact (@lem3884332 (term24 _100455 s a)). Qed.
Lemma lem3884334 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term26 _100455 s a) = (term24 _100455 s a).
Proof. exact (SYM (@lem3884333 _100455 s a)). Qed.
Lemma lem3884335 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term27 _100455 s a) : term27 _100455 s a.
Proof. exact (h1). Qed.
Lemma lem3884338 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term26 _100455 s a) : term26 _100455 s a.
Proof. exact (h1). Qed.
Lemma lem3884339 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term28 _100455 s a.
Proof. exact (fun h0 : term26 _100455 s a => @lem3884338 _100455 s a h0). Qed.
Lemma lem3884340 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term28 _100455 s a) : term28 _100455 s a.
Proof. exact (h1). Qed.
Lemma lem3884341 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term26 _100455 s a) : term26 _100455 s a.
Proof. exact (h1). Qed.
Lemma lem3884342 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term26 _100455 s a) (h2 : term28 _100455 s a) : term26 _100455 s a.
Proof. exact (@lem3884340 _100455 s a h2 (@lem3884341 _100455 s a h1)). Qed.
Lemma lem3884343 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term26 _100455 s a) : term29 _100455 s a.
Proof. exact (fun h0 : term28 _100455 s a => @lem3884342 _100455 s a h1 h0). Qed.
Lemma lem3884344 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term28 _100455 s a) : term28 _100455 s a.
Proof. exact (h1). Qed.
Lemma lem3884345 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term26 _100455 s a) (h2 : term28 _100455 s a) : term26 _100455 s a.
Proof. exact (@lem3884343 _100455 s a h1 (@lem3884344 _100455 s a h2)). Qed.
Lemma lem3884346 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term28 _100455 s a) : term28 _100455 s a.
Proof. exact (fun h0 : term26 _100455 s a => @lem3884345 _100455 s a h0 h1). Qed.
Lemma lem3884347 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term30 _100455 s a.
Proof. exact (fun h0 : term28 _100455 s a => @lem3884346 _100455 s a h0). Qed.
Lemma lem3884350 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term28 _100455 s a.
Proof. exact (@lem3884347 _100455 s a (@lem3884339 _100455 s a)). Qed.
Lemma lem3884351 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term28 _100455 s a.
Proof. exact (@lem3884350 _100455 s a). Qed.
Lemma lem3884361 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3884362 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term26 _100455 s a) = (term31 _100455 s a).
Proof. exact (@lem3884361 (term27 _100455 s a)). Qed.
Lemma lem3884364 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3884365 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term31 _100455 s a) = (term24 _100455 s a).
Proof. exact (@lem3884364 (term24 _100455 s a)). Qed.
Lemma lem3884368 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term26 _100455 s a) = (term24 _100455 s a).
Proof. exact (TRANS (@lem3884362 _100455 s a) (@lem3884365 _100455 s a)). Qed.
Lemma lem3884377 {_100455 : Type'} (a : _100455) : (term33 _100455 a) = (term34 _100455 a).
Proof. exact (fun_ext (fun s : _100455 -> Prop => @lem3884368 _100455 s a)). Qed.
Lemma lem3884378 {_100455 : Type'} : (@all (_100455 -> Prop)) = (@all (_100455 -> Prop)).
Proof. exact (eq_refl (@all (_100455 -> Prop))). Qed.
Lemma lem3884379 {_100455 : Type'} (a : _100455) : (term35 _100455 a) = (term36 _100455 a).
Proof. exact (MK_COMB (@lem3884378 _100455) (@lem3884377 _100455 a)). Qed.
Lemma lem3884384 {_100455 : Type'} : (term37 _100455) = (term38 _100455).
Proof. exact (fun_ext (fun a : _100455 => @lem3884379 _100455 a)). Qed.
Lemma lem3884385 {_100455 : Type'} : (@all _100455) = (@all _100455).
Proof. exact (eq_refl (@all _100455)). Qed.
Lemma lem3884394 {_100455 : Type'} : (term39 _100455) = (term40 _100455).
Proof. exact (MK_COMB (@lem3884385 _100455) (@lem3884384 _100455)). Qed.
Lemma lem3884409 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : ((s x) = (term20 _100455 s x a)) = ((s x) = (term20 _100455 s x a)).
Proof. exact (eq_refl ((s x) = (term20 _100455 s x a))). Qed.
Lemma lem3884410 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term22 _100455 s a) = (term22 _100455 s a).
Proof. exact (fun_ext (fun x : _100455 => @lem3884409 _100455 s x a)). Qed.
Lemma lem3884411 {_100455 : Type'} : (@all _100455) = (@all _100455).
Proof. exact (eq_refl (@all _100455)). Qed.
Lemma lem3884412 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term23 _100455 s a) = (term23 _100455 s a).
Proof. exact (MK_COMB (@lem3884411 _100455) (@lem3884410 _100455 s a)). Qed.
Lemma lem3884415 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term6 _100455 s a) = (term6 _100455 s a).
Proof. exact (eq_refl (term6 _100455 s a)). Qed.
Lemma lem3884416 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term24 _100455 s a) = (term24 _100455 s a).
Proof. exact (MK_COMB (@lem3884415 _100455 s a) (@lem3884412 _100455 s a)). Qed.
Lemma lem3884417 {_100455 : Type'} (a : _100455) : (term34 _100455 a) = (term34 _100455 a).
Proof. exact (fun_ext (fun s : _100455 -> Prop => @lem3884416 _100455 s a)). Qed.
Lemma lem3884418 {_100455 : Type'} : (@all (_100455 -> Prop)) = (@all (_100455 -> Prop)).
Proof. exact (eq_refl (@all (_100455 -> Prop))). Qed.
Lemma lem3884419 {_100455 : Type'} (a : _100455) : (term36 _100455 a) = (term36 _100455 a).
Proof. exact (MK_COMB (@lem3884418 _100455) (@lem3884417 _100455 a)). Qed.
Lemma lem3884420 {_100455 : Type'} : (term38 _100455) = (term38 _100455).
Proof. exact (fun_ext (fun a : _100455 => @lem3884419 _100455 a)). Qed.
Lemma lem3884421 {_100455 : Type'} : (@all _100455) = (@all _100455).
Proof. exact (eq_refl (@all _100455)). Qed.
Lemma lem3884422 {_100455 : Type'} : (term40 _100455) = (term40 _100455).
Proof. exact (MK_COMB (@lem3884421 _100455) (@lem3884420 _100455)). Qed.
Lemma lem3884449 {_100455 : Type'} : (term39 _100455) = (term40 _100455).
Proof. exact (TRANS (@lem3884394 _100455) (@lem3884422 _100455)). Qed.
Lemma lem3884450 {_100455 : Type'} : (term40 _100455) = (term39 _100455).
Proof. exact (SYM (@lem3884449 _100455)). Qed.
Lemma lem3884453 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3884454 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : ((s x) = (term20 _100455 s x a)) = (term41 _100455 s x a).
Proof. exact (@lem3884453 ((s x) = (term20 _100455 s x a))). Qed.
Lemma lem3884455 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term41 _100455 s x a) = ((s x) = (term20 _100455 s x a)).
Proof. exact (SYM (@lem3884454 _100455 s x a)). Qed.
Lemma lem3884456 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term42 _100455 s x a) : term42 _100455 s x a.
Proof. exact (h1). Qed.
Lemma lem3884462 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3884472 {_100455 : Type'} (x : _100455) (a : _100455) : (term43 _100455 x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem3884474 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term44 _100455 s x) = (term44 _100455 s x).
Proof. exact (eq_refl (term44 _100455 s x)). Qed.
Lemma lem3884475 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term45 _100455 s x a) = (term46 _100455 s x a).
Proof. exact (MK_COMB (@lem3884474 _100455 s x) (@lem3884472 _100455 x a)). Qed.
Lemma lem3884476 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term47 _100455 s x a) = (term45 _100455 s x a).
Proof. exact (@lem17045 (s x) (term17 _100455 x a)). Qed.
Lemma lem3884477 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term47 _100455 s x a) = (term46 _100455 s x a).
Proof. exact (TRANS (@lem3884476 _100455 s x a) (@lem3884475 _100455 s x a)). Qed.
Lemma lem3884482 {_100455 : Type'} (x : _100455) (a : _100455) : (term48 _100455 x a) = (term48 _100455 x a).
Proof. exact (eq_refl (term48 _100455 x a)). Qed.
Lemma lem3884483 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term49 _100455 s x a) = (term50 _100455 s x a).
Proof. exact (MK_COMB (@lem3884482 _100455 x a) (@lem3884477 _100455 s x a)). Qed.
Lemma lem3884484 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term51 _100455 s x a) = (term49 _100455 s x a).
Proof. exact (@lem17160 (x = a) (term18 _100455 s x a)). Qed.
Lemma lem3884485 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term51 _100455 s x a) = (term50 _100455 s x a).
Proof. exact (TRANS (@lem3884484 _100455 s x a) (@lem3884483 _100455 s x a)). Qed.
Lemma lem3884491 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term52 _100455 s x a) = (term52 _100455 s x a).
Proof. exact (eq_refl (term52 _100455 s x a)). Qed.
Lemma lem3884493 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term16 _100455 s x) = (term16 _100455 s x).
Proof. exact (eq_refl (term16 _100455 s x)). Qed.
Lemma lem3884494 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term53 _100455 s x a) = (term54 _100455 s x a).
Proof. exact (MK_COMB (@lem3884493 _100455 s x) (@lem3884485 _100455 s x a)). Qed.
Lemma lem3884495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3884496 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term55 _100455 s x a) = (term56 _100455 s x a).
Proof. exact (MK_COMB (@lem3884495) (@lem3884494 _100455 s x a)). Qed.
Lemma lem3884497 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term57 _100455 s x a) = (term58 _100455 s x a).
Proof. exact (MK_COMB (@lem3884496 _100455 s x a) (@lem3884491 _100455 s x a)). Qed.
Lemma lem3884498 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term42 _100455 s x a) = (term57 _100455 s x a).
Proof. exact (@lem17646 (s x) (term20 _100455 s x a)). Qed.
Lemma lem3884503 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) : (term42 _100455 s x a) = (term58 _100455 s x a).
Proof. exact (TRANS (@lem3884498 _100455 s x a) (@lem3884497 _100455 s x a)). Qed.
Lemma lem3884508 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3884570 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term42 _100455 s x a) : term58 _100455 s x a.
Proof. exact (EQ_MP (@lem3884503 _100455 s x a) (@lem3884456 _100455 s x a h1)). Qed.
Lemma lem3884571 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : term54 _100455 s x a.
Proof. exact (h1). Qed.
Lemma lem3884572 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) : term52 _100455 s x a.
Proof. exact (h1). Qed.
Lemma lem3884573 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : term50 _100455 s x a.
Proof. exact (proj2 (@lem3884571 _100455 s x a h1)). Qed.
Lemma lem3884575 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : term46 _100455 s x a.
Proof. exact (proj2 (@lem3884573 _100455 s x a h1)). Qed.
Lemma lem3884579 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) : term20 _100455 s x a.
Proof. exact (proj2 (@lem3884572 _100455 s x a h1)). Qed.
Lemma lem3884582 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term18 _100455 s x a) : term18 _100455 s x a.
Proof. exact (h1). Qed.
Lemma lem3884600 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (h1 : term59 _100455 s x) : term59 _100455 s x.
Proof. exact (h1). Qed.
Lemma lem3884616 {_100455 : Type'} (x : _100455) (a : _100455) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3884620 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3884628 {_100455 : Type'} (x : _100455) (a : _100455) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3884652 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (h1 : term59 _100455 s x) : term59 _100455 s x.
Proof. exact (h1). Qed.
Lemma lem3884658 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : term17 _100455 x a.
Proof. exact (proj1 (@lem3884573 _100455 s x a h1)). Qed.
Lemma lem3884660 {_100455 : Type'} (x : _100455) (a : _100455) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3884662 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3884664 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) : term59 _100455 s x.
Proof. exact (proj1 (@lem3884572 _100455 s x a h1)). Qed.
Lemma lem3884666 {_100455 : Type'} (x : _100455) (a : _100455) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3884670 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) : term59 _100455 s x.
Proof. exact (proj1 (@lem3884572 _100455 s x a h1)). Qed.
Lemma lem3884716 {_100455 : Type'} (a : _100455) : (term60 _100455 a) = (term60 _100455 a).
Proof. exact (eq_refl (term60 _100455 a)). Qed.
Lemma lem3884717 {_100455 : Type'} (x : _100455) (a : _100455) (h1 : x = a) : (term61 _100455 a x) = (term62 _100455 a).
Proof. exact (MK_COMB (@lem3884716 _100455 a) (@lem3884660 _100455 x a h1)). Qed.
Lemma lem3884718 {_100455 : Type'} (a : _100455) : (term62 _100455 a) = (term63 _100455 a).
Proof. exact (eq_refl (term62 _100455 a)). Qed.
Lemma lem3884719 {_100455 : Type'} (a : _100455) (x : _100455) : (term64 _100455 a x) = (term64 _100455 a x).
Proof. exact (eq_refl (term64 _100455 a x)). Qed.
Lemma lem3884720 {_100455 : Type'} (x : _100455) (a : _100455) : ((term61 _100455 a x) = (term62 _100455 a)) = ((term61 _100455 a x) = (term63 _100455 a)).
Proof. exact (MK_COMB (@lem3884719 _100455 a x) (@lem3884718 _100455 a)). Qed.
Lemma lem3884721 {_100455 : Type'} (x : _100455) (a : _100455) : (term61 _100455 a x) = (term17 _100455 x a).
Proof. exact (eq_refl (term61 _100455 a x)). Qed.
Lemma lem3884722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3884723 {_100455 : Type'} (x : _100455) (a : _100455) : (term64 _100455 a x) = (term65 _100455 x a).
Proof. exact (MK_COMB (@lem3884722) (@lem3884721 _100455 x a)). Qed.
Lemma lem3884724 {_100455 : Type'} (a : _100455) : (term63 _100455 a) = (term63 _100455 a).
Proof. exact (eq_refl (term63 _100455 a)). Qed.
Lemma lem3884725 {_100455 : Type'} (x : _100455) (a : _100455) : ((term61 _100455 a x) = (term63 _100455 a)) = ((term17 _100455 x a) = (term63 _100455 a)).
Proof. exact (MK_COMB (@lem3884723 _100455 x a) (@lem3884724 _100455 a)). Qed.
Lemma lem3884726 {_100455 : Type'} (x : _100455) (a : _100455) : ((term61 _100455 a x) = (term62 _100455 a)) = ((term17 _100455 x a) = (term63 _100455 a)).
Proof. exact (TRANS (@lem3884720 _100455 x a) (@lem3884725 _100455 x a)). Qed.
Lemma lem3884727 {_100455 : Type'} (x : _100455) (a : _100455) (h1 : x = a) : (term17 _100455 x a) = (term63 _100455 a).
Proof. exact (EQ_MP (@lem3884726 _100455 x a) (@lem3884717 _100455 x a h1)). Qed.
Lemma lem3884728 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : term63 _100455 a.
Proof. exact (EQ_MP (@lem3884727 _100455 x a h2) (@lem3884658 _100455 s x a h1)). Qed.
Lemma lem3884756 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3884757 {_100455 : Type'} (s : _100455 -> Prop) : (term66 _100455 s) = (term66 _100455 s).
Proof. exact (eq_refl (term66 _100455 s)). Qed.
Lemma lem3884758 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : x = a) : (term67 _100455 s x) = (term67 _100455 s a).
Proof. exact (MK_COMB (@lem3884757 _100455 s) (@lem3884666 _100455 x a h1)). Qed.
Lemma lem3884759 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term67 _100455 s a) = (term59 _100455 s a).
Proof. exact (eq_refl (term67 _100455 s a)). Qed.
Lemma lem3884760 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term68 _100455 s x) = (term68 _100455 s x).
Proof. exact (eq_refl (term68 _100455 s x)). Qed.
Lemma lem3884761 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) : ((term67 _100455 s x) = (term67 _100455 s a)) = ((term67 _100455 s x) = (term59 _100455 s a)).
Proof. exact (MK_COMB (@lem3884760 _100455 s x) (@lem3884759 _100455 s a)). Qed.
Lemma lem3884762 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term67 _100455 s x) = (term59 _100455 s x).
Proof. exact (eq_refl (term67 _100455 s x)). Qed.
Lemma lem3884763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3884764 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term68 _100455 s x) = (term69 _100455 s x).
Proof. exact (MK_COMB (@lem3884763) (@lem3884762 _100455 s x)). Qed.
Lemma lem3884765 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term59 _100455 s a) = (term59 _100455 s a).
Proof. exact (eq_refl (term59 _100455 s a)). Qed.
Lemma lem3884766 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) : ((term67 _100455 s x) = (term59 _100455 s a)) = ((term59 _100455 s x) = (term59 _100455 s a)).
Proof. exact (MK_COMB (@lem3884764 _100455 s x) (@lem3884765 _100455 s a)). Qed.
Lemma lem3884767 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) : ((term67 _100455 s x) = (term67 _100455 s a)) = ((term59 _100455 s x) = (term59 _100455 s a)).
Proof. exact (TRANS (@lem3884761 _100455 x s a) (@lem3884766 _100455 x s a)). Qed.
Lemma lem3884768 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : x = a) : (term59 _100455 s x) = (term59 _100455 s a).
Proof. exact (EQ_MP (@lem3884767 _100455 x s a) (@lem3884758 _100455 s x a h1)). Qed.
Lemma lem3884769 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) (h2 : x = a) : term59 _100455 s a.
Proof. exact (EQ_MP (@lem3884768 _100455 s x a h2) (@lem3884664 _100455 s x a h1)). Qed.
Lemma lem3884785 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : s x.
Proof. exact (proj1 (@lem3884571 _100455 s x a h1)). Qed.
Lemma lem3884786 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : term70 _100455 s x.
Proof. exact (fun h0 : term59 _100455 s x => @lem3884785 _100455 s x a h1). Qed.
Lemma lem3884788 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884789 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term70 _100455 s x) = (s x).
Proof. exact (@lem3884788 (s x)). Qed.
Lemma lem3884790 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : s x.
Proof. exact (EQ_MP (@lem3884789 _100455 s x) (@lem3884786 _100455 s x a h1)). Qed.
Lemma lem3884793 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3884795 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term59 _100455 s x) = (term72 _100455 s x).
Proof. exact (@lem3884793 (s x)). Qed.
Lemma lem3884798 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (h1 : term59 _100455 s x) : term72 _100455 s x.
Proof. exact (EQ_MP (@lem3884795 _100455 s x) (@lem3884652 _100455 s x h1)). Qed.
Lemma lem3884801 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : False.
Proof. exact (@lem3884798 _100455 s x h1 (@lem3884790 _100455 s x a h2)). Qed.
Lemma lem3884802 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : term73.
Proof. exact (fun h0 : ~ False => @lem3884801 _100455 s x a h1 h2). Qed.
Lemma lem3884804 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884805 : term73 = False.
Proof. exact (@lem3884804 False). Qed.
Lemma lem3884806 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : False.
Proof. exact (EQ_MP (@lem3884805) (@lem3884802 _100455 s x a h1 h2)). Qed.
Lemma lem3884822 {_100455 : Type'} (x : _100455) : x = x.
Proof. exact (@lem21386 _100455 x). Qed.
Lemma lem3884823 {_100455 : Type'} (x : _100455) : x = x.
Proof. exact (@lem3884822 _100455 x). Qed.
Lemma lem3884824 {_100455 : Type'} (a : _100455) : a = a.
Proof. exact (@lem3884823 _100455 a). Qed.
Lemma lem3884825 {_100455 : Type'} (a : _100455) : term74 _100455 a.
Proof. exact (fun h0 : term63 _100455 a => @lem3884824 _100455 a). Qed.
Lemma lem3884827 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884828 {_100455 : Type'} (a : _100455) : (term74 _100455 a) = (a = a).
Proof. exact (@lem3884827 (a = a)). Qed.
Lemma lem3884829 {_100455 : Type'} (a : _100455) : a = a.
Proof. exact (EQ_MP (@lem3884828 _100455 a) (@lem3884825 _100455 a)). Qed.
Lemma lem3884832 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3884834 {_100455 : Type'} (a : _100455) : (term63 _100455 a) = (term75 _100455 a).
Proof. exact (@lem3884832 (a = a)). Qed.
Lemma lem3884837 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : term75 _100455 a.
Proof. exact (EQ_MP (@lem3884834 _100455 a) (@lem3884728 _100455 s x a h1 h2)). Qed.
Lemma lem3884840 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : False.
Proof. exact (@lem3884837 _100455 s x a h1 h2 (@lem3884829 _100455 a)). Qed.
Lemma lem3884841 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : term73.
Proof. exact (fun h0 : ~ False => @lem3884840 _100455 s x a h1 h2). Qed.
Lemma lem3884843 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884844 : term73 = False.
Proof. exact (@lem3884843 False). Qed.
Lemma lem3884847 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3884848 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : term70 _100455 s a.
Proof. exact (fun h0 : term59 _100455 s a => @lem3884847 _100455 s a h1). Qed.
Lemma lem3884850 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884851 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term70 _100455 s a) = (s a).
Proof. exact (@lem3884850 (s a)). Qed.
Lemma lem3884852 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : s a.
Proof. exact (EQ_MP (@lem3884851 _100455 s a) (@lem3884848 _100455 s a h1)). Qed.
Lemma lem3884855 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3884857 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term59 _100455 s a) = (term72 _100455 s a).
Proof. exact (@lem3884855 (s a)). Qed.
Lemma lem3884860 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) (h2 : x = a) : term72 _100455 s a.
Proof. exact (EQ_MP (@lem3884857 _100455 s a) (@lem3884769 _100455 s x a h1 h2)). Qed.
Lemma lem3884863 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (@lem3884860 _100455 s x a h2 h3 (@lem3884852 _100455 s a h1)). Qed.
Lemma lem3884864 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : term73.
Proof. exact (fun h0 : ~ False => @lem3884863 _100455 s x a h1 h2 h3). Qed.
Lemma lem3884866 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884867 : term73 = False.
Proof. exact (@lem3884866 False). Qed.
Lemma lem3884868 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884867) (@lem3884864 _100455 s x a h1 h2 h3)). Qed.
Lemma lem3884884 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term18 _100455 s x a) : s x.
Proof. exact (proj1 (@lem3884582 _100455 s x a h1)). Qed.
Lemma lem3884885 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term18 _100455 s x a) : term70 _100455 s x.
Proof. exact (fun h0 : term59 _100455 s x => @lem3884884 _100455 s x a h1). Qed.
Lemma lem3884887 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884888 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term70 _100455 s x) = (s x).
Proof. exact (@lem3884887 (s x)). Qed.
Lemma lem3884889 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term18 _100455 s x a) : s x.
Proof. exact (EQ_MP (@lem3884888 _100455 s x) (@lem3884885 _100455 s x a h1)). Qed.
Lemma lem3884892 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3884894 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) : (term59 _100455 s x) = (term72 _100455 s x).
Proof. exact (@lem3884892 (s x)). Qed.
Lemma lem3884897 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) : term72 _100455 s x.
Proof. exact (EQ_MP (@lem3884894 _100455 s x) (@lem3884670 _100455 s x a h1)). Qed.
Lemma lem3884900 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) (h2 : term18 _100455 s x a) : False.
Proof. exact (@lem3884897 _100455 s x a h1 (@lem3884889 _100455 s x a h2)). Qed.
Lemma lem3884901 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) (h2 : term18 _100455 s x a) : term73.
Proof. exact (fun h0 : ~ False => @lem3884900 _100455 s x a h1 h2). Qed.
Lemma lem3884903 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3884904 : term73 = False.
Proof. exact (@lem3884903 False). Qed.
Lemma lem3884905 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term52 _100455 s x a) (h2 : term18 _100455 s x a) : False.
Proof. exact (EQ_MP (@lem3884904) (@lem3884901 _100455 s x a h1 h2)). Qed.
Lemma lem3884906 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3884868 _100455 s x a h1 h2 h3) (fun h4 : False => @lem3884756 _100455 s a h1)). Qed.
Lemma lem3884908 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884906 _100455 s x a h1 h2 h3) (@lem3884756 _100455 s a h1)). Qed.
Lemma lem3884909 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3884844) (@lem3884841 _100455 s x a h1 h2)). Qed.
Lemma lem3884910 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3884908 _100455 s x a h1 h2 h3) (fun h4 : False => @lem3884666 _100455 x a h3)). Qed.
Lemma lem3884911 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884910 _100455 s x a h1 h2 h3) (@lem3884666 _100455 x a h3)). Qed.
Lemma lem3884912 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3884911 _100455 s x a h1 h2 h3) (fun h4 : False => @lem3884662 _100455 s a h1)). Qed.
Lemma lem3884913 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884912 _100455 s x a h1 h2 h3) (@lem3884662 _100455 s a h1)). Qed.
Lemma lem3884914 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3884909 _100455 s x a h1 h2) (fun h3 : False => @lem3884660 _100455 x a h2)). Qed.
Lemma lem3884915 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3884914 _100455 s x a h1 h2) (@lem3884660 _100455 x a h2)). Qed.
Lemma lem3884916 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : (term59 _100455 s x) = False.
Proof. exact (prop_ext (fun h3 : term59 _100455 s x => @lem3884806 _100455 s x a h1 h2) (fun h3 : False => @lem3884652 _100455 s x h1)). Qed.
Lemma lem3884917 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : False.
Proof. exact (EQ_MP (@lem3884916 _100455 s x a h1 h2) (@lem3884652 _100455 s x h1)). Qed.
Lemma lem3884918 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3884913 _100455 s x a h1 h2 h3) (fun h4 : False => @lem3884628 _100455 x a h3)). Qed.
Lemma lem3884919 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884918 _100455 s x a h1 h2 h3) (@lem3884628 _100455 x a h3)). Qed.
Lemma lem3884920 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3884919 _100455 s x a h1 h2 h3) (fun h4 : False => @lem3884620 _100455 s a h1)). Qed.
Lemma lem3884921 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884920 _100455 s x a h1 h2 h3) (@lem3884620 _100455 s a h1)). Qed.
Lemma lem3884922 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3884915 _100455 s x a h1 h2) (fun h3 : False => @lem3884616 _100455 x a h2)). Qed.
Lemma lem3884923 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3884922 _100455 s x a h1 h2) (@lem3884616 _100455 x a h2)). Qed.
Lemma lem3884924 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : (term59 _100455 s x) = False.
Proof. exact (prop_ext (fun h3 : term59 _100455 s x => @lem3884917 _100455 s x a h1 h2) (fun h3 : False => @lem3884600 _100455 s x h1)). Qed.
Lemma lem3884925 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : False.
Proof. exact (EQ_MP (@lem3884924 _100455 s x a h1 h2) (@lem3884600 _100455 s x h1)). Qed.
Lemma lem3884926 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3884921 _100455 s x a h1 h2 h3) (fun h4 : False => @lem3884628 _100455 x a h3)). Qed.
Lemma lem3884927 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884926 _100455 s x a h1 h2 h3) (@lem3884628 _100455 x a h3)). Qed.
Lemma lem3884928 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3884927 _100455 s x a h1 h2 h3) (fun h4 : False => @lem3884620 _100455 s a h1)). Qed.
Lemma lem3884929 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3884928 _100455 s x a h1 h2 h3) (@lem3884620 _100455 s a h1)). Qed.
Lemma lem3884930 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3884923 _100455 s x a h1 h2) (fun h3 : False => @lem3884616 _100455 x a h2)). Qed.
Lemma lem3884931 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3884930 _100455 s x a h1 h2) (@lem3884616 _100455 x a h2)). Qed.
Lemma lem3884932 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : (term59 _100455 s x) = False.
Proof. exact (prop_ext (fun h3 : term59 _100455 s x => @lem3884925 _100455 s x a h1 h2) (fun h3 : False => @lem3884600 _100455 s x h1)). Qed.
Lemma lem3884933 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term59 _100455 s x) (h2 : term54 _100455 s x a) : False.
Proof. exact (EQ_MP (@lem3884932 _100455 s x a h1 h2) (@lem3884600 _100455 s x h1)). Qed.
Lemma lem3884934 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : s a) (h2 : term52 _100455 s x a) : False.
Proof. exact (or_elim (@lem3884579 _100455 s x a h2) (fun h0 : x = a => @lem3884929 _100455 s x a h1 h2 h0) (fun h0 : term18 _100455 s x a => @lem3884905 _100455 s x a h2 h0)). Qed.
Lemma lem3884935 {_100455 : Type'} (s : _100455 -> Prop) (x : _100455) (a : _100455) (h1 : term54 _100455 s x a) : False.
Proof. exact (or_elim (@lem3884575 _100455 s x a h1) (fun h0 : term59 _100455 s x => @lem3884933 _100455 s x a h0 h1) (fun h0 : x = a => @lem3884931 _100455 s x a h1 h0)). Qed.
Lemma lem3884936 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : term42 _100455 s x a) (h2 : s a) : False.
Proof. exact (or_elim (@lem3884570 _100455 s x a h1) (fun h0 : term54 _100455 s x a => @lem3884935 _100455 s x a h0) (fun h0 : term52 _100455 s x a => @lem3884934 _100455 s x a h2 h0)). Qed.
Lemma lem3884937 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : term42 _100455 s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem3884936 _100455 x s a h1 h2) (fun h3 : False => @lem3884508 _100455 s a h2)). Qed.
Lemma lem3884938 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : term42 _100455 s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3884937 _100455 x s a h1 h2) (@lem3884508 _100455 s a h2)). Qed.
Lemma lem3884939 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : term42 _100455 s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem3884938 _100455 x s a h1 h2) (fun h3 : False => @lem3884462 _100455 s a h2)). Qed.
Lemma lem3884940 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : term42 _100455 s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3884939 _100455 x s a h1 h2) (@lem3884462 _100455 s a h2)). Qed.
Lemma lem3884941 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : term42 _100455 s x a) (h2 : s a) : (term42 _100455 s x a) = False.
Proof. exact (prop_ext (fun h3 : term42 _100455 s x a => @lem3884940 _100455 x s a h1 h2) (fun h3 : False => @lem3884456 _100455 s x a h1)). Qed.
Lemma lem3884942 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : term42 _100455 s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3884941 _100455 x s a h1 h2) (@lem3884456 _100455 s x a h1)). Qed.
Lemma lem3884943 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : s a) : term41 _100455 s x a.
Proof. exact (fun h0 : term42 _100455 s x a => @lem3884942 _100455 x s a h0 h1). Qed.
Lemma lem3884944 {_100455 : Type'} (x : _100455) (s : _100455 -> Prop) (a : _100455) (h1 : s a) : (s x) = (term20 _100455 s x a).
Proof. exact (EQ_MP (@lem3884455 _100455 s x a) (@lem3884943 _100455 x s a h1)). Qed.
Lemma lem3884949 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : s a) : term23 _100455 s a.
Proof. exact (fun x : _100455 => @lem3884944 _100455 x s a h1). Qed.
Lemma lem3884950 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term24 _100455 s a.
Proof. exact (fun h0 : s a => @lem3884949 _100455 s a h0). Qed.
Lemma lem3884955 {_100455 : Type'} (a : _100455) : term36 _100455 a.
Proof. exact (fun s : _100455 -> Prop => @lem3884950 _100455 s a). Qed.
Lemma lem3884960 {_100455 : Type'} : term40 _100455.
Proof. exact (fun a : _100455 => @lem3884955 _100455 a). Qed.
Lemma lem3884961 {_100455 : Type'} : term39 _100455.
Proof. exact (EQ_MP (@lem3884450 _100455) (@lem3884960 _100455)). Qed.
Lemma lem3884962 {_100455 : Type'} (a : _100455) : term76 _100455 a.
Proof. exact (@lem3884961 _100455 a). Qed.
Lemma lem3884963 {_100455 : Type'} (a : _100455) : (term76 _100455 a) = (term35 _100455 a).
Proof. exact (eq_refl (term76 _100455 a)). Qed.
Lemma lem3884964 {_100455 : Type'} (a : _100455) : term35 _100455 a.
Proof. exact (EQ_MP (@lem3884963 _100455 a) (@lem3884962 _100455 a)). Qed.
Lemma lem3884965 {_100455 : Type'} (a : _100455) (s : _100455 -> Prop) : term77 _100455 a s.
Proof. exact (@lem3884964 _100455 a s). Qed.
Lemma lem3884966 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : (term77 _100455 a s) = (term26 _100455 s a).
Proof. exact (eq_refl (term77 _100455 a s)). Qed.
Lemma lem3884967 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term26 _100455 s a.
Proof. exact (EQ_MP (@lem3884966 _100455 s a) (@lem3884965 _100455 a s)). Qed.
Lemma lem3884969 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term26 _100455 s a.
Proof. exact (@lem3884351 _100455 s a (@lem3884967 _100455 s a)). Qed.
Lemma lem3884970 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term27 _100455 s a) : False.
Proof. exact (@lem3884969 _100455 s a (@lem3884335 _100455 s a h1)). Qed.
Lemma lem3884971 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term27 _100455 s a) : (term27 _100455 s a) = False.
Proof. exact (prop_ext (fun h2 : term27 _100455 s a => @lem3884970 _100455 s a h1) (fun h2 : False => @lem3884335 _100455 s a h1)). Qed.
Lemma lem3884972 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) (h1 : term27 _100455 s a) : False.
Proof. exact (EQ_MP (@lem3884971 _100455 s a h1) (@lem3884335 _100455 s a h1)). Qed.
Lemma lem3884973 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term26 _100455 s a.
Proof. exact (fun h0 : term27 _100455 s a => @lem3884972 _100455 s a h0). Qed.
Lemma lem3884974 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term24 _100455 s a.
Proof. exact (EQ_MP (@lem3884334 _100455 s a) (@lem3884973 _100455 s a)). Qed.
Lemma lem3884975 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term5 _100455 s a.
Proof. exact (EQ_MP (@lem3884330 _100455 s a) (@lem3884974 _100455 s a)). Qed.
Lemma lem3884976 {_100455 : Type'} (s : _100455 -> Prop) (a : _100455) : term4 _100455 s a.
Proof. exact (EQ_MP (@lem3884264 _100455 s a) (@lem3884975 _100455 s a)). Qed.
Lemma lem3884977 {A : Type'} (s : A -> Prop) : term78 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem3884978 {A : Type'} (s : A -> Prop) : (term78 A s) = (term79 A s).
Proof. exact (eq_refl (term78 A s)). Qed.
Lemma lem3884979 {A : Type'} (s : A -> Prop) : term79 A s.
Proof. exact (EQ_MP (@lem3884978 A s) (@lem3884977 A s)). Qed.
Lemma lem3884980 {A : Type'} (s : A -> Prop) (x : A) : term80 A s x.
Proof. exact (@lem3884979 A s x). Qed.
Lemma lem3884981 {A : Type'} (x : A) (s : A -> Prop) : (term80 A s x) = ((term81 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term80 A s x)). Qed.
Lemma lem3884983 {A : Type'} : term82 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3884984 {A : Type'} (x : A) : term83 A x.
Proof. exact (@lem3884983 A x). Qed.
Lemma lem3884985 {A : Type'} (x : A) : (term83 A x) = (term84 A x).
Proof. exact (eq_refl (term83 A x)). Qed.
Lemma lem3884986 {A : Type'} (x : A) : term84 A x.
Proof. exact (EQ_MP (@lem3884985 A x) (@lem3884984 A x)). Qed.
Lemma lem3884987 {A : Type'} (x : A) (s : A -> Prop) : term85 A x s.
Proof. exact (@lem3884986 A x s). Qed.
Lemma lem3884988 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term86 A x s).
Proof. exact (eq_refl (term85 A x s)). Qed.
Lemma lem3884989 {A : Type'} (x : A) (s : A -> Prop) : term86 A x s.
Proof. exact (EQ_MP (@lem3884988 A x s) (@lem3884987 A x s)). Qed.
Lemma lem3884990 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3884991 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term87 A x s) = (term88 A x s).
Proof. exact (@lem3884989 A x s (@lem3884990 A s h1)). Qed.
Lemma lem3884998 {_100044 : Type'} (s : _100044 -> Prop) : term89 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3884999 {_100044 : Type'} (s : _100044 -> Prop) : (term89 _100044 s) = (term90 _100044 s).
Proof. exact (eq_refl (term89 _100044 s)). Qed.
Lemma lem3885000 {_100044 : Type'} (s : _100044 -> Prop) : term90 _100044 s.
Proof. exact (EQ_MP (@lem3884999 _100044 s) (@lem3884998 _100044 s)). Qed.
Lemma lem3885001 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term91 _100044 s n.
Proof. exact (@lem3885000 _100044 s n). Qed.
Lemma lem3885002 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term91 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term92 _100044 s n)).
Proof. exact (eq_refl (term91 _100044 s n)). Qed.
Lemma lem3885004 {A : Type'} (P : A -> Prop) : term93 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem3885005 {A : Type'} (P : A -> Prop) : (term93 A P) = (term94 A P).
Proof. exact (eq_refl (term93 A P)). Qed.
Lemma lem3885006 {A : Type'} (P : A -> Prop) : term94 A P.
Proof. exact (EQ_MP (@lem3885005 A P) (@lem3885004 A P)). Qed.
Lemma lem3885007 {A : Type'} (P : A -> Prop) (Q : Prop) : term95 A P Q.
Proof. exact (@lem3885006 A P Q). Qed.
Lemma lem3885008 {A : Type'} (P : A -> Prop) (Q : Prop) : (term95 A P Q) = ((term96 A P Q) = (term97 A P Q)).
Proof. exact (eq_refl (term95 A P Q)). Qed.
Lemma lem3885020 {_100455 : Type'} (s : _100455 -> Prop) : term98 _100455 s.
Proof. exact (fun a : _100455 => @lem3884976 _100455 s a). Qed.
Lemma lem3885021 {_100455 : Type'} : term99 _100455.
Proof. exact (fun s : _100455 -> Prop => @lem3885020 _100455 s). Qed.
Lemma lem3885023 {A : Type'} (s : A -> Prop) (h1 : (term100 A s) = (term101 A s)) : (term100 A s) = (term101 A s).
Proof. exact (h1). Qed.
Lemma lem3885024 {A : Type'} (s : A -> Prop) (h1 : (term100 A s) = (term101 A s)) : (term101 A s) = (term100 A s).
Proof. exact (SYM (@lem3885023 A s h1)). Qed.
Lemma lem3885025 {A : Type'} (s : A -> Prop) (h1 : (term101 A s) = (term100 A s)) : (term101 A s) = (term100 A s).
Proof. exact (h1). Qed.
Lemma lem3885026 {A : Type'} (s : A -> Prop) (h1 : (term101 A s) = (term100 A s)) : (term100 A s) = (term101 A s).
Proof. exact (SYM (@lem3885025 A s h1)). Qed.
Lemma lem3885027 {A : Type'} (s : A -> Prop) : ((term100 A s) = (term101 A s)) = ((term101 A s) = (term100 A s)).
Proof. exact (prop_ext (fun h1 : (term100 A s) = (term101 A s) => @lem3885024 A s h1) (fun h1 : (term101 A s) = (term100 A s) => @lem3885026 A s h1)). Qed.
Lemma lem3885028 {A : Type'} : (term102 A) = (term103 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3885027 A s)). Qed.
Lemma lem3885029 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3885030 {A : Type'} : (term104 A) = (term105 A).
Proof. exact (MK_COMB (@lem3885029 A) (@lem3885028 A)). Qed.
Lemma lem3885031 {A : Type'} : term105 A.
Proof. exact (EQ_MP (@lem3885030 A) (@lem3216368 A)). Qed.
Lemma lem3885032 {A : Type'} (s : A -> Prop) : term106 A s.
Proof. exact (@lem3885031 A s). Qed.
Lemma lem3885033 {A : Type'} (s : A -> Prop) : (term106 A s) = ((term101 A s) = (term100 A s)).
Proof. exact (eq_refl (term106 A s)). Qed.
Lemma lem3885035 {A : Type'} (s : A -> Prop) : term107 A s.
Proof. exact (@lem3867912 A s). Qed.
Lemma lem3885036 {A : Type'} (s : A -> Prop) : (term107 A s) = (term108 A s).
Proof. exact (eq_refl (term107 A s)). Qed.
Lemma lem3885037 {A : Type'} (s : A -> Prop) : term108 A s.
Proof. exact (EQ_MP (@lem3885036 A s) (@lem3885035 A s)). Qed.
Lemma lem3885038 {A : Type'} (s : A -> Prop) (n : nat) : term109 A s n.
Proof. exact (@lem3885037 A s n). Qed.
Lemma lem3885039 {A : Type'} (s : A -> Prop) (n : nat) : (term109 A s n) = ((term110 A s n) = (term111 A s n)).
Proof. exact (eq_refl (term109 A s n)). Qed.
Lemma lem3885041 {A : Type'} (s : A -> Prop) : term112 A s.
Proof. exact (@lem3864294 A s). Qed.
Lemma lem3885042 {A : Type'} (s : A -> Prop) : (term112 A s) = ((term113 A s) = (s = (@EMPTY A))).
Proof. exact (eq_refl (term112 A s)). Qed.
Lemma lem3885049 {A : Type'} (s : A -> Prop) : (term113 A s) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3885042 A s) (@lem3885041 A s)). Qed.
Lemma lem3885050 {_100499 : Type'} (s : _100499 -> Prop) : (term113 _100499 s) = (s = (@EMPTY _100499)).
Proof. exact (@lem3885049 _100499 s). Qed.
Lemma lem3885053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3885054 {_100499 : Type'} (s : _100499 -> Prop) : (term114 _100499 s) = (term115 _100499 s).
Proof. exact (MK_COMB (@lem3885053) (@lem3885050 _100499 s)). Qed.
Lemma lem3885057 {_100499 : Type'} (s : _100499 -> Prop) : (s = (@EMPTY _100499)) = (s = (@EMPTY _100499)).
Proof. exact (eq_refl (s = (@EMPTY _100499))). Qed.
Lemma lem3885058 {_100499 : Type'} (s : _100499 -> Prop) : ((term113 _100499 s) = (s = (@EMPTY _100499))) = ((s = (@EMPTY _100499)) = (s = (@EMPTY _100499))).
Proof. exact (MK_COMB (@lem3885054 _100499 s) (@lem3885057 _100499 s)). Qed.
Lemma lem3885060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3885061 (x : Prop) : (x = x) = True.
Proof. exact (@lem3885060 Prop x). Qed.
Lemma lem3885062 {_100499 : Type'} (s : _100499 -> Prop) : ((s = (@EMPTY _100499)) = (s = (@EMPTY _100499))) = True.
Proof. exact (@lem3885061 (s = (@EMPTY _100499))). Qed.
Lemma lem3885063 {_100499 : Type'} (s : _100499 -> Prop) : ((term113 _100499 s) = (s = (@EMPTY _100499))) = True.
Proof. exact (TRANS (@lem3885058 _100499 s) (@lem3885062 _100499 s)). Qed.
Lemma lem3885064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885065 {_100499 : Type'} (s : _100499 -> Prop) : (term116 _100499 s) = (and True).
Proof. exact (MK_COMB (@lem3885064) (@lem3885063 _100499 s)). Qed.
Lemma lem3885082 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : ((term110 _100499 s n) = (term117 _100499 n s)) = ((term110 _100499 s n) = (term117 _100499 n s)).
Proof. exact (eq_refl ((term110 _100499 s n) = (term117 _100499 n s))). Qed.
Lemma lem3885083 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term118 _100499 n s) = (term119 _100499 n s).
Proof. exact (MK_COMB (@lem3885065 _100499 s) (@lem3885082 _100499 n s)). Qed.
Lemma lem3885085 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3885086 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term119 _100499 n s) = ((term110 _100499 s n) = (term117 _100499 n s)).
Proof. exact (@lem3885085 ((term110 _100499 s n) = (term117 _100499 n s))). Qed.
Lemma lem3885103 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term118 _100499 n s) = ((term110 _100499 s n) = (term117 _100499 n s)).
Proof. exact (TRANS (@lem3885083 _100499 n s) (@lem3885086 _100499 n s)). Qed.
Lemma lem3885104 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : ((term110 _100499 s n) = (term117 _100499 n s)) = (term118 _100499 n s).
Proof. exact (SYM (@lem3885103 _100499 n s)). Qed.
Lemma lem3885108 {A : Type'} (s : A -> Prop) (n : nat) : (term110 A s n) = (term111 A s n).
Proof. exact (EQ_MP (@lem3885039 A s n) (@lem3885038 A s n)). Qed.
Lemma lem3885109 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term110 _100499 s n) = (term111 _100499 s n).
Proof. exact (@lem3885108 _100499 s n). Qed.
Lemma lem3885113 {A : Type'} (s : A -> Prop) : (term101 A s) = (term100 A s).
Proof. exact (EQ_MP (@lem3885033 A s) (@lem3885032 A s)). Qed.
Lemma lem3885114 {_100499 : Type'} (s : _100499 -> Prop) : (term101 _100499 s) = (term100 _100499 s).
Proof. exact (@lem3885113 _100499 s). Qed.
Lemma lem3885119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885120 {_100499 : Type'} (s : _100499 -> Prop) : (term120 _100499 s) = (term121 _100499 s).
Proof. exact (MK_COMB (@lem3885119) (@lem3885114 _100499 s)). Qed.
Lemma lem3885127 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term122 _100499 s n) = (term122 _100499 s n).
Proof. exact (eq_refl (term122 _100499 s n)). Qed.
Lemma lem3885128 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term111 _100499 s n) = (term123 _100499 s n).
Proof. exact (MK_COMB (@lem3885120 _100499 s) (@lem3885127 _100499 s n)). Qed.
Lemma lem3885131 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term110 _100499 s n) = (term123 _100499 s n).
Proof. exact (TRANS (@lem3885109 _100499 s n) (@lem3885128 _100499 s n)). Qed.
Lemma lem3885132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3885133 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term124 _100499 s n) = (term125 _100499 s n).
Proof. exact (MK_COMB (@lem3885132) (@lem3885131 _100499 s n)). Qed.
Lemma lem3885148 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term117 _100499 n s) = (term117 _100499 n s).
Proof. exact (eq_refl (term117 _100499 n s)). Qed.
Lemma lem3885149 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term126 _100499 n s) = (term127 _100499 n s).
Proof. exact (MK_COMB (@lem3885133 _100499 s n) (@lem3885148 _100499 n s)). Qed.
Lemma lem3885152 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term127 _100499 n s) = (term126 _100499 n s).
Proof. exact (SYM (@lem3885149 _100499 n s)). Qed.
Lemma lem3885154 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3885155 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term127 _100499 n s) = (term128 _100499 n s).
Proof. exact (@lem3885154 (term127 _100499 n s)). Qed.
Lemma lem3885156 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term128 _100499 n s) = (term127 _100499 n s).
Proof. exact (SYM (@lem3885155 _100499 n s)). Qed.
Lemma lem3885157 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : term129 _100499 n s.
Proof. exact (h1). Qed.
Lemma lem3885158 {_100499 : Type'} : term99 _100499.
Proof. exact (@lem3885021 _100499). Qed.
Lemma lem3885162 {_100499 : Type'} : term130 _100499.
Proof. exact (@lem3205803 _100499). Qed.
Lemma lem3885164 {_100499 : Type'} : term131 _100499.
Proof. exact (@lem3205803 (_100499 -> Prop)). Qed.
Lemma lem3885167 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term132 _100499 n s) : term132 _100499 n s.
Proof. exact (h1). Qed.
Lemma lem3885168 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term133 _100499 n s.
Proof. exact (fun h0 : term132 _100499 n s => @lem3885167 _100499 n s h0). Qed.
Lemma lem3885169 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term133 _100499 n s) : term133 _100499 n s.
Proof. exact (h1). Qed.
Lemma lem3885170 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term132 _100499 n s) : term132 _100499 n s.
Proof. exact (h1). Qed.
Lemma lem3885171 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term132 _100499 n s) (h2 : term133 _100499 n s) : term132 _100499 n s.
Proof. exact (@lem3885169 _100499 n s h2 (@lem3885170 _100499 n s h1)). Qed.
Lemma lem3885172 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term132 _100499 n s) : term134 _100499 n s.
Proof. exact (fun h0 : term133 _100499 n s => @lem3885171 _100499 n s h1 h0). Qed.
Lemma lem3885173 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term133 _100499 n s) : term133 _100499 n s.
Proof. exact (h1). Qed.
Lemma lem3885174 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term132 _100499 n s) (h2 : term133 _100499 n s) : term132 _100499 n s.
Proof. exact (@lem3885172 _100499 n s h1 (@lem3885173 _100499 n s h2)). Qed.
Lemma lem3885175 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term133 _100499 n s) : term133 _100499 n s.
Proof. exact (fun h0 : term132 _100499 n s => @lem3885174 _100499 n s h0 h1). Qed.
Lemma lem3885176 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term135 _100499 n s.
Proof. exact (fun h0 : term133 _100499 n s => @lem3885175 _100499 n s h0). Qed.
Lemma lem3885179 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term133 _100499 n s.
Proof. exact (@lem3885176 _100499 n s (@lem3885168 _100499 n s)). Qed.
Lemma lem3885180 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term133 _100499 n s.
Proof. exact (@lem3885179 _100499 n s). Qed.
Lemma lem3885294 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3885295 {_100499 : Type'} : (term136 _100499) = (term137 _100499).
Proof. exact (@lem3885294 (term99 _100499)). Qed.
Lemma lem3885306 {_100499 : Type'} : (term138 _100499) = (term138 _100499).
Proof. exact (eq_refl (term138 _100499)). Qed.
Lemma lem3885307 {_100499 : Type'} : (term139 _100499) = (term140 _100499).
Proof. exact (MK_COMB (@lem3885306 _100499) (@lem3885295 _100499)). Qed.
Lemma lem3885310 {_100499 : Type'} : (term141 _100499) = (term141 _100499).
Proof. exact (eq_refl (term141 _100499)). Qed.
Lemma lem3885311 {_100499 : Type'} : (term142 _100499) = (term143 _100499).
Proof. exact (MK_COMB (@lem3885310 _100499) (@lem3885307 _100499)). Qed.
Lemma lem3885314 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term144 _100499 n s) = (term144 _100499 n s).
Proof. exact (eq_refl (term144 _100499 n s)). Qed.
Lemma lem3885315 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term132 _100499 n s) = (term145 _100499 n s).
Proof. exact (MK_COMB (@lem3885314 _100499 n s) (@lem3885311 _100499)). Qed.
Lemma lem3885318 {_100499 : Type'} (s : _100499 -> Prop) : (term146 _100499 s) = (term147 _100499 s).
Proof. exact (fun_ext (fun n : nat => @lem3885315 _100499 n s)). Qed.
Lemma lem3885319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3885320 {_100499 : Type'} (s : _100499 -> Prop) : (term148 _100499 s) = (term149 _100499 s).
Proof. exact (MK_COMB (@lem3885319) (@lem3885318 _100499 s)). Qed.
Lemma lem3885325 {_100499 : Type'} : (term150 _100499) = (term151 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3885320 _100499 s)). Qed.
Lemma lem3885326 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885335 {_100499 : Type'} : (term152 _100499) = (term153 _100499).
Proof. exact (MK_COMB (@lem3885326 _100499) (@lem3885325 _100499)). Qed.
Lemma lem3885340 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) : (term4 _100499 s a) = (term4 _100499 s a).
Proof. exact (eq_refl (term4 _100499 s a)). Qed.
Lemma lem3885341 {_100499 : Type'} (s : _100499 -> Prop) : (term154 _100499 s) = (term154 _100499 s).
Proof. exact (fun_ext (fun a : _100499 => @lem3885340 _100499 s a)). Qed.
Lemma lem3885342 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885343 {_100499 : Type'} (s : _100499 -> Prop) : (term98 _100499 s) = (term98 _100499 s).
Proof. exact (MK_COMB (@lem3885342 _100499) (@lem3885341 _100499 s)). Qed.
Lemma lem3885344 {_100499 : Type'} : (term155 _100499) = (term155 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3885343 _100499 s)). Qed.
Lemma lem3885345 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885346 {_100499 : Type'} : (term99 _100499) = (term99 _100499).
Proof. exact (MK_COMB (@lem3885345 _100499) (@lem3885344 _100499)). Qed.
Lemma lem3885347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3885348 {_100499 : Type'} : (term137 _100499) = (term137 _100499).
Proof. exact (MK_COMB (@lem3885347) (@lem3885346 _100499)). Qed.
Lemma lem3885359 {_100499 : Type'} (s : type686 _100499) (x : _100499 -> Prop) (y : _100499 -> Prop) : ((term156 _100499 x s y) = (term157 _100499 s x y)) = ((term156 _100499 x s y) = (term157 _100499 s x y)).
Proof. exact (eq_refl ((term156 _100499 x s y) = (term157 _100499 s x y))). Qed.
Lemma lem3885360 {_100499 : Type'} (s : type686 _100499) (x : _100499 -> Prop) : (term158 _100499 s x) = (term158 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 -> Prop => @lem3885359 _100499 s x y)). Qed.
Lemma lem3885361 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885362 {_100499 : Type'} (s : type686 _100499) (x : _100499 -> Prop) : (term159 _100499 s x) = (term159 _100499 s x).
Proof. exact (MK_COMB (@lem3885361 _100499) (@lem3885360 _100499 s x)). Qed.
Lemma lem3885363 {_100499 : Type'} (s : type686 _100499) : (term160 _100499 s) = (term160 _100499 s).
Proof. exact (fun_ext (fun x : _100499 -> Prop => @lem3885362 _100499 s x)). Qed.
Lemma lem3885364 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885365 {_100499 : Type'} (s : type686 _100499) : (term161 _100499 s) = (term161 _100499 s).
Proof. exact (MK_COMB (@lem3885364 _100499) (@lem3885363 _100499 s)). Qed.
Lemma lem3885366 {_100499 : Type'} : (term162 _100499) = (term162 _100499).
Proof. exact (fun_ext (fun s : type686 _100499 => @lem3885365 _100499 s)). Qed.
Lemma lem3885367 {_100499 : Type'} : (@all ((_100499 -> Prop) -> Prop)) = (@all ((_100499 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_100499 -> Prop) -> Prop))). Qed.
Lemma lem3885368 {_100499 : Type'} : (term131 _100499) = (term131 _100499).
Proof. exact (MK_COMB (@lem3885367 _100499) (@lem3885366 _100499)). Qed.
Lemma lem3885369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3885370 {_100499 : Type'} : (term138 _100499) = (term138 _100499).
Proof. exact (MK_COMB (@lem3885369) (@lem3885368 _100499)). Qed.
Lemma lem3885371 {_100499 : Type'} : (term140 _100499) = (term140 _100499).
Proof. exact (MK_COMB (@lem3885370 _100499) (@lem3885348 _100499)). Qed.
Lemma lem3885382 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : ((term13 _100499 x s y) = (term14 _100499 s x y)) = ((term13 _100499 x s y) = (term14 _100499 s x y)).
Proof. exact (eq_refl ((term13 _100499 x s y) = (term14 _100499 s x y))). Qed.
Lemma lem3885383 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term163 _100499 s x) = (term163 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3885382 _100499 s x y)). Qed.
Lemma lem3885384 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885385 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term164 _100499 s x) = (term164 _100499 s x).
Proof. exact (MK_COMB (@lem3885384 _100499) (@lem3885383 _100499 s x)). Qed.
Lemma lem3885386 {_100499 : Type'} (s : _100499 -> Prop) : (term165 _100499 s) = (term165 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885385 _100499 s x)). Qed.
Lemma lem3885387 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885388 {_100499 : Type'} (s : _100499 -> Prop) : (term166 _100499 s) = (term166 _100499 s).
Proof. exact (MK_COMB (@lem3885387 _100499) (@lem3885386 _100499 s)). Qed.
Lemma lem3885389 {_100499 : Type'} : (term167 _100499) = (term167 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3885388 _100499 s)). Qed.
Lemma lem3885390 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885391 {_100499 : Type'} : (term130 _100499) = (term130 _100499).
Proof. exact (MK_COMB (@lem3885390 _100499) (@lem3885389 _100499)). Qed.
Lemma lem3885392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3885393 {_100499 : Type'} : (term141 _100499) = (term141 _100499).
Proof. exact (MK_COMB (@lem3885392) (@lem3885391 _100499)). Qed.
Lemma lem3885394 {_100499 : Type'} : (term143 _100499) = (term143 _100499).
Proof. exact (MK_COMB (@lem3885393 _100499) (@lem3885371 _100499)). Qed.
Lemma lem3885405 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term168 _100499 n s a t) = (term168 _100499 n s a t).
Proof. exact (eq_refl (term168 _100499 n s a t)). Qed.
Lemma lem3885406 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term169 _100499 n s a) = (term169 _100499 n s a).
Proof. exact (fun_ext (fun t : _100499 -> Prop => @lem3885405 _100499 n s a t)). Qed.
Lemma lem3885407 {_100499 : Type'} : (@ex (_100499 -> Prop)) = (@ex (_100499 -> Prop)).
Proof. exact (eq_refl (@ex (_100499 -> Prop))). Qed.
Lemma lem3885408 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term170 _100499 n s a) = (term170 _100499 n s a).
Proof. exact (MK_COMB (@lem3885407 _100499) (@lem3885406 _100499 n s a)). Qed.
Lemma lem3885409 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term171 _100499 n s) = (term171 _100499 n s).
Proof. exact (fun_ext (fun a : _100499 => @lem3885408 _100499 n s a)). Qed.
Lemma lem3885410 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3885411 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term117 _100499 n s) = (term117 _100499 n s).
Proof. exact (MK_COMB (@lem3885410 _100499) (@lem3885409 _100499 n s)). Qed.
Lemma lem3885416 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (n : nat) : (term172 _100499 s a n) = (term172 _100499 s a n).
Proof. exact (eq_refl (term172 _100499 s a n)). Qed.
Lemma lem3885417 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term173 _100499 s n) = (term173 _100499 s n).
Proof. exact (fun_ext (fun a : _100499 => @lem3885416 _100499 s a n)). Qed.
Lemma lem3885418 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885419 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term122 _100499 s n) = (term122 _100499 s n).
Proof. exact (MK_COMB (@lem3885418 _100499) (@lem3885417 _100499 s n)). Qed.
Lemma lem3885420 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (@IN _100499 x s) = (@IN _100499 x s).
Proof. exact (eq_refl (@IN _100499 x s)). Qed.
Lemma lem3885421 {_100499 : Type'} (s : _100499 -> Prop) : (term174 _100499 s) = (term174 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885420 _100499 x s)). Qed.
Lemma lem3885422 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3885423 {_100499 : Type'} (s : _100499 -> Prop) : (term100 _100499 s) = (term100 _100499 s).
Proof. exact (MK_COMB (@lem3885422 _100499) (@lem3885421 _100499 s)). Qed.
Lemma lem3885424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885425 {_100499 : Type'} (s : _100499 -> Prop) : (term121 _100499 s) = (term121 _100499 s).
Proof. exact (MK_COMB (@lem3885424) (@lem3885423 _100499 s)). Qed.
Lemma lem3885426 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term123 _100499 s n) = (term123 _100499 s n).
Proof. exact (MK_COMB (@lem3885425 _100499 s) (@lem3885419 _100499 s n)). Qed.
Lemma lem3885427 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3885428 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term125 _100499 s n) = (term125 _100499 s n).
Proof. exact (MK_COMB (@lem3885427) (@lem3885426 _100499 s n)). Qed.
Lemma lem3885429 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term127 _100499 n s) = (term127 _100499 n s).
Proof. exact (MK_COMB (@lem3885428 _100499 s n) (@lem3885411 _100499 n s)). Qed.
Lemma lem3885430 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3885431 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term129 _100499 n s) = (term129 _100499 n s).
Proof. exact (MK_COMB (@lem3885430) (@lem3885429 _100499 n s)). Qed.
Lemma lem3885432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3885433 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term144 _100499 n s) = (term144 _100499 n s).
Proof. exact (MK_COMB (@lem3885432) (@lem3885431 _100499 n s)). Qed.
Lemma lem3885434 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term145 _100499 n s) = (term145 _100499 n s).
Proof. exact (MK_COMB (@lem3885433 _100499 n s) (@lem3885394 _100499)). Qed.
Lemma lem3885435 {_100499 : Type'} (s : _100499 -> Prop) : (term147 _100499 s) = (term147 _100499 s).
Proof. exact (fun_ext (fun n : nat => @lem3885434 _100499 n s)). Qed.
Lemma lem3885436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3885437 {_100499 : Type'} (s : _100499 -> Prop) : (term149 _100499 s) = (term149 _100499 s).
Proof. exact (MK_COMB (@lem3885436) (@lem3885435 _100499 s)). Qed.
Lemma lem3885438 {_100499 : Type'} : (term151 _100499) = (term151 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3885437 _100499 s)). Qed.
Lemma lem3885439 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885440 {_100499 : Type'} : (term153 _100499) = (term153 _100499).
Proof. exact (MK_COMB (@lem3885439 _100499) (@lem3885438 _100499)). Qed.
Lemma lem3885549 {_100499 : Type'} : (term152 _100499) = (term153 _100499).
Proof. exact (TRANS (@lem3885335 _100499) (@lem3885440 _100499)). Qed.
Lemma lem3885550 {_100499 : Type'} : (term153 _100499) = (term152 _100499).
Proof. exact (SYM (@lem3885549 _100499)). Qed.
Lemma lem3885551 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : term129 _100499 n s.
Proof. exact (h1). Qed.
Lemma lem3885552 {_100499 : Type'} (h1 : term130 _100499) : term130 _100499.
Proof. exact (h1). Qed.
Lemma lem3885554 {_100499 : Type'} (h1 : term99 _100499) : term99 _100499.
Proof. exact (h1). Qed.
Lemma lem3885555 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (@IN _100499 x s) = (@IN _100499 x s).
Proof. exact (eq_refl (@IN _100499 x s)). Qed.
Lemma lem3885556 {_100499 : Type'} (s : _100499 -> Prop) : (term174 _100499 s) = (term174 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885555 _100499 x s)). Qed.
Lemma lem3885557 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3885558 {_100499 : Type'} (s : _100499 -> Prop) : (term100 _100499 s) = (term100 _100499 s).
Proof. exact (MK_COMB (@lem3885557 _100499) (@lem3885556 _100499 s)). Qed.
Lemma lem3885565 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (n : nat) : (term172 _100499 s a n) = (term175 _100499 s a n).
Proof. exact (@lem17265 (@IN _100499 a s) (term176 _100499 s a n)). Qed.
Lemma lem3885566 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term173 _100499 s n) = (term177 _100499 s n).
Proof. exact (fun_ext (fun a : _100499 => @lem3885565 _100499 s a n)). Qed.
Lemma lem3885567 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885568 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term122 _100499 s n) = (term178 _100499 s n).
Proof. exact (MK_COMB (@lem3885567 _100499) (@lem3885566 _100499 s n)). Qed.
Lemma lem3885569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885570 {_100499 : Type'} (s : _100499 -> Prop) : (term121 _100499 s) = (term121 _100499 s).
Proof. exact (MK_COMB (@lem3885569) (@lem3885558 _100499 s)). Qed.
Lemma lem3885571 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term123 _100499 s n) = (term179 _100499 s n).
Proof. exact (MK_COMB (@lem3885570 _100499 s) (@lem3885568 _100499 s n)). Qed.
Lemma lem3885575 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) : (term180 _100499 a t) = (@IN _100499 a t).
Proof. exact (@lem16933 (@IN _100499 a t)). Qed.
Lemma lem3885576 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term181 _100499 s a t) = (term181 _100499 s a t).
Proof. exact (eq_refl (term181 _100499 s a t)). Qed.
Lemma lem3885577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3885578 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) : (term182 _100499 a t) = (term183 _100499 a t).
Proof. exact (MK_COMB (@lem3885577) (@lem3885575 _100499 a t)). Qed.
Lemma lem3885579 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term184 _100499 s a t) = (term185 _100499 s a t).
Proof. exact (MK_COMB (@lem3885578 _100499 a t) (@lem3885576 _100499 s a t)). Qed.
Lemma lem3885580 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term186 _100499 s a t) = (term184 _100499 s a t).
Proof. exact (@lem17045 (term187 _100499 a t) (s = (@INSERT _100499 a t))). Qed.
Lemma lem3885581 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term186 _100499 s a t) = (term185 _100499 s a t).
Proof. exact (TRANS (@lem3885580 _100499 s a t) (@lem3885579 _100499 s a t)). Qed.
Lemma lem3885583 {_100499 : Type'} (t : _100499 -> Prop) (n : nat) : (term188 _100499 t n) = (term188 _100499 t n).
Proof. exact (eq_refl (term188 _100499 t n)). Qed.
Lemma lem3885584 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term189 _100499 n s a t) = (term190 _100499 n s a t).
Proof. exact (MK_COMB (@lem3885583 _100499 t n) (@lem3885581 _100499 s a t)). Qed.
Lemma lem3885585 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term191 _100499 n s a t) = (term189 _100499 n s a t).
Proof. exact (@lem17045 (@HAS_SIZE _100499 t n) (term192 _100499 s a t)). Qed.
Lemma lem3885586 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term191 _100499 n s a t) = (term190 _100499 n s a t).
Proof. exact (TRANS (@lem3885585 _100499 n s a t) (@lem3885584 _100499 n s a t)). Qed.
Lemma lem3885587 {_100499 : Type'} (P : type686 _100499) : (term193 _100499 P) = (term194 _100499 P).
Proof. exact (@lem18394 (_100499 -> Prop) P). Qed.
Lemma lem3885588 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term195 _100499 n s a) = (term196 _100499 n s a).
Proof. exact (@lem3885587 _100499 (term169 _100499 n s a)). Qed.
Lemma lem3885589 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term197 _100499 n s a t) = (term168 _100499 n s a t).
Proof. exact (eq_refl (term197 _100499 n s a t)). Qed.
Lemma lem3885590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3885591 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term198 _100499 n s a t) = (term191 _100499 n s a t).
Proof. exact (MK_COMB (@lem3885590) (@lem3885589 _100499 n s a t)). Qed.
Lemma lem3885592 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term198 _100499 n s a t) = (term190 _100499 n s a t).
Proof. exact (TRANS (@lem3885591 _100499 n s a t) (@lem3885586 _100499 n s a t)). Qed.
Lemma lem3885593 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term199 _100499 n s a) = (term200 _100499 n s a).
Proof. exact (fun_ext (fun t : _100499 -> Prop => @lem3885592 _100499 n s a t)). Qed.
Lemma lem3885594 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885595 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term196 _100499 n s a) = (term201 _100499 n s a).
Proof. exact (MK_COMB (@lem3885594 _100499) (@lem3885593 _100499 n s a)). Qed.
Lemma lem3885596 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term195 _100499 n s a) = (term201 _100499 n s a).
Proof. exact (TRANS (@lem3885588 _100499 n s a) (@lem3885595 _100499 n s a)). Qed.
Lemma lem3885597 {_100499 : Type'} (P : _100499 -> Prop) : (term202 _100499 P) = (term203 _100499 P).
Proof. exact (@lem18394 _100499 P). Qed.
Lemma lem3885598 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term204 _100499 n s) = (term205 _100499 n s).
Proof. exact (@lem3885597 _100499 (term171 _100499 n s)). Qed.
Lemma lem3885599 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term206 _100499 n s a) = (term170 _100499 n s a).
Proof. exact (eq_refl (term206 _100499 n s a)). Qed.
Lemma lem3885600 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3885601 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term207 _100499 n s a) = (term195 _100499 n s a).
Proof. exact (MK_COMB (@lem3885600) (@lem3885599 _100499 n s a)). Qed.
Lemma lem3885602 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term207 _100499 n s a) = (term201 _100499 n s a).
Proof. exact (TRANS (@lem3885601 _100499 n s a) (@lem3885596 _100499 n s a)). Qed.
Lemma lem3885603 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term208 _100499 n s) = (term209 _100499 n s).
Proof. exact (fun_ext (fun a : _100499 => @lem3885602 _100499 n s a)). Qed.
Lemma lem3885604 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885605 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term205 _100499 n s) = (term210 _100499 n s).
Proof. exact (MK_COMB (@lem3885604 _100499) (@lem3885603 _100499 n s)). Qed.
Lemma lem3885606 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term204 _100499 n s) = (term210 _100499 n s).
Proof. exact (TRANS (@lem3885598 _100499 n s) (@lem3885605 _100499 n s)). Qed.
Lemma lem3885607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885608 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term211 _100499 s n) = (term212 _100499 s n).
Proof. exact (MK_COMB (@lem3885607) (@lem3885571 _100499 s n)). Qed.
Lemma lem3885609 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term213 _100499 n s) = (term214 _100499 n s).
Proof. exact (MK_COMB (@lem3885608 _100499 s n) (@lem3885606 _100499 n s)). Qed.
Lemma lem3885610 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term129 _100499 n s) = (term213 _100499 n s).
Proof. exact (@lem17362 (term123 _100499 s n) (term117 _100499 n s)). Qed.
Lemma lem3885611 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term129 _100499 n s) = (term214 _100499 n s).
Proof. exact (TRANS (@lem3885610 _100499 n s) (@lem3885609 _100499 n s)). Qed.
Lemma lem3885718 {A : Type'} (P : A -> Prop) (Q : Prop) : (term215 A P Q) = (term216 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3885719 {_100499 : Type'} (P : _100499 -> Prop) (Q : Prop) : (term215 _100499 P Q) = (term216 _100499 P Q).
Proof. exact (@lem3885718 _100499 P Q). Qed.
Lemma lem3885720 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term217 _100499 s n) = (term218 _100499 s n).
Proof. exact (@lem3885719 _100499 (term174 _100499 s) (term178 _100499 s n)). Qed.
Lemma lem3885721 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term219 _100499 s x) = (@IN _100499 x s).
Proof. exact (eq_refl (term219 _100499 s x)). Qed.
Lemma lem3885722 {_100499 : Type'} (s : _100499 -> Prop) : (term220 _100499 s) = (term174 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885721 _100499 x s)). Qed.
Lemma lem3885723 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3885724 {_100499 : Type'} (s : _100499 -> Prop) : (term221 _100499 s) = (term100 _100499 s).
Proof. exact (MK_COMB (@lem3885723 _100499) (@lem3885722 _100499 s)). Qed.
Lemma lem3885725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885726 {_100499 : Type'} (s : _100499 -> Prop) : (term222 _100499 s) = (term121 _100499 s).
Proof. exact (MK_COMB (@lem3885725) (@lem3885724 _100499 s)). Qed.
Lemma lem3885727 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term178 _100499 s n) = (term178 _100499 s n).
Proof. exact (eq_refl (term178 _100499 s n)). Qed.
Lemma lem3885728 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term217 _100499 s n) = (term179 _100499 s n).
Proof. exact (MK_COMB (@lem3885726 _100499 s) (@lem3885727 _100499 s n)). Qed.
Lemma lem3885729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3885730 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term223 _100499 s n) = (term224 _100499 s n).
Proof. exact (MK_COMB (@lem3885729) (@lem3885728 _100499 s n)). Qed.
Lemma lem3885731 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term219 _100499 s x) = (@IN _100499 x s).
Proof. exact (eq_refl (term219 _100499 s x)). Qed.
Lemma lem3885732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885733 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term225 _100499 s x) = (term15 _100499 x s).
Proof. exact (MK_COMB (@lem3885732) (@lem3885731 _100499 x s)). Qed.
Lemma lem3885734 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term178 _100499 s n) = (term178 _100499 s n).
Proof. exact (eq_refl (term178 _100499 s n)). Qed.
Lemma lem3885735 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) (n : nat) : (term226 _100499 x s n) = (term227 _100499 x s n).
Proof. exact (MK_COMB (@lem3885733 _100499 x s) (@lem3885734 _100499 s n)). Qed.
Lemma lem3885736 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term228 _100499 s n) = (term229 _100499 s n).
Proof. exact (fun_ext (fun x : _100499 => @lem3885735 _100499 x s n)). Qed.
Lemma lem3885737 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3885738 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term218 _100499 s n) = (term230 _100499 s n).
Proof. exact (MK_COMB (@lem3885737 _100499) (@lem3885736 _100499 s n)). Qed.
Lemma lem3885739 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : ((term217 _100499 s n) = (term218 _100499 s n)) = ((term179 _100499 s n) = (term230 _100499 s n)).
Proof. exact (MK_COMB (@lem3885730 _100499 s n) (@lem3885738 _100499 s n)). Qed.
Lemma lem3885740 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term179 _100499 s n) = (term230 _100499 s n).
Proof. exact (EQ_MP (@lem3885739 _100499 s n) (@lem3885720 _100499 s n)). Qed.
Lemma lem3885741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885742 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term212 _100499 s n) = (term231 _100499 s n).
Proof. exact (MK_COMB (@lem3885741) (@lem3885740 _100499 s n)). Qed.
Lemma lem3885743 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term210 _100499 n s) = (term210 _100499 n s).
Proof. exact (eq_refl (term210 _100499 n s)). Qed.
Lemma lem3885744 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term214 _100499 n s) = (term232 _100499 n s).
Proof. exact (MK_COMB (@lem3885742 _100499 s n) (@lem3885743 _100499 n s)). Qed.
Lemma lem3885746 {A : Type'} (P : A -> Prop) (Q : Prop) : (term215 A P Q) = (term216 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3885747 {_100499 : Type'} (P : _100499 -> Prop) (Q : Prop) : (term215 _100499 P Q) = (term216 _100499 P Q).
Proof. exact (@lem3885746 _100499 P Q). Qed.
Lemma lem3885748 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term233 _100499 n s) = (term234 _100499 n s).
Proof. exact (@lem3885747 _100499 (term229 _100499 s n) (term210 _100499 n s)). Qed.
Lemma lem3885749 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) (n : nat) : (term235 _100499 s n x) = (term227 _100499 x s n).
Proof. exact (eq_refl (term235 _100499 s n x)). Qed.
Lemma lem3885750 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term236 _100499 s n) = (term229 _100499 s n).
Proof. exact (fun_ext (fun x : _100499 => @lem3885749 _100499 x s n)). Qed.
Lemma lem3885751 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3885752 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term237 _100499 s n) = (term230 _100499 s n).
Proof. exact (MK_COMB (@lem3885751 _100499) (@lem3885750 _100499 s n)). Qed.
Lemma lem3885753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885754 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term238 _100499 s n) = (term231 _100499 s n).
Proof. exact (MK_COMB (@lem3885753) (@lem3885752 _100499 s n)). Qed.
Lemma lem3885755 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term210 _100499 n s) = (term210 _100499 n s).
Proof. exact (eq_refl (term210 _100499 n s)). Qed.
Lemma lem3885756 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term233 _100499 n s) = (term232 _100499 n s).
Proof. exact (MK_COMB (@lem3885754 _100499 s n) (@lem3885755 _100499 n s)). Qed.
Lemma lem3885757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3885758 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term239 _100499 n s) = (term240 _100499 n s).
Proof. exact (MK_COMB (@lem3885757) (@lem3885756 _100499 n s)). Qed.
Lemma lem3885759 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) (n : nat) : (term235 _100499 s n x) = (term227 _100499 x s n).
Proof. exact (eq_refl (term235 _100499 s n x)). Qed.
Lemma lem3885760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885761 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) (n : nat) : (term241 _100499 s n x) = (term242 _100499 x s n).
Proof. exact (MK_COMB (@lem3885760) (@lem3885759 _100499 x s n)). Qed.
Lemma lem3885762 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term210 _100499 n s) = (term210 _100499 n s).
Proof. exact (eq_refl (term210 _100499 n s)). Qed.
Lemma lem3885763 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) : (term243 _100499 x n s) = (term244 _100499 x n s).
Proof. exact (MK_COMB (@lem3885761 _100499 x s n) (@lem3885762 _100499 n s)). Qed.
Lemma lem3885764 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term245 _100499 n s) = (term246 _100499 n s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885763 _100499 x n s)). Qed.
Lemma lem3885765 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3885766 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term234 _100499 n s) = (term247 _100499 n s).
Proof. exact (MK_COMB (@lem3885765 _100499) (@lem3885764 _100499 n s)). Qed.
Lemma lem3885767 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : ((term233 _100499 n s) = (term234 _100499 n s)) = ((term232 _100499 n s) = (term247 _100499 n s)).
Proof. exact (MK_COMB (@lem3885758 _100499 n s) (@lem3885766 _100499 n s)). Qed.
Lemma lem3885768 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term232 _100499 n s) = (term247 _100499 n s).
Proof. exact (EQ_MP (@lem3885767 _100499 n s) (@lem3885748 _100499 n s)). Qed.
Lemma lem3885770 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term214 _100499 n s) = (term247 _100499 n s).
Proof. exact (TRANS (@lem3885744 _100499 n s) (@lem3885768 _100499 n s)). Qed.
Lemma lem3885771 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term129 _100499 n s) = (term247 _100499 n s).
Proof. exact (TRANS (@lem3885611 _100499 n s) (@lem3885770 _100499 n s)). Qed.
Lemma lem3885772 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : term247 _100499 n s.
Proof. exact (EQ_MP (@lem3885771 _100499 n s) (@lem3885551 _100499 n s h1)). Qed.
Lemma lem3885780 {_100499 : Type'} (x : _100499) (y : _100499) : (term43 _100499 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem3885782 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term248 _100499 x s) = (term248 _100499 x s).
Proof. exact (eq_refl (term248 _100499 x s)). Qed.
Lemma lem3885783 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term249 _100499 s x y) = (term250 _100499 s x y).
Proof. exact (MK_COMB (@lem3885782 _100499 x s) (@lem3885780 _100499 x y)). Qed.
Lemma lem3885784 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term251 _100499 s x y) = (term249 _100499 s x y).
Proof. exact (@lem17045 (@IN _100499 x s) (term17 _100499 x y)). Qed.
Lemma lem3885785 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term251 _100499 s x y) = (term250 _100499 s x y).
Proof. exact (TRANS (@lem3885784 _100499 s x y) (@lem3885783 _100499 s x y)). Qed.
Lemma lem3885791 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term252 _100499 s x y) = (term252 _100499 s x y).
Proof. exact (eq_refl (term252 _100499 s x y)). Qed.
Lemma lem3885793 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) (y : _100499) : (term253 _100499 x s y) = (term253 _100499 x s y).
Proof. exact (eq_refl (term253 _100499 x s y)). Qed.
Lemma lem3885794 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term254 _100499 s x y) = (term255 _100499 s x y).
Proof. exact (MK_COMB (@lem3885793 _100499 x s y) (@lem3885785 _100499 s x y)). Qed.
Lemma lem3885795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885796 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term256 _100499 s x y) = (term257 _100499 s x y).
Proof. exact (MK_COMB (@lem3885795) (@lem3885794 _100499 s x y)). Qed.
Lemma lem3885797 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term258 _100499 s x y) = (term259 _100499 s x y).
Proof. exact (MK_COMB (@lem3885796 _100499 s x y) (@lem3885791 _100499 s x y)). Qed.
Lemma lem3885798 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : ((term13 _100499 x s y) = (term14 _100499 s x y)) = (term258 _100499 s x y).
Proof. exact (@lem17784 (term13 _100499 x s y) (term14 _100499 s x y)). Qed.
Lemma lem3885799 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : ((term13 _100499 x s y) = (term14 _100499 s x y)) = (term259 _100499 s x y).
Proof. exact (TRANS (@lem3885798 _100499 s x y) (@lem3885797 _100499 s x y)). Qed.
Lemma lem3885800 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term163 _100499 s x) = (term260 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3885799 _100499 s x y)). Qed.
Lemma lem3885801 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885802 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term164 _100499 s x) = (term261 _100499 s x).
Proof. exact (MK_COMB (@lem3885801 _100499) (@lem3885800 _100499 s x)). Qed.
Lemma lem3885803 {_100499 : Type'} (s : _100499 -> Prop) : (term165 _100499 s) = (term262 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885802 _100499 s x)). Qed.
Lemma lem3885804 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885805 {_100499 : Type'} (s : _100499 -> Prop) : (term166 _100499 s) = (term263 _100499 s).
Proof. exact (MK_COMB (@lem3885804 _100499) (@lem3885803 _100499 s)). Qed.
Lemma lem3885806 {_100499 : Type'} : (term167 _100499) = (term264 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3885805 _100499 s)). Qed.
Lemma lem3885807 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3885808 {_100499 : Type'} : (term130 _100499) = (term265 _100499).
Proof. exact (MK_COMB (@lem3885807 _100499) (@lem3885806 _100499)). Qed.
Lemma lem3885818 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3885819 {_100499 : Type'} (P : _100499 -> Prop) (Q : _100499 -> Prop) : (term266 _100499 P Q) = (term267 _100499 P Q).
Proof. exact (@lem3885818 _100499 P Q). Qed.
Lemma lem3885820 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term268 _100499 s x) = (term269 _100499 s x).
Proof. exact (@lem3885819 _100499 (term270 _100499 s x) (term271 _100499 s x)). Qed.
Lemma lem3885821 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term272 _100499 s x y) = (term255 _100499 s x y).
Proof. exact (eq_refl (term272 _100499 s x y)). Qed.
Lemma lem3885822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885823 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term273 _100499 s x y) = (term257 _100499 s x y).
Proof. exact (MK_COMB (@lem3885822) (@lem3885821 _100499 s x y)). Qed.
Lemma lem3885824 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term274 _100499 s x y) = (term252 _100499 s x y).
Proof. exact (eq_refl (term274 _100499 s x y)). Qed.
Lemma lem3885825 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term275 _100499 s x y) = (term259 _100499 s x y).
Proof. exact (MK_COMB (@lem3885823 _100499 s x y) (@lem3885824 _100499 s x y)). Qed.
Lemma lem3885826 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term276 _100499 s x) = (term260 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3885825 _100499 s x y)). Qed.
Lemma lem3885827 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885828 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term268 _100499 s x) = (term261 _100499 s x).
Proof. exact (MK_COMB (@lem3885827 _100499) (@lem3885826 _100499 s x)). Qed.
Lemma lem3885829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3885830 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term277 _100499 s x) = (term278 _100499 s x).
Proof. exact (MK_COMB (@lem3885829) (@lem3885828 _100499 s x)). Qed.
Lemma lem3885831 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term272 _100499 s x y) = (term255 _100499 s x y).
Proof. exact (eq_refl (term272 _100499 s x y)). Qed.
Lemma lem3885832 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term279 _100499 s x) = (term270 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3885831 _100499 s x y)). Qed.
Lemma lem3885833 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885834 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term280 _100499 s x) = (term281 _100499 s x).
Proof. exact (MK_COMB (@lem3885833 _100499) (@lem3885832 _100499 s x)). Qed.
Lemma lem3885835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885836 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term282 _100499 s x) = (term283 _100499 s x).
Proof. exact (MK_COMB (@lem3885835) (@lem3885834 _100499 s x)). Qed.
Lemma lem3885837 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term274 _100499 s x y) = (term252 _100499 s x y).
Proof. exact (eq_refl (term274 _100499 s x y)). Qed.
Lemma lem3885838 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term284 _100499 s x) = (term271 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3885837 _100499 s x y)). Qed.
Lemma lem3885839 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885840 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term285 _100499 s x) = (term286 _100499 s x).
Proof. exact (MK_COMB (@lem3885839 _100499) (@lem3885838 _100499 s x)). Qed.
Lemma lem3885841 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term269 _100499 s x) = (term287 _100499 s x).
Proof. exact (MK_COMB (@lem3885836 _100499 s x) (@lem3885840 _100499 s x)). Qed.
Lemma lem3885842 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : ((term268 _100499 s x) = (term269 _100499 s x)) = ((term261 _100499 s x) = (term287 _100499 s x)).
Proof. exact (MK_COMB (@lem3885830 _100499 s x) (@lem3885841 _100499 s x)). Qed.
Lemma lem3885843 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term261 _100499 s x) = (term287 _100499 s x).
Proof. exact (EQ_MP (@lem3885842 _100499 s x) (@lem3885820 _100499 s x)). Qed.
Lemma lem3885940 {_100499 : Type'} (s : _100499 -> Prop) : (term262 _100499 s) = (term288 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885843 _100499 s x)). Qed.
Lemma lem3885941 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885942 {_100499 : Type'} (s : _100499 -> Prop) : (term263 _100499 s) = (term289 _100499 s).
Proof. exact (MK_COMB (@lem3885941 _100499) (@lem3885940 _100499 s)). Qed.
Lemma lem3885944 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3885945 {_100499 : Type'} (P : _100499 -> Prop) (Q : _100499 -> Prop) : (term266 _100499 P Q) = (term267 _100499 P Q).
Proof. exact (@lem3885944 _100499 P Q). Qed.
Lemma lem3885946 {_100499 : Type'} (s : _100499 -> Prop) : (term290 _100499 s) = (term291 _100499 s).
Proof. exact (@lem3885945 _100499 (term292 _100499 s) (term293 _100499 s)). Qed.
Lemma lem3885947 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term294 _100499 s x) = (term281 _100499 s x).
Proof. exact (eq_refl (term294 _100499 s x)). Qed.
Lemma lem3885948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885949 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term295 _100499 s x) = (term283 _100499 s x).
Proof. exact (MK_COMB (@lem3885948) (@lem3885947 _100499 s x)). Qed.
Lemma lem3885950 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term296 _100499 s x) = (term286 _100499 s x).
Proof. exact (eq_refl (term296 _100499 s x)). Qed.
Lemma lem3885951 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term297 _100499 s x) = (term287 _100499 s x).
Proof. exact (MK_COMB (@lem3885949 _100499 s x) (@lem3885950 _100499 s x)). Qed.
Lemma lem3885952 {_100499 : Type'} (s : _100499 -> Prop) : (term298 _100499 s) = (term288 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885951 _100499 s x)). Qed.
Lemma lem3885953 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885954 {_100499 : Type'} (s : _100499 -> Prop) : (term290 _100499 s) = (term289 _100499 s).
Proof. exact (MK_COMB (@lem3885953 _100499) (@lem3885952 _100499 s)). Qed.
Lemma lem3885955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3885956 {_100499 : Type'} (s : _100499 -> Prop) : (term299 _100499 s) = (term300 _100499 s).
Proof. exact (MK_COMB (@lem3885955) (@lem3885954 _100499 s)). Qed.
Lemma lem3885957 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term294 _100499 s x) = (term281 _100499 s x).
Proof. exact (eq_refl (term294 _100499 s x)). Qed.
Lemma lem3885958 {_100499 : Type'} (s : _100499 -> Prop) : (term301 _100499 s) = (term292 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885957 _100499 s x)). Qed.
Lemma lem3885959 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885960 {_100499 : Type'} (s : _100499 -> Prop) : (term302 _100499 s) = (term303 _100499 s).
Proof. exact (MK_COMB (@lem3885959 _100499) (@lem3885958 _100499 s)). Qed.
Lemma lem3885961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3885962 {_100499 : Type'} (s : _100499 -> Prop) : (term304 _100499 s) = (term305 _100499 s).
Proof. exact (MK_COMB (@lem3885961) (@lem3885960 _100499 s)). Qed.
Lemma lem3885963 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term296 _100499 s x) = (term286 _100499 s x).
Proof. exact (eq_refl (term296 _100499 s x)). Qed.
Lemma lem3885964 {_100499 : Type'} (s : _100499 -> Prop) : (term306 _100499 s) = (term293 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3885963 _100499 s x)). Qed.
Lemma lem3885965 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3885966 {_100499 : Type'} (s : _100499 -> Prop) : (term307 _100499 s) = (term308 _100499 s).
Proof. exact (MK_COMB (@lem3885965 _100499) (@lem3885964 _100499 s)). Qed.
Lemma lem3885967 {_100499 : Type'} (s : _100499 -> Prop) : (term291 _100499 s) = (term309 _100499 s).
Proof. exact (MK_COMB (@lem3885962 _100499 s) (@lem3885966 _100499 s)). Qed.
Lemma lem3885968 {_100499 : Type'} (s : _100499 -> Prop) : ((term290 _100499 s) = (term291 _100499 s)) = ((term289 _100499 s) = (term309 _100499 s)).
Proof. exact (MK_COMB (@lem3885956 _100499 s) (@lem3885967 _100499 s)). Qed.
Lemma lem3885969 {_100499 : Type'} (s : _100499 -> Prop) : (term289 _100499 s) = (term309 _100499 s).
Proof. exact (EQ_MP (@lem3885968 _100499 s) (@lem3885946 _100499 s)). Qed.
Lemma lem3886074 {_100499 : Type'} (s : _100499 -> Prop) : (term263 _100499 s) = (term309 _100499 s).
Proof. exact (TRANS (@lem3885942 _100499 s) (@lem3885969 _100499 s)). Qed.
Lemma lem3886075 {_100499 : Type'} : (term264 _100499) = (term310 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886074 _100499 s)). Qed.
Lemma lem3886076 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886077 {_100499 : Type'} : (term265 _100499) = (term311 _100499).
Proof. exact (MK_COMB (@lem3886076 _100499) (@lem3886075 _100499)). Qed.
Lemma lem3886079 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3886080 {_100499 : Type'} (P : type686 _100499) (Q : type686 _100499) : (term312 _100499 P Q) = (term313 _100499 P Q).
Proof. exact (@lem3886079 (_100499 -> Prop) P Q). Qed.
Lemma lem3886081 {_100499 : Type'} : (term314 _100499) = (term315 _100499).
Proof. exact (@lem3886080 _100499 (term316 _100499) (term317 _100499)). Qed.
Lemma lem3886082 {_100499 : Type'} (s : _100499 -> Prop) : (term318 _100499 s) = (term303 _100499 s).
Proof. exact (eq_refl (term318 _100499 s)). Qed.
Lemma lem3886083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3886084 {_100499 : Type'} (s : _100499 -> Prop) : (term319 _100499 s) = (term305 _100499 s).
Proof. exact (MK_COMB (@lem3886083) (@lem3886082 _100499 s)). Qed.
Lemma lem3886085 {_100499 : Type'} (s : _100499 -> Prop) : (term320 _100499 s) = (term308 _100499 s).
Proof. exact (eq_refl (term320 _100499 s)). Qed.
Lemma lem3886086 {_100499 : Type'} (s : _100499 -> Prop) : (term321 _100499 s) = (term309 _100499 s).
Proof. exact (MK_COMB (@lem3886084 _100499 s) (@lem3886085 _100499 s)). Qed.
Lemma lem3886087 {_100499 : Type'} : (term322 _100499) = (term310 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886086 _100499 s)). Qed.
Lemma lem3886088 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886089 {_100499 : Type'} : (term314 _100499) = (term311 _100499).
Proof. exact (MK_COMB (@lem3886088 _100499) (@lem3886087 _100499)). Qed.
Lemma lem3886090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3886091 {_100499 : Type'} : (term323 _100499) = (term324 _100499).
Proof. exact (MK_COMB (@lem3886090) (@lem3886089 _100499)). Qed.
Lemma lem3886092 {_100499 : Type'} (s : _100499 -> Prop) : (term318 _100499 s) = (term303 _100499 s).
Proof. exact (eq_refl (term318 _100499 s)). Qed.
Lemma lem3886093 {_100499 : Type'} : (term325 _100499) = (term316 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886092 _100499 s)). Qed.
Lemma lem3886094 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886095 {_100499 : Type'} : (term326 _100499) = (term327 _100499).
Proof. exact (MK_COMB (@lem3886094 _100499) (@lem3886093 _100499)). Qed.
Lemma lem3886096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3886097 {_100499 : Type'} : (term328 _100499) = (term329 _100499).
Proof. exact (MK_COMB (@lem3886096) (@lem3886095 _100499)). Qed.
Lemma lem3886098 {_100499 : Type'} (s : _100499 -> Prop) : (term320 _100499 s) = (term308 _100499 s).
Proof. exact (eq_refl (term320 _100499 s)). Qed.
Lemma lem3886099 {_100499 : Type'} : (term330 _100499) = (term317 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886098 _100499 s)). Qed.
Lemma lem3886100 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886101 {_100499 : Type'} : (term331 _100499) = (term332 _100499).
Proof. exact (MK_COMB (@lem3886100 _100499) (@lem3886099 _100499)). Qed.
Lemma lem3886102 {_100499 : Type'} : (term315 _100499) = (term333 _100499).
Proof. exact (MK_COMB (@lem3886097 _100499) (@lem3886101 _100499)). Qed.
Lemma lem3886103 {_100499 : Type'} : ((term314 _100499) = (term315 _100499)) = ((term311 _100499) = (term333 _100499)).
Proof. exact (MK_COMB (@lem3886091 _100499) (@lem3886102 _100499)). Qed.
Lemma lem3886104 {_100499 : Type'} : (term311 _100499) = (term333 _100499).
Proof. exact (EQ_MP (@lem3886103 _100499) (@lem3886081 _100499)). Qed.
Lemma lem3886219 {_100499 : Type'} : (term265 _100499) = (term333 _100499).
Proof. exact (TRANS (@lem3886077 _100499) (@lem3886104 _100499)). Qed.
Lemma lem3886220 {_100499 : Type'} : (term130 _100499) = (term333 _100499).
Proof. exact (TRANS (@lem3885808 _100499) (@lem3886219 _100499)). Qed.
Lemma lem3886221 {_100499 : Type'} (h1 : term130 _100499) : term333 _100499.
Proof. exact (EQ_MP (@lem3886220 _100499) (@lem3885552 _100499 h1)). Qed.
Lemma lem3886677 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) : (term4 _100499 s a) = (term334 _100499 s a).
Proof. exact (@lem17265 (@IN _100499 a s) (s = (term1 _100499 s a))). Qed.
Lemma lem3886678 {_100499 : Type'} (s : _100499 -> Prop) : (term154 _100499 s) = (term335 _100499 s).
Proof. exact (fun_ext (fun a : _100499 => @lem3886677 _100499 s a)). Qed.
Lemma lem3886679 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886680 {_100499 : Type'} (s : _100499 -> Prop) : (term98 _100499 s) = (term336 _100499 s).
Proof. exact (MK_COMB (@lem3886679 _100499) (@lem3886678 _100499 s)). Qed.
Lemma lem3886681 {_100499 : Type'} : (term155 _100499) = (term337 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886680 _100499 s)). Qed.
Lemma lem3886682 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886739 {_100499 : Type'} : (term99 _100499) = (term338 _100499).
Proof. exact (MK_COMB (@lem3886682 _100499) (@lem3886681 _100499)). Qed.
Lemma lem3886740 {_100499 : Type'} (h1 : term99 _100499) : term338 _100499.
Proof. exact (EQ_MP (@lem3886739 _100499) (@lem3885554 _100499 h1)). Qed.
Lemma lem3886741 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term244 _100499 x n s.
Proof. exact (h1). Qed.
Lemma lem3886770 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term252 _100499 s x y) = (term252 _100499 s x y).
Proof. exact (eq_refl (term252 _100499 s x y)). Qed.
Lemma lem3886771 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term271 _100499 s x) = (term271 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3886770 _100499 s x y)). Qed.
Lemma lem3886772 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886773 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term286 _100499 s x) = (term286 _100499 s x).
Proof. exact (MK_COMB (@lem3886772 _100499) (@lem3886771 _100499 s x)). Qed.
Lemma lem3886774 {_100499 : Type'} (s : _100499 -> Prop) : (term293 _100499 s) = (term293 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3886773 _100499 s x)). Qed.
Lemma lem3886775 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886776 {_100499 : Type'} (s : _100499 -> Prop) : (term308 _100499 s) = (term308 _100499 s).
Proof. exact (MK_COMB (@lem3886775 _100499) (@lem3886774 _100499 s)). Qed.
Lemma lem3886777 {_100499 : Type'} : (term317 _100499) = (term317 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886776 _100499 s)). Qed.
Lemma lem3886778 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886779 {_100499 : Type'} : (term332 _100499) = (term332 _100499).
Proof. exact (MK_COMB (@lem3886778 _100499) (@lem3886777 _100499)). Qed.
Lemma lem3886806 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term255 _100499 s x y) = (term255 _100499 s x y).
Proof. exact (eq_refl (term255 _100499 s x y)). Qed.
Lemma lem3886807 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term270 _100499 s x) = (term270 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3886806 _100499 s x y)). Qed.
Lemma lem3886808 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886809 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term281 _100499 s x) = (term281 _100499 s x).
Proof. exact (MK_COMB (@lem3886808 _100499) (@lem3886807 _100499 s x)). Qed.
Lemma lem3886810 {_100499 : Type'} (s : _100499 -> Prop) : (term292 _100499 s) = (term292 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3886809 _100499 s x)). Qed.
Lemma lem3886811 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886812 {_100499 : Type'} (s : _100499 -> Prop) : (term303 _100499 s) = (term303 _100499 s).
Proof. exact (MK_COMB (@lem3886811 _100499) (@lem3886810 _100499 s)). Qed.
Lemma lem3886813 {_100499 : Type'} : (term316 _100499) = (term316 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886812 _100499 s)). Qed.
Lemma lem3886814 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886815 {_100499 : Type'} : (term327 _100499) = (term327 _100499).
Proof. exact (MK_COMB (@lem3886814 _100499) (@lem3886813 _100499)). Qed.
Lemma lem3886816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3886817 {_100499 : Type'} : (term329 _100499) = (term329 _100499).
Proof. exact (MK_COMB (@lem3886816) (@lem3886815 _100499)). Qed.
Lemma lem3886818 {_100499 : Type'} : (term333 _100499) = (term333 _100499).
Proof. exact (MK_COMB (@lem3886817 _100499) (@lem3886779 _100499)). Qed.
Lemma lem3886819 {_100499 : Type'} (h1 : term130 _100499) : term333 _100499.
Proof. exact (EQ_MP (@lem3886818 _100499) (@lem3886221 _100499 h1)). Qed.
Lemma lem3886920 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) : (term334 _100499 s a) = (term334 _100499 s a).
Proof. exact (eq_refl (term334 _100499 s a)). Qed.
Lemma lem3886921 {_100499 : Type'} (s : _100499 -> Prop) : (term335 _100499 s) = (term335 _100499 s).
Proof. exact (fun_ext (fun a : _100499 => @lem3886920 _100499 s a)). Qed.
Lemma lem3886922 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886923 {_100499 : Type'} (s : _100499 -> Prop) : (term336 _100499 s) = (term336 _100499 s).
Proof. exact (MK_COMB (@lem3886922 _100499) (@lem3886921 _100499 s)). Qed.
Lemma lem3886924 {_100499 : Type'} : (term337 _100499) = (term337 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3886923 _100499 s)). Qed.
Lemma lem3886925 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886926 {_100499 : Type'} : (term338 _100499) = (term338 _100499).
Proof. exact (MK_COMB (@lem3886925 _100499) (@lem3886924 _100499)). Qed.
Lemma lem3886927 {_100499 : Type'} (h1 : term99 _100499) : term338 _100499.
Proof. exact (EQ_MP (@lem3886926 _100499) (@lem3886740 _100499 h1)). Qed.
Lemma lem3886956 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term190 _100499 n s a t) = (term190 _100499 n s a t).
Proof. exact (eq_refl (term190 _100499 n s a t)). Qed.
Lemma lem3886957 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term200 _100499 n s a) = (term200 _100499 n s a).
Proof. exact (fun_ext (fun t : _100499 -> Prop => @lem3886956 _100499 n s a t)). Qed.
Lemma lem3886958 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3886959 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term201 _100499 n s a) = (term201 _100499 n s a).
Proof. exact (MK_COMB (@lem3886958 _100499) (@lem3886957 _100499 n s a)). Qed.
Lemma lem3886960 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term209 _100499 n s) = (term209 _100499 n s).
Proof. exact (fun_ext (fun a : _100499 => @lem3886959 _100499 n s a)). Qed.
Lemma lem3886961 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886962 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term210 _100499 n s) = (term210 _100499 n s).
Proof. exact (MK_COMB (@lem3886961 _100499) (@lem3886960 _100499 n s)). Qed.
Lemma lem3886981 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (n : nat) : (term175 _100499 s a n) = (term175 _100499 s a n).
Proof. exact (eq_refl (term175 _100499 s a n)). Qed.
Lemma lem3886982 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term177 _100499 s n) = (term177 _100499 s n).
Proof. exact (fun_ext (fun a : _100499 => @lem3886981 _100499 s a n)). Qed.
Lemma lem3886983 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3886984 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term178 _100499 s n) = (term178 _100499 s n).
Proof. exact (MK_COMB (@lem3886983 _100499) (@lem3886982 _100499 s n)). Qed.
Lemma lem3886991 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term15 _100499 x s) = (term15 _100499 x s).
Proof. exact (eq_refl (term15 _100499 x s)). Qed.
Lemma lem3886992 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) (n : nat) : (term227 _100499 x s n) = (term227 _100499 x s n).
Proof. exact (MK_COMB (@lem3886991 _100499 x s) (@lem3886984 _100499 s n)). Qed.
Lemma lem3886993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3886994 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) (n : nat) : (term242 _100499 x s n) = (term242 _100499 x s n).
Proof. exact (MK_COMB (@lem3886993) (@lem3886992 _100499 x s n)). Qed.
Lemma lem3886995 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) : (term244 _100499 x n s) = (term244 _100499 x n s).
Proof. exact (MK_COMB (@lem3886994 _100499 x s n) (@lem3886962 _100499 n s)). Qed.
Lemma lem3886996 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term244 _100499 x n s.
Proof. exact (EQ_MP (@lem3886995 _100499 x n s) (@lem3886741 _100499 x n s h1)). Qed.
Lemma lem3886997 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term210 _100499 n s.
Proof. exact (proj2 (@lem3886996 _100499 x n s h1)). Qed.
Lemma lem3886998 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term227 _100499 x s n.
Proof. exact (proj1 (@lem3886996 _100499 x n s h1)). Qed.
Lemma lem3886999 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term178 _100499 s n.
Proof. exact (proj2 (@lem3886998 _100499 x n s h1)). Qed.
Lemma lem3887003 {_100499 : Type'} (h1 : term130 _100499) : term332 _100499.
Proof. exact (proj2 (@lem3886819 _100499 h1)). Qed.
Lemma lem3887012 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) : (term334 _100499 s a) = (term334 _100499 s a).
Proof. exact (eq_refl (term334 _100499 s a)). Qed.
Lemma lem3887013 {_100499 : Type'} (s : _100499 -> Prop) : (term335 _100499 s) = (term335 _100499 s).
Proof. exact (fun_ext (fun a : _100499 => @lem3887012 _100499 s a)). Qed.
Lemma lem3887014 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3887015 {_100499 : Type'} (s : _100499 -> Prop) : (term336 _100499 s) = (term336 _100499 s).
Proof. exact (MK_COMB (@lem3887014 _100499) (@lem3887013 _100499 s)). Qed.
Lemma lem3887016 {_100499 : Type'} : (term337 _100499) = (term337 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3887015 _100499 s)). Qed.
Lemma lem3887017 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3887019 {_100499 : Type'} : (term338 _100499) = (term338 _100499).
Proof. exact (MK_COMB (@lem3887017 _100499) (@lem3887016 _100499)). Qed.
Lemma lem3887020 {_100499 : Type'} (h1 : term99 _100499) : term338 _100499.
Proof. exact (EQ_MP (@lem3887019 _100499) (@lem3886927 _100499 h1)). Qed.
Lemma lem3887034 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term190 _100499 n s a t) = (term190 _100499 n s a t).
Proof. exact (eq_refl (term190 _100499 n s a t)). Qed.
Lemma lem3887035 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term200 _100499 n s a) = (term200 _100499 n s a).
Proof. exact (fun_ext (fun t : _100499 -> Prop => @lem3887034 _100499 n s a t)). Qed.
Lemma lem3887036 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3887037 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term201 _100499 n s a) = (term201 _100499 n s a).
Proof. exact (MK_COMB (@lem3887036 _100499) (@lem3887035 _100499 n s a)). Qed.
Lemma lem3887038 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term209 _100499 n s) = (term209 _100499 n s).
Proof. exact (fun_ext (fun a : _100499 => @lem3887037 _100499 n s a)). Qed.
Lemma lem3887039 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3887041 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term210 _100499 n s) = (term210 _100499 n s).
Proof. exact (MK_COMB (@lem3887039 _100499) (@lem3887038 _100499 n s)). Qed.
Lemma lem3887042 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term210 _100499 n s.
Proof. exact (EQ_MP (@lem3887041 _100499 n s) (@lem3886997 _100499 x n s h1)). Qed.
Lemma lem3887054 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (n : nat) : (term175 _100499 s a n) = (term175 _100499 s a n).
Proof. exact (eq_refl (term175 _100499 s a n)). Qed.
Lemma lem3887055 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term177 _100499 s n) = (term177 _100499 s n).
Proof. exact (fun_ext (fun a : _100499 => @lem3887054 _100499 s a n)). Qed.
Lemma lem3887056 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3887058 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term178 _100499 s n) = (term178 _100499 s n).
Proof. exact (MK_COMB (@lem3887056 _100499) (@lem3887055 _100499 s n)). Qed.
Lemma lem3887059 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term178 _100499 s n.
Proof. exact (EQ_MP (@lem3887058 _100499 s n) (@lem3886999 _100499 x n s h1)). Qed.
Lemma lem3887156 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (y : _100499) : (term252 _100499 s x y) = (term339 _100499 s x y).
Proof. exact (@lem19490 (@IN _100499 x s) (term340 _100499 x s y) (term17 _100499 x y)). Qed.
Lemma lem3887157 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term271 _100499 s x) = (term341 _100499 s x).
Proof. exact (fun_ext (fun y : _100499 => @lem3887156 _100499 s x y)). Qed.
Lemma lem3887158 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3887159 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term286 _100499 s x) = (term342 _100499 s x).
Proof. exact (MK_COMB (@lem3887158 _100499) (@lem3887157 _100499 s x)). Qed.
Lemma lem3887160 {_100499 : Type'} (s : _100499 -> Prop) : (term293 _100499 s) = (term343 _100499 s).
Proof. exact (fun_ext (fun x : _100499 => @lem3887159 _100499 s x)). Qed.
Lemma lem3887161 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3887162 {_100499 : Type'} (s : _100499 -> Prop) : (term308 _100499 s) = (term344 _100499 s).
Proof. exact (MK_COMB (@lem3887161 _100499) (@lem3887160 _100499 s)). Qed.
Lemma lem3887163 {_100499 : Type'} : (term317 _100499) = (term345 _100499).
Proof. exact (fun_ext (fun s : _100499 -> Prop => @lem3887162 _100499 s)). Qed.
Lemma lem3887164 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3887166 {_100499 : Type'} : (term332 _100499) = (term346 _100499).
Proof. exact (MK_COMB (@lem3887164 _100499) (@lem3887163 _100499)). Qed.
Lemma lem3887167 {_100499 : Type'} (h1 : term130 _100499) : term346 _100499.
Proof. exact (EQ_MP (@lem3887166 _100499) (@lem3887003 _100499 h1)). Qed.
Lemma lem3887168 {_100499 : Type'} (_45181 : _100499 -> Prop) (h1 : term99 _100499) : term347 _100499 _45181.
Proof. exact (@lem3887020 _100499 h1 _45181). Qed.
Lemma lem3887169 {_100499 : Type'} (_45181 : _100499 -> Prop) : (term347 _100499 _45181) = (term336 _100499 _45181).
Proof. exact (eq_refl (term347 _100499 _45181)). Qed.
Lemma lem3887170 {_100499 : Type'} (_45181 : _100499 -> Prop) (h1 : term99 _100499) : term336 _100499 _45181.
Proof. exact (EQ_MP (@lem3887169 _100499 _45181) (@lem3887168 _100499 _45181 h1)). Qed.
Lemma lem3887171 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) (h1 : term99 _100499) : term348 _100499 _45181 _45182.
Proof. exact (@lem3887170 _100499 _45181 h1 _45182). Qed.
Lemma lem3887172 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) : (term348 _100499 _45181 _45182) = (term334 _100499 _45181 _45182).
Proof. exact (eq_refl (term348 _100499 _45181 _45182)). Qed.
Lemma lem3887174 {_100499 : Type'} (_45183 : _100499) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term349 _100499 n s _45183.
Proof. exact (@lem3887042 _100499 x n s h1 _45183). Qed.
Lemma lem3887175 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) : (term349 _100499 n s _45183) = (term201 _100499 n s _45183).
Proof. exact (eq_refl (term349 _100499 n s _45183)). Qed.
Lemma lem3887176 {_100499 : Type'} (_45183 : _100499) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term201 _100499 n s _45183.
Proof. exact (EQ_MP (@lem3887175 _100499 n s _45183) (@lem3887174 _100499 _45183 x n s h1)). Qed.
Lemma lem3887177 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term350 _100499 n s _45183 _45184.
Proof. exact (@lem3887176 _100499 _45183 x n s h1 _45184). Qed.
Lemma lem3887178 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term350 _100499 n s _45183 _45184) = (term190 _100499 n s _45183 _45184).
Proof. exact (eq_refl (term350 _100499 n s _45183 _45184)). Qed.
Lemma lem3887180 {_100499 : Type'} (_45185 : _100499) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term351 _100499 s n _45185.
Proof. exact (@lem3887059 _100499 x n s h1 _45185). Qed.
Lemma lem3887181 {_100499 : Type'} (s : _100499 -> Prop) (_45185 : _100499) (n : nat) : (term351 _100499 s n _45185) = (term175 _100499 s _45185 n).
Proof. exact (eq_refl (term351 _100499 s n _45185)). Qed.
Lemma lem3887210 {_100499 : Type'} (_45195 : _100499 -> Prop) (h1 : term130 _100499) : term352 _100499 _45195.
Proof. exact (@lem3887167 _100499 h1 _45195). Qed.
Lemma lem3887211 {_100499 : Type'} (_45195 : _100499 -> Prop) : (term352 _100499 _45195) = (term344 _100499 _45195).
Proof. exact (eq_refl (term352 _100499 _45195)). Qed.
Lemma lem3887212 {_100499 : Type'} (_45195 : _100499 -> Prop) (h1 : term130 _100499) : term344 _100499 _45195.
Proof. exact (EQ_MP (@lem3887211 _100499 _45195) (@lem3887210 _100499 _45195 h1)). Qed.
Lemma lem3887213 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (h1 : term130 _100499) : term353 _100499 _45195 _45196.
Proof. exact (@lem3887212 _100499 _45195 h1 _45196). Qed.
Lemma lem3887214 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) : (term353 _100499 _45195 _45196) = (term342 _100499 _45195 _45196).
Proof. exact (eq_refl (term353 _100499 _45195 _45196)). Qed.
Lemma lem3887215 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (h1 : term130 _100499) : term342 _100499 _45195 _45196.
Proof. exact (EQ_MP (@lem3887214 _100499 _45195 _45196) (@lem3887213 _100499 _45195 _45196 h1)). Qed.
Lemma lem3887216 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) (h1 : term130 _100499) : term354 _100499 _45195 _45196 _45197.
Proof. exact (@lem3887215 _100499 _45195 _45196 h1 _45197). Qed.
Lemma lem3887217 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) : (term354 _100499 _45195 _45196 _45197) = (term339 _100499 _45195 _45196 _45197).
Proof. exact (eq_refl (term354 _100499 _45195 _45196 _45197)). Qed.
Lemma lem3887218 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) (h1 : term130 _100499) : term339 _100499 _45195 _45196 _45197.
Proof. exact (EQ_MP (@lem3887217 _100499 _45195 _45196 _45197) (@lem3887216 _100499 _45195 _45196 _45197 h1)). Qed.
Lemma lem3887228 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) (h1 : term99 _100499) : term334 _100499 _45181 _45182.
Proof. exact (EQ_MP (@lem3887172 _100499 _45181 _45182) (@lem3887171 _100499 _45181 _45182 h1)). Qed.
Lemma lem3887238 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term190 _100499 n s _45183 _45184.
Proof. exact (EQ_MP (@lem3887178 _100499 n s _45183 _45184) (@lem3887177 _100499 _45183 _45184 x n s h1)). Qed.
Lemma lem3887246 {_100499 : Type'} (_45185 : _100499) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term175 _100499 s _45185 n.
Proof. exact (EQ_MP (@lem3887181 _100499 s _45185 n) (@lem3887180 _100499 _45185 x n s h1)). Qed.
Lemma lem3887278 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) (h1 : term130 _100499) : term355 _100499 _45195 _45196 _45197.
Proof. exact (proj2 (@lem3887218 _100499 _45195 _45196 _45197 h1)). Qed.
Lemma lem3887402 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : @IN _100499 x s.
Proof. exact (proj1 (@lem3886998 _100499 x n s h1)). Qed.
Lemma lem3887403 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term356 _100499 x s.
Proof. exact (fun h0 : term187 _100499 x s => @lem3887402 _100499 x n s h1). Qed.
Lemma lem3887405 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3887406 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term356 _100499 x s) = (@IN _100499 x s).
Proof. exact (@lem3887405 (@IN _100499 x s)). Qed.
Lemma lem3887407 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : @IN _100499 x s.
Proof. exact (EQ_MP (@lem3887406 _100499 x s) (@lem3887403 _100499 x n s h1)). Qed.
Lemma lem3887413 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3887414 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : (term175 _100499 s _45185 n) = (term357 _100499 n _45185 s).
Proof. exact (@lem3887413 (term176 _100499 s _45185 n) (term187 _100499 _45185 s)). Qed.
Lemma lem3887420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3887421 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : (term358 _100499 s _45185 n) = (term359 _100499 n _45185 s).
Proof. exact (MK_COMB (@lem3887420) (@lem3887414 _100499 n _45185 s)). Qed.
Lemma lem3887427 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : (term357 _100499 n _45185 s) = (term357 _100499 n _45185 s).
Proof. exact (eq_refl (term357 _100499 n _45185 s)). Qed.
Lemma lem3887428 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : ((term175 _100499 s _45185 n) = (term357 _100499 n _45185 s)) = ((term357 _100499 n _45185 s) = (term357 _100499 n _45185 s)).
Proof. exact (MK_COMB (@lem3887421 _100499 n _45185 s) (@lem3887427 _100499 n _45185 s)). Qed.
Lemma lem3887430 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3887431 (x : Prop) : (x = x) = True.
Proof. exact (@lem3887430 Prop x). Qed.
Lemma lem3887432 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : ((term357 _100499 n _45185 s) = (term357 _100499 n _45185 s)) = True.
Proof. exact (@lem3887431 (term357 _100499 n _45185 s)). Qed.
Lemma lem3887433 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : ((term175 _100499 s _45185 n) = (term357 _100499 n _45185 s)) = True.
Proof. exact (TRANS (@lem3887428 _100499 n _45185 s) (@lem3887432 _100499 n _45185 s)). Qed.
Lemma lem3887434 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : True = ((term175 _100499 s _45185 n) = (term357 _100499 n _45185 s)).
Proof. exact (SYM (@lem3887433 _100499 n _45185 s)). Qed.
Lemma lem3887435 {_100499 : Type'} (n : nat) (_45185 : _100499) (s : _100499 -> Prop) : (term175 _100499 s _45185 n) = (term357 _100499 n _45185 s).
Proof. exact (EQ_MP (@lem3887434 _100499 n _45185 s) (@lem0)). Qed.
Lemma lem3887436 {_100499 : Type'} (_45185 : _100499) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term357 _100499 n _45185 s.
Proof. exact (EQ_MP (@lem3887435 _100499 n _45185 s) (@lem3887246 _100499 _45185 x n s h1)). Qed.
Lemma lem3887438 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3887439 {_100499 : Type'} (s : _100499 -> Prop) (_45185 : _100499) (n : nat) : (term357 _100499 n _45185 s) = (term361 _100499 s _45185 n).
Proof. exact (@lem3887438 (term187 _100499 _45185 s) (term176 _100499 s _45185 n)). Qed.
Lemma lem3887441 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3887442 {_100499 : Type'} (_45185 : _100499) (s : _100499 -> Prop) : (term180 _100499 _45185 s) = (@IN _100499 _45185 s).
Proof. exact (@lem3887441 (@IN _100499 _45185 s)). Qed.
Lemma lem3887443 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3887444 {_100499 : Type'} (_45185 : _100499) (s : _100499 -> Prop) : (term362 _100499 _45185 s) = (term3 _100499 _45185 s).
Proof. exact (MK_COMB (@lem3887443) (@lem3887442 _100499 _45185 s)). Qed.
Lemma lem3887445 {_100499 : Type'} (s : _100499 -> Prop) (_45185 : _100499) (n : nat) : (term176 _100499 s _45185 n) = (term176 _100499 s _45185 n).
Proof. exact (eq_refl (term176 _100499 s _45185 n)). Qed.
Lemma lem3887446 {_100499 : Type'} (s : _100499 -> Prop) (_45185 : _100499) (n : nat) : (term361 _100499 s _45185 n) = (term172 _100499 s _45185 n).
Proof. exact (MK_COMB (@lem3887444 _100499 _45185 s) (@lem3887445 _100499 s _45185 n)). Qed.
Lemma lem3887447 {_100499 : Type'} (s : _100499 -> Prop) (_45185 : _100499) (n : nat) : (term357 _100499 n _45185 s) = (term172 _100499 s _45185 n).
Proof. exact (TRANS (@lem3887439 _100499 s _45185 n) (@lem3887446 _100499 s _45185 n)). Qed.
Lemma lem3887450 {_100499 : Type'} (_45185 : _100499) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term172 _100499 s _45185 n.
Proof. exact (EQ_MP (@lem3887447 _100499 s _45185 n) (@lem3887436 _100499 _45185 x n s h1)). Qed.
Lemma lem3887451 {_100499 : Type'} (_45185 : _100499) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term172 _100499 s _45185 n.
Proof. exact (@lem3887450 _100499 _45185 x n s h1). Qed.
Lemma lem3887452 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term172 _100499 s x n.
Proof. exact (@lem3887451 _100499 x x n s h1). Qed.
Lemma lem3887455 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term176 _100499 s x n.
Proof. exact (@lem3887452 _100499 x n s h1 (@lem3887407 _100499 x n s h1)). Qed.
Lemma lem3887456 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term363 _100499 s x n.
Proof. exact (fun h0 : term364 _100499 s x n => @lem3887455 _100499 x n s h1). Qed.
Lemma lem3887458 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3887459 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (n : nat) : (term363 _100499 s x n) = (term176 _100499 s x n).
Proof. exact (@lem3887458 (term176 _100499 s x n)). Qed.
Lemma lem3887460 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term176 _100499 s x n.
Proof. exact (EQ_MP (@lem3887459 _100499 s x n) (@lem3887456 _100499 x n s h1)). Qed.
Lemma lem3887462 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : @IN _100499 x s.
Proof. exact (proj1 (@lem3886998 _100499 x n s h1)). Qed.
Lemma lem3887463 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term356 _100499 x s.
Proof. exact (fun h0 : term187 _100499 x s => @lem3887462 _100499 x n s h1). Qed.
Lemma lem3887465 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3887466 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term356 _100499 x s) = (@IN _100499 x s).
Proof. exact (@lem3887465 (@IN _100499 x s)). Qed.
Lemma lem3887467 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : @IN _100499 x s.
Proof. exact (EQ_MP (@lem3887466 _100499 x s) (@lem3887463 _100499 x n s h1)). Qed.
Lemma lem3887473 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3887474 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : (term334 _100499 _45181 _45182) = (term365 _100499 _45182 _45181).
Proof. exact (@lem3887473 (_45181 = (term1 _100499 _45181 _45182)) (term187 _100499 _45182 _45181)). Qed.
Lemma lem3887482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3887483 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : (term366 _100499 _45181 _45182) = (term367 _100499 _45182 _45181).
Proof. exact (MK_COMB (@lem3887482) (@lem3887474 _100499 _45182 _45181)). Qed.
Lemma lem3887491 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : (term365 _100499 _45182 _45181) = (term365 _100499 _45182 _45181).
Proof. exact (eq_refl (term365 _100499 _45182 _45181)). Qed.
Lemma lem3887492 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : ((term334 _100499 _45181 _45182) = (term365 _100499 _45182 _45181)) = ((term365 _100499 _45182 _45181) = (term365 _100499 _45182 _45181)).
Proof. exact (MK_COMB (@lem3887483 _100499 _45182 _45181) (@lem3887491 _100499 _45182 _45181)). Qed.
Lemma lem3887494 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3887495 (x : Prop) : (x = x) = True.
Proof. exact (@lem3887494 Prop x). Qed.
Lemma lem3887496 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : ((term365 _100499 _45182 _45181) = (term365 _100499 _45182 _45181)) = True.
Proof. exact (@lem3887495 (term365 _100499 _45182 _45181)). Qed.
Lemma lem3887497 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : ((term334 _100499 _45181 _45182) = (term365 _100499 _45182 _45181)) = True.
Proof. exact (TRANS (@lem3887492 _100499 _45182 _45181) (@lem3887496 _100499 _45182 _45181)). Qed.
Lemma lem3887498 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : True = ((term334 _100499 _45181 _45182) = (term365 _100499 _45182 _45181)).
Proof. exact (SYM (@lem3887497 _100499 _45182 _45181)). Qed.
Lemma lem3887499 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : (term334 _100499 _45181 _45182) = (term365 _100499 _45182 _45181).
Proof. exact (EQ_MP (@lem3887498 _100499 _45182 _45181) (@lem0)). Qed.
Lemma lem3887500 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) (h1 : term99 _100499) : term365 _100499 _45182 _45181.
Proof. exact (EQ_MP (@lem3887499 _100499 _45182 _45181) (@lem3887228 _100499 _45181 _45182 h1)). Qed.
Lemma lem3887502 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3887503 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) : (term365 _100499 _45182 _45181) = (term368 _100499 _45181 _45182).
Proof. exact (@lem3887502 (term187 _100499 _45182 _45181) (_45181 = (term1 _100499 _45181 _45182))). Qed.
Lemma lem3887505 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3887506 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : (term180 _100499 _45182 _45181) = (@IN _100499 _45182 _45181).
Proof. exact (@lem3887505 (@IN _100499 _45182 _45181)). Qed.
Lemma lem3887507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3887508 {_100499 : Type'} (_45182 : _100499) (_45181 : _100499 -> Prop) : (term362 _100499 _45182 _45181) = (term3 _100499 _45182 _45181).
Proof. exact (MK_COMB (@lem3887507) (@lem3887506 _100499 _45182 _45181)). Qed.
Lemma lem3887509 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) : (_45181 = (term1 _100499 _45181 _45182)) = (_45181 = (term1 _100499 _45181 _45182)).
Proof. exact (eq_refl (_45181 = (term1 _100499 _45181 _45182))). Qed.
Lemma lem3887510 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) : (term368 _100499 _45181 _45182) = (term4 _100499 _45181 _45182).
Proof. exact (MK_COMB (@lem3887508 _100499 _45182 _45181) (@lem3887509 _100499 _45181 _45182)). Qed.
Lemma lem3887511 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) : (term365 _100499 _45182 _45181) = (term4 _100499 _45181 _45182).
Proof. exact (TRANS (@lem3887503 _100499 _45181 _45182) (@lem3887510 _100499 _45181 _45182)). Qed.
Lemma lem3887514 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) (h1 : term99 _100499) : term4 _100499 _45181 _45182.
Proof. exact (EQ_MP (@lem3887511 _100499 _45181 _45182) (@lem3887500 _100499 _45182 _45181 h1)). Qed.
Lemma lem3887515 {_100499 : Type'} (_45181 : _100499 -> Prop) (_45182 : _100499) (h1 : term99 _100499) : term4 _100499 _45181 _45182.
Proof. exact (@lem3887514 _100499 _45181 _45182 h1). Qed.
Lemma lem3887516 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (h1 : term99 _100499) : term4 _100499 s x.
Proof. exact (@lem3887515 _100499 s x h1). Qed.
Lemma lem3887519 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : s = (term1 _100499 s x).
Proof. exact (@lem3887516 _100499 s x h1 (@lem3887467 _100499 x n s h2)). Qed.
Lemma lem3887520 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : term369 _100499 s x.
Proof. exact (fun h0 : term370 _100499 s x => @lem3887519 _100499 x n s h1 h2). Qed.
Lemma lem3887522 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3887523 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term369 _100499 s x) = (s = (term1 _100499 s x)).
Proof. exact (@lem3887522 (s = (term1 _100499 s x))). Qed.
Lemma lem3887524 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : s = (term1 _100499 s x).
Proof. exact (EQ_MP (@lem3887523 _100499 s x) (@lem3887520 _100499 x n s h1 h2)). Qed.
Lemma lem3887530 (q : Prop) (p : Prop) (r : Prop) : (term371 p q r) = (term371 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3887531 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term190 _100499 n s _45183 _45184) = (term372 _100499 n s _45183 _45184).
Proof. exact (@lem3887530 (@IN _100499 _45183 _45184) (term373 _100499 _45184 n) (term181 _100499 s _45183 _45184)). Qed.
Lemma lem3887545 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3887546 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : (term374 _100499 n s _45183 _45184) = (term375 _100499 s _45183 _45184 n).
Proof. exact (@lem3887545 (term181 _100499 s _45183 _45184) (term373 _100499 _45184 n)). Qed.
Lemma lem3887554 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) : (term183 _100499 _45183 _45184) = (term183 _100499 _45183 _45184).
Proof. exact (eq_refl (term183 _100499 _45183 _45184)). Qed.
Lemma lem3887555 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : (term372 _100499 n s _45183 _45184) = (term376 _100499 s _45183 _45184 n).
Proof. exact (MK_COMB (@lem3887554 _100499 _45183 _45184) (@lem3887546 _100499 s _45183 _45184 n)). Qed.
Lemma lem3887566 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : (term190 _100499 n s _45183 _45184) = (term376 _100499 s _45183 _45184 n).
Proof. exact (TRANS (@lem3887531 _100499 n s _45183 _45184) (@lem3887555 _100499 s _45183 _45184 n)). Qed.
Lemma lem3887567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3887568 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : (term377 _100499 n s _45183 _45184) = (term378 _100499 s _45183 _45184 n).
Proof. exact (MK_COMB (@lem3887567) (@lem3887566 _100499 s _45183 _45184 n)). Qed.
Lemma lem3887582 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3887583 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : (term374 _100499 n s _45183 _45184) = (term375 _100499 s _45183 _45184 n).
Proof. exact (@lem3887582 (term181 _100499 s _45183 _45184) (term373 _100499 _45184 n)). Qed.
Lemma lem3887591 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) : (term183 _100499 _45183 _45184) = (term183 _100499 _45183 _45184).
Proof. exact (eq_refl (term183 _100499 _45183 _45184)). Qed.
Lemma lem3887592 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : (term372 _100499 n s _45183 _45184) = (term376 _100499 s _45183 _45184 n).
Proof. exact (MK_COMB (@lem3887591 _100499 _45183 _45184) (@lem3887583 _100499 s _45183 _45184 n)). Qed.
Lemma lem3887603 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : ((term190 _100499 n s _45183 _45184) = (term372 _100499 n s _45183 _45184)) = ((term376 _100499 s _45183 _45184 n) = (term376 _100499 s _45183 _45184 n)).
Proof. exact (MK_COMB (@lem3887568 _100499 s _45183 _45184 n) (@lem3887592 _100499 s _45183 _45184 n)). Qed.
Lemma lem3887605 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3887606 (x : Prop) : (x = x) = True.
Proof. exact (@lem3887605 Prop x). Qed.
Lemma lem3887607 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) (n : nat) : ((term376 _100499 s _45183 _45184 n) = (term376 _100499 s _45183 _45184 n)) = True.
Proof. exact (@lem3887606 (term376 _100499 s _45183 _45184 n)). Qed.
Lemma lem3887608 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : ((term190 _100499 n s _45183 _45184) = (term372 _100499 n s _45183 _45184)) = True.
Proof. exact (TRANS (@lem3887603 _100499 s _45183 _45184 n) (@lem3887607 _100499 s _45183 _45184 n)). Qed.
Lemma lem3887609 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : True = ((term190 _100499 n s _45183 _45184) = (term372 _100499 n s _45183 _45184)).
Proof. exact (SYM (@lem3887608 _100499 n s _45183 _45184)). Qed.
Lemma lem3887610 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term190 _100499 n s _45183 _45184) = (term372 _100499 n s _45183 _45184).
Proof. exact (EQ_MP (@lem3887609 _100499 n s _45183 _45184) (@lem0)). Qed.
Lemma lem3887611 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term372 _100499 n s _45183 _45184.
Proof. exact (EQ_MP (@lem3887610 _100499 n s _45183 _45184) (@lem3887238 _100499 _45183 _45184 x n s h1)). Qed.
Lemma lem3887613 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3887614 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term372 _100499 n s _45183 _45184) = (term379 _100499 n s _45183 _45184).
Proof. exact (@lem3887613 (term374 _100499 n s _45183 _45184) (@IN _100499 _45183 _45184)). Qed.
Lemma lem3887616 (a : Prop) (b : Prop) : (term380 a b) = (term381 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3887617 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term382 _100499 n s _45183 _45184) = (term383 _100499 n s _45183 _45184).
Proof. exact (@lem3887616 (term373 _100499 _45184 n) (term181 _100499 s _45183 _45184)). Qed.
Lemma lem3887619 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3887620 {_100499 : Type'} (_45184 : _100499 -> Prop) (n : nat) : (term384 _100499 _45184 n) = (@HAS_SIZE _100499 _45184 n).
Proof. exact (@lem3887619 (@HAS_SIZE _100499 _45184 n)). Qed.
Lemma lem3887621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3887622 {_100499 : Type'} (_45184 : _100499 -> Prop) (n : nat) : (term385 _100499 _45184 n) = (term386 _100499 _45184 n).
Proof. exact (MK_COMB (@lem3887621) (@lem3887620 _100499 _45184 n)). Qed.
Lemma lem3887624 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3887625 {_100499 : Type'} (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term387 _100499 s _45183 _45184) = (s = (@INSERT _100499 _45183 _45184)).
Proof. exact (@lem3887624 (s = (@INSERT _100499 _45183 _45184))). Qed.
Lemma lem3887626 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term383 _100499 n s _45183 _45184) = (term388 _100499 n s _45183 _45184).
Proof. exact (MK_COMB (@lem3887622 _100499 _45184 n) (@lem3887625 _100499 s _45183 _45184)). Qed.
Lemma lem3887627 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term382 _100499 n s _45183 _45184) = (term388 _100499 n s _45183 _45184).
Proof. exact (TRANS (@lem3887617 _100499 n s _45183 _45184) (@lem3887626 _100499 n s _45183 _45184)). Qed.
Lemma lem3887628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3887629 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term389 _100499 n s _45183 _45184) = (term390 _100499 n s _45183 _45184).
Proof. exact (MK_COMB (@lem3887628) (@lem3887627 _100499 n s _45183 _45184)). Qed.
Lemma lem3887630 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) : (@IN _100499 _45183 _45184) = (@IN _100499 _45183 _45184).
Proof. exact (eq_refl (@IN _100499 _45183 _45184)). Qed.
Lemma lem3887631 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term379 _100499 n s _45183 _45184) = (term391 _100499 n s _45183 _45184).
Proof. exact (MK_COMB (@lem3887629 _100499 n s _45183 _45184) (@lem3887630 _100499 _45183 _45184)). Qed.
Lemma lem3887632 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (_45183 : _100499) (_45184 : _100499 -> Prop) : (term372 _100499 n s _45183 _45184) = (term391 _100499 n s _45183 _45184).
Proof. exact (TRANS (@lem3887614 _100499 n s _45183 _45184) (@lem3887631 _100499 n s _45183 _45184)). Qed.
Lemma lem3887634 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : term392 _100499 n s x.
Proof. exact (conj (@lem3887460 _100499 x n s h2) (@lem3887524 _100499 x n s h1 h2)). Qed.
Lemma lem3887636 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term391 _100499 n s _45183 _45184.
Proof. exact (EQ_MP (@lem3887632 _100499 n s _45183 _45184) (@lem3887611 _100499 _45183 _45184 x n s h1)). Qed.
Lemma lem3887637 {_100499 : Type'} (_45183 : _100499) (_45184 : _100499 -> Prop) (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term391 _100499 n s _45183 _45184.
Proof. exact (@lem3887636 _100499 _45183 _45184 x n s h1). Qed.
Lemma lem3887638 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term244 _100499 x n s) : term393 _100499 n s x.
Proof. exact (@lem3887637 _100499 x (@DELETE _100499 s x) x n s h1). Qed.
Lemma lem3887641 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : term394 _100499 s x.
Proof. exact (@lem3887638 _100499 x n s h2 (@lem3887634 _100499 x n s h1 h2)). Qed.
Lemma lem3887642 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : term395 _100499 s x.
Proof. exact (fun h0 : term396 _100499 s x => @lem3887641 _100499 x n s h1 h2). Qed.
Lemma lem3887644 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3887645 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) : (term395 _100499 s x) = (term394 _100499 s x).
Proof. exact (@lem3887644 (term394 _100499 s x)). Qed.
Lemma lem3887646 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : term394 _100499 s x.
Proof. exact (EQ_MP (@lem3887645 _100499 s x) (@lem3887642 _100499 x n s h1 h2)). Qed.
Lemma lem3887648 {_100499 : Type'} (x : _100499) : x = x.
Proof. exact (@lem21386 _100499 x). Qed.
Lemma lem3887649 {_100499 : Type'} (x : _100499) : x = x.
Proof. exact (@lem3887648 _100499 x). Qed.
Lemma lem3887650 {_100499 : Type'} (x : _100499) : term74 _100499 x.
Proof. exact (fun h0 : term63 _100499 x => @lem3887649 _100499 x). Qed.
Lemma lem3887652 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3887653 {_100499 : Type'} (x : _100499) : (term74 _100499 x) = (x = x).
Proof. exact (@lem3887652 (x = x)). Qed.
Lemma lem3887654 {_100499 : Type'} (x : _100499) : x = x.
Proof. exact (EQ_MP (@lem3887653 _100499 x) (@lem3887650 _100499 x)). Qed.
Lemma lem3887656 (a : Prop) (b : Prop) : (term397 a b) = (term398 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3887657 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) : (term355 _100499 _45195 _45196 _45197) = (term399 _100499 _45195 _45196 _45197).
Proof. exact (@lem3887656 (term13 _100499 _45196 _45195 _45197) (_45196 = _45197)). Qed.
Lemma lem3887659 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3887660 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) : (term399 _100499 _45195 _45196 _45197) = (term400 _100499 _45195 _45196 _45197).
Proof. exact (@lem3887659 (term401 _100499 _45195 _45196 _45197)). Qed.
Lemma lem3887661 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) : (term355 _100499 _45195 _45196 _45197) = (term400 _100499 _45195 _45196 _45197).
Proof. exact (TRANS (@lem3887657 _100499 _45195 _45196 _45197) (@lem3887660 _100499 _45195 _45196 _45197)). Qed.
Lemma lem3887663 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term99 _100499) (h2 : term244 _100499 x n s) : term402 _100499 s x.
Proof. exact (conj (@lem3887646 _100499 x n s h1 h2) (@lem3887654 _100499 x)). Qed.
Lemma lem3887665 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) (h1 : term130 _100499) : term400 _100499 _45195 _45196 _45197.
Proof. exact (EQ_MP (@lem3887661 _100499 _45195 _45196 _45197) (@lem3887278 _100499 _45195 _45196 _45197 h1)). Qed.
Lemma lem3887666 {_100499 : Type'} (_45195 : _100499 -> Prop) (_45196 : _100499) (_45197 : _100499) (h1 : term130 _100499) : term400 _100499 _45195 _45196 _45197.
Proof. exact (@lem3887665 _100499 _45195 _45196 _45197 h1). Qed.
Lemma lem3887667 {_100499 : Type'} (s : _100499 -> Prop) (x : _100499) (h1 : term130 _100499) : term403 _100499 s x.
Proof. exact (@lem3887666 _100499 s x x h1). Qed.
Lemma lem3887670 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term99 _100499) (h3 : term244 _100499 x n s) : False.
Proof. exact (@lem3887667 _100499 s x h1 (@lem3887663 _100499 x n s h2 h3)). Qed.
Lemma lem3887671 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term99 _100499) (h3 : term244 _100499 x n s) : term73.
Proof. exact (fun h0 : ~ False => @lem3887670 _100499 x n s h1 h2 h3). Qed.
Lemma lem3887673 (p : Prop) : (term71 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3887674 : term73 = False.
Proof. exact (@lem3887673 False). Qed.
Lemma lem3887675 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term99 _100499) (h3 : term244 _100499 x n s) : False.
Proof. exact (EQ_MP (@lem3887674) (@lem3887671 _100499 x n s h1 h2 h3)). Qed.
Lemma lem3887676 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term99 _100499) (h3 : term244 _100499 x n s) : (term244 _100499 x n s) = False.
Proof. exact (prop_ext (fun h4 : term244 _100499 x n s => @lem3887675 _100499 x n s h1 h2 h3) (fun h4 : False => @lem3886996 _100499 x n s h3)). Qed.
Lemma lem3887677 {_100499 : Type'} (x : _100499) (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term99 _100499) (h3 : term244 _100499 x n s) : False.
Proof. exact (EQ_MP (@lem3887676 _100499 x n s h1 h2 h3) (@lem3886996 _100499 x n s h3)). Qed.
Lemma lem3887678 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term99 _100499) (h3 : term129 _100499 n s) : False.
Proof. exact (ex_elim (@lem3885772 _100499 n s h3) (fun x : _100499 => fun h0 : term246 _100499 n s x => @lem3887677 _100499 x n s h1 h2 h0)). Qed.
Lemma lem3887679 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term129 _100499 n s) : term136 _100499.
Proof. exact (fun h0 : term99 _100499 => @lem3887678 _100499 n s h1 h0 h2). Qed.
Lemma lem3887680 {_100499 : Type'} : (term136 _100499) = (term137 _100499).
Proof. exact (@lem69 (term99 _100499)). Qed.
Lemma lem3887681 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term129 _100499 n s) : term137 _100499.
Proof. exact (EQ_MP (@lem3887680 _100499) (@lem3887679 _100499 n s h1 h2)). Qed.
Lemma lem3887682 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term130 _100499) (h2 : term129 _100499 n s) : term140 _100499.
Proof. exact (fun h0 : term131 _100499 => @lem3887681 _100499 n s h1 h2). Qed.
Lemma lem3887683 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : term143 _100499.
Proof. exact (fun h0 : term130 _100499 => @lem3887682 _100499 n s h0 h1). Qed.
Lemma lem3887684 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term145 _100499 n s.
Proof. exact (fun h0 : term129 _100499 n s => @lem3887683 _100499 n s h0). Qed.
Lemma lem3887689 {_100499 : Type'} (s : _100499 -> Prop) : term149 _100499 s.
Proof. exact (fun n : nat => @lem3887684 _100499 n s). Qed.
Lemma lem3887694 {_100499 : Type'} : term153 _100499.
Proof. exact (fun s : _100499 -> Prop => @lem3887689 _100499 s). Qed.
Lemma lem3887695 {_100499 : Type'} : term152 _100499.
Proof. exact (EQ_MP (@lem3885550 _100499) (@lem3887694 _100499)). Qed.
Lemma lem3887696 {_100499 : Type'} (s : _100499 -> Prop) : term404 _100499 s.
Proof. exact (@lem3887695 _100499 s). Qed.
Lemma lem3887697 {_100499 : Type'} (s : _100499 -> Prop) : (term404 _100499 s) = (term148 _100499 s).
Proof. exact (eq_refl (term404 _100499 s)). Qed.
Lemma lem3887698 {_100499 : Type'} (s : _100499 -> Prop) : term148 _100499 s.
Proof. exact (EQ_MP (@lem3887697 _100499 s) (@lem3887696 _100499 s)). Qed.
Lemma lem3887699 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : term405 _100499 s n.
Proof. exact (@lem3887698 _100499 s n). Qed.
Lemma lem3887700 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term405 _100499 s n) = (term132 _100499 n s).
Proof. exact (eq_refl (term405 _100499 s n)). Qed.
Lemma lem3887701 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term132 _100499 n s.
Proof. exact (EQ_MP (@lem3887700 _100499 n s) (@lem3887699 _100499 s n)). Qed.
Lemma lem3887703 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term132 _100499 n s.
Proof. exact (@lem3885180 _100499 n s (@lem3887701 _100499 n s)). Qed.
Lemma lem3887704 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : term142 _100499.
Proof. exact (@lem3887703 _100499 n s (@lem3885157 _100499 n s h1)). Qed.
Lemma lem3887705 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : term139 _100499.
Proof. exact (@lem3887704 _100499 n s h1 (@lem3885162 _100499)). Qed.
Lemma lem3887706 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : term136 _100499.
Proof. exact (@lem3887705 _100499 n s h1 (@lem3885164 _100499)). Qed.
Lemma lem3887707 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : False.
Proof. exact (@lem3887706 _100499 n s h1 (@lem3885158 _100499)). Qed.
Lemma lem3887708 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : (term129 _100499 n s) = False.
Proof. exact (prop_ext (fun h2 : term129 _100499 n s => @lem3887707 _100499 n s h1) (fun h2 : False => @lem3885157 _100499 n s h1)). Qed.
Lemma lem3887709 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (h1 : term129 _100499 n s) : False.
Proof. exact (EQ_MP (@lem3887708 _100499 n s h1) (@lem3885157 _100499 n s h1)). Qed.
Lemma lem3887710 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term128 _100499 n s.
Proof. exact (fun h0 : term129 _100499 n s => @lem3887709 _100499 n s h0). Qed.
Lemma lem3887711 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term127 _100499 n s.
Proof. exact (EQ_MP (@lem3885156 _100499 n s) (@lem3887710 _100499 n s)). Qed.
Lemma lem3887712 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term126 _100499 n s.
Proof. exact (EQ_MP (@lem3885152 _100499 n s) (@lem3887711 _100499 n s)). Qed.
Lemma lem3887714 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem3885008 A P Q) (@lem3885007 A P Q)). Qed.
Lemma lem3887715 {_100499 : Type'} (P : _100499 -> Prop) (Q : Prop) : (term96 _100499 P Q) = (term97 _100499 P Q).
Proof. exact (@lem3887714 _100499 P Q). Qed.
Lemma lem3887716 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term406 _100499 s n) = (term407 _100499 s n).
Proof. exact (@lem3887715 _100499 (term171 _100499 n s) (term110 _100499 s n)). Qed.
Lemma lem3887717 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term206 _100499 n s a) = (term170 _100499 n s a).
Proof. exact (eq_refl (term206 _100499 n s a)). Qed.
Lemma lem3887718 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term408 _100499 n s) = (term171 _100499 n s).
Proof. exact (fun_ext (fun a : _100499 => @lem3887717 _100499 n s a)). Qed.
Lemma lem3887719 {_100499 : Type'} : (@ex _100499) = (@ex _100499).
Proof. exact (eq_refl (@ex _100499)). Qed.
Lemma lem3887720 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term409 _100499 n s) = (term117 _100499 n s).
Proof. exact (MK_COMB (@lem3887719 _100499) (@lem3887718 _100499 n s)). Qed.
Lemma lem3887721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3887722 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term410 _100499 n s) = (term411 _100499 n s).
Proof. exact (MK_COMB (@lem3887721) (@lem3887720 _100499 n s)). Qed.
Lemma lem3887723 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term110 _100499 s n) = (term110 _100499 s n).
Proof. exact (eq_refl (term110 _100499 s n)). Qed.
Lemma lem3887724 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term406 _100499 s n) = (term412 _100499 s n).
Proof. exact (MK_COMB (@lem3887722 _100499 n s) (@lem3887723 _100499 s n)). Qed.
Lemma lem3887725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3887726 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term413 _100499 s n) = (term414 _100499 s n).
Proof. exact (MK_COMB (@lem3887725) (@lem3887724 _100499 s n)). Qed.
Lemma lem3887727 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term206 _100499 n s a) = (term170 _100499 n s a).
Proof. exact (eq_refl (term206 _100499 n s a)). Qed.
Lemma lem3887728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3887729 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term415 _100499 n s a) = (term416 _100499 n s a).
Proof. exact (MK_COMB (@lem3887728) (@lem3887727 _100499 n s a)). Qed.
Lemma lem3887730 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term110 _100499 s n) = (term110 _100499 s n).
Proof. exact (eq_refl (term110 _100499 s n)). Qed.
Lemma lem3887731 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term417 _100499 a s n) = (term418 _100499 a s n).
Proof. exact (MK_COMB (@lem3887729 _100499 n s a) (@lem3887730 _100499 s n)). Qed.
Lemma lem3887732 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term419 _100499 s n) = (term420 _100499 s n).
Proof. exact (fun_ext (fun a : _100499 => @lem3887731 _100499 a s n)). Qed.
Lemma lem3887733 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3887734 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term407 _100499 s n) = (term421 _100499 s n).
Proof. exact (MK_COMB (@lem3887733 _100499) (@lem3887732 _100499 s n)). Qed.
Lemma lem3887735 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : ((term406 _100499 s n) = (term407 _100499 s n)) = ((term412 _100499 s n) = (term421 _100499 s n)).
Proof. exact (MK_COMB (@lem3887726 _100499 s n) (@lem3887734 _100499 s n)). Qed.
Lemma lem3887736 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term412 _100499 s n) = (term421 _100499 s n).
Proof. exact (EQ_MP (@lem3887735 _100499 s n) (@lem3887716 _100499 s n)). Qed.
Lemma lem3887742 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem3885008 A P Q) (@lem3885007 A P Q)). Qed.
Lemma lem3887743 {_100499 : Type'} (P : type686 _100499) (Q : Prop) : (term422 _100499 P Q) = (term423 _100499 P Q).
Proof. exact (@lem3887742 (_100499 -> Prop) P Q). Qed.
Lemma lem3887744 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term424 _100499 a s n) = (term425 _100499 a s n).
Proof. exact (@lem3887743 _100499 (term169 _100499 n s a) (term110 _100499 s n)). Qed.
Lemma lem3887745 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term197 _100499 n s a t) = (term168 _100499 n s a t).
Proof. exact (eq_refl (term197 _100499 n s a t)). Qed.
Lemma lem3887746 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term426 _100499 n s a) = (term169 _100499 n s a).
Proof. exact (fun_ext (fun t : _100499 -> Prop => @lem3887745 _100499 n s a t)). Qed.
Lemma lem3887747 {_100499 : Type'} : (@ex (_100499 -> Prop)) = (@ex (_100499 -> Prop)).
Proof. exact (eq_refl (@ex (_100499 -> Prop))). Qed.
Lemma lem3887748 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term427 _100499 n s a) = (term170 _100499 n s a).
Proof. exact (MK_COMB (@lem3887747 _100499) (@lem3887746 _100499 n s a)). Qed.
Lemma lem3887749 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3887750 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) : (term428 _100499 n s a) = (term416 _100499 n s a).
Proof. exact (MK_COMB (@lem3887749) (@lem3887748 _100499 n s a)). Qed.
Lemma lem3887751 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term110 _100499 s n) = (term110 _100499 s n).
Proof. exact (eq_refl (term110 _100499 s n)). Qed.
Lemma lem3887752 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term424 _100499 a s n) = (term418 _100499 a s n).
Proof. exact (MK_COMB (@lem3887750 _100499 n s a) (@lem3887751 _100499 s n)). Qed.
Lemma lem3887753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3887754 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term429 _100499 a s n) = (term430 _100499 a s n).
Proof. exact (MK_COMB (@lem3887753) (@lem3887752 _100499 a s n)). Qed.
Lemma lem3887755 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term197 _100499 n s a t) = (term168 _100499 n s a t).
Proof. exact (eq_refl (term197 _100499 n s a t)). Qed.
Lemma lem3887756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3887757 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term431 _100499 n s a t) = (term432 _100499 n s a t).
Proof. exact (MK_COMB (@lem3887756) (@lem3887755 _100499 n s a t)). Qed.
Lemma lem3887758 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term110 _100499 s n) = (term110 _100499 s n).
Proof. exact (eq_refl (term110 _100499 s n)). Qed.
Lemma lem3887759 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) : (term433 _100499 a t s n) = (term434 _100499 a t s n).
Proof. exact (MK_COMB (@lem3887757 _100499 n s a t) (@lem3887758 _100499 s n)). Qed.
Lemma lem3887760 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term435 _100499 a s n) = (term436 _100499 a s n).
Proof. exact (fun_ext (fun t : _100499 -> Prop => @lem3887759 _100499 a t s n)). Qed.
Lemma lem3887761 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3887762 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term425 _100499 a s n) = (term437 _100499 a s n).
Proof. exact (MK_COMB (@lem3887761 _100499) (@lem3887760 _100499 a s n)). Qed.
Lemma lem3887763 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : ((term424 _100499 a s n) = (term425 _100499 a s n)) = ((term418 _100499 a s n) = (term437 _100499 a s n)).
Proof. exact (MK_COMB (@lem3887754 _100499 a s n) (@lem3887762 _100499 a s n)). Qed.
Lemma lem3887764 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term418 _100499 a s n) = (term437 _100499 a s n).
Proof. exact (EQ_MP (@lem3887763 _100499 a s n) (@lem3887744 _100499 a s n)). Qed.
Lemma lem3887772 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term438 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3887773 (p : Prop) (q : Prop) (p' : Prop) : term439 p q p'.
Proof. exact (fun q' : Prop => @lem3887772 p q p' q'). Qed.
Lemma lem3887774 (p : Prop) (q : Prop) : term440 p q.
Proof. exact (fun p' : Prop => @lem3887773 p q p'). Qed.
Lemma lem3887775 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) : term441 _100499 a t s n.
Proof. exact (@lem3887774 (term168 _100499 n s a t) (term110 _100499 s n)). Qed.
Lemma lem3887776 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) (p' : Prop) : term442 _100499 a t s n p'.
Proof. exact (@lem3887775 _100499 a t s n p'). Qed.
Lemma lem3887777 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) (p' : Prop) : (term442 _100499 a t s n p') = (term443 _100499 a t s n p').
Proof. exact (eq_refl (term442 _100499 a t s n p')). Qed.
Lemma lem3887778 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) (p' : Prop) : term443 _100499 a t s n p'.
Proof. exact (EQ_MP (@lem3887777 _100499 a t s n p') (@lem3887776 _100499 a t s n p')). Qed.
Lemma lem3887779 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term444 _100499 a t s n p' q'.
Proof. exact (@lem3887778 _100499 a t s n p' q'). Qed.
Lemma lem3887780 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) (p' : Prop) (q' : Prop) : (term444 _100499 a t s n p' q') = (term445 _100499 a t s n p' q').
Proof. exact (eq_refl (term444 _100499 a t s n p' q')). Qed.
Lemma lem3887781 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term445 _100499 a t s n p' q'.
Proof. exact (EQ_MP (@lem3887780 _100499 a t s n p' q') (@lem3887779 _100499 a t s n p' q')). Qed.
Lemma lem3887785 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term92 _100044 s n).
Proof. exact (EQ_MP (@lem3885002 _100044 s n) (@lem3885001 _100044 s n)). Qed.
Lemma lem3887786 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (@HAS_SIZE _100499 s n) = (term92 _100499 s n).
Proof. exact (@lem3887785 _100499 s n). Qed.
Lemma lem3887787 {_100499 : Type'} (t : _100499 -> Prop) (n : nat) : (@HAS_SIZE _100499 t n) = (term92 _100499 t n).
Proof. exact (@lem3887786 _100499 t n). Qed.
Lemma lem3887792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3887793 {_100499 : Type'} (t : _100499 -> Prop) (n : nat) : (term386 _100499 t n) = (term446 _100499 t n).
Proof. exact (MK_COMB (@lem3887792) (@lem3887787 _100499 t n)). Qed.
Lemma lem3887802 {_100499 : Type'} (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term192 _100499 s a t) = (term192 _100499 s a t).
Proof. exact (eq_refl (term192 _100499 s a t)). Qed.
Lemma lem3887803 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term168 _100499 n s a t) = (term447 _100499 n s a t).
Proof. exact (MK_COMB (@lem3887793 _100499 t n) (@lem3887802 _100499 s a t)). Qed.
Lemma lem3887814 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (q' : Prop) : term448 _100499 n s a t q'.
Proof. exact (@lem3887781 _100499 a t s n (term447 _100499 n s a t) q'). Qed.
Lemma lem3887815 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (q' : Prop) : term449 _100499 n s a t q'.
Proof. exact (@lem3887814 _100499 n s a t q' (@lem3887803 _100499 n s a t)). Qed.
Lemma lem3887816 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term447 _100499 n s a t.
Proof. exact (h1). Qed.
Lemma lem3887817 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term192 _100499 s a t.
Proof. exact (proj2 (@lem3887816 _100499 n s a t h1)). Qed.
Lemma lem3887819 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term187 _100499 a t.
Proof. exact (proj1 (@lem3887817 _100499 n s a t h1)). Qed.
Lemma lem3887820 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) : term450 _100499 a t.
Proof. exact (@lem82 (@IN _100499 a t)). Qed.
Lemma lem3887822 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term92 _100499 t n.
Proof. exact (proj1 (@lem3887816 _100499 n s a t h1)). Qed.
Lemma lem3887824 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : @FINITE _100499 t.
Proof. exact (proj1 (@lem3887822 _100499 n s a t h1)). Qed.
Lemma lem3887825 {_100499 : Type'} (t : _100499 -> Prop) : (@FINITE _100499 t) = ((@FINITE _100499 t) = True).
Proof. exact (@lem7 (@FINITE _100499 t)). Qed.
Lemma lem3887828 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term92 _100044 s n).
Proof. exact (EQ_MP (@lem3885002 _100044 s n) (@lem3885001 _100044 s n)). Qed.
Lemma lem3887829 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (@HAS_SIZE _100499 s n) = (term92 _100499 s n).
Proof. exact (@lem3887828 _100499 s n). Qed.
Lemma lem3887830 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term110 _100499 s n) = (term451 _100499 s n).
Proof. exact (@lem3887829 _100499 s (S n)). Qed.
Lemma lem3887834 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : s = (@INSERT _100499 a t).
Proof. exact (proj2 (@lem3887817 _100499 n s a t h1)). Qed.
Lemma lem3887835 {_100499 : Type'} : (@FINITE _100499) = (@FINITE _100499).
Proof. exact (eq_refl (@FINITE _100499)). Qed.
Lemma lem3887836 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@FINITE _100499 s) = (term81 _100499 a t).
Proof. exact (MK_COMB (@lem3887835 _100499) (@lem3887834 _100499 n s a t h1)). Qed.
Lemma lem3887838 {A : Type'} (x : A) (s : A -> Prop) : (term81 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3884981 A x s) (@lem3884980 A s x)). Qed.
Lemma lem3887839 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : (term81 _100499 x s) = (@FINITE _100499 s).
Proof. exact (@lem3887838 _100499 x s). Qed.
Lemma lem3887840 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) : (term81 _100499 a t) = (@FINITE _100499 t).
Proof. exact (@lem3887839 _100499 a t). Qed.
Lemma lem3887842 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@FINITE _100499 t) = True.
Proof. exact (EQ_MP (@lem3887825 _100499 t) (@lem3887824 _100499 n s a t h1)). Qed.
Lemma lem3887843 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term81 _100499 a t) = True.
Proof. exact (TRANS (@lem3887840 _100499 a t) (@lem3887842 _100499 n s a t h1)). Qed.
Lemma lem3887844 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@FINITE _100499 s) = True.
Proof. exact (TRANS (@lem3887836 _100499 n s a t h1) (@lem3887843 _100499 n s a t h1)). Qed.
Lemma lem3887845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3887846 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term452 _100499 s) = (and True).
Proof. exact (MK_COMB (@lem3887845) (@lem3887844 _100499 n s a t h1)). Qed.
Lemma lem3887850 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : s = (@INSERT _100499 a t).
Proof. exact (proj2 (@lem3887817 _100499 n s a t h1)). Qed.
Lemma lem3887851 {_100499 : Type'} : (@CARD _100499) = (@CARD _100499).
Proof. exact (eq_refl (@CARD _100499)). Qed.
Lemma lem3887852 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@CARD _100499 s) = (term87 _100499 a t).
Proof. exact (MK_COMB (@lem3887851 _100499) (@lem3887850 _100499 n s a t h1)). Qed.
Lemma lem3887854 {A : Type'} (x : A) (s : A -> Prop) : term86 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3884991 A x s h0). Qed.
Lemma lem3887855 {_100499 : Type'} (x : _100499) (s : _100499 -> Prop) : term86 _100499 x s.
Proof. exact (@lem3887854 _100499 x s). Qed.
Lemma lem3887856 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) : term86 _100499 a t.
Proof. exact (@lem3887855 _100499 a t). Qed.
Lemma lem3887858 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@FINITE _100499 t) = True.
Proof. exact (EQ_MP (@lem3887825 _100499 t) (@lem3887824 _100499 n s a t h1)). Qed.
Lemma lem3887859 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : True = (@FINITE _100499 t).
Proof. exact (SYM (@lem3887858 _100499 n s a t h1)). Qed.
Lemma lem3887860 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : @FINITE _100499 t.
Proof. exact (EQ_MP (@lem3887859 _100499 n s a t h1) (@lem0)). Qed.
Lemma lem3887861 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term87 _100499 a t) = (term88 _100499 a t).
Proof. exact (@lem3887856 _100499 a t (@lem3887860 _100499 n s a t h1)). Qed.
Lemma lem3887863 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term453 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3887864 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term454 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3887863 _2963 g t e g' t' e'). Qed.
Lemma lem3887865 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term455 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3887864 _2963 g t e g' t'). Qed.
Lemma lem3887866 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term456 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3887865 _2963 g t e g'). Qed.
Lemma lem3887867 (g : Prop) (t : nat) (e : nat) : term457 g t e.
Proof. exact (@lem3887866 nat g t e). Qed.
Lemma lem3887868 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) : term458 _100499 a t.
Proof. exact (@lem3887867 (@IN _100499 a t) (@CARD _100499 t) (term459 _100499 t)). Qed.
Lemma lem3887869 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) : term460 _100499 a t g'.
Proof. exact (@lem3887868 _100499 a t g'). Qed.
Lemma lem3887870 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) : (term460 _100499 a t g') = (term461 _100499 a t g').
Proof. exact (eq_refl (term460 _100499 a t g')). Qed.
Lemma lem3887871 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) : term461 _100499 a t g'.
Proof. exact (EQ_MP (@lem3887870 _100499 a t g') (@lem3887869 _100499 a t g')). Qed.
Lemma lem3887872 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) (t' : nat) : term462 _100499 a t g' t'.
Proof. exact (@lem3887871 _100499 a t g' t'). Qed.
Lemma lem3887873 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) (t' : nat) : (term462 _100499 a t g' t') = (term463 _100499 a t g' t').
Proof. exact (eq_refl (term462 _100499 a t g' t')). Qed.
Lemma lem3887874 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) (t' : nat) : term463 _100499 a t g' t'.
Proof. exact (EQ_MP (@lem3887873 _100499 a t g' t') (@lem3887872 _100499 a t g' t')). Qed.
Lemma lem3887875 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term464 _100499 a t g' t' e'.
Proof. exact (@lem3887874 _100499 a t g' t' e'). Qed.
Lemma lem3887876 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term464 _100499 a t g' t' e') = (term465 _100499 a t g' t' e').
Proof. exact (eq_refl (term464 _100499 a t g' t' e')). Qed.
Lemma lem3887877 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term465 _100499 a t g' t' e'.
Proof. exact (EQ_MP (@lem3887876 _100499 a t g' t' e') (@lem3887875 _100499 a t g' t' e')). Qed.
Lemma lem3887879 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@IN _100499 a t) = False.
Proof. exact (@lem3887820 _100499 a t (@lem3887819 _100499 n s a t h1)). Qed.
Lemma lem3887880 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (t' : nat) (e' : nat) : term466 _100499 a t t' e'.
Proof. exact (@lem3887877 _100499 a t False t' e'). Qed.
Lemma lem3887881 {_100499 : Type'} (t' : nat) (e' : nat) (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term467 _100499 a t t' e'.
Proof. exact (@lem3887880 _100499 a t t' e' (@lem3887879 _100499 n s a t h1)). Qed.
Lemma lem3887886 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@CARD _100499 t) = n.
Proof. exact (proj2 (@lem3887822 _100499 n s a t h1)). Qed.
Lemma lem3887887 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term468 _100499 t n.
Proof. exact (fun h0 : False => @lem3887886 _100499 n s a t h1). Qed.
Lemma lem3887888 {_100499 : Type'} (e' : nat) (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term467 _100499 a t n e'.
Proof. exact (@lem3887881 _100499 n e' n s a t h1). Qed.
Lemma lem3887889 {_100499 : Type'} (e' : nat) (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term469 _100499 a t n e'.
Proof. exact (@lem3887888 _100499 e' n s a t h1 (@lem3887887 _100499 n s a t h1)). Qed.
Lemma lem3887896 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@CARD _100499 t) = n.
Proof. exact (proj2 (@lem3887822 _100499 n s a t h1)). Qed.
Lemma lem3887897 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem3887898 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term459 _100499 t) = (S n).
Proof. exact (MK_COMB (@lem3887897) (@lem3887896 _100499 n s a t h1)). Qed.
Lemma lem3887899 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term470 _100499 t n.
Proof. exact (fun h0 : ~ False => @lem3887898 _100499 n s a t h1). Qed.
Lemma lem3887900 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : term471 _100499 a t n.
Proof. exact (@lem3887889 _100499 (S n) n s a t h1). Qed.
Lemma lem3887901 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term88 _100499 a t) = (term472 n).
Proof. exact (@lem3887900 _100499 n s a t h1 (@lem3887899 _100499 n s a t h1)). Qed.
Lemma lem3887903 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3887904 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3887903 nat t1 t2). Qed.
Lemma lem3887905 (n : nat) : (term472 n) = (S n).
Proof. exact (@lem3887904 n (S n)). Qed.
Lemma lem3887906 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term88 _100499 a t) = (S n).
Proof. exact (TRANS (@lem3887901 _100499 n s a t h1) (@lem3887905 n)). Qed.
Lemma lem3887907 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term87 _100499 a t) = (S n).
Proof. exact (TRANS (@lem3887861 _100499 n s a t h1) (@lem3887906 _100499 n s a t h1)). Qed.
Lemma lem3887908 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (@CARD _100499 s) = (S n).
Proof. exact (TRANS (@lem3887852 _100499 n s a t h1) (@lem3887907 _100499 n s a t h1)). Qed.
Lemma lem3887909 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3887910 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term473 _100499 s) = (term474 n).
Proof. exact (MK_COMB (@lem3887909) (@lem3887908 _100499 n s a t h1)). Qed.
Lemma lem3887911 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem3887912 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : ((@CARD _100499 s) = (S n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem3887910 _100499 n s a t h1) (@lem3887911 n)). Qed.
Lemma lem3887914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3887915 (x : nat) : (x = x) = True.
Proof. exact (@lem3887914 nat x). Qed.
Lemma lem3887916 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem3887915 (S n)). Qed.
Lemma lem3887917 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : ((@CARD _100499 s) = (S n)) = True.
Proof. exact (TRANS (@lem3887912 _100499 n s a t h1) (@lem3887916 n)). Qed.
Lemma lem3887918 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term451 _100499 s n) = (True /\ True).
Proof. exact (MK_COMB (@lem3887846 _100499 n s a t h1) (@lem3887917 _100499 n s a t h1)). Qed.
Lemma lem3887920 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3887921 : (True /\ True) = True.
Proof. exact (@lem3887920 True). Qed.
Lemma lem3887922 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term451 _100499 s n) = True.
Proof. exact (TRANS (@lem3887918 _100499 n s a t h1) (@lem3887921)). Qed.
Lemma lem3887923 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) (h1 : term447 _100499 n s a t) : (term110 _100499 s n) = True.
Proof. exact (TRANS (@lem3887830 _100499 s n) (@lem3887922 _100499 n s a t h1)). Qed.
Lemma lem3887924 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) : term475 _100499 a t s n.
Proof. exact (fun h0 : term447 _100499 n s a t => @lem3887923 _100499 n s a t h0). Qed.
Lemma lem3887925 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : term476 _100499 n s a t.
Proof. exact (@lem3887815 _100499 n s a t True). Qed.
Lemma lem3887926 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term434 _100499 a t s n) = (term477 _100499 n s a t).
Proof. exact (@lem3887925 _100499 n s a t (@lem3887924 _100499 a t s n)). Qed.
Lemma lem3887928 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3887929 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) (a : _100499) (t : _100499 -> Prop) : (term477 _100499 n s a t) = True.
Proof. exact (@lem3887928 (term447 _100499 n s a t)). Qed.
Lemma lem3887930 {_100499 : Type'} (a : _100499) (t : _100499 -> Prop) (s : _100499 -> Prop) (n : nat) : (term434 _100499 a t s n) = True.
Proof. exact (TRANS (@lem3887926 _100499 n s a t) (@lem3887929 _100499 n s a t)). Qed.
Lemma lem3887931 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term436 _100499 a s n) = (term478 _100499).
Proof. exact (fun_ext (fun t : _100499 -> Prop => @lem3887930 _100499 a t s n)). Qed.
Lemma lem3887932 {_100499 : Type'} : (@all (_100499 -> Prop)) = (@all (_100499 -> Prop)).
Proof. exact (eq_refl (@all (_100499 -> Prop))). Qed.
Lemma lem3887933 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term437 _100499 a s n) = (term479 _100499).
Proof. exact (MK_COMB (@lem3887932 _100499) (@lem3887931 _100499 a s n)). Qed.
Lemma lem3887935 {A : Type'} (t : Prop) : (term480 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3887936 {_100499 : Type'} (t : Prop) : (term481 _100499 t) = t.
Proof. exact (@lem3887935 (_100499 -> Prop) t). Qed.
Lemma lem3887937 {_100499 : Type'} : (term479 _100499) = True.
Proof. exact (@lem3887936 _100499 True). Qed.
Lemma lem3887938 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term437 _100499 a s n) = True.
Proof. exact (TRANS (@lem3887933 _100499 a s n) (@lem3887937 _100499)). Qed.
Lemma lem3887939 {_100499 : Type'} (a : _100499) (s : _100499 -> Prop) (n : nat) : (term418 _100499 a s n) = True.
Proof. exact (TRANS (@lem3887764 _100499 a s n) (@lem3887938 _100499 a s n)). Qed.
Lemma lem3887940 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term420 _100499 s n) = (term482 _100499).
Proof. exact (fun_ext (fun a : _100499 => @lem3887939 _100499 a s n)). Qed.
Lemma lem3887941 {_100499 : Type'} : (@all _100499) = (@all _100499).
Proof. exact (eq_refl (@all _100499)). Qed.
Lemma lem3887942 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term421 _100499 s n) = (term483 _100499).
Proof. exact (MK_COMB (@lem3887941 _100499) (@lem3887940 _100499 s n)). Qed.
Lemma lem3887944 {A : Type'} (t : Prop) : (term480 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3887945 {_100499 : Type'} (t : Prop) : (term480 _100499 t) = t.
Proof. exact (@lem3887944 _100499 t). Qed.
Lemma lem3887946 {_100499 : Type'} : (term483 _100499) = True.
Proof. exact (@lem3887945 _100499 True). Qed.
Lemma lem3887947 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term421 _100499 s n) = True.
Proof. exact (TRANS (@lem3887942 _100499 s n) (@lem3887946 _100499)). Qed.
Lemma lem3887948 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : (term412 _100499 s n) = True.
Proof. exact (TRANS (@lem3887736 _100499 s n) (@lem3887947 _100499 s n)). Qed.
Lemma lem3887949 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : True = (term412 _100499 s n).
Proof. exact (SYM (@lem3887948 _100499 s n)). Qed.
Lemma lem3887950 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : term412 _100499 s n.
Proof. exact (EQ_MP (@lem3887949 _100499 s n) (@lem0)). Qed.
Lemma lem3887951 {_100499 : Type'} (s : _100499 -> Prop) (n : nat) : term484 _100499 s n.
Proof. exact (conj (@lem3887712 _100499 n s) (@lem3887950 _100499 s n)). Qed.
Lemma lem3887952 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term484 _100499 s n) = ((term110 _100499 s n) = (term117 _100499 n s)).
Proof. exact (@lem32 (term110 _100499 s n) (term117 _100499 n s)). Qed.
Lemma lem3887953 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term110 _100499 s n) = (term117 _100499 n s).
Proof. exact (EQ_MP (@lem3887952 _100499 n s) (@lem3887951 _100499 s n)). Qed.
Lemma lem3887954 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : term118 _100499 n s.
Proof. exact (EQ_MP (@lem3885104 _100499 n s) (@lem3887953 _100499 n s)). Qed.
