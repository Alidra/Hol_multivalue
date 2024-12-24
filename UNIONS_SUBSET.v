Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3341280 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3341281 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3341282 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3341281 t1) (@lem3341280 t1)). Qed.
Lemma lem3341283 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3341282 t1 t2). Qed.
Lemma lem3341284 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3341285 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3341284 t1 t2) (@lem3341283 t1 t2)). Qed.
Lemma lem3341286 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3341285 t1 t2 t3). Qed.
Lemma lem3341287 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3341288 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3341287 t1 t2 t3) (@lem3341286 t1 t2 t3)). Qed.
Lemma lem3341289 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3341288 t1 t2 t3)). Qed.
Lemma lem3341303 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3341304 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (@SUBSET _87042 s t) = (term7 _87042 s t).
Proof. exact (@lem3341303 _87042 s t). Qed.
Lemma lem3341305 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term8 _87042 f t) = (term9 _87042 f t).
Proof. exact (@lem3341304 _87042 (@UNIONS _87042 f) t). Qed.
Lemma lem3341312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3341313 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term10 _87042 f t) = (term11 _87042 f t).
Proof. exact (MK_COMB (@lem3341312) (@lem3341305 _87042 f t)). Qed.
Lemma lem3341321 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3341322 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (@SUBSET _87042 s t) = (term7 _87042 s t).
Proof. exact (@lem3341321 _87042 s t). Qed.
Lemma lem3341329 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) : (term12 _87042 s f) = (term12 _87042 s f).
Proof. exact (eq_refl (term12 _87042 s f)). Qed.
Lemma lem3341330 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term13 _87042 f s t) = (term14 _87042 f s t).
Proof. exact (MK_COMB (@lem3341329 _87042 s f) (@lem3341322 _87042 s t)). Qed.
Lemma lem3341333 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term15 _87042 f t) = (term16 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3341330 _87042 f s t)). Qed.
Lemma lem3341334 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341335 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term17 _87042 f t) = (term18 _87042 f t).
Proof. exact (MK_COMB (@lem3341334 _87042) (@lem3341333 _87042 f t)). Qed.
Lemma lem3341340 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : ((term8 _87042 f t) = (term17 _87042 f t)) = ((term9 _87042 f t) = (term18 _87042 f t)).
Proof. exact (MK_COMB (@lem3341313 _87042 f t) (@lem3341335 _87042 f t)). Qed.
Lemma lem3341345 {_87042 : Type'} (f : type686 _87042) : (term19 _87042 f) = (term20 _87042 f).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3341340 _87042 f t)). Qed.
Lemma lem3341346 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341347 {_87042 : Type'} (f : type686 _87042) : (term21 _87042 f) = (term22 _87042 f).
Proof. exact (MK_COMB (@lem3341346 _87042) (@lem3341345 _87042 f)). Qed.
Lemma lem3341352 {_87042 : Type'} : (term23 _87042) = (term24 _87042).
Proof. exact (fun_ext (fun f : type686 _87042 => @lem3341347 _87042 f)). Qed.
Lemma lem3341353 {_87042 : Type'} : (@all ((_87042 -> Prop) -> Prop)) = (@all ((_87042 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87042 -> Prop) -> Prop))). Qed.
Lemma lem3341354 {_87042 : Type'} : (term25 _87042) = (term26 _87042).
Proof. exact (MK_COMB (@lem3341353 _87042) (@lem3341352 _87042)). Qed.
Lemma lem3341359 {_87042 : Type'} : (term26 _87042) = (term25 _87042).
Proof. exact (SYM (@lem3341354 _87042)). Qed.
Lemma lem3341377 {A : Type'} (s : type686 A) (x : A) : (term27 A x s) = (term28 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3341378 {_87042 : Type'} (s : type686 _87042) (x : _87042) : (term27 _87042 x s) = (term28 _87042 s x).
Proof. exact (@lem3341377 _87042 s x). Qed.
Lemma lem3341379 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term27 _87042 x f) = (term28 _87042 f x).
Proof. exact (@lem3341378 _87042 f x). Qed.
Lemma lem3341387 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3341388 {_87042 : Type'} (P : type686 _87042) (x : _87042 -> Prop) : (@IN (_87042 -> Prop) x P) = (P x).
Proof. exact (@lem3341387 (_87042 -> Prop) P x). Qed.
Lemma lem3341389 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (@IN (_87042 -> Prop) t f) = (f t).
Proof. exact (@lem3341388 _87042 f t). Qed.
Lemma lem3341390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3341391 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term29 _87042 t f) = (term30 _87042 f t).
Proof. exact (MK_COMB (@lem3341390) (@lem3341389 _87042 f t)). Qed.
Lemma lem3341393 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3341394 {_87042 : Type'} (P : _87042 -> Prop) (x : _87042) : (@IN _87042 x P) = (P x).
Proof. exact (@lem3341393 _87042 P x). Qed.
Lemma lem3341395 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (@IN _87042 x t) = (t x).
Proof. exact (@lem3341394 _87042 t x). Qed.
Lemma lem3341396 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term31 _87042 f x t) = (term32 _87042 f t x).
Proof. exact (MK_COMB (@lem3341391 _87042 f t) (@lem3341395 _87042 t x)). Qed.
Lemma lem3341399 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term33 _87042 f x) = (term34 _87042 f x).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3341396 _87042 f t x)). Qed.
Lemma lem3341400 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3341401 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term28 _87042 f x) = (term35 _87042 f x).
Proof. exact (MK_COMB (@lem3341400 _87042) (@lem3341399 _87042 f x)). Qed.
Lemma lem3341406 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term27 _87042 x f) = (term35 _87042 f x).
Proof. exact (TRANS (@lem3341379 _87042 f x) (@lem3341401 _87042 f x)). Qed.
Lemma lem3341407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3341408 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term36 _87042 x f) = (term37 _87042 f x).
Proof. exact (MK_COMB (@lem3341407) (@lem3341406 _87042 f x)). Qed.
Lemma lem3341410 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3341411 {_87042 : Type'} (P : _87042 -> Prop) (x : _87042) : (@IN _87042 x P) = (P x).
Proof. exact (@lem3341410 _87042 P x). Qed.
Lemma lem3341412 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (@IN _87042 x t) = (t x).
Proof. exact (@lem3341411 _87042 t x). Qed.
Lemma lem3341413 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term38 _87042 f x t) = (term39 _87042 f t x).
Proof. exact (MK_COMB (@lem3341408 _87042 f x) (@lem3341412 _87042 t x)). Qed.
Lemma lem3341416 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term40 _87042 f t) = (term41 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341413 _87042 f t x)). Qed.
Lemma lem3341417 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3341418 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term9 _87042 f t) = (term42 _87042 f t).
Proof. exact (MK_COMB (@lem3341417 _87042) (@lem3341416 _87042 f t)). Qed.
Lemma lem3341423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3341424 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term11 _87042 f t) = (term43 _87042 f t).
Proof. exact (MK_COMB (@lem3341423) (@lem3341418 _87042 f t)). Qed.
Lemma lem3341432 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3341433 {_87042 : Type'} (P : type686 _87042) (x : _87042 -> Prop) : (@IN (_87042 -> Prop) x P) = (P x).
Proof. exact (@lem3341432 (_87042 -> Prop) P x). Qed.
Lemma lem3341434 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (@IN (_87042 -> Prop) s f) = (f s).
Proof. exact (@lem3341433 _87042 f s). Qed.
Lemma lem3341435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3341436 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term12 _87042 s f) = (term44 _87042 f s).
Proof. exact (MK_COMB (@lem3341435) (@lem3341434 _87042 f s)). Qed.
Lemma lem3341444 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3341445 {_87042 : Type'} (P : _87042 -> Prop) (x : _87042) : (@IN _87042 x P) = (P x).
Proof. exact (@lem3341444 _87042 P x). Qed.
Lemma lem3341446 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (@IN _87042 x s) = (s x).
Proof. exact (@lem3341445 _87042 s x). Qed.
Lemma lem3341447 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3341448 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (term45 _87042 x s) = (term46 _87042 s x).
Proof. exact (MK_COMB (@lem3341447) (@lem3341446 _87042 s x)). Qed.
Lemma lem3341450 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3341451 {_87042 : Type'} (P : _87042 -> Prop) (x : _87042) : (@IN _87042 x P) = (P x).
Proof. exact (@lem3341450 _87042 P x). Qed.
Lemma lem3341452 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (@IN _87042 x t) = (t x).
Proof. exact (@lem3341451 _87042 t x). Qed.
Lemma lem3341453 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term47 _87042 s x t) = (term48 _87042 s t x).
Proof. exact (MK_COMB (@lem3341448 _87042 s x) (@lem3341452 _87042 t x)). Qed.
Lemma lem3341456 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term49 _87042 s t) = (term50 _87042 s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341453 _87042 s t x)). Qed.
Lemma lem3341457 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3341458 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term7 _87042 s t) = (term51 _87042 s t).
Proof. exact (MK_COMB (@lem3341457 _87042) (@lem3341456 _87042 s t)). Qed.
Lemma lem3341463 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term14 _87042 f s t) = (term52 _87042 f s t).
Proof. exact (MK_COMB (@lem3341436 _87042 f s) (@lem3341458 _87042 s t)). Qed.
Lemma lem3341466 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term16 _87042 f t) = (term53 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3341463 _87042 f s t)). Qed.
Lemma lem3341467 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341468 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term18 _87042 f t) = (term54 _87042 f t).
Proof. exact (MK_COMB (@lem3341467 _87042) (@lem3341466 _87042 f t)). Qed.
Lemma lem3341473 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : ((term9 _87042 f t) = (term18 _87042 f t)) = ((term42 _87042 f t) = (term54 _87042 f t)).
Proof. exact (MK_COMB (@lem3341424 _87042 f t) (@lem3341468 _87042 f t)). Qed.
Lemma lem3341476 {_87042 : Type'} (f : type686 _87042) : (term20 _87042 f) = (term55 _87042 f).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3341473 _87042 f t)). Qed.
Lemma lem3341477 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341478 {_87042 : Type'} (f : type686 _87042) : (term22 _87042 f) = (term56 _87042 f).
Proof. exact (MK_COMB (@lem3341477 _87042) (@lem3341476 _87042 f)). Qed.
Lemma lem3341483 {_87042 : Type'} : (term24 _87042) = (term57 _87042).
Proof. exact (fun_ext (fun f : type686 _87042 => @lem3341478 _87042 f)). Qed.
Lemma lem3341484 {_87042 : Type'} : (@all ((_87042 -> Prop) -> Prop)) = (@all ((_87042 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87042 -> Prop) -> Prop))). Qed.
Lemma lem3341485 {_87042 : Type'} : (term26 _87042) = (term58 _87042).
Proof. exact (MK_COMB (@lem3341484 _87042) (@lem3341483 _87042)). Qed.
Lemma lem3341490 {_87042 : Type'} : (term58 _87042) = (term26 _87042).
Proof. exact (SYM (@lem3341485 _87042)). Qed.
Lemma lem3341492 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3341493 {_87042 : Type'} : (term58 _87042) = (term60 _87042).
Proof. exact (@lem3341492 (term58 _87042)). Qed.
Lemma lem3341494 {_87042 : Type'} : (term60 _87042) = (term58 _87042).
Proof. exact (SYM (@lem3341493 _87042)). Qed.
Lemma lem3341495 {_87042 : Type'} (h1 : term61 _87042) : term61 _87042.
Proof. exact (h1). Qed.
Lemma lem3341498 {_87042 : Type'} (h1 : term60 _87042) : term60 _87042.
Proof. exact (h1). Qed.
Lemma lem3341499 {_87042 : Type'} : term62 _87042.
Proof. exact (fun h0 : term60 _87042 => @lem3341498 _87042 h0). Qed.
Lemma lem3341500 {_87042 : Type'} (h1 : term62 _87042) : term62 _87042.
Proof. exact (h1). Qed.
Lemma lem3341501 {_87042 : Type'} (h1 : term60 _87042) : term60 _87042.
Proof. exact (h1). Qed.
Lemma lem3341502 {_87042 : Type'} (h1 : term60 _87042) (h2 : term62 _87042) : term60 _87042.
Proof. exact (@lem3341500 _87042 h2 (@lem3341501 _87042 h1)). Qed.
Lemma lem3341503 {_87042 : Type'} (h1 : term60 _87042) : term63 _87042.
Proof. exact (fun h0 : term62 _87042 => @lem3341502 _87042 h1 h0). Qed.
Lemma lem3341504 {_87042 : Type'} (h1 : term62 _87042) : term62 _87042.
Proof. exact (h1). Qed.
Lemma lem3341505 {_87042 : Type'} (h1 : term60 _87042) (h2 : term62 _87042) : term60 _87042.
Proof. exact (@lem3341503 _87042 h1 (@lem3341504 _87042 h2)). Qed.
Lemma lem3341506 {_87042 : Type'} (h1 : term62 _87042) : term62 _87042.
Proof. exact (fun h0 : term60 _87042 => @lem3341505 _87042 h0 h1). Qed.
Lemma lem3341507 {_87042 : Type'} : term64 _87042.
Proof. exact (fun h0 : term62 _87042 => @lem3341506 _87042 h0). Qed.
Lemma lem3341510 {_87042 : Type'} : term62 _87042.
Proof. exact (@lem3341507 _87042 (@lem3341499 _87042)). Qed.
Lemma lem3341511 {_87042 : Type'} : term62 _87042.
Proof. exact (@lem3341510 _87042). Qed.
Lemma lem3341513 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3341514 {_87042 : Type'} : (term60 _87042) = (term65 _87042).
Proof. exact (@lem3341513 (term61 _87042)). Qed.
Lemma lem3341516 (t : Prop) : (term66 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3341517 {_87042 : Type'} : (term65 _87042) = (term58 _87042).
Proof. exact (@lem3341516 (term58 _87042)). Qed.
Lemma lem3341578 {_87042 : Type'} : (term60 _87042) = (term58 _87042).
Proof. exact (TRANS (@lem3341514 _87042) (@lem3341517 _87042)). Qed.
Lemma lem3341583 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term48 _87042 s t x) = (term48 _87042 s t x).
Proof. exact (eq_refl (term48 _87042 s t x)). Qed.
Lemma lem3341584 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term50 _87042 s t) = (term50 _87042 s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341583 _87042 s t x)). Qed.
Lemma lem3341585 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3341586 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term51 _87042 s t) = (term51 _87042 s t).
Proof. exact (MK_COMB (@lem3341585 _87042) (@lem3341584 _87042 s t)). Qed.
Lemma lem3341589 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term44 _87042 f s) = (term44 _87042 f s).
Proof. exact (eq_refl (term44 _87042 f s)). Qed.
Lemma lem3341590 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term52 _87042 f s t) = (term52 _87042 f s t).
Proof. exact (MK_COMB (@lem3341589 _87042 f s) (@lem3341586 _87042 s t)). Qed.
Lemma lem3341591 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term53 _87042 f t) = (term53 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3341590 _87042 f s t)). Qed.
Lemma lem3341592 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341593 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term54 _87042 f t) = (term54 _87042 f t).
Proof. exact (MK_COMB (@lem3341592 _87042) (@lem3341591 _87042 f t)). Qed.
Lemma lem3341594 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3341599 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term32 _87042 f t x) = (term32 _87042 f t x).
Proof. exact (eq_refl (term32 _87042 f t x)). Qed.
Lemma lem3341600 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term34 _87042 f x) = (term34 _87042 f x).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3341599 _87042 f t x)). Qed.
Lemma lem3341601 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3341602 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term35 _87042 f x) = (term35 _87042 f x).
Proof. exact (MK_COMB (@lem3341601 _87042) (@lem3341600 _87042 f x)). Qed.
Lemma lem3341603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3341604 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term37 _87042 f x) = (term37 _87042 f x).
Proof. exact (MK_COMB (@lem3341603) (@lem3341602 _87042 f x)). Qed.
Lemma lem3341605 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term39 _87042 f t x) = (term39 _87042 f t x).
Proof. exact (MK_COMB (@lem3341604 _87042 f x) (@lem3341594 _87042 t x)). Qed.
Lemma lem3341606 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term41 _87042 f t) = (term41 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341605 _87042 f t x)). Qed.
Lemma lem3341607 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3341608 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term42 _87042 f t) = (term42 _87042 f t).
Proof. exact (MK_COMB (@lem3341607 _87042) (@lem3341606 _87042 f t)). Qed.
Lemma lem3341609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3341610 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term43 _87042 f t) = (term43 _87042 f t).
Proof. exact (MK_COMB (@lem3341609) (@lem3341608 _87042 f t)). Qed.
Lemma lem3341611 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : ((term42 _87042 f t) = (term54 _87042 f t)) = ((term42 _87042 f t) = (term54 _87042 f t)).
Proof. exact (MK_COMB (@lem3341610 _87042 f t) (@lem3341593 _87042 f t)). Qed.
Lemma lem3341612 {_87042 : Type'} (f : type686 _87042) : (term55 _87042 f) = (term55 _87042 f).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3341611 _87042 f t)). Qed.
Lemma lem3341613 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341614 {_87042 : Type'} (f : type686 _87042) : (term56 _87042 f) = (term56 _87042 f).
Proof. exact (MK_COMB (@lem3341613 _87042) (@lem3341612 _87042 f)). Qed.
Lemma lem3341615 {_87042 : Type'} : (term57 _87042) = (term57 _87042).
Proof. exact (fun_ext (fun f : type686 _87042 => @lem3341614 _87042 f)). Qed.
Lemma lem3341616 {_87042 : Type'} : (@all ((_87042 -> Prop) -> Prop)) = (@all ((_87042 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87042 -> Prop) -> Prop))). Qed.
Lemma lem3341617 {_87042 : Type'} : (term58 _87042) = (term58 _87042).
Proof. exact (MK_COMB (@lem3341616 _87042) (@lem3341615 _87042)). Qed.
Lemma lem3341664 {_87042 : Type'} : (term60 _87042) = (term58 _87042).
Proof. exact (TRANS (@lem3341578 _87042) (@lem3341617 _87042)). Qed.
Lemma lem3341665 {_87042 : Type'} : (term58 _87042) = (term60 _87042).
Proof. exact (SYM (@lem3341664 _87042)). Qed.
Lemma lem3341667 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3341668 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : ((term42 _87042 f t) = (term54 _87042 f t)) = (term67 _87042 f t).
Proof. exact (@lem3341667 ((term42 _87042 f t) = (term54 _87042 f t))). Qed.
Lemma lem3341669 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term67 _87042 f t) = ((term42 _87042 f t) = (term54 _87042 f t)).
Proof. exact (SYM (@lem3341668 _87042 f t)). Qed.
Lemma lem3341670 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (h1 : term68 _87042 f t) : term68 _87042 f t.
Proof. exact (h1). Qed.
Lemma lem3341679 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term69 _87042 f t x) = (term70 _87042 f t x).
Proof. exact (@lem17045 (f t) (t x)). Qed.
Lemma lem3341682 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term32 _87042 f t x) = (term32 _87042 f t x).
Proof. exact (eq_refl (term32 _87042 f t x)). Qed.
Lemma lem3341683 {_87042 : Type'} (P : type686 _87042) : (term71 _87042 P) = (term72 _87042 P).
Proof. exact (@lem18394 (_87042 -> Prop) P). Qed.
Lemma lem3341684 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term73 _87042 f x) = (term74 _87042 f x).
Proof. exact (@lem3341683 _87042 (term34 _87042 f x)). Qed.
Lemma lem3341685 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term75 _87042 f x t) = (term32 _87042 f t x).
Proof. exact (eq_refl (term75 _87042 f x t)). Qed.
Lemma lem3341686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3341687 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term76 _87042 f x t) = (term69 _87042 f t x).
Proof. exact (MK_COMB (@lem3341686) (@lem3341685 _87042 f t x)). Qed.
Lemma lem3341688 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term76 _87042 f x t) = (term70 _87042 f t x).
Proof. exact (TRANS (@lem3341687 _87042 f t x) (@lem3341679 _87042 f t x)). Qed.
Lemma lem3341689 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term77 _87042 f x) = (term78 _87042 f x).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3341688 _87042 f t x)). Qed.
Lemma lem3341690 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341691 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term74 _87042 f x) = (term79 _87042 f x).
Proof. exact (MK_COMB (@lem3341690 _87042) (@lem3341689 _87042 f x)). Qed.
Lemma lem3341692 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term73 _87042 f x) = (term79 _87042 f x).
Proof. exact (TRANS (@lem3341684 _87042 f x) (@lem3341691 _87042 f x)). Qed.
Lemma lem3341693 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term34 _87042 f x) = (term34 _87042 f x).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3341682 _87042 f t x)). Qed.
Lemma lem3341694 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3341695 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term35 _87042 f x) = (term35 _87042 f x).
Proof. exact (MK_COMB (@lem3341694 _87042) (@lem3341693 _87042 f x)). Qed.
Lemma lem3341696 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term80 _87042 t x) = (term80 _87042 t x).
Proof. exact (eq_refl (term80 _87042 t x)). Qed.
Lemma lem3341697 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3341698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3341699 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term81 _87042 f x) = (term81 _87042 f x).
Proof. exact (MK_COMB (@lem3341698) (@lem3341695 _87042 f x)). Qed.
Lemma lem3341700 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term82 _87042 f t x) = (term82 _87042 f t x).
Proof. exact (MK_COMB (@lem3341699 _87042 f x) (@lem3341696 _87042 t x)). Qed.
Lemma lem3341701 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term83 _87042 f t x) = (term82 _87042 f t x).
Proof. exact (@lem17362 (term35 _87042 f x) (t x)). Qed.
Lemma lem3341702 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term83 _87042 f t x) = (term82 _87042 f t x).
Proof. exact (TRANS (@lem3341701 _87042 f t x) (@lem3341700 _87042 f t x)). Qed.
Lemma lem3341703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3341704 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term84 _87042 f x) = (term85 _87042 f x).
Proof. exact (MK_COMB (@lem3341703) (@lem3341692 _87042 f x)). Qed.
Lemma lem3341705 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term86 _87042 f t x) = (term87 _87042 f t x).
Proof. exact (MK_COMB (@lem3341704 _87042 f x) (@lem3341697 _87042 t x)). Qed.
Lemma lem3341706 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term39 _87042 f t x) = (term86 _87042 f t x).
Proof. exact (@lem17265 (term35 _87042 f x) (t x)). Qed.
Lemma lem3341707 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term39 _87042 f t x) = (term87 _87042 f t x).
Proof. exact (TRANS (@lem3341706 _87042 f t x) (@lem3341705 _87042 f t x)). Qed.
Lemma lem3341708 {_87042 : Type'} (P : _87042 -> Prop) : (term88 _87042 P) = (term89 _87042 P).
Proof. exact (@lem18392 _87042 P). Qed.
Lemma lem3341709 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term90 _87042 f t) = (term91 _87042 f t).
Proof. exact (@lem3341708 _87042 (term41 _87042 f t)). Qed.
Lemma lem3341710 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term92 _87042 f t x) = (term39 _87042 f t x).
Proof. exact (eq_refl (term92 _87042 f t x)). Qed.
Lemma lem3341711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3341712 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term93 _87042 f t x) = (term83 _87042 f t x).
Proof. exact (MK_COMB (@lem3341711) (@lem3341710 _87042 f t x)). Qed.
Lemma lem3341713 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term93 _87042 f t x) = (term82 _87042 f t x).
Proof. exact (TRANS (@lem3341712 _87042 f t x) (@lem3341702 _87042 f t x)). Qed.
Lemma lem3341714 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term94 _87042 f t) = (term95 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341713 _87042 f t x)). Qed.
Lemma lem3341715 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3341716 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term91 _87042 f t) = (term96 _87042 f t).
Proof. exact (MK_COMB (@lem3341715 _87042) (@lem3341714 _87042 f t)). Qed.
Lemma lem3341717 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term90 _87042 f t) = (term96 _87042 f t).
Proof. exact (TRANS (@lem3341709 _87042 f t) (@lem3341716 _87042 f t)). Qed.
Lemma lem3341718 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term41 _87042 f t) = (term97 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341707 _87042 f t x)). Qed.
Lemma lem3341719 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3341720 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term42 _87042 f t) = (term98 _87042 f t).
Proof. exact (MK_COMB (@lem3341719 _87042) (@lem3341718 _87042 f t)). Qed.
Lemma lem3341731 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term99 _87042 s t x) = (term100 _87042 s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3341736 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term48 _87042 s t x) = (term101 _87042 s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3341737 {_87042 : Type'} (P : _87042 -> Prop) : (term88 _87042 P) = (term89 _87042 P).
Proof. exact (@lem18392 _87042 P). Qed.
Lemma lem3341738 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term102 _87042 s t) = (term103 _87042 s t).
Proof. exact (@lem3341737 _87042 (term50 _87042 s t)). Qed.
Lemma lem3341739 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term104 _87042 s t x) = (term48 _87042 s t x).
Proof. exact (eq_refl (term104 _87042 s t x)). Qed.
Lemma lem3341740 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3341741 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term105 _87042 s t x) = (term99 _87042 s t x).
Proof. exact (MK_COMB (@lem3341740) (@lem3341739 _87042 s t x)). Qed.
Lemma lem3341742 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term105 _87042 s t x) = (term100 _87042 s t x).
Proof. exact (TRANS (@lem3341741 _87042 s t x) (@lem3341731 _87042 s t x)). Qed.
Lemma lem3341743 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term106 _87042 s t) = (term107 _87042 s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341742 _87042 s t x)). Qed.
Lemma lem3341744 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3341745 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term103 _87042 s t) = (term108 _87042 s t).
Proof. exact (MK_COMB (@lem3341744 _87042) (@lem3341743 _87042 s t)). Qed.
Lemma lem3341746 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term102 _87042 s t) = (term108 _87042 s t).
Proof. exact (TRANS (@lem3341738 _87042 s t) (@lem3341745 _87042 s t)). Qed.
Lemma lem3341747 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term50 _87042 s t) = (term109 _87042 s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3341736 _87042 s t x)). Qed.
Lemma lem3341748 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3341749 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term51 _87042 s t) = (term110 _87042 s t).
Proof. exact (MK_COMB (@lem3341748 _87042) (@lem3341747 _87042 s t)). Qed.
Lemma lem3341751 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term30 _87042 f s) = (term30 _87042 f s).
Proof. exact (eq_refl (term30 _87042 f s)). Qed.
Lemma lem3341752 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term111 _87042 f s t) = (term112 _87042 f s t).
Proof. exact (MK_COMB (@lem3341751 _87042 f s) (@lem3341746 _87042 s t)). Qed.
Lemma lem3341753 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term113 _87042 f s t) = (term111 _87042 f s t).
Proof. exact (@lem17362 (f s) (term51 _87042 s t)). Qed.
Lemma lem3341754 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term113 _87042 f s t) = (term112 _87042 f s t).
Proof. exact (TRANS (@lem3341753 _87042 f s t) (@lem3341752 _87042 f s t)). Qed.
Lemma lem3341756 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term114 _87042 f s) = (term114 _87042 f s).
Proof. exact (eq_refl (term114 _87042 f s)). Qed.
Lemma lem3341757 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term115 _87042 f s t) = (term116 _87042 f s t).
Proof. exact (MK_COMB (@lem3341756 _87042 f s) (@lem3341749 _87042 s t)). Qed.
Lemma lem3341758 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term52 _87042 f s t) = (term115 _87042 f s t).
Proof. exact (@lem17265 (f s) (term51 _87042 s t)). Qed.
Lemma lem3341759 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term52 _87042 f s t) = (term116 _87042 f s t).
Proof. exact (TRANS (@lem3341758 _87042 f s t) (@lem3341757 _87042 f s t)). Qed.
Lemma lem3341760 {_87042 : Type'} (P : type686 _87042) : (term117 _87042 P) = (term118 _87042 P).
Proof. exact (@lem18392 (_87042 -> Prop) P). Qed.
Lemma lem3341761 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term119 _87042 f t) = (term120 _87042 f t).
Proof. exact (@lem3341760 _87042 (term53 _87042 f t)). Qed.
Lemma lem3341762 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term121 _87042 f t s) = (term52 _87042 f s t).
Proof. exact (eq_refl (term121 _87042 f t s)). Qed.
Lemma lem3341763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3341764 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term122 _87042 f t s) = (term113 _87042 f s t).
Proof. exact (MK_COMB (@lem3341763) (@lem3341762 _87042 f s t)). Qed.
Lemma lem3341765 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term122 _87042 f t s) = (term112 _87042 f s t).
Proof. exact (TRANS (@lem3341764 _87042 f s t) (@lem3341754 _87042 f s t)). Qed.
Lemma lem3341766 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term123 _87042 f t) = (term124 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3341765 _87042 f s t)). Qed.
Lemma lem3341767 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3341768 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term120 _87042 f t) = (term125 _87042 f t).
Proof. exact (MK_COMB (@lem3341767 _87042) (@lem3341766 _87042 f t)). Qed.
Lemma lem3341769 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term119 _87042 f t) = (term125 _87042 f t).
Proof. exact (TRANS (@lem3341761 _87042 f t) (@lem3341768 _87042 f t)). Qed.
Lemma lem3341770 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term53 _87042 f t) = (term126 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3341759 _87042 f s t)). Qed.
Lemma lem3341771 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3341772 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term54 _87042 f t) = (term127 _87042 f t).
Proof. exact (MK_COMB (@lem3341771 _87042) (@lem3341770 _87042 f t)). Qed.
Lemma lem3341773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3341774 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term128 _87042 f t) = (term129 _87042 f t).
Proof. exact (MK_COMB (@lem3341773) (@lem3341717 _87042 f t)). Qed.
Lemma lem3341775 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term130 _87042 f t) = (term131 _87042 f t).
Proof. exact (MK_COMB (@lem3341774 _87042 f t) (@lem3341772 _87042 f t)). Qed.
Lemma lem3341776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3341777 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term132 _87042 f t) = (term133 _87042 f t).
Proof. exact (MK_COMB (@lem3341776) (@lem3341720 _87042 f t)). Qed.
Lemma lem3341778 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term134 _87042 f t) = (term135 _87042 f t).
Proof. exact (MK_COMB (@lem3341777 _87042 f t) (@lem3341769 _87042 f t)). Qed.
Lemma lem3341779 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3341780 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term136 _87042 f t) = (term137 _87042 f t).
Proof. exact (MK_COMB (@lem3341779) (@lem3341778 _87042 f t)). Qed.
Lemma lem3341781 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term138 _87042 f t) = (term139 _87042 f t).
Proof. exact (MK_COMB (@lem3341780 _87042 f t) (@lem3341775 _87042 f t)). Qed.
Lemma lem3341782 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term68 _87042 f t) = (term138 _87042 f t).
Proof. exact (@lem17646 (term42 _87042 f t) (term54 _87042 f t)). Qed.
Lemma lem3341783 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term68 _87042 f t) = (term139 _87042 f t).
Proof. exact (TRANS (@lem3341782 _87042 f t) (@lem3341781 _87042 f t)). Qed.
Lemma lem3342078 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3342079 {_87042 : Type'} (P : Prop) (Q : _87042 -> Prop) : (term140 _87042 P Q) = (term141 _87042 P Q).
Proof. exact (@lem3342078 _87042 P Q). Qed.
Lemma lem3342080 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term142 _87042 f s t) = (term143 _87042 f s t).
Proof. exact (@lem3342079 _87042 (f s) (term107 _87042 s t)). Qed.
Lemma lem3342081 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term144 _87042 s t x) = (term100 _87042 s t x).
Proof. exact (eq_refl (term144 _87042 s t x)). Qed.
Lemma lem3342082 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term145 _87042 s t) = (term107 _87042 s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342081 _87042 s t x)). Qed.
Lemma lem3342083 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342084 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term146 _87042 s t) = (term108 _87042 s t).
Proof. exact (MK_COMB (@lem3342083 _87042) (@lem3342082 _87042 s t)). Qed.
Lemma lem3342085 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term30 _87042 f s) = (term30 _87042 f s).
Proof. exact (eq_refl (term30 _87042 f s)). Qed.
Lemma lem3342086 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term142 _87042 f s t) = (term112 _87042 f s t).
Proof. exact (MK_COMB (@lem3342085 _87042 f s) (@lem3342084 _87042 s t)). Qed.
Lemma lem3342087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342088 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term147 _87042 f s t) = (term148 _87042 f s t).
Proof. exact (MK_COMB (@lem3342087) (@lem3342086 _87042 f s t)). Qed.
Lemma lem3342089 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term144 _87042 s t x) = (term100 _87042 s t x).
Proof. exact (eq_refl (term144 _87042 s t x)). Qed.
Lemma lem3342090 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term30 _87042 f s) = (term30 _87042 f s).
Proof. exact (eq_refl (term30 _87042 f s)). Qed.
Lemma lem3342091 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term149 _87042 f s t x) = (term150 _87042 f s t x).
Proof. exact (MK_COMB (@lem3342090 _87042 f s) (@lem3342089 _87042 s t x)). Qed.
Lemma lem3342092 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term151 _87042 f s t) = (term152 _87042 f s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342091 _87042 f s t x)). Qed.
Lemma lem3342093 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342094 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term143 _87042 f s t) = (term153 _87042 f s t).
Proof. exact (MK_COMB (@lem3342093 _87042) (@lem3342092 _87042 f s t)). Qed.
Lemma lem3342095 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : ((term142 _87042 f s t) = (term143 _87042 f s t)) = ((term112 _87042 f s t) = (term153 _87042 f s t)).
Proof. exact (MK_COMB (@lem3342088 _87042 f s t) (@lem3342094 _87042 f s t)). Qed.
Lemma lem3342096 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term112 _87042 f s t) = (term153 _87042 f s t).
Proof. exact (EQ_MP (@lem3342095 _87042 f s t) (@lem3342080 _87042 f s t)). Qed.
Lemma lem3342097 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term124 _87042 f t) = (term154 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342096 _87042 f s t)). Qed.
Lemma lem3342098 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342099 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term125 _87042 f t) = (term155 _87042 f t).
Proof. exact (MK_COMB (@lem3342098 _87042) (@lem3342097 _87042 f t)). Qed.
Lemma lem3342100 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term133 _87042 f t) = (term133 _87042 f t).
Proof. exact (eq_refl (term133 _87042 f t)). Qed.
Lemma lem3342101 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term135 _87042 f t) = (term156 _87042 f t).
Proof. exact (MK_COMB (@lem3342100 _87042 f t) (@lem3342099 _87042 f t)). Qed.
Lemma lem3342103 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3342104 {_87042 : Type'} (P : Prop) (Q : type686 _87042) : (term157 _87042 P Q) = (term158 _87042 P Q).
Proof. exact (@lem3342103 (_87042 -> Prop) P Q). Qed.
Lemma lem3342105 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term159 _87042 f t) = (term160 _87042 f t).
Proof. exact (@lem3342104 _87042 (term98 _87042 f t) (term154 _87042 f t)). Qed.
Lemma lem3342106 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term161 _87042 f t s) = (term153 _87042 f s t).
Proof. exact (eq_refl (term161 _87042 f t s)). Qed.
Lemma lem3342107 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term162 _87042 f t) = (term154 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342106 _87042 f s t)). Qed.
Lemma lem3342108 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342109 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term163 _87042 f t) = (term155 _87042 f t).
Proof. exact (MK_COMB (@lem3342108 _87042) (@lem3342107 _87042 f t)). Qed.
Lemma lem3342110 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term133 _87042 f t) = (term133 _87042 f t).
Proof. exact (eq_refl (term133 _87042 f t)). Qed.
Lemma lem3342111 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term159 _87042 f t) = (term156 _87042 f t).
Proof. exact (MK_COMB (@lem3342110 _87042 f t) (@lem3342109 _87042 f t)). Qed.
Lemma lem3342112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342113 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term164 _87042 f t) = (term165 _87042 f t).
Proof. exact (MK_COMB (@lem3342112) (@lem3342111 _87042 f t)). Qed.
Lemma lem3342114 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term161 _87042 f t s) = (term153 _87042 f s t).
Proof. exact (eq_refl (term161 _87042 f t s)). Qed.
Lemma lem3342115 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term133 _87042 f t) = (term133 _87042 f t).
Proof. exact (eq_refl (term133 _87042 f t)). Qed.
Lemma lem3342116 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term166 _87042 f t s) = (term167 _87042 f s t).
Proof. exact (MK_COMB (@lem3342115 _87042 f t) (@lem3342114 _87042 f s t)). Qed.
Lemma lem3342117 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term168 _87042 f t) = (term169 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342116 _87042 f s t)). Qed.
Lemma lem3342118 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342119 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term160 _87042 f t) = (term170 _87042 f t).
Proof. exact (MK_COMB (@lem3342118 _87042) (@lem3342117 _87042 f t)). Qed.
Lemma lem3342120 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : ((term159 _87042 f t) = (term160 _87042 f t)) = ((term156 _87042 f t) = (term170 _87042 f t)).
Proof. exact (MK_COMB (@lem3342113 _87042 f t) (@lem3342119 _87042 f t)). Qed.
Lemma lem3342121 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term156 _87042 f t) = (term170 _87042 f t).
Proof. exact (EQ_MP (@lem3342120 _87042 f t) (@lem3342105 _87042 f t)). Qed.
Lemma lem3342123 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3342124 {_87042 : Type'} (P : Prop) (Q : _87042 -> Prop) : (term140 _87042 P Q) = (term141 _87042 P Q).
Proof. exact (@lem3342123 _87042 P Q). Qed.
Lemma lem3342125 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term171 _87042 f s t) = (term172 _87042 f s t).
Proof. exact (@lem3342124 _87042 (term98 _87042 f t) (term152 _87042 f s t)). Qed.
Lemma lem3342126 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term173 _87042 f s t x) = (term150 _87042 f s t x).
Proof. exact (eq_refl (term173 _87042 f s t x)). Qed.
Lemma lem3342127 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term174 _87042 f s t) = (term152 _87042 f s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342126 _87042 f s t x)). Qed.
Lemma lem3342128 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342129 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term175 _87042 f s t) = (term153 _87042 f s t).
Proof. exact (MK_COMB (@lem3342128 _87042) (@lem3342127 _87042 f s t)). Qed.
Lemma lem3342130 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term133 _87042 f t) = (term133 _87042 f t).
Proof. exact (eq_refl (term133 _87042 f t)). Qed.
Lemma lem3342131 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term171 _87042 f s t) = (term167 _87042 f s t).
Proof. exact (MK_COMB (@lem3342130 _87042 f t) (@lem3342129 _87042 f s t)). Qed.
Lemma lem3342132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342133 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term176 _87042 f s t) = (term177 _87042 f s t).
Proof. exact (MK_COMB (@lem3342132) (@lem3342131 _87042 f s t)). Qed.
Lemma lem3342134 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term173 _87042 f s t x) = (term150 _87042 f s t x).
Proof. exact (eq_refl (term173 _87042 f s t x)). Qed.
Lemma lem3342135 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term133 _87042 f t) = (term133 _87042 f t).
Proof. exact (eq_refl (term133 _87042 f t)). Qed.
Lemma lem3342136 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term178 _87042 f s t x) = (term179 _87042 f s t x).
Proof. exact (MK_COMB (@lem3342135 _87042 f t) (@lem3342134 _87042 f s t x)). Qed.
Lemma lem3342137 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term180 _87042 f s t) = (term181 _87042 f s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342136 _87042 f s t x)). Qed.
Lemma lem3342138 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342139 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term172 _87042 f s t) = (term182 _87042 f s t).
Proof. exact (MK_COMB (@lem3342138 _87042) (@lem3342137 _87042 f s t)). Qed.
Lemma lem3342140 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : ((term171 _87042 f s t) = (term172 _87042 f s t)) = ((term167 _87042 f s t) = (term182 _87042 f s t)).
Proof. exact (MK_COMB (@lem3342133 _87042 f s t) (@lem3342139 _87042 f s t)). Qed.
Lemma lem3342141 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term167 _87042 f s t) = (term182 _87042 f s t).
Proof. exact (EQ_MP (@lem3342140 _87042 f s t) (@lem3342125 _87042 f s t)). Qed.
Lemma lem3342142 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term169 _87042 f t) = (term183 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342141 _87042 f s t)). Qed.
Lemma lem3342143 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342144 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term170 _87042 f t) = (term184 _87042 f t).
Proof. exact (MK_COMB (@lem3342143 _87042) (@lem3342142 _87042 f t)). Qed.
Lemma lem3342145 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term156 _87042 f t) = (term184 _87042 f t).
Proof. exact (TRANS (@lem3342121 _87042 f t) (@lem3342144 _87042 f t)). Qed.
Lemma lem3342146 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term135 _87042 f t) = (term184 _87042 f t).
Proof. exact (TRANS (@lem3342101 _87042 f t) (@lem3342145 _87042 f t)). Qed.
Lemma lem3342147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342148 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term137 _87042 f t) = (term185 _87042 f t).
Proof. exact (MK_COMB (@lem3342147) (@lem3342146 _87042 f t)). Qed.
Lemma lem3342150 {A : Type'} (P : A -> Prop) (Q : Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3342151 {_87042 : Type'} (P : type686 _87042) (Q : Prop) : (term188 _87042 P Q) = (term189 _87042 P Q).
Proof. exact (@lem3342150 (_87042 -> Prop) P Q). Qed.
Lemma lem3342152 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term190 _87042 f t x) = (term191 _87042 f t x).
Proof. exact (@lem3342151 _87042 (term34 _87042 f x) (term80 _87042 t x)). Qed.
Lemma lem3342153 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term75 _87042 f x t) = (term32 _87042 f t x).
Proof. exact (eq_refl (term75 _87042 f x t)). Qed.
Lemma lem3342154 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term192 _87042 f x) = (term34 _87042 f x).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3342153 _87042 f t x)). Qed.
Lemma lem3342155 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342156 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term193 _87042 f x) = (term35 _87042 f x).
Proof. exact (MK_COMB (@lem3342155 _87042) (@lem3342154 _87042 f x)). Qed.
Lemma lem3342157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342158 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term194 _87042 f x) = (term81 _87042 f x).
Proof. exact (MK_COMB (@lem3342157) (@lem3342156 _87042 f x)). Qed.
Lemma lem3342159 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term80 _87042 t x) = (term80 _87042 t x).
Proof. exact (eq_refl (term80 _87042 t x)). Qed.
Lemma lem3342160 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term190 _87042 f t x) = (term82 _87042 f t x).
Proof. exact (MK_COMB (@lem3342158 _87042 f x) (@lem3342159 _87042 t x)). Qed.
Lemma lem3342161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342162 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term195 _87042 f t x) = (term196 _87042 f t x).
Proof. exact (MK_COMB (@lem3342161) (@lem3342160 _87042 f t x)). Qed.
Lemma lem3342163 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (x : _87042) : (term75 _87042 f x t') = (term32 _87042 f t' x).
Proof. exact (eq_refl (term75 _87042 f x t')). Qed.
Lemma lem3342164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342165 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (x : _87042) : (term197 _87042 f x t') = (term198 _87042 f t' x).
Proof. exact (MK_COMB (@lem3342164) (@lem3342163 _87042 f t' x)). Qed.
Lemma lem3342166 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term80 _87042 t x) = (term80 _87042 t x).
Proof. exact (eq_refl (term80 _87042 t x)). Qed.
Lemma lem3342167 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term199 _87042 f t' t x) = (term200 _87042 f t' t x).
Proof. exact (MK_COMB (@lem3342165 _87042 f t' x) (@lem3342166 _87042 t x)). Qed.
Lemma lem3342168 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term201 _87042 f t x) = (term202 _87042 f t x).
Proof. exact (fun_ext (fun t' : _87042 -> Prop => @lem3342167 _87042 f t' t x)). Qed.
Lemma lem3342169 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342170 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term191 _87042 f t x) = (term203 _87042 f t x).
Proof. exact (MK_COMB (@lem3342169 _87042) (@lem3342168 _87042 f t x)). Qed.
Lemma lem3342171 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : ((term190 _87042 f t x) = (term191 _87042 f t x)) = ((term82 _87042 f t x) = (term203 _87042 f t x)).
Proof. exact (MK_COMB (@lem3342162 _87042 f t x) (@lem3342170 _87042 f t x)). Qed.
Lemma lem3342172 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term82 _87042 f t x) = (term203 _87042 f t x).
Proof. exact (EQ_MP (@lem3342171 _87042 f t x) (@lem3342152 _87042 f t x)). Qed.
Lemma lem3342173 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term95 _87042 f t) = (term204 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342172 _87042 f t x)). Qed.
Lemma lem3342174 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342175 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term96 _87042 f t) = (term205 _87042 f t).
Proof. exact (MK_COMB (@lem3342174 _87042) (@lem3342173 _87042 f t)). Qed.
Lemma lem3342176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342177 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term129 _87042 f t) = (term206 _87042 f t).
Proof. exact (MK_COMB (@lem3342176) (@lem3342175 _87042 f t)). Qed.
Lemma lem3342178 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term127 _87042 f t) = (term127 _87042 f t).
Proof. exact (eq_refl (term127 _87042 f t)). Qed.
Lemma lem3342179 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term131 _87042 f t) = (term207 _87042 f t).
Proof. exact (MK_COMB (@lem3342177 _87042 f t) (@lem3342178 _87042 f t)). Qed.
Lemma lem3342181 {A : Type'} (P : A -> Prop) (Q : Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3342182 {_87042 : Type'} (P : _87042 -> Prop) (Q : Prop) : (term186 _87042 P Q) = (term187 _87042 P Q).
Proof. exact (@lem3342181 _87042 P Q). Qed.
Lemma lem3342183 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term208 _87042 f t) = (term209 _87042 f t).
Proof. exact (@lem3342182 _87042 (term204 _87042 f t) (term127 _87042 f t)). Qed.
Lemma lem3342184 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term210 _87042 f t x) = (term203 _87042 f t x).
Proof. exact (eq_refl (term210 _87042 f t x)). Qed.
Lemma lem3342185 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term211 _87042 f t) = (term204 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342184 _87042 f t x)). Qed.
Lemma lem3342186 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342187 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term212 _87042 f t) = (term205 _87042 f t).
Proof. exact (MK_COMB (@lem3342186 _87042) (@lem3342185 _87042 f t)). Qed.
Lemma lem3342188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342189 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term213 _87042 f t) = (term206 _87042 f t).
Proof. exact (MK_COMB (@lem3342188) (@lem3342187 _87042 f t)). Qed.
Lemma lem3342190 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term127 _87042 f t) = (term127 _87042 f t).
Proof. exact (eq_refl (term127 _87042 f t)). Qed.
Lemma lem3342191 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term208 _87042 f t) = (term207 _87042 f t).
Proof. exact (MK_COMB (@lem3342189 _87042 f t) (@lem3342190 _87042 f t)). Qed.
Lemma lem3342192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342193 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term214 _87042 f t) = (term215 _87042 f t).
Proof. exact (MK_COMB (@lem3342192) (@lem3342191 _87042 f t)). Qed.
Lemma lem3342194 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term210 _87042 f t x) = (term203 _87042 f t x).
Proof. exact (eq_refl (term210 _87042 f t x)). Qed.
Lemma lem3342195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342196 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term216 _87042 f t x) = (term217 _87042 f t x).
Proof. exact (MK_COMB (@lem3342195) (@lem3342194 _87042 f t x)). Qed.
Lemma lem3342197 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term127 _87042 f t) = (term127 _87042 f t).
Proof. exact (eq_refl (term127 _87042 f t)). Qed.
Lemma lem3342198 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term218 _87042 x f t) = (term219 _87042 x f t).
Proof. exact (MK_COMB (@lem3342196 _87042 f t x) (@lem3342197 _87042 f t)). Qed.
Lemma lem3342199 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term220 _87042 f t) = (term221 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342198 _87042 x f t)). Qed.
Lemma lem3342200 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342201 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term209 _87042 f t) = (term222 _87042 f t).
Proof. exact (MK_COMB (@lem3342200 _87042) (@lem3342199 _87042 f t)). Qed.
Lemma lem3342202 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : ((term208 _87042 f t) = (term209 _87042 f t)) = ((term207 _87042 f t) = (term222 _87042 f t)).
Proof. exact (MK_COMB (@lem3342193 _87042 f t) (@lem3342201 _87042 f t)). Qed.
Lemma lem3342203 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term207 _87042 f t) = (term222 _87042 f t).
Proof. exact (EQ_MP (@lem3342202 _87042 f t) (@lem3342183 _87042 f t)). Qed.
Lemma lem3342205 {A : Type'} (P : A -> Prop) (Q : Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3342206 {_87042 : Type'} (P : type686 _87042) (Q : Prop) : (term188 _87042 P Q) = (term189 _87042 P Q).
Proof. exact (@lem3342205 (_87042 -> Prop) P Q). Qed.
Lemma lem3342207 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term223 _87042 x f t) = (term224 _87042 x f t).
Proof. exact (@lem3342206 _87042 (term202 _87042 f t x) (term127 _87042 f t)). Qed.
Lemma lem3342208 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term225 _87042 f t x t') = (term200 _87042 f t' t x).
Proof. exact (eq_refl (term225 _87042 f t x t')). Qed.
Lemma lem3342209 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term226 _87042 f t x) = (term202 _87042 f t x).
Proof. exact (fun_ext (fun t' : _87042 -> Prop => @lem3342208 _87042 f t' t x)). Qed.
Lemma lem3342210 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342211 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term227 _87042 f t x) = (term203 _87042 f t x).
Proof. exact (MK_COMB (@lem3342210 _87042) (@lem3342209 _87042 f t x)). Qed.
Lemma lem3342212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342213 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term228 _87042 f t x) = (term217 _87042 f t x).
Proof. exact (MK_COMB (@lem3342212) (@lem3342211 _87042 f t x)). Qed.
Lemma lem3342214 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term127 _87042 f t) = (term127 _87042 f t).
Proof. exact (eq_refl (term127 _87042 f t)). Qed.
Lemma lem3342215 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term223 _87042 x f t) = (term219 _87042 x f t).
Proof. exact (MK_COMB (@lem3342213 _87042 f t x) (@lem3342214 _87042 f t)). Qed.
Lemma lem3342216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342217 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term229 _87042 x f t) = (term230 _87042 x f t).
Proof. exact (MK_COMB (@lem3342216) (@lem3342215 _87042 x f t)). Qed.
Lemma lem3342218 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term225 _87042 f t x t') = (term200 _87042 f t' t x).
Proof. exact (eq_refl (term225 _87042 f t x t')). Qed.
Lemma lem3342219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342220 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term231 _87042 f t x t') = (term232 _87042 f t' t x).
Proof. exact (MK_COMB (@lem3342219) (@lem3342218 _87042 f t' t x)). Qed.
Lemma lem3342221 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term127 _87042 f t) = (term127 _87042 f t).
Proof. exact (eq_refl (term127 _87042 f t)). Qed.
Lemma lem3342222 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term233 _87042 x t' f t) = (term234 _87042 t' x f t).
Proof. exact (MK_COMB (@lem3342220 _87042 f t' t x) (@lem3342221 _87042 f t)). Qed.
Lemma lem3342223 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term235 _87042 x f t) = (term236 _87042 x f t).
Proof. exact (fun_ext (fun t' : _87042 -> Prop => @lem3342222 _87042 t' x f t)). Qed.
Lemma lem3342224 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342225 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term224 _87042 x f t) = (term237 _87042 x f t).
Proof. exact (MK_COMB (@lem3342224 _87042) (@lem3342223 _87042 x f t)). Qed.
Lemma lem3342226 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : ((term223 _87042 x f t) = (term224 _87042 x f t)) = ((term219 _87042 x f t) = (term237 _87042 x f t)).
Proof. exact (MK_COMB (@lem3342217 _87042 x f t) (@lem3342225 _87042 x f t)). Qed.
Lemma lem3342227 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term219 _87042 x f t) = (term237 _87042 x f t).
Proof. exact (EQ_MP (@lem3342226 _87042 x f t) (@lem3342207 _87042 x f t)). Qed.
Lemma lem3342228 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term221 _87042 f t) = (term238 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342227 _87042 x f t)). Qed.
Lemma lem3342229 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342230 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term222 _87042 f t) = (term239 _87042 f t).
Proof. exact (MK_COMB (@lem3342229 _87042) (@lem3342228 _87042 f t)). Qed.
Lemma lem3342231 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term207 _87042 f t) = (term239 _87042 f t).
Proof. exact (TRANS (@lem3342203 _87042 f t) (@lem3342230 _87042 f t)). Qed.
Lemma lem3342232 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term131 _87042 f t) = (term239 _87042 f t).
Proof. exact (TRANS (@lem3342179 _87042 f t) (@lem3342231 _87042 f t)). Qed.
Lemma lem3342233 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term139 _87042 f t) = (term240 _87042 f t).
Proof. exact (MK_COMB (@lem3342148 _87042 f t) (@lem3342232 _87042 f t)). Qed.
Lemma lem3342237 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3342238 {_87042 : Type'} (P : type686 _87042) (Q : Prop) : (term243 _87042 P Q) = (term244 _87042 P Q).
Proof. exact (@lem3342237 (_87042 -> Prop) P Q). Qed.
Lemma lem3342239 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term245 _87042 f t) = (term246 _87042 f t).
Proof. exact (@lem3342238 _87042 (term183 _87042 f t) (term239 _87042 f t)). Qed.
Lemma lem3342240 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term247 _87042 f t s) = (term182 _87042 f s t).
Proof. exact (eq_refl (term247 _87042 f t s)). Qed.
Lemma lem3342241 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term248 _87042 f t) = (term183 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342240 _87042 f s t)). Qed.
Lemma lem3342242 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342243 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term249 _87042 f t) = (term184 _87042 f t).
Proof. exact (MK_COMB (@lem3342242 _87042) (@lem3342241 _87042 f t)). Qed.
Lemma lem3342244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342245 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term250 _87042 f t) = (term185 _87042 f t).
Proof. exact (MK_COMB (@lem3342244) (@lem3342243 _87042 f t)). Qed.
Lemma lem3342246 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term239 _87042 f t) = (term239 _87042 f t).
Proof. exact (eq_refl (term239 _87042 f t)). Qed.
Lemma lem3342247 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term245 _87042 f t) = (term240 _87042 f t).
Proof. exact (MK_COMB (@lem3342245 _87042 f t) (@lem3342246 _87042 f t)). Qed.
Lemma lem3342248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342249 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term251 _87042 f t) = (term252 _87042 f t).
Proof. exact (MK_COMB (@lem3342248) (@lem3342247 _87042 f t)). Qed.
Lemma lem3342250 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term247 _87042 f t s) = (term182 _87042 f s t).
Proof. exact (eq_refl (term247 _87042 f t s)). Qed.
Lemma lem3342251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342252 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term253 _87042 f t s) = (term254 _87042 f s t).
Proof. exact (MK_COMB (@lem3342251) (@lem3342250 _87042 f s t)). Qed.
Lemma lem3342253 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term239 _87042 f t) = (term239 _87042 f t).
Proof. exact (eq_refl (term239 _87042 f t)). Qed.
Lemma lem3342254 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term255 _87042 s f t) = (term256 _87042 s f t).
Proof. exact (MK_COMB (@lem3342252 _87042 f s t) (@lem3342253 _87042 f t)). Qed.
Lemma lem3342255 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term257 _87042 f t) = (term258 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342254 _87042 s f t)). Qed.
Lemma lem3342256 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342257 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term246 _87042 f t) = (term259 _87042 f t).
Proof. exact (MK_COMB (@lem3342256 _87042) (@lem3342255 _87042 f t)). Qed.
Lemma lem3342258 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : ((term245 _87042 f t) = (term246 _87042 f t)) = ((term240 _87042 f t) = (term259 _87042 f t)).
Proof. exact (MK_COMB (@lem3342249 _87042 f t) (@lem3342257 _87042 f t)). Qed.
Lemma lem3342259 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term240 _87042 f t) = (term259 _87042 f t).
Proof. exact (EQ_MP (@lem3342258 _87042 f t) (@lem3342239 _87042 f t)). Qed.
Lemma lem3342261 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3342262 {_87042 : Type'} (P : _87042 -> Prop) (Q : _87042 -> Prop) : (term260 _87042 P Q) = (term261 _87042 P Q).
Proof. exact (@lem3342261 _87042 P Q). Qed.
Lemma lem3342263 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term262 _87042 s f t) = (term263 _87042 s f t).
Proof. exact (@lem3342262 _87042 (term181 _87042 f s t) (term238 _87042 f t)). Qed.
Lemma lem3342264 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term264 _87042 f s t x) = (term179 _87042 f s t x).
Proof. exact (eq_refl (term264 _87042 f s t x)). Qed.
Lemma lem3342265 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term265 _87042 f s t) = (term181 _87042 f s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342264 _87042 f s t x)). Qed.
Lemma lem3342266 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342267 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term266 _87042 f s t) = (term182 _87042 f s t).
Proof. exact (MK_COMB (@lem3342266 _87042) (@lem3342265 _87042 f s t)). Qed.
Lemma lem3342268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342269 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term267 _87042 f s t) = (term254 _87042 f s t).
Proof. exact (MK_COMB (@lem3342268) (@lem3342267 _87042 f s t)). Qed.
Lemma lem3342270 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term268 _87042 f t x) = (term237 _87042 x f t).
Proof. exact (eq_refl (term268 _87042 f t x)). Qed.
Lemma lem3342271 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term269 _87042 f t) = (term238 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342270 _87042 x f t)). Qed.
Lemma lem3342272 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342273 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term270 _87042 f t) = (term239 _87042 f t).
Proof. exact (MK_COMB (@lem3342272 _87042) (@lem3342271 _87042 f t)). Qed.
Lemma lem3342274 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term262 _87042 s f t) = (term256 _87042 s f t).
Proof. exact (MK_COMB (@lem3342269 _87042 f s t) (@lem3342273 _87042 f t)). Qed.
Lemma lem3342275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342276 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term271 _87042 s f t) = (term272 _87042 s f t).
Proof. exact (MK_COMB (@lem3342275) (@lem3342274 _87042 s f t)). Qed.
Lemma lem3342277 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term264 _87042 f s t x) = (term179 _87042 f s t x).
Proof. exact (eq_refl (term264 _87042 f s t x)). Qed.
Lemma lem3342278 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342279 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term273 _87042 f s t x) = (term274 _87042 f s t x).
Proof. exact (MK_COMB (@lem3342278) (@lem3342277 _87042 f s t x)). Qed.
Lemma lem3342280 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term268 _87042 f t x) = (term237 _87042 x f t).
Proof. exact (eq_refl (term268 _87042 f t x)). Qed.
Lemma lem3342281 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term275 _87042 s f t x) = (term276 _87042 s x f t).
Proof. exact (MK_COMB (@lem3342279 _87042 f s t x) (@lem3342280 _87042 x f t)). Qed.
Lemma lem3342282 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term277 _87042 s f t) = (term278 _87042 s f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342281 _87042 s x f t)). Qed.
Lemma lem3342283 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342284 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term263 _87042 s f t) = (term279 _87042 s f t).
Proof. exact (MK_COMB (@lem3342283 _87042) (@lem3342282 _87042 s f t)). Qed.
Lemma lem3342285 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : ((term262 _87042 s f t) = (term263 _87042 s f t)) = ((term256 _87042 s f t) = (term279 _87042 s f t)).
Proof. exact (MK_COMB (@lem3342276 _87042 s f t) (@lem3342284 _87042 s f t)). Qed.
Lemma lem3342286 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term256 _87042 s f t) = (term279 _87042 s f t).
Proof. exact (EQ_MP (@lem3342285 _87042 s f t) (@lem3342263 _87042 s f t)). Qed.
Lemma lem3342288 {A : Type'} (P : Prop) (Q : A -> Prop) : (term280 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3342289 {_87042 : Type'} (P : Prop) (Q : type686 _87042) : (term282 _87042 P Q) = (term283 _87042 P Q).
Proof. exact (@lem3342288 (_87042 -> Prop) P Q). Qed.
Lemma lem3342290 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term284 _87042 s x f t) = (term285 _87042 s x f t).
Proof. exact (@lem3342289 _87042 (term179 _87042 f s t x) (term236 _87042 x f t)). Qed.
Lemma lem3342291 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term286 _87042 x f t t') = (term234 _87042 t' x f t).
Proof. exact (eq_refl (term286 _87042 x f t t')). Qed.
Lemma lem3342292 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term287 _87042 x f t) = (term236 _87042 x f t).
Proof. exact (fun_ext (fun t' : _87042 -> Prop => @lem3342291 _87042 t' x f t)). Qed.
Lemma lem3342293 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342294 {_87042 : Type'} (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term288 _87042 x f t) = (term237 _87042 x f t).
Proof. exact (MK_COMB (@lem3342293 _87042) (@lem3342292 _87042 x f t)). Qed.
Lemma lem3342295 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term274 _87042 f s t x) = (term274 _87042 f s t x).
Proof. exact (eq_refl (term274 _87042 f s t x)). Qed.
Lemma lem3342296 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term284 _87042 s x f t) = (term276 _87042 s x f t).
Proof. exact (MK_COMB (@lem3342295 _87042 f s t x) (@lem3342294 _87042 x f t)). Qed.
Lemma lem3342297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342298 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term289 _87042 s x f t) = (term290 _87042 s x f t).
Proof. exact (MK_COMB (@lem3342297) (@lem3342296 _87042 s x f t)). Qed.
Lemma lem3342299 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term286 _87042 x f t t') = (term234 _87042 t' x f t).
Proof. exact (eq_refl (term286 _87042 x f t t')). Qed.
Lemma lem3342300 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term274 _87042 f s t x) = (term274 _87042 f s t x).
Proof. exact (eq_refl (term274 _87042 f s t x)). Qed.
Lemma lem3342301 {_87042 : Type'} (s : _87042 -> Prop) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term291 _87042 s x f t t') = (term292 _87042 s t' x f t).
Proof. exact (MK_COMB (@lem3342300 _87042 f s t x) (@lem3342299 _87042 t' x f t)). Qed.
Lemma lem3342302 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term293 _87042 s x f t) = (term294 _87042 s x f t).
Proof. exact (fun_ext (fun t' : _87042 -> Prop => @lem3342301 _87042 s t' x f t)). Qed.
Lemma lem3342303 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342304 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term285 _87042 s x f t) = (term295 _87042 s x f t).
Proof. exact (MK_COMB (@lem3342303 _87042) (@lem3342302 _87042 s x f t)). Qed.
Lemma lem3342305 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : ((term284 _87042 s x f t) = (term285 _87042 s x f t)) = ((term276 _87042 s x f t) = (term295 _87042 s x f t)).
Proof. exact (MK_COMB (@lem3342298 _87042 s x f t) (@lem3342304 _87042 s x f t)). Qed.
Lemma lem3342306 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term276 _87042 s x f t) = (term295 _87042 s x f t).
Proof. exact (EQ_MP (@lem3342305 _87042 s x f t) (@lem3342290 _87042 s x f t)). Qed.
Lemma lem3342307 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term278 _87042 s f t) = (term296 _87042 s f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342306 _87042 s x f t)). Qed.
Lemma lem3342308 {_87042 : Type'} : (@ex _87042) = (@ex _87042).
Proof. exact (eq_refl (@ex _87042)). Qed.
Lemma lem3342309 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term279 _87042 s f t) = (term297 _87042 s f t).
Proof. exact (MK_COMB (@lem3342308 _87042) (@lem3342307 _87042 s f t)). Qed.
Lemma lem3342310 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) : (term256 _87042 s f t) = (term297 _87042 s f t).
Proof. exact (TRANS (@lem3342286 _87042 s f t) (@lem3342309 _87042 s f t)). Qed.
Lemma lem3342311 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term258 _87042 f t) = (term298 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342310 _87042 s f t)). Qed.
Lemma lem3342312 {_87042 : Type'} : (@ex (_87042 -> Prop)) = (@ex (_87042 -> Prop)).
Proof. exact (eq_refl (@ex (_87042 -> Prop))). Qed.
Lemma lem3342313 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term259 _87042 f t) = (term299 _87042 f t).
Proof. exact (MK_COMB (@lem3342312 _87042) (@lem3342311 _87042 f t)). Qed.
Lemma lem3342314 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term240 _87042 f t) = (term299 _87042 f t).
Proof. exact (TRANS (@lem3342259 _87042 f t) (@lem3342313 _87042 f t)). Qed.
Lemma lem3342316 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term139 _87042 f t) = (term299 _87042 f t).
Proof. exact (TRANS (@lem3342233 _87042 f t) (@lem3342314 _87042 f t)). Qed.
Lemma lem3342317 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term68 _87042 f t) = (term299 _87042 f t).
Proof. exact (TRANS (@lem3341783 _87042 f t) (@lem3342316 _87042 f t)). Qed.
Lemma lem3342318 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (h1 : term68 _87042 f t) : term299 _87042 f t.
Proof. exact (EQ_MP (@lem3342317 _87042 f t) (@lem3341670 _87042 f t h1)). Qed.
Lemma lem3342319 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term297 _87042 s f t) : term297 _87042 s f t.
Proof. exact (h1). Qed.
Lemma lem3342320 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term295 _87042 s x f t) : term295 _87042 s x f t.
Proof. exact (h1). Qed.
Lemma lem3342321 {_87042 : Type'} (s : _87042 -> Prop) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term292 _87042 s t' x f t) : term292 _87042 s t' x f t.
Proof. exact (h1). Qed.
Lemma lem3342326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342327 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342326 _87042 Prop f x). Qed.
Lemma lem3342329 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (t x) = (@I (_87042 -> Prop) t x).
Proof. exact (@lem3342327 _87042 t x). Qed.
Lemma lem3342330 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3342335 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342336 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342335 _87042 Prop f x). Qed.
Lemma lem3342338 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (s x) = (@I (_87042 -> Prop) s x).
Proof. exact (@lem3342336 _87042 s x). Qed.
Lemma lem3342339 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (term80 _87042 s x) = (term300 _87042 s x).
Proof. exact (MK_COMB (@lem3342330) (@lem3342338 _87042 s x)). Qed.
Lemma lem3342340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342341 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (term301 _87042 s x) = (term302 _87042 s x).
Proof. exact (MK_COMB (@lem3342340) (@lem3342339 _87042 s x)). Qed.
Lemma lem3342342 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term101 _87042 s t x) = (term303 _87042 s t x).
Proof. exact (MK_COMB (@lem3342341 _87042 s x) (@lem3342329 _87042 t x)). Qed.
Lemma lem3342343 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term109 _87042 s t) = (term304 _87042 s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342342 _87042 s t x)). Qed.
Lemma lem3342344 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3342345 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term110 _87042 s t) = (term305 _87042 s t).
Proof. exact (MK_COMB (@lem3342344 _87042) (@lem3342343 _87042 s t)). Qed.
Lemma lem3342346 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3342351 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342352 {_87042 : Type'} (f : type686 _87042) (x : _87042 -> Prop) : (f x) = (@I ((_87042 -> Prop) -> Prop) f x).
Proof. exact (@lem3342351 (_87042 -> Prop) Prop f x). Qed.
Lemma lem3342354 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (f s) = (@I ((_87042 -> Prop) -> Prop) f s).
Proof. exact (@lem3342352 _87042 f s). Qed.
Lemma lem3342355 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term306 _87042 f s) = (term307 _87042 f s).
Proof. exact (MK_COMB (@lem3342346) (@lem3342354 _87042 f s)). Qed.
Lemma lem3342356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342357 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term114 _87042 f s) = (term308 _87042 f s).
Proof. exact (MK_COMB (@lem3342356) (@lem3342355 _87042 f s)). Qed.
Lemma lem3342358 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term116 _87042 f s t) = (term309 _87042 f s t).
Proof. exact (MK_COMB (@lem3342357 _87042 f s) (@lem3342345 _87042 s t)). Qed.
Lemma lem3342359 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term126 _87042 f t) = (term310 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342358 _87042 f s t)). Qed.
Lemma lem3342360 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3342361 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term127 _87042 f t) = (term311 _87042 f t).
Proof. exact (MK_COMB (@lem3342360 _87042) (@lem3342359 _87042 f t)). Qed.
Lemma lem3342362 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3342367 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342368 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342367 _87042 Prop f x). Qed.
Lemma lem3342370 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (t x) = (@I (_87042 -> Prop) t x).
Proof. exact (@lem3342368 _87042 t x). Qed.
Lemma lem3342371 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term80 _87042 t x) = (term300 _87042 t x).
Proof. exact (MK_COMB (@lem3342362) (@lem3342370 _87042 t x)). Qed.
Lemma lem3342376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342377 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342376 _87042 Prop f x). Qed.
Lemma lem3342379 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) : (t' x) = (@I (_87042 -> Prop) t' x).
Proof. exact (@lem3342377 _87042 t' x). Qed.
Lemma lem3342384 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342385 {_87042 : Type'} (f : type686 _87042) (x : _87042 -> Prop) : (f x) = (@I ((_87042 -> Prop) -> Prop) f x).
Proof. exact (@lem3342384 (_87042 -> Prop) Prop f x). Qed.
Lemma lem3342387 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) : (f t') = (@I ((_87042 -> Prop) -> Prop) f t').
Proof. exact (@lem3342385 _87042 f t'). Qed.
Lemma lem3342388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342389 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) : (term30 _87042 f t') = (term312 _87042 f t').
Proof. exact (MK_COMB (@lem3342388) (@lem3342387 _87042 f t')). Qed.
Lemma lem3342390 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (x : _87042) : (term32 _87042 f t' x) = (term313 _87042 f t' x).
Proof. exact (MK_COMB (@lem3342389 _87042 f t') (@lem3342379 _87042 t' x)). Qed.
Lemma lem3342391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342392 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (x : _87042) : (term198 _87042 f t' x) = (term314 _87042 f t' x).
Proof. exact (MK_COMB (@lem3342391) (@lem3342390 _87042 f t' x)). Qed.
Lemma lem3342393 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term200 _87042 f t' t x) = (term315 _87042 f t' t x).
Proof. exact (MK_COMB (@lem3342392 _87042 f t' x) (@lem3342371 _87042 t x)). Qed.
Lemma lem3342394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342395 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term232 _87042 f t' t x) = (term316 _87042 f t' t x).
Proof. exact (MK_COMB (@lem3342394) (@lem3342393 _87042 f t' t x)). Qed.
Lemma lem3342396 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term234 _87042 t' x f t) = (term317 _87042 t' x f t).
Proof. exact (MK_COMB (@lem3342395 _87042 f t' t x) (@lem3342361 _87042 f t)). Qed.
Lemma lem3342397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3342402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342403 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342402 _87042 Prop f x). Qed.
Lemma lem3342405 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (t x) = (@I (_87042 -> Prop) t x).
Proof. exact (@lem3342403 _87042 t x). Qed.
Lemma lem3342406 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term80 _87042 t x) = (term300 _87042 t x).
Proof. exact (MK_COMB (@lem3342397) (@lem3342405 _87042 t x)). Qed.
Lemma lem3342411 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342412 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342411 _87042 Prop f x). Qed.
Lemma lem3342414 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (s x) = (@I (_87042 -> Prop) s x).
Proof. exact (@lem3342412 _87042 s x). Qed.
Lemma lem3342415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342416 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (term318 _87042 s x) = (term319 _87042 s x).
Proof. exact (MK_COMB (@lem3342415) (@lem3342414 _87042 s x)). Qed.
Lemma lem3342417 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term100 _87042 s t x) = (term320 _87042 s t x).
Proof. exact (MK_COMB (@lem3342416 _87042 s x) (@lem3342406 _87042 t x)). Qed.
Lemma lem3342422 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342423 {_87042 : Type'} (f : type686 _87042) (x : _87042 -> Prop) : (f x) = (@I ((_87042 -> Prop) -> Prop) f x).
Proof. exact (@lem3342422 (_87042 -> Prop) Prop f x). Qed.
Lemma lem3342425 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (f s) = (@I ((_87042 -> Prop) -> Prop) f s).
Proof. exact (@lem3342423 _87042 f s). Qed.
Lemma lem3342426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342427 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term30 _87042 f s) = (term312 _87042 f s).
Proof. exact (MK_COMB (@lem3342426) (@lem3342425 _87042 f s)). Qed.
Lemma lem3342428 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term150 _87042 f s t x) = (term321 _87042 f s t x).
Proof. exact (MK_COMB (@lem3342427 _87042 f s) (@lem3342417 _87042 s t x)). Qed.
Lemma lem3342433 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342434 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342433 _87042 Prop f x). Qed.
Lemma lem3342436 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (t x) = (@I (_87042 -> Prop) t x).
Proof. exact (@lem3342434 _87042 t x). Qed.
Lemma lem3342437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3342442 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342443 {_87042 : Type'} (f : _87042 -> Prop) (x : _87042) : (f x) = (@I (_87042 -> Prop) f x).
Proof. exact (@lem3342442 _87042 Prop f x). Qed.
Lemma lem3342445 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (t x) = (@I (_87042 -> Prop) t x).
Proof. exact (@lem3342443 _87042 t x). Qed.
Lemma lem3342446 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term80 _87042 t x) = (term300 _87042 t x).
Proof. exact (MK_COMB (@lem3342437) (@lem3342445 _87042 t x)). Qed.
Lemma lem3342447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3342452 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3342453 {_87042 : Type'} (f : type686 _87042) (x : _87042 -> Prop) : (f x) = (@I ((_87042 -> Prop) -> Prop) f x).
Proof. exact (@lem3342452 (_87042 -> Prop) Prop f x). Qed.
Lemma lem3342455 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (f t) = (@I ((_87042 -> Prop) -> Prop) f t).
Proof. exact (@lem3342453 _87042 f t). Qed.
Lemma lem3342456 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term306 _87042 f t) = (term307 _87042 f t).
Proof. exact (MK_COMB (@lem3342447) (@lem3342455 _87042 f t)). Qed.
Lemma lem3342457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342458 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term114 _87042 f t) = (term308 _87042 f t).
Proof. exact (MK_COMB (@lem3342457) (@lem3342456 _87042 f t)). Qed.
Lemma lem3342459 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term70 _87042 f t x) = (term322 _87042 f t x).
Proof. exact (MK_COMB (@lem3342458 _87042 f t) (@lem3342446 _87042 t x)). Qed.
Lemma lem3342460 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term78 _87042 f x) = (term323 _87042 f x).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3342459 _87042 f t x)). Qed.
Lemma lem3342461 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3342462 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term79 _87042 f x) = (term324 _87042 f x).
Proof. exact (MK_COMB (@lem3342461 _87042) (@lem3342460 _87042 f x)). Qed.
Lemma lem3342463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342464 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term85 _87042 f x) = (term325 _87042 f x).
Proof. exact (MK_COMB (@lem3342463) (@lem3342462 _87042 f x)). Qed.
Lemma lem3342465 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term87 _87042 f t x) = (term326 _87042 f t x).
Proof. exact (MK_COMB (@lem3342464 _87042 f x) (@lem3342436 _87042 t x)). Qed.
Lemma lem3342466 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term97 _87042 f t) = (term327 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342465 _87042 f t x)). Qed.
Lemma lem3342467 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3342468 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term98 _87042 f t) = (term328 _87042 f t).
Proof. exact (MK_COMB (@lem3342467 _87042) (@lem3342466 _87042 f t)). Qed.
Lemma lem3342469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342470 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term133 _87042 f t) = (term329 _87042 f t).
Proof. exact (MK_COMB (@lem3342469) (@lem3342468 _87042 f t)). Qed.
Lemma lem3342471 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term179 _87042 f s t x) = (term330 _87042 f s t x).
Proof. exact (MK_COMB (@lem3342470 _87042 f t) (@lem3342428 _87042 f s t x)). Qed.
Lemma lem3342472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342473 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term274 _87042 f s t x) = (term331 _87042 f s t x).
Proof. exact (MK_COMB (@lem3342472) (@lem3342471 _87042 f s t x)). Qed.
Lemma lem3342474 {_87042 : Type'} (s : _87042 -> Prop) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) : (term292 _87042 s t' x f t) = (term332 _87042 s t' x f t).
Proof. exact (MK_COMB (@lem3342473 _87042 f s t x) (@lem3342396 _87042 t' x f t)). Qed.
Lemma lem3342475 {_87042 : Type'} (s : _87042 -> Prop) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term292 _87042 s t' x f t) : term332 _87042 s t' x f t.
Proof. exact (EQ_MP (@lem3342474 _87042 s t' x f t) (@lem3342321 _87042 s t' x f t h1)). Qed.
Lemma lem3342476 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term330 _87042 f s t x.
Proof. exact (h1). Qed.
Lemma lem3342477 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term317 _87042 t' x f t.
Proof. exact (h1). Qed.
Lemma lem3342478 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term321 _87042 f s t x.
Proof. exact (proj2 (@lem3342476 _87042 f s t x h1)). Qed.
Lemma lem3342479 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term328 _87042 f t.
Proof. exact (proj1 (@lem3342476 _87042 f s t x h1)). Qed.
Lemma lem3342480 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term320 _87042 s t x.
Proof. exact (proj2 (@lem3342478 _87042 f s t x h1)). Qed.
Lemma lem3342484 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term311 _87042 f t.
Proof. exact (proj2 (@lem3342477 _87042 t' x f t h1)). Qed.
Lemma lem3342485 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term315 _87042 f t' t x.
Proof. exact (proj1 (@lem3342477 _87042 t' x f t h1)). Qed.
Lemma lem3342487 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term313 _87042 f t' x.
Proof. exact (proj1 (@lem3342485 _87042 t' x f t h1)). Qed.
Lemma lem3342491 {A : Type'} (P : A -> Prop) (Q : Prop) : (term333 A P Q) = (term334 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3342492 {_87042 : Type'} (P : type686 _87042) (Q : Prop) : (term335 _87042 P Q) = (term336 _87042 P Q).
Proof. exact (@lem3342491 (_87042 -> Prop) P Q). Qed.
Lemma lem3342493 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term337 _87042 f t x) = (term338 _87042 f t x).
Proof. exact (@lem3342492 _87042 (term323 _87042 f x) (@I (_87042 -> Prop) t x)). Qed.
Lemma lem3342494 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term339 _87042 f x t) = (term322 _87042 f t x).
Proof. exact (eq_refl (term339 _87042 f x t)). Qed.
Lemma lem3342495 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term340 _87042 f x) = (term323 _87042 f x).
Proof. exact (fun_ext (fun t : _87042 -> Prop => @lem3342494 _87042 f t x)). Qed.
Lemma lem3342496 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3342497 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term341 _87042 f x) = (term324 _87042 f x).
Proof. exact (MK_COMB (@lem3342496 _87042) (@lem3342495 _87042 f x)). Qed.
Lemma lem3342498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342499 {_87042 : Type'} (f : type686 _87042) (x : _87042) : (term342 _87042 f x) = (term325 _87042 f x).
Proof. exact (MK_COMB (@lem3342498) (@lem3342497 _87042 f x)). Qed.
Lemma lem3342500 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (@I (_87042 -> Prop) t x) = (@I (_87042 -> Prop) t x).
Proof. exact (eq_refl (@I (_87042 -> Prop) t x)). Qed.
Lemma lem3342501 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term337 _87042 f t x) = (term326 _87042 f t x).
Proof. exact (MK_COMB (@lem3342499 _87042 f x) (@lem3342500 _87042 t x)). Qed.
Lemma lem3342502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342503 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term343 _87042 f t x) = (term344 _87042 f t x).
Proof. exact (MK_COMB (@lem3342502) (@lem3342501 _87042 f t x)). Qed.
Lemma lem3342504 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (x : _87042) : (term339 _87042 f x t') = (term322 _87042 f t' x).
Proof. exact (eq_refl (term339 _87042 f x t')). Qed.
Lemma lem3342505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3342506 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (x : _87042) : (term345 _87042 f x t') = (term346 _87042 f t' x).
Proof. exact (MK_COMB (@lem3342505) (@lem3342504 _87042 f t' x)). Qed.
Lemma lem3342507 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (@I (_87042 -> Prop) t x) = (@I (_87042 -> Prop) t x).
Proof. exact (eq_refl (@I (_87042 -> Prop) t x)). Qed.
Lemma lem3342508 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term347 _87042 f t' t x) = (term348 _87042 f t' t x).
Proof. exact (MK_COMB (@lem3342506 _87042 f t' x) (@lem3342507 _87042 t x)). Qed.
Lemma lem3342509 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term349 _87042 f t x) = (term350 _87042 f t x).
Proof. exact (fun_ext (fun t' : _87042 -> Prop => @lem3342508 _87042 f t' t x)). Qed.
Lemma lem3342510 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3342511 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term338 _87042 f t x) = (term351 _87042 f t x).
Proof. exact (MK_COMB (@lem3342510 _87042) (@lem3342509 _87042 f t x)). Qed.
Lemma lem3342512 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : ((term337 _87042 f t x) = (term338 _87042 f t x)) = ((term326 _87042 f t x) = (term351 _87042 f t x)).
Proof. exact (MK_COMB (@lem3342503 _87042 f t x) (@lem3342511 _87042 f t x)). Qed.
Lemma lem3342513 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term326 _87042 f t x) = (term351 _87042 f t x).
Proof. exact (EQ_MP (@lem3342512 _87042 f t x) (@lem3342493 _87042 f t x)). Qed.
Lemma lem3342514 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term327 _87042 f t) = (term352 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342513 _87042 f t x)). Qed.
Lemma lem3342515 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3342516 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term328 _87042 f t) = (term353 _87042 f t).
Proof. exact (MK_COMB (@lem3342515 _87042) (@lem3342514 _87042 f t)). Qed.
Lemma lem3342529 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term348 _87042 f t' t x) = (term348 _87042 f t' t x).
Proof. exact (eq_refl (term348 _87042 f t' t x)). Qed.
Lemma lem3342530 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term350 _87042 f t x) = (term350 _87042 f t x).
Proof. exact (fun_ext (fun t' : _87042 -> Prop => @lem3342529 _87042 f t' t x)). Qed.
Lemma lem3342531 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3342532 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (x : _87042) : (term351 _87042 f t x) = (term351 _87042 f t x).
Proof. exact (MK_COMB (@lem3342531 _87042) (@lem3342530 _87042 f t x)). Qed.
Lemma lem3342533 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term352 _87042 f t) = (term352 _87042 f t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342532 _87042 f t x)). Qed.
Lemma lem3342534 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3342535 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term353 _87042 f t) = (term353 _87042 f t).
Proof. exact (MK_COMB (@lem3342534 _87042) (@lem3342533 _87042 f t)). Qed.
Lemma lem3342536 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term328 _87042 f t) = (term353 _87042 f t).
Proof. exact (TRANS (@lem3342516 _87042 f t) (@lem3342535 _87042 f t)). Qed.
Lemma lem3342537 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term353 _87042 f t.
Proof. exact (EQ_MP (@lem3342536 _87042 f t) (@lem3342479 _87042 f s t x h1)). Qed.
Lemma lem3342551 {A : Type'} (P : Prop) (Q : A -> Prop) : (term354 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3342552 {_87042 : Type'} (P : Prop) (Q : _87042 -> Prop) : (term354 _87042 P Q) = (term355 _87042 P Q).
Proof. exact (@lem3342551 _87042 P Q). Qed.
Lemma lem3342553 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term356 _87042 f s t) = (term357 _87042 f s t).
Proof. exact (@lem3342552 _87042 (term307 _87042 f s) (term304 _87042 s t)). Qed.
Lemma lem3342554 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term358 _87042 s t x) = (term303 _87042 s t x).
Proof. exact (eq_refl (term358 _87042 s t x)). Qed.
Lemma lem3342555 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term359 _87042 s t) = (term304 _87042 s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342554 _87042 s t x)). Qed.
Lemma lem3342556 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3342557 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) : (term360 _87042 s t) = (term305 _87042 s t).
Proof. exact (MK_COMB (@lem3342556 _87042) (@lem3342555 _87042 s t)). Qed.
Lemma lem3342558 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term308 _87042 f s) = (term308 _87042 f s).
Proof. exact (eq_refl (term308 _87042 f s)). Qed.
Lemma lem3342559 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term356 _87042 f s t) = (term309 _87042 f s t).
Proof. exact (MK_COMB (@lem3342558 _87042 f s) (@lem3342557 _87042 s t)). Qed.
Lemma lem3342560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342561 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term361 _87042 f s t) = (term362 _87042 f s t).
Proof. exact (MK_COMB (@lem3342560) (@lem3342559 _87042 f s t)). Qed.
Lemma lem3342562 {_87042 : Type'} (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term358 _87042 s t x) = (term303 _87042 s t x).
Proof. exact (eq_refl (term358 _87042 s t x)). Qed.
Lemma lem3342563 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term308 _87042 f s) = (term308 _87042 f s).
Proof. exact (eq_refl (term308 _87042 f s)). Qed.
Lemma lem3342564 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term363 _87042 f s t x) = (term364 _87042 f s t x).
Proof. exact (MK_COMB (@lem3342563 _87042 f s) (@lem3342562 _87042 s t x)). Qed.
Lemma lem3342565 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term365 _87042 f s t) = (term366 _87042 f s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342564 _87042 f s t x)). Qed.
Lemma lem3342566 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3342567 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term357 _87042 f s t) = (term367 _87042 f s t).
Proof. exact (MK_COMB (@lem3342566 _87042) (@lem3342565 _87042 f s t)). Qed.
Lemma lem3342568 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : ((term356 _87042 f s t) = (term357 _87042 f s t)) = ((term309 _87042 f s t) = (term367 _87042 f s t)).
Proof. exact (MK_COMB (@lem3342561 _87042 f s t) (@lem3342567 _87042 f s t)). Qed.
Lemma lem3342569 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term309 _87042 f s t) = (term367 _87042 f s t).
Proof. exact (EQ_MP (@lem3342568 _87042 f s t) (@lem3342553 _87042 f s t)). Qed.
Lemma lem3342570 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term310 _87042 f t) = (term368 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342569 _87042 f s t)). Qed.
Lemma lem3342571 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3342572 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term311 _87042 f t) = (term369 _87042 f t).
Proof. exact (MK_COMB (@lem3342571 _87042) (@lem3342570 _87042 f t)). Qed.
Lemma lem3342585 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) : (term364 _87042 f s t x) = (term364 _87042 f s t x).
Proof. exact (eq_refl (term364 _87042 f s t x)). Qed.
Lemma lem3342586 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term366 _87042 f s t) = (term366 _87042 f s t).
Proof. exact (fun_ext (fun x : _87042 => @lem3342585 _87042 f s t x)). Qed.
Lemma lem3342587 {_87042 : Type'} : (@all _87042) = (@all _87042).
Proof. exact (eq_refl (@all _87042)). Qed.
Lemma lem3342588 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) : (term367 _87042 f s t) = (term367 _87042 f s t).
Proof. exact (MK_COMB (@lem3342587 _87042) (@lem3342586 _87042 f s t)). Qed.
Lemma lem3342589 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term368 _87042 f t) = (term368 _87042 f t).
Proof. exact (fun_ext (fun s : _87042 -> Prop => @lem3342588 _87042 f s t)). Qed.
Lemma lem3342590 {_87042 : Type'} : (@all (_87042 -> Prop)) = (@all (_87042 -> Prop)).
Proof. exact (eq_refl (@all (_87042 -> Prop))). Qed.
Lemma lem3342591 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term369 _87042 f t) = (term369 _87042 f t).
Proof. exact (MK_COMB (@lem3342590 _87042) (@lem3342589 _87042 f t)). Qed.
Lemma lem3342592 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term311 _87042 f t) = (term369 _87042 f t).
Proof. exact (TRANS (@lem3342572 _87042 f t) (@lem3342591 _87042 f t)). Qed.
Lemma lem3342593 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term369 _87042 f t.
Proof. exact (EQ_MP (@lem3342592 _87042 f t) (@lem3342484 _87042 t' x f t h1)). Qed.
Lemma lem3342606 {_87042 : Type'} (_34887 : _87042) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term370 _87042 f t _34887.
Proof. exact (@lem3342537 _87042 f s t x h1 _34887). Qed.
Lemma lem3342607 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (_34887 : _87042) : (term370 _87042 f t _34887) = (term351 _87042 f t _34887).
Proof. exact (eq_refl (term370 _87042 f t _34887)). Qed.
Lemma lem3342608 {_87042 : Type'} (_34887 : _87042) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term351 _87042 f t _34887.
Proof. exact (EQ_MP (@lem3342607 _87042 f t _34887) (@lem3342606 _87042 _34887 f s t x h1)). Qed.
Lemma lem3342609 {_87042 : Type'} (_34887 : _87042) (_34888 : _87042 -> Prop) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term371 _87042 f t _34887 _34888.
Proof. exact (@lem3342608 _87042 _34887 f s t x h1 _34888). Qed.
Lemma lem3342610 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (t : _87042 -> Prop) (_34887 : _87042) : (term371 _87042 f t _34887 _34888) = (term348 _87042 f _34888 t _34887).
Proof. exact (eq_refl (term371 _87042 f t _34887 _34888)). Qed.
Lemma lem3342611 {_87042 : Type'} (_34888 : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term348 _87042 f _34888 t _34887.
Proof. exact (EQ_MP (@lem3342610 _87042 f _34888 t _34887) (@lem3342609 _87042 _34887 _34888 f s t x h1)). Qed.
Lemma lem3342612 {_87042 : Type'} (_34889 : _87042 -> Prop) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term372 _87042 f t _34889.
Proof. exact (@lem3342593 _87042 t' x f t h1 _34889). Qed.
Lemma lem3342613 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (t : _87042 -> Prop) : (term372 _87042 f t _34889) = (term367 _87042 f _34889 t).
Proof. exact (eq_refl (term372 _87042 f t _34889)). Qed.
Lemma lem3342614 {_87042 : Type'} (_34889 : _87042 -> Prop) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term367 _87042 f _34889 t.
Proof. exact (EQ_MP (@lem3342613 _87042 f _34889 t) (@lem3342612 _87042 _34889 t' x f t h1)). Qed.
Lemma lem3342615 {_87042 : Type'} (_34889 : _87042 -> Prop) (_34890 : _87042) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term373 _87042 f _34889 t _34890.
Proof. exact (@lem3342614 _87042 _34889 t' x f t h1 _34890). Qed.
Lemma lem3342616 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (t : _87042 -> Prop) (_34890 : _87042) : (term373 _87042 f _34889 t _34890) = (term364 _87042 f _34889 t _34890).
Proof. exact (eq_refl (term373 _87042 f _34889 t _34890)). Qed.
Lemma lem3342628 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (t : _87042 -> Prop) (_34887 : _87042) : (term348 _87042 f _34888 t _34887) = (term364 _87042 f _34888 t _34887).
Proof. exact (@lem3341289 (term307 _87042 f _34888) (term300 _87042 _34888 _34887) (@I (_87042 -> Prop) t _34887)). Qed.
Lemma lem3342629 {_87042 : Type'} (_34888 : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term364 _87042 f _34888 t _34887.
Proof. exact (EQ_MP (@lem3342628 _87042 f _34888 t _34887) (@lem3342611 _87042 _34888 _34887 f s t x h1)). Qed.
Lemma lem3342635 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term300 _87042 t x.
Proof. exact (proj2 (@lem3342480 _87042 f s t x h1)). Qed.
Lemma lem3342645 {_87042 : Type'} (_34889 : _87042 -> Prop) (_34890 : _87042) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term364 _87042 f _34889 t _34890.
Proof. exact (EQ_MP (@lem3342616 _87042 f _34889 t _34890) (@lem3342615 _87042 _34889 _34890 t' x f t h1)). Qed.
Lemma lem3342647 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term300 _87042 t x.
Proof. exact (proj2 (@lem3342485 _87042 t' x f t h1)). Qed.
Lemma lem3342653 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : @I ((_87042 -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem3342478 _87042 f s t x h1)). Qed.
Lemma lem3342654 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term374 _87042 f s.
Proof. exact (fun h0 : term307 _87042 f s => @lem3342653 _87042 f s t x h1). Qed.
Lemma lem3342656 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342657 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) : (term374 _87042 f s) = (@I ((_87042 -> Prop) -> Prop) f s).
Proof. exact (@lem3342656 (@I ((_87042 -> Prop) -> Prop) f s)). Qed.
Lemma lem3342658 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : @I ((_87042 -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem3342657 _87042 f s) (@lem3342654 _87042 f s t x h1)). Qed.
Lemma lem3342660 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : @I (_87042 -> Prop) s x.
Proof. exact (proj1 (@lem3342480 _87042 f s t x h1)). Qed.
Lemma lem3342661 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term376 _87042 s x.
Proof. exact (fun h0 : term300 _87042 s x => @lem3342660 _87042 f s t x h1). Qed.
Lemma lem3342663 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342664 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) : (term376 _87042 s x) = (@I (_87042 -> Prop) s x).
Proof. exact (@lem3342663 (@I (_87042 -> Prop) s x)). Qed.
Lemma lem3342665 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : @I (_87042 -> Prop) s x.
Proof. exact (EQ_MP (@lem3342664 _87042 s x) (@lem3342661 _87042 f s t x h1)). Qed.
Lemma lem3342671 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3342672 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (t : _87042 -> Prop) (_34887 : _87042) : (term364 _87042 f _34888 t _34887) = (term377 _87042 f _34888 t _34887).
Proof. exact (@lem3342671 (term300 _87042 _34888 _34887) (term307 _87042 f _34888) (@I (_87042 -> Prop) t _34887)). Qed.
Lemma lem3342686 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3342687 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term378 _87042 f _34888 t _34887) = (term379 _87042 t _34887 f _34888).
Proof. exact (@lem3342686 (@I (_87042 -> Prop) t _34887) (term307 _87042 f _34888)). Qed.
Lemma lem3342693 {_87042 : Type'} (_34888 : _87042 -> Prop) (_34887 : _87042) : (term302 _87042 _34888 _34887) = (term302 _87042 _34888 _34887).
Proof. exact (eq_refl (term302 _87042 _34888 _34887)). Qed.
Lemma lem3342694 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term377 _87042 f _34888 t _34887) = (term380 _87042 t _34887 f _34888).
Proof. exact (MK_COMB (@lem3342693 _87042 _34888 _34887) (@lem3342687 _87042 t _34887 f _34888)). Qed.
Lemma lem3342698 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3342699 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term380 _87042 t _34887 f _34888) = (term381 _87042 t _34887 f _34888).
Proof. exact (@lem3342698 (@I (_87042 -> Prop) t _34887) (term300 _87042 _34888 _34887) (term307 _87042 f _34888)). Qed.
Lemma lem3342715 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term377 _87042 f _34888 t _34887) = (term381 _87042 t _34887 f _34888).
Proof. exact (TRANS (@lem3342694 _87042 t _34887 f _34888) (@lem3342699 _87042 t _34887 f _34888)). Qed.
Lemma lem3342716 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term364 _87042 f _34888 t _34887) = (term381 _87042 t _34887 f _34888).
Proof. exact (TRANS (@lem3342672 _87042 f _34888 t _34887) (@lem3342715 _87042 t _34887 f _34888)). Qed.
Lemma lem3342717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342718 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term382 _87042 f _34888 t _34887) = (term383 _87042 t _34887 f _34888).
Proof. exact (MK_COMB (@lem3342717) (@lem3342716 _87042 t _34887 f _34888)). Qed.
Lemma lem3342732 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3342733 {_87042 : Type'} (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term322 _87042 f _34888 _34887) = (term384 _87042 _34887 f _34888).
Proof. exact (@lem3342732 (term300 _87042 _34888 _34887) (term307 _87042 f _34888)). Qed.
Lemma lem3342739 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) : (term385 _87042 t _34887) = (term385 _87042 t _34887).
Proof. exact (eq_refl (term385 _87042 t _34887)). Qed.
Lemma lem3342740 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : (term386 _87042 t f _34888 _34887) = (term381 _87042 t _34887 f _34888).
Proof. exact (MK_COMB (@lem3342739 _87042 t _34887) (@lem3342733 _87042 _34887 f _34888)). Qed.
Lemma lem3342751 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : ((term364 _87042 f _34888 t _34887) = (term386 _87042 t f _34888 _34887)) = ((term381 _87042 t _34887 f _34888) = (term381 _87042 t _34887 f _34888)).
Proof. exact (MK_COMB (@lem3342718 _87042 t _34887 f _34888) (@lem3342740 _87042 t _34887 f _34888)). Qed.
Lemma lem3342753 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3342754 (x : Prop) : (x = x) = True.
Proof. exact (@lem3342753 Prop x). Qed.
Lemma lem3342755 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (_34888 : _87042 -> Prop) : ((term381 _87042 t _34887 f _34888) = (term381 _87042 t _34887 f _34888)) = True.
Proof. exact (@lem3342754 (term381 _87042 t _34887 f _34888)). Qed.
Lemma lem3342756 {_87042 : Type'} (t : _87042 -> Prop) (f : type686 _87042) (_34888 : _87042 -> Prop) (_34887 : _87042) : ((term364 _87042 f _34888 t _34887) = (term386 _87042 t f _34888 _34887)) = True.
Proof. exact (TRANS (@lem3342751 _87042 t _34887 f _34888) (@lem3342755 _87042 t _34887 f _34888)). Qed.
Lemma lem3342757 {_87042 : Type'} (t : _87042 -> Prop) (f : type686 _87042) (_34888 : _87042 -> Prop) (_34887 : _87042) : True = ((term364 _87042 f _34888 t _34887) = (term386 _87042 t f _34888 _34887)).
Proof. exact (SYM (@lem3342756 _87042 t f _34888 _34887)). Qed.
Lemma lem3342758 {_87042 : Type'} (t : _87042 -> Prop) (f : type686 _87042) (_34888 : _87042 -> Prop) (_34887 : _87042) : (term364 _87042 f _34888 t _34887) = (term386 _87042 t f _34888 _34887).
Proof. exact (EQ_MP (@lem3342757 _87042 t f _34888 _34887) (@lem0)). Qed.
Lemma lem3342759 {_87042 : Type'} (_34888 : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term386 _87042 t f _34888 _34887.
Proof. exact (EQ_MP (@lem3342758 _87042 t f _34888 _34887) (@lem3342629 _87042 _34888 _34887 f s t x h1)). Qed.
Lemma lem3342761 (b : Prop) (a : Prop) : (a \/ b) = (term387 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3342762 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (t : _87042 -> Prop) (_34887 : _87042) : (term386 _87042 t f _34888 _34887) = (term388 _87042 f _34888 t _34887).
Proof. exact (@lem3342761 (term322 _87042 f _34888 _34887) (@I (_87042 -> Prop) t _34887)). Qed.
Lemma lem3342764 (a : Prop) (b : Prop) : (term389 a b) = (term390 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3342765 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (_34887 : _87042) : (term391 _87042 f _34888 _34887) = (term392 _87042 f _34888 _34887).
Proof. exact (@lem3342764 (term307 _87042 f _34888) (term300 _87042 _34888 _34887)). Qed.
Lemma lem3342767 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3342768 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) : (term393 _87042 f _34888) = (@I ((_87042 -> Prop) -> Prop) f _34888).
Proof. exact (@lem3342767 (@I ((_87042 -> Prop) -> Prop) f _34888)). Qed.
Lemma lem3342769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342770 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) : (term394 _87042 f _34888) = (term312 _87042 f _34888).
Proof. exact (MK_COMB (@lem3342769) (@lem3342768 _87042 f _34888)). Qed.
Lemma lem3342772 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3342773 {_87042 : Type'} (_34888 : _87042 -> Prop) (_34887 : _87042) : (term395 _87042 _34888 _34887) = (@I (_87042 -> Prop) _34888 _34887).
Proof. exact (@lem3342772 (@I (_87042 -> Prop) _34888 _34887)). Qed.
Lemma lem3342774 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (_34887 : _87042) : (term392 _87042 f _34888 _34887) = (term313 _87042 f _34888 _34887).
Proof. exact (MK_COMB (@lem3342770 _87042 f _34888) (@lem3342773 _87042 _34888 _34887)). Qed.
Lemma lem3342775 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (_34887 : _87042) : (term391 _87042 f _34888 _34887) = (term313 _87042 f _34888 _34887).
Proof. exact (TRANS (@lem3342765 _87042 f _34888 _34887) (@lem3342774 _87042 f _34888 _34887)). Qed.
Lemma lem3342776 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3342777 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (_34887 : _87042) : (term396 _87042 f _34888 _34887) = (term397 _87042 f _34888 _34887).
Proof. exact (MK_COMB (@lem3342776) (@lem3342775 _87042 f _34888 _34887)). Qed.
Lemma lem3342778 {_87042 : Type'} (t : _87042 -> Prop) (_34887 : _87042) : (@I (_87042 -> Prop) t _34887) = (@I (_87042 -> Prop) t _34887).
Proof. exact (eq_refl (@I (_87042 -> Prop) t _34887)). Qed.
Lemma lem3342779 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (t : _87042 -> Prop) (_34887 : _87042) : (term388 _87042 f _34888 t _34887) = (term398 _87042 f _34888 t _34887).
Proof. exact (MK_COMB (@lem3342777 _87042 f _34888 _34887) (@lem3342778 _87042 t _34887)). Qed.
Lemma lem3342780 {_87042 : Type'} (f : type686 _87042) (_34888 : _87042 -> Prop) (t : _87042 -> Prop) (_34887 : _87042) : (term386 _87042 t f _34888 _34887) = (term398 _87042 f _34888 t _34887).
Proof. exact (TRANS (@lem3342762 _87042 f _34888 t _34887) (@lem3342779 _87042 f _34888 t _34887)). Qed.
Lemma lem3342782 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term313 _87042 f s x.
Proof. exact (conj (@lem3342658 _87042 f s t x h1) (@lem3342665 _87042 f s t x h1)). Qed.
Lemma lem3342784 {_87042 : Type'} (_34888 : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term398 _87042 f _34888 t _34887.
Proof. exact (EQ_MP (@lem3342780 _87042 f _34888 t _34887) (@lem3342759 _87042 _34888 _34887 f s t x h1)). Qed.
Lemma lem3342785 {_87042 : Type'} (_34888 : _87042 -> Prop) (_34887 : _87042) (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term398 _87042 f _34888 t _34887.
Proof. exact (@lem3342784 _87042 _34888 _34887 f s t x h1). Qed.
Lemma lem3342786 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term398 _87042 f s t x.
Proof. exact (@lem3342785 _87042 s x f s t x h1). Qed.
Lemma lem3342789 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : @I (_87042 -> Prop) t x.
Proof. exact (@lem3342786 _87042 f s t x h1 (@lem3342782 _87042 f s t x h1)). Qed.
Lemma lem3342790 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term376 _87042 t x.
Proof. exact (fun h0 : term300 _87042 t x => @lem3342789 _87042 f s t x h1). Qed.
Lemma lem3342792 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342793 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term376 _87042 t x) = (@I (_87042 -> Prop) t x).
Proof. exact (@lem3342792 (@I (_87042 -> Prop) t x)). Qed.
Lemma lem3342794 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : @I (_87042 -> Prop) t x.
Proof. exact (EQ_MP (@lem3342793 _87042 t x) (@lem3342790 _87042 f s t x h1)). Qed.
Lemma lem3342797 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3342799 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term300 _87042 t x) = (term399 _87042 t x).
Proof. exact (@lem3342797 (@I (_87042 -> Prop) t x)). Qed.
Lemma lem3342802 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term399 _87042 t x.
Proof. exact (EQ_MP (@lem3342799 _87042 t x) (@lem3342635 _87042 f s t x h1)). Qed.
Lemma lem3342805 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : False.
Proof. exact (@lem3342802 _87042 f s t x h1 (@lem3342794 _87042 f s t x h1)). Qed.
Lemma lem3342806 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : term400.
Proof. exact (fun h0 : ~ False => @lem3342805 _87042 f s t x h1). Qed.
Lemma lem3342808 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342809 : term400 = False.
Proof. exact (@lem3342808 False). Qed.
Lemma lem3342810 {_87042 : Type'} (f : type686 _87042) (s : _87042 -> Prop) (t : _87042 -> Prop) (x : _87042) (h1 : term330 _87042 f s t x) : False.
Proof. exact (EQ_MP (@lem3342809) (@lem3342806 _87042 f s t x h1)). Qed.
Lemma lem3342812 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : @I ((_87042 -> Prop) -> Prop) f t'.
Proof. exact (proj1 (@lem3342487 _87042 t' x f t h1)). Qed.
Lemma lem3342813 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term374 _87042 f t'.
Proof. exact (fun h0 : term307 _87042 f t' => @lem3342812 _87042 t' x f t h1). Qed.
Lemma lem3342815 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342816 {_87042 : Type'} (f : type686 _87042) (t' : _87042 -> Prop) : (term374 _87042 f t') = (@I ((_87042 -> Prop) -> Prop) f t').
Proof. exact (@lem3342815 (@I ((_87042 -> Prop) -> Prop) f t')). Qed.
Lemma lem3342817 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : @I ((_87042 -> Prop) -> Prop) f t'.
Proof. exact (EQ_MP (@lem3342816 _87042 f t') (@lem3342813 _87042 t' x f t h1)). Qed.
Lemma lem3342819 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : @I (_87042 -> Prop) t' x.
Proof. exact (proj2 (@lem3342487 _87042 t' x f t h1)). Qed.
Lemma lem3342820 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term376 _87042 t' x.
Proof. exact (fun h0 : term300 _87042 t' x => @lem3342819 _87042 t' x f t h1). Qed.
Lemma lem3342822 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342823 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) : (term376 _87042 t' x) = (@I (_87042 -> Prop) t' x).
Proof. exact (@lem3342822 (@I (_87042 -> Prop) t' x)). Qed.
Lemma lem3342824 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : @I (_87042 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3342823 _87042 t' x) (@lem3342820 _87042 t' x f t h1)). Qed.
Lemma lem3342830 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3342831 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (t : _87042 -> Prop) (_34890 : _87042) : (term364 _87042 f _34889 t _34890) = (term377 _87042 f _34889 t _34890).
Proof. exact (@lem3342830 (term300 _87042 _34889 _34890) (term307 _87042 f _34889) (@I (_87042 -> Prop) t _34890)). Qed.
Lemma lem3342845 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3342846 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term378 _87042 f _34889 t _34890) = (term379 _87042 t _34890 f _34889).
Proof. exact (@lem3342845 (@I (_87042 -> Prop) t _34890) (term307 _87042 f _34889)). Qed.
Lemma lem3342852 {_87042 : Type'} (_34889 : _87042 -> Prop) (_34890 : _87042) : (term302 _87042 _34889 _34890) = (term302 _87042 _34889 _34890).
Proof. exact (eq_refl (term302 _87042 _34889 _34890)). Qed.
Lemma lem3342853 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term377 _87042 f _34889 t _34890) = (term380 _87042 t _34890 f _34889).
Proof. exact (MK_COMB (@lem3342852 _87042 _34889 _34890) (@lem3342846 _87042 t _34890 f _34889)). Qed.
Lemma lem3342857 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3342858 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term380 _87042 t _34890 f _34889) = (term381 _87042 t _34890 f _34889).
Proof. exact (@lem3342857 (@I (_87042 -> Prop) t _34890) (term300 _87042 _34889 _34890) (term307 _87042 f _34889)). Qed.
Lemma lem3342874 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term377 _87042 f _34889 t _34890) = (term381 _87042 t _34890 f _34889).
Proof. exact (TRANS (@lem3342853 _87042 t _34890 f _34889) (@lem3342858 _87042 t _34890 f _34889)). Qed.
Lemma lem3342875 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term364 _87042 f _34889 t _34890) = (term381 _87042 t _34890 f _34889).
Proof. exact (TRANS (@lem3342831 _87042 f _34889 t _34890) (@lem3342874 _87042 t _34890 f _34889)). Qed.
Lemma lem3342876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3342877 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term382 _87042 f _34889 t _34890) = (term383 _87042 t _34890 f _34889).
Proof. exact (MK_COMB (@lem3342876) (@lem3342875 _87042 t _34890 f _34889)). Qed.
Lemma lem3342891 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3342892 {_87042 : Type'} (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term322 _87042 f _34889 _34890) = (term384 _87042 _34890 f _34889).
Proof. exact (@lem3342891 (term300 _87042 _34889 _34890) (term307 _87042 f _34889)). Qed.
Lemma lem3342898 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) : (term385 _87042 t _34890) = (term385 _87042 t _34890).
Proof. exact (eq_refl (term385 _87042 t _34890)). Qed.
Lemma lem3342899 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : (term386 _87042 t f _34889 _34890) = (term381 _87042 t _34890 f _34889).
Proof. exact (MK_COMB (@lem3342898 _87042 t _34890) (@lem3342892 _87042 _34890 f _34889)). Qed.
Lemma lem3342910 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : ((term364 _87042 f _34889 t _34890) = (term386 _87042 t f _34889 _34890)) = ((term381 _87042 t _34890 f _34889) = (term381 _87042 t _34890 f _34889)).
Proof. exact (MK_COMB (@lem3342877 _87042 t _34890 f _34889) (@lem3342899 _87042 t _34890 f _34889)). Qed.
Lemma lem3342912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3342913 (x : Prop) : (x = x) = True.
Proof. exact (@lem3342912 Prop x). Qed.
Lemma lem3342914 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) (f : type686 _87042) (_34889 : _87042 -> Prop) : ((term381 _87042 t _34890 f _34889) = (term381 _87042 t _34890 f _34889)) = True.
Proof. exact (@lem3342913 (term381 _87042 t _34890 f _34889)). Qed.
Lemma lem3342915 {_87042 : Type'} (t : _87042 -> Prop) (f : type686 _87042) (_34889 : _87042 -> Prop) (_34890 : _87042) : ((term364 _87042 f _34889 t _34890) = (term386 _87042 t f _34889 _34890)) = True.
Proof. exact (TRANS (@lem3342910 _87042 t _34890 f _34889) (@lem3342914 _87042 t _34890 f _34889)). Qed.
Lemma lem3342916 {_87042 : Type'} (t : _87042 -> Prop) (f : type686 _87042) (_34889 : _87042 -> Prop) (_34890 : _87042) : True = ((term364 _87042 f _34889 t _34890) = (term386 _87042 t f _34889 _34890)).
Proof. exact (SYM (@lem3342915 _87042 t f _34889 _34890)). Qed.
Lemma lem3342917 {_87042 : Type'} (t : _87042 -> Prop) (f : type686 _87042) (_34889 : _87042 -> Prop) (_34890 : _87042) : (term364 _87042 f _34889 t _34890) = (term386 _87042 t f _34889 _34890).
Proof. exact (EQ_MP (@lem3342916 _87042 t f _34889 _34890) (@lem0)). Qed.
Lemma lem3342918 {_87042 : Type'} (_34889 : _87042 -> Prop) (_34890 : _87042) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term386 _87042 t f _34889 _34890.
Proof. exact (EQ_MP (@lem3342917 _87042 t f _34889 _34890) (@lem3342645 _87042 _34889 _34890 t' x f t h1)). Qed.
Lemma lem3342920 (b : Prop) (a : Prop) : (a \/ b) = (term387 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3342921 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (t : _87042 -> Prop) (_34890 : _87042) : (term386 _87042 t f _34889 _34890) = (term388 _87042 f _34889 t _34890).
Proof. exact (@lem3342920 (term322 _87042 f _34889 _34890) (@I (_87042 -> Prop) t _34890)). Qed.
Lemma lem3342923 (a : Prop) (b : Prop) : (term389 a b) = (term390 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3342924 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (_34890 : _87042) : (term391 _87042 f _34889 _34890) = (term392 _87042 f _34889 _34890).
Proof. exact (@lem3342923 (term307 _87042 f _34889) (term300 _87042 _34889 _34890)). Qed.
Lemma lem3342926 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3342927 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) : (term393 _87042 f _34889) = (@I ((_87042 -> Prop) -> Prop) f _34889).
Proof. exact (@lem3342926 (@I ((_87042 -> Prop) -> Prop) f _34889)). Qed.
Lemma lem3342928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3342929 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) : (term394 _87042 f _34889) = (term312 _87042 f _34889).
Proof. exact (MK_COMB (@lem3342928) (@lem3342927 _87042 f _34889)). Qed.
Lemma lem3342931 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3342932 {_87042 : Type'} (_34889 : _87042 -> Prop) (_34890 : _87042) : (term395 _87042 _34889 _34890) = (@I (_87042 -> Prop) _34889 _34890).
Proof. exact (@lem3342931 (@I (_87042 -> Prop) _34889 _34890)). Qed.
Lemma lem3342933 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (_34890 : _87042) : (term392 _87042 f _34889 _34890) = (term313 _87042 f _34889 _34890).
Proof. exact (MK_COMB (@lem3342929 _87042 f _34889) (@lem3342932 _87042 _34889 _34890)). Qed.
Lemma lem3342934 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (_34890 : _87042) : (term391 _87042 f _34889 _34890) = (term313 _87042 f _34889 _34890).
Proof. exact (TRANS (@lem3342924 _87042 f _34889 _34890) (@lem3342933 _87042 f _34889 _34890)). Qed.
Lemma lem3342935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3342936 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (_34890 : _87042) : (term396 _87042 f _34889 _34890) = (term397 _87042 f _34889 _34890).
Proof. exact (MK_COMB (@lem3342935) (@lem3342934 _87042 f _34889 _34890)). Qed.
Lemma lem3342937 {_87042 : Type'} (t : _87042 -> Prop) (_34890 : _87042) : (@I (_87042 -> Prop) t _34890) = (@I (_87042 -> Prop) t _34890).
Proof. exact (eq_refl (@I (_87042 -> Prop) t _34890)). Qed.
Lemma lem3342938 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (t : _87042 -> Prop) (_34890 : _87042) : (term388 _87042 f _34889 t _34890) = (term398 _87042 f _34889 t _34890).
Proof. exact (MK_COMB (@lem3342936 _87042 f _34889 _34890) (@lem3342937 _87042 t _34890)). Qed.
Lemma lem3342939 {_87042 : Type'} (f : type686 _87042) (_34889 : _87042 -> Prop) (t : _87042 -> Prop) (_34890 : _87042) : (term386 _87042 t f _34889 _34890) = (term398 _87042 f _34889 t _34890).
Proof. exact (TRANS (@lem3342921 _87042 f _34889 t _34890) (@lem3342938 _87042 f _34889 t _34890)). Qed.
Lemma lem3342941 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term313 _87042 f t' x.
Proof. exact (conj (@lem3342817 _87042 t' x f t h1) (@lem3342824 _87042 t' x f t h1)). Qed.
Lemma lem3342943 {_87042 : Type'} (_34889 : _87042 -> Prop) (_34890 : _87042) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term398 _87042 f _34889 t _34890.
Proof. exact (EQ_MP (@lem3342939 _87042 f _34889 t _34890) (@lem3342918 _87042 _34889 _34890 t' x f t h1)). Qed.
Lemma lem3342944 {_87042 : Type'} (_34889 : _87042 -> Prop) (_34890 : _87042) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term398 _87042 f _34889 t _34890.
Proof. exact (@lem3342943 _87042 _34889 _34890 t' x f t h1). Qed.
Lemma lem3342945 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term398 _87042 f t' t x.
Proof. exact (@lem3342944 _87042 t' x t' x f t h1). Qed.
Lemma lem3342948 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : @I (_87042 -> Prop) t x.
Proof. exact (@lem3342945 _87042 t' x f t h1 (@lem3342941 _87042 t' x f t h1)). Qed.
Lemma lem3342949 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term376 _87042 t x.
Proof. exact (fun h0 : term300 _87042 t x => @lem3342948 _87042 t' x f t h1). Qed.
Lemma lem3342951 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342952 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term376 _87042 t x) = (@I (_87042 -> Prop) t x).
Proof. exact (@lem3342951 (@I (_87042 -> Prop) t x)). Qed.
Lemma lem3342953 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : @I (_87042 -> Prop) t x.
Proof. exact (EQ_MP (@lem3342952 _87042 t x) (@lem3342949 _87042 t' x f t h1)). Qed.
Lemma lem3342956 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3342958 {_87042 : Type'} (t : _87042 -> Prop) (x : _87042) : (term300 _87042 t x) = (term399 _87042 t x).
Proof. exact (@lem3342956 (@I (_87042 -> Prop) t x)). Qed.
Lemma lem3342961 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term399 _87042 t x.
Proof. exact (EQ_MP (@lem3342958 _87042 t x) (@lem3342647 _87042 t' x f t h1)). Qed.
Lemma lem3342964 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : False.
Proof. exact (@lem3342961 _87042 t' x f t h1 (@lem3342953 _87042 t' x f t h1)). Qed.
Lemma lem3342965 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : term400.
Proof. exact (fun h0 : ~ False => @lem3342964 _87042 t' x f t h1). Qed.
Lemma lem3342967 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3342968 : term400 = False.
Proof. exact (@lem3342967 False). Qed.
Lemma lem3342969 {_87042 : Type'} (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term317 _87042 t' x f t) : False.
Proof. exact (EQ_MP (@lem3342968) (@lem3342965 _87042 t' x f t h1)). Qed.
Lemma lem3342970 {_87042 : Type'} (s : _87042 -> Prop) (t' : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term292 _87042 s t' x f t) : False.
Proof. exact (or_elim (@lem3342475 _87042 s t' x f t h1) (fun h0 : term330 _87042 f s t x => @lem3342810 _87042 f s t x h0) (fun h0 : term317 _87042 t' x f t => @lem3342969 _87042 t' x f t h0)). Qed.
Lemma lem3342971 {_87042 : Type'} (s : _87042 -> Prop) (x : _87042) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term295 _87042 s x f t) : False.
Proof. exact (ex_elim (@lem3342320 _87042 s x f t h1) (fun t' : _87042 -> Prop => fun h0 : term294 _87042 s x f t t' => @lem3342970 _87042 s t' x f t h0)). Qed.
Lemma lem3342972 {_87042 : Type'} (s : _87042 -> Prop) (f : type686 _87042) (t : _87042 -> Prop) (h1 : term297 _87042 s f t) : False.
Proof. exact (ex_elim (@lem3342319 _87042 s f t h1) (fun x : _87042 => fun h0 : term296 _87042 s f t x => @lem3342971 _87042 s x f t h0)). Qed.
Lemma lem3342973 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (h1 : term68 _87042 f t) : False.
Proof. exact (ex_elim (@lem3342318 _87042 f t h1) (fun s : _87042 -> Prop => fun h0 : term298 _87042 f t s => @lem3342972 _87042 s f t h0)). Qed.
Lemma lem3342974 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (h1 : term68 _87042 f t) : (term68 _87042 f t) = False.
Proof. exact (prop_ext (fun h2 : term68 _87042 f t => @lem3342973 _87042 f t h1) (fun h2 : False => @lem3341670 _87042 f t h1)). Qed.
Lemma lem3342975 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) (h1 : term68 _87042 f t) : False.
Proof. exact (EQ_MP (@lem3342974 _87042 f t h1) (@lem3341670 _87042 f t h1)). Qed.
Lemma lem3342976 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : term67 _87042 f t.
Proof. exact (fun h0 : term68 _87042 f t => @lem3342975 _87042 f t h0). Qed.
Lemma lem3342977 {_87042 : Type'} (f : type686 _87042) (t : _87042 -> Prop) : (term42 _87042 f t) = (term54 _87042 f t).
Proof. exact (EQ_MP (@lem3341669 _87042 f t) (@lem3342976 _87042 f t)). Qed.
Lemma lem3342982 {_87042 : Type'} (f : type686 _87042) : term56 _87042 f.
Proof. exact (fun t : _87042 -> Prop => @lem3342977 _87042 f t). Qed.
Lemma lem3342987 {_87042 : Type'} : term58 _87042.
Proof. exact (fun f : type686 _87042 => @lem3342982 _87042 f). Qed.
Lemma lem3342988 {_87042 : Type'} : term60 _87042.
Proof. exact (EQ_MP (@lem3341665 _87042) (@lem3342987 _87042)). Qed.
Lemma lem3342990 {_87042 : Type'} : term60 _87042.
Proof. exact (@lem3341511 _87042 (@lem3342988 _87042)). Qed.
Lemma lem3342991 {_87042 : Type'} (h1 : term61 _87042) : False.
Proof. exact (@lem3342990 _87042 (@lem3341495 _87042 h1)). Qed.
Lemma lem3342992 {_87042 : Type'} (h1 : term61 _87042) : (term61 _87042) = False.
Proof. exact (prop_ext (fun h2 : term61 _87042 => @lem3342991 _87042 h1) (fun h2 : False => @lem3341495 _87042 h1)). Qed.
Lemma lem3342993 {_87042 : Type'} (h1 : term61 _87042) : False.
Proof. exact (EQ_MP (@lem3342992 _87042 h1) (@lem3341495 _87042 h1)). Qed.
Lemma lem3342994 {_87042 : Type'} : term60 _87042.
Proof. exact (fun h0 : term61 _87042 => @lem3342993 _87042 h0). Qed.
Lemma lem3342995 {_87042 : Type'} : term58 _87042.
Proof. exact (EQ_MP (@lem3341494 _87042) (@lem3342994 _87042)). Qed.
Lemma lem3342996 {_87042 : Type'} : term26 _87042.
Proof. exact (EQ_MP (@lem3341490 _87042) (@lem3342995 _87042)). Qed.
Lemma lem3342997 {_87042 : Type'} : term25 _87042.
Proof. exact (EQ_MP (@lem3341359 _87042) (@lem3342996 _87042)). Qed.
