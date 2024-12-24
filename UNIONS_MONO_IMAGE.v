Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_MONO_IMAGE_term_abbrevs.
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
Require Import thm18394_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3348273 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3348274 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3348275 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3348274 t1) (@lem3348273 t1)). Qed.
Lemma lem3348276 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3348275 t1 t2). Qed.
Lemma lem3348277 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3348278 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3348277 t1 t2) (@lem3348276 t1 t2)). Qed.
Lemma lem3348279 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3348278 t1 t2 t3). Qed.
Lemma lem3348280 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3348281 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3348280 t1 t2 t3) (@lem3348279 t1 t2 t3)). Qed.
Lemma lem3348282 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3348281 t1 t2 t3)). Qed.
Lemma lem3348292 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3348293 {_87182 : Type'} (s : _87182 -> Prop) (t : _87182 -> Prop) : (@SUBSET _87182 s t) = (term7 _87182 s t).
Proof. exact (@lem3348292 _87182 s t). Qed.
Lemma lem3348294 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term8 _87171 _87182 f g x) = (term9 _87171 _87182 f g x).
Proof. exact (@lem3348293 _87182 (f x) (g x)). Qed.
Lemma lem3348301 {_87171 : Type'} (x : _87171) (s : _87171 -> Prop) : (term10 _87171 x s) = (term10 _87171 x s).
Proof. exact (eq_refl (term10 _87171 x s)). Qed.
Lemma lem3348302 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term11 _87171 _87182 s f g x) = (term12 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3348301 _87171 x s) (@lem3348294 _87171 _87182 f g x)). Qed.
Lemma lem3348305 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term13 _87171 _87182 s f g) = (term14 _87171 _87182 s f g).
Proof. exact (fun_ext (fun x : _87171 => @lem3348302 _87171 _87182 s f g x)). Qed.
Lemma lem3348306 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3348307 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term15 _87171 _87182 s f g) = (term16 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3348306 _87171) (@lem3348305 _87171 _87182 s f g)). Qed.
Lemma lem3348312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348313 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term17 _87171 _87182 s f g) = (term18 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3348312) (@lem3348307 _87171 _87182 s f g)). Qed.
Lemma lem3348315 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3348316 {_87182 : Type'} (s : _87182 -> Prop) (t : _87182 -> Prop) : (@SUBSET _87182 s t) = (term7 _87182 s t).
Proof. exact (@lem3348315 _87182 s t). Qed.
Lemma lem3348317 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term19 _87171 _87182 f g s) = (term20 _87171 _87182 f g s).
Proof. exact (@lem3348316 _87182 (term21 _87171 _87182 f s) (term21 _87171 _87182 g s)). Qed.
Lemma lem3348324 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term22 _87171 _87182 f g s) = (term23 _87171 _87182 f g s).
Proof. exact (MK_COMB (@lem3348313 _87171 _87182 s f g) (@lem3348317 _87171 _87182 f g s)). Qed.
Lemma lem3348327 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term23 _87171 _87182 f g s) = (term22 _87171 _87182 f g s).
Proof. exact (SYM (@lem3348324 _87171 _87182 f g s)). Qed.
Lemma lem3348337 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3348338 {_87171 : Type'} (P : _87171 -> Prop) (x : _87171) : (@IN _87171 x P) = (P x).
Proof. exact (@lem3348337 _87171 P x). Qed.
Lemma lem3348339 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (@IN _87171 x s) = (s x).
Proof. exact (@lem3348338 _87171 s x). Qed.
Lemma lem3348340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348341 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term10 _87171 x s) = (term24 _87171 s x).
Proof. exact (MK_COMB (@lem3348340) (@lem3348339 _87171 s x)). Qed.
Lemma lem3348349 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3348350 {_87182 : Type'} (P : _87182 -> Prop) (x : _87182) : (@IN _87182 x P) = (P x).
Proof. exact (@lem3348349 _87182 P x). Qed.
Lemma lem3348351 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term25 _87171 _87182 x' f x) = (f x x').
Proof. exact (@lem3348350 _87182 (f x) x'). Qed.
Lemma lem3348352 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348353 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term26 _87171 _87182 x' f x) = (term27 _87171 _87182 f x x').
Proof. exact (MK_COMB (@lem3348352) (@lem3348351 _87171 _87182 f x x')). Qed.
Lemma lem3348355 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3348356 {_87182 : Type'} (P : _87182 -> Prop) (x : _87182) : (@IN _87182 x P) = (P x).
Proof. exact (@lem3348355 _87182 P x). Qed.
Lemma lem3348357 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term25 _87171 _87182 x' g x) = (g x x').
Proof. exact (@lem3348356 _87182 (g x) x'). Qed.
Lemma lem3348358 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term28 _87171 _87182 f x' g x) = (term29 _87171 _87182 f g x x').
Proof. exact (MK_COMB (@lem3348353 _87171 _87182 f x x') (@lem3348357 _87171 _87182 g x x')). Qed.
Lemma lem3348361 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term30 _87171 _87182 f g x) = (term31 _87171 _87182 f g x).
Proof. exact (fun_ext (fun x' : _87182 => @lem3348358 _87171 _87182 f g x x')). Qed.
Lemma lem3348362 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3348363 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term9 _87171 _87182 f g x) = (term32 _87171 _87182 f g x).
Proof. exact (MK_COMB (@lem3348362 _87182) (@lem3348361 _87171 _87182 f g x)). Qed.
Lemma lem3348368 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term12 _87171 _87182 s f g x) = (term33 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3348341 _87171 s x) (@lem3348363 _87171 _87182 f g x)). Qed.
Lemma lem3348371 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term14 _87171 _87182 s f g) = (term34 _87171 _87182 s f g).
Proof. exact (fun_ext (fun x : _87171 => @lem3348368 _87171 _87182 s f g x)). Qed.
Lemma lem3348372 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3348373 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term16 _87171 _87182 s f g) = (term35 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3348372 _87171) (@lem3348371 _87171 _87182 s f g)). Qed.
Lemma lem3348378 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348379 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term18 _87171 _87182 s f g) = (term36 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3348378) (@lem3348373 _87171 _87182 s f g)). Qed.
Lemma lem3348387 {A : Type'} (s : type686 A) (x : A) : (term37 A x s) = (term38 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3348388 {_87182 : Type'} (s : type686 _87182) (x : _87182) : (term37 _87182 x s) = (term38 _87182 s x).
Proof. exact (@lem3348387 _87182 s x). Qed.
Lemma lem3348389 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term39 _87171 _87182 x f s) = (term40 _87171 _87182 f s x).
Proof. exact (@lem3348388 _87182 (@IMAGE _87171 (_87182 -> Prop) f s) x). Qed.
Lemma lem3348397 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term41 A B y f s) = (term42 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3348398 {_87171 _87182 : Type'} (y : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term43 _87171 _87182 y f s) = (term44 _87171 _87182 y f s).
Proof. exact (@lem3348397 _87171 (_87182 -> Prop) y f s). Qed.
Lemma lem3348399 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term43 _87171 _87182 t f s) = (term44 _87171 _87182 t f s).
Proof. exact (@lem3348398 _87171 _87182 t f s). Qed.
Lemma lem3348409 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3348410 {_87171 : Type'} (P : _87171 -> Prop) (x : _87171) : (@IN _87171 x P) = (P x).
Proof. exact (@lem3348409 _87171 P x). Qed.
Lemma lem3348411 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (@IN _87171 x s) = (s x).
Proof. exact (@lem3348410 _87171 s x). Qed.
Lemma lem3348412 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (x : _87171) : (term45 _87171 _87182 t f x) = (term45 _87171 _87182 t f x).
Proof. exact (eq_refl (term45 _87171 _87182 t f x)). Qed.
Lemma lem3348413 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term46 _87171 _87182 t f x s) = (term47 _87171 _87182 t f s x).
Proof. exact (MK_COMB (@lem3348412 _87171 _87182 t f x) (@lem3348411 _87171 s x)). Qed.
Lemma lem3348416 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term48 _87171 _87182 t f s) = (term49 _87171 _87182 t f s).
Proof. exact (fun_ext (fun x : _87171 => @lem3348413 _87171 _87182 t f s x)). Qed.
Lemma lem3348417 {_87171 : Type'} : (@ex _87171) = (@ex _87171).
Proof. exact (eq_refl (@ex _87171)). Qed.
Lemma lem3348418 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term44 _87171 _87182 t f s) = (term50 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3348417 _87171) (@lem3348416 _87171 _87182 t f s)). Qed.
Lemma lem3348423 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term43 _87171 _87182 t f s) = (term50 _87171 _87182 t f s).
Proof. exact (TRANS (@lem3348399 _87171 _87182 t f s) (@lem3348418 _87171 _87182 t f s)). Qed.
Lemma lem3348424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3348425 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term51 _87171 _87182 t f s) = (term52 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3348424) (@lem3348423 _87171 _87182 t f s)). Qed.
Lemma lem3348427 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3348428 {_87182 : Type'} (P : _87182 -> Prop) (x : _87182) : (@IN _87182 x P) = (P x).
Proof. exact (@lem3348427 _87182 P x). Qed.
Lemma lem3348429 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (@IN _87182 x t) = (t x).
Proof. exact (@lem3348428 _87182 t x). Qed.
Lemma lem3348430 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term53 _87171 _87182 f s x t) = (term54 _87171 _87182 f s t x).
Proof. exact (MK_COMB (@lem3348425 _87171 _87182 t f s) (@lem3348429 _87182 t x)). Qed.
Lemma lem3348433 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term55 _87171 _87182 f s x) = (term56 _87171 _87182 f s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3348430 _87171 _87182 f s t x)). Qed.
Lemma lem3348434 {_87182 : Type'} : (@ex (_87182 -> Prop)) = (@ex (_87182 -> Prop)).
Proof. exact (eq_refl (@ex (_87182 -> Prop))). Qed.
Lemma lem3348435 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term40 _87171 _87182 f s x) = (term57 _87171 _87182 f s x).
Proof. exact (MK_COMB (@lem3348434 _87182) (@lem3348433 _87171 _87182 f s x)). Qed.
Lemma lem3348440 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term39 _87171 _87182 x f s) = (term57 _87171 _87182 f s x).
Proof. exact (TRANS (@lem3348389 _87171 _87182 f s x) (@lem3348435 _87171 _87182 f s x)). Qed.
Lemma lem3348441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348442 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term58 _87171 _87182 x f s) = (term59 _87171 _87182 f s x).
Proof. exact (MK_COMB (@lem3348441) (@lem3348440 _87171 _87182 f s x)). Qed.
Lemma lem3348444 {A : Type'} (s : type686 A) (x : A) : (term37 A x s) = (term38 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3348445 {_87182 : Type'} (s : type686 _87182) (x : _87182) : (term37 _87182 x s) = (term38 _87182 s x).
Proof. exact (@lem3348444 _87182 s x). Qed.
Lemma lem3348446 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term39 _87171 _87182 x g s) = (term40 _87171 _87182 g s x).
Proof. exact (@lem3348445 _87182 (@IMAGE _87171 (_87182 -> Prop) g s) x). Qed.
Lemma lem3348454 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term41 A B y f s) = (term42 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3348455 {_87171 _87182 : Type'} (y : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term43 _87171 _87182 y f s) = (term44 _87171 _87182 y f s).
Proof. exact (@lem3348454 _87171 (_87182 -> Prop) y f s). Qed.
Lemma lem3348456 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term43 _87171 _87182 t g s) = (term44 _87171 _87182 t g s).
Proof. exact (@lem3348455 _87171 _87182 t g s). Qed.
Lemma lem3348466 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3348467 {_87171 : Type'} (P : _87171 -> Prop) (x : _87171) : (@IN _87171 x P) = (P x).
Proof. exact (@lem3348466 _87171 P x). Qed.
Lemma lem3348468 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (@IN _87171 x s) = (s x).
Proof. exact (@lem3348467 _87171 s x). Qed.
Lemma lem3348469 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (x : _87171) : (term45 _87171 _87182 t g x) = (term45 _87171 _87182 t g x).
Proof. exact (eq_refl (term45 _87171 _87182 t g x)). Qed.
Lemma lem3348470 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term46 _87171 _87182 t g x s) = (term47 _87171 _87182 t g s x).
Proof. exact (MK_COMB (@lem3348469 _87171 _87182 t g x) (@lem3348468 _87171 s x)). Qed.
Lemma lem3348473 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term48 _87171 _87182 t g s) = (term49 _87171 _87182 t g s).
Proof. exact (fun_ext (fun x : _87171 => @lem3348470 _87171 _87182 t g s x)). Qed.
Lemma lem3348474 {_87171 : Type'} : (@ex _87171) = (@ex _87171).
Proof. exact (eq_refl (@ex _87171)). Qed.
Lemma lem3348475 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term44 _87171 _87182 t g s) = (term50 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3348474 _87171) (@lem3348473 _87171 _87182 t g s)). Qed.
Lemma lem3348480 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term43 _87171 _87182 t g s) = (term50 _87171 _87182 t g s).
Proof. exact (TRANS (@lem3348456 _87171 _87182 t g s) (@lem3348475 _87171 _87182 t g s)). Qed.
Lemma lem3348481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3348482 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term51 _87171 _87182 t g s) = (term52 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3348481) (@lem3348480 _87171 _87182 t g s)). Qed.
Lemma lem3348484 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3348485 {_87182 : Type'} (P : _87182 -> Prop) (x : _87182) : (@IN _87182 x P) = (P x).
Proof. exact (@lem3348484 _87182 P x). Qed.
Lemma lem3348486 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (@IN _87182 x t) = (t x).
Proof. exact (@lem3348485 _87182 t x). Qed.
Lemma lem3348487 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term53 _87171 _87182 g s x t) = (term54 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3348482 _87171 _87182 t g s) (@lem3348486 _87182 t x)). Qed.
Lemma lem3348490 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term55 _87171 _87182 g s x) = (term56 _87171 _87182 g s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3348487 _87171 _87182 g s t x)). Qed.
Lemma lem3348491 {_87182 : Type'} : (@ex (_87182 -> Prop)) = (@ex (_87182 -> Prop)).
Proof. exact (eq_refl (@ex (_87182 -> Prop))). Qed.
Lemma lem3348492 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term40 _87171 _87182 g s x) = (term57 _87171 _87182 g s x).
Proof. exact (MK_COMB (@lem3348491 _87182) (@lem3348490 _87171 _87182 g s x)). Qed.
Lemma lem3348497 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term39 _87171 _87182 x g s) = (term57 _87171 _87182 g s x).
Proof. exact (TRANS (@lem3348446 _87171 _87182 g s x) (@lem3348492 _87171 _87182 g s x)). Qed.
Lemma lem3348498 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term60 _87171 _87182 f x g s) = (term61 _87171 _87182 f g s x).
Proof. exact (MK_COMB (@lem3348442 _87171 _87182 f s x) (@lem3348497 _87171 _87182 g s x)). Qed.
Lemma lem3348501 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term62 _87171 _87182 f g s) = (term63 _87171 _87182 f g s).
Proof. exact (fun_ext (fun x : _87182 => @lem3348498 _87171 _87182 f g s x)). Qed.
Lemma lem3348502 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3348503 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term20 _87171 _87182 f g s) = (term64 _87171 _87182 f g s).
Proof. exact (MK_COMB (@lem3348502 _87182) (@lem3348501 _87171 _87182 f g s)). Qed.
Lemma lem3348508 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term23 _87171 _87182 f g s) = (term65 _87171 _87182 f g s).
Proof. exact (MK_COMB (@lem3348379 _87171 _87182 s f g) (@lem3348503 _87171 _87182 f g s)). Qed.
Lemma lem3348511 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term65 _87171 _87182 f g s) = (term23 _87171 _87182 f g s).
Proof. exact (SYM (@lem3348508 _87171 _87182 f g s)). Qed.
Lemma lem3348513 (p : Prop) : p = (term66 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3348514 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term65 _87171 _87182 f g s) = (term67 _87171 _87182 f g s).
Proof. exact (@lem3348513 (term65 _87171 _87182 f g s)). Qed.
Lemma lem3348515 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term67 _87171 _87182 f g s) = (term65 _87171 _87182 f g s).
Proof. exact (SYM (@lem3348514 _87171 _87182 f g s)). Qed.
Lemma lem3348516 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term68 _87171 _87182 f g s) : term68 _87171 _87182 f g s.
Proof. exact (h1). Qed.
Lemma lem3348519 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term67 _87171 _87182 f g s) : term67 _87171 _87182 f g s.
Proof. exact (h1). Qed.
Lemma lem3348520 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term69 _87171 _87182 f g s.
Proof. exact (fun h0 : term67 _87171 _87182 f g s => @lem3348519 _87171 _87182 f g s h0). Qed.
Lemma lem3348521 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term69 _87171 _87182 f g s) : term69 _87171 _87182 f g s.
Proof. exact (h1). Qed.
Lemma lem3348522 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term67 _87171 _87182 f g s) : term67 _87171 _87182 f g s.
Proof. exact (h1). Qed.
Lemma lem3348523 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term67 _87171 _87182 f g s) (h2 : term69 _87171 _87182 f g s) : term67 _87171 _87182 f g s.
Proof. exact (@lem3348521 _87171 _87182 f g s h2 (@lem3348522 _87171 _87182 f g s h1)). Qed.
Lemma lem3348524 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term67 _87171 _87182 f g s) : term70 _87171 _87182 f g s.
Proof. exact (fun h0 : term69 _87171 _87182 f g s => @lem3348523 _87171 _87182 f g s h1 h0). Qed.
Lemma lem3348525 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term69 _87171 _87182 f g s) : term69 _87171 _87182 f g s.
Proof. exact (h1). Qed.
Lemma lem3348526 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term67 _87171 _87182 f g s) (h2 : term69 _87171 _87182 f g s) : term67 _87171 _87182 f g s.
Proof. exact (@lem3348524 _87171 _87182 f g s h1 (@lem3348525 _87171 _87182 f g s h2)). Qed.
Lemma lem3348527 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term69 _87171 _87182 f g s) : term69 _87171 _87182 f g s.
Proof. exact (fun h0 : term67 _87171 _87182 f g s => @lem3348526 _87171 _87182 f g s h0 h1). Qed.
Lemma lem3348528 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term71 _87171 _87182 f g s.
Proof. exact (fun h0 : term69 _87171 _87182 f g s => @lem3348527 _87171 _87182 f g s h0). Qed.
Lemma lem3348531 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term69 _87171 _87182 f g s.
Proof. exact (@lem3348528 _87171 _87182 f g s (@lem3348520 _87171 _87182 f g s)). Qed.
Lemma lem3348532 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term69 _87171 _87182 f g s.
Proof. exact (@lem3348531 _87171 _87182 f g s). Qed.
Lemma lem3348546 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3348547 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term67 _87171 _87182 f g s) = (term72 _87171 _87182 f g s).
Proof. exact (@lem3348546 (term68 _87171 _87182 f g s)). Qed.
Lemma lem3348549 (t : Prop) : (term73 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3348550 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term72 _87171 _87182 f g s) = (term65 _87171 _87182 f g s).
Proof. exact (@lem3348549 (term65 _87171 _87182 f g s)). Qed.
Lemma lem3348553 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term67 _87171 _87182 f g s) = (term65 _87171 _87182 f g s).
Proof. exact (TRANS (@lem3348547 _87171 _87182 f g s) (@lem3348550 _87171 _87182 f g s)). Qed.
Lemma lem3348740 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term74 _87171 _87182 g s) = (term75 _87171 _87182 g s).
Proof. exact (fun_ext (fun f : type1413 _87171 _87182 => @lem3348553 _87171 _87182 f g s)). Qed.
Lemma lem3348741 {_87171 _87182 : Type'} : (@all (_87171 -> _87182 -> Prop)) = (@all (_87171 -> _87182 -> Prop)).
Proof. exact (eq_refl (@all (_87171 -> _87182 -> Prop))). Qed.
Lemma lem3348742 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term76 _87171 _87182 g s) = (term77 _87171 _87182 g s).
Proof. exact (MK_COMB (@lem3348741 _87171 _87182) (@lem3348740 _87171 _87182 g s)). Qed.
Lemma lem3348747 {_87171 _87182 : Type'} (s : _87171 -> Prop) : (term78 _87171 _87182 s) = (term79 _87171 _87182 s).
Proof. exact (fun_ext (fun g : type1413 _87171 _87182 => @lem3348742 _87171 _87182 g s)). Qed.
Lemma lem3348748 {_87171 _87182 : Type'} : (@all (_87171 -> _87182 -> Prop)) = (@all (_87171 -> _87182 -> Prop)).
Proof. exact (eq_refl (@all (_87171 -> _87182 -> Prop))). Qed.
Lemma lem3348749 {_87171 _87182 : Type'} (s : _87171 -> Prop) : (term80 _87171 _87182 s) = (term81 _87171 _87182 s).
Proof. exact (MK_COMB (@lem3348748 _87171 _87182) (@lem3348747 _87171 _87182 s)). Qed.
Lemma lem3348754 {_87171 _87182 : Type'} : (term82 _87171 _87182) = (term83 _87171 _87182).
Proof. exact (fun_ext (fun s : _87171 -> Prop => @lem3348749 _87171 _87182 s)). Qed.
Lemma lem3348755 {_87171 : Type'} : (@all (_87171 -> Prop)) = (@all (_87171 -> Prop)).
Proof. exact (eq_refl (@all (_87171 -> Prop))). Qed.
Lemma lem3348764 {_87171 _87182 : Type'} : (term84 _87171 _87182) = (term85 _87171 _87182).
Proof. exact (MK_COMB (@lem3348755 _87171) (@lem3348754 _87171 _87182)). Qed.
Lemma lem3348765 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3348770 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term47 _87171 _87182 t g s x) = (term47 _87171 _87182 t g s x).
Proof. exact (eq_refl (term47 _87171 _87182 t g s x)). Qed.
Lemma lem3348771 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term49 _87171 _87182 t g s) = (term49 _87171 _87182 t g s).
Proof. exact (fun_ext (fun x : _87171 => @lem3348770 _87171 _87182 t g s x)). Qed.
Lemma lem3348772 {_87171 : Type'} : (@ex _87171) = (@ex _87171).
Proof. exact (eq_refl (@ex _87171)). Qed.
Lemma lem3348773 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term50 _87171 _87182 t g s) = (term50 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3348772 _87171) (@lem3348771 _87171 _87182 t g s)). Qed.
Lemma lem3348774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3348775 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term52 _87171 _87182 t g s) = (term52 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3348774) (@lem3348773 _87171 _87182 t g s)). Qed.
Lemma lem3348776 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term54 _87171 _87182 g s t x) = (term54 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3348775 _87171 _87182 t g s) (@lem3348765 _87182 t x)). Qed.
Lemma lem3348777 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term56 _87171 _87182 g s x) = (term56 _87171 _87182 g s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3348776 _87171 _87182 g s t x)). Qed.
Lemma lem3348778 {_87182 : Type'} : (@ex (_87182 -> Prop)) = (@ex (_87182 -> Prop)).
Proof. exact (eq_refl (@ex (_87182 -> Prop))). Qed.
Lemma lem3348779 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term57 _87171 _87182 g s x) = (term57 _87171 _87182 g s x).
Proof. exact (MK_COMB (@lem3348778 _87182) (@lem3348777 _87171 _87182 g s x)). Qed.
Lemma lem3348780 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3348785 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term47 _87171 _87182 t f s x) = (term47 _87171 _87182 t f s x).
Proof. exact (eq_refl (term47 _87171 _87182 t f s x)). Qed.
Lemma lem3348786 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term49 _87171 _87182 t f s) = (term49 _87171 _87182 t f s).
Proof. exact (fun_ext (fun x : _87171 => @lem3348785 _87171 _87182 t f s x)). Qed.
Lemma lem3348787 {_87171 : Type'} : (@ex _87171) = (@ex _87171).
Proof. exact (eq_refl (@ex _87171)). Qed.
Lemma lem3348788 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term50 _87171 _87182 t f s) = (term50 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3348787 _87171) (@lem3348786 _87171 _87182 t f s)). Qed.
Lemma lem3348789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3348790 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term52 _87171 _87182 t f s) = (term52 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3348789) (@lem3348788 _87171 _87182 t f s)). Qed.
Lemma lem3348791 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term54 _87171 _87182 f s t x) = (term54 _87171 _87182 f s t x).
Proof. exact (MK_COMB (@lem3348790 _87171 _87182 t f s) (@lem3348780 _87182 t x)). Qed.
Lemma lem3348792 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term56 _87171 _87182 f s x) = (term56 _87171 _87182 f s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3348791 _87171 _87182 f s t x)). Qed.
Lemma lem3348793 {_87182 : Type'} : (@ex (_87182 -> Prop)) = (@ex (_87182 -> Prop)).
Proof. exact (eq_refl (@ex (_87182 -> Prop))). Qed.
Lemma lem3348794 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term57 _87171 _87182 f s x) = (term57 _87171 _87182 f s x).
Proof. exact (MK_COMB (@lem3348793 _87182) (@lem3348792 _87171 _87182 f s x)). Qed.
Lemma lem3348795 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348796 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term59 _87171 _87182 f s x) = (term59 _87171 _87182 f s x).
Proof. exact (MK_COMB (@lem3348795) (@lem3348794 _87171 _87182 f s x)). Qed.
Lemma lem3348797 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term61 _87171 _87182 f g s x) = (term61 _87171 _87182 f g s x).
Proof. exact (MK_COMB (@lem3348796 _87171 _87182 f s x) (@lem3348779 _87171 _87182 g s x)). Qed.
Lemma lem3348798 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term63 _87171 _87182 f g s) = (term63 _87171 _87182 f g s).
Proof. exact (fun_ext (fun x : _87182 => @lem3348797 _87171 _87182 f g s x)). Qed.
Lemma lem3348799 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3348800 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term64 _87171 _87182 f g s) = (term64 _87171 _87182 f g s).
Proof. exact (MK_COMB (@lem3348799 _87182) (@lem3348798 _87171 _87182 f g s)). Qed.
Lemma lem3348805 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term29 _87171 _87182 f g x x') = (term29 _87171 _87182 f g x x').
Proof. exact (eq_refl (term29 _87171 _87182 f g x x')). Qed.
Lemma lem3348806 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term31 _87171 _87182 f g x) = (term31 _87171 _87182 f g x).
Proof. exact (fun_ext (fun x' : _87182 => @lem3348805 _87171 _87182 f g x x')). Qed.
Lemma lem3348807 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3348808 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term32 _87171 _87182 f g x) = (term32 _87171 _87182 f g x).
Proof. exact (MK_COMB (@lem3348807 _87182) (@lem3348806 _87171 _87182 f g x)). Qed.
Lemma lem3348811 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term24 _87171 s x) = (term24 _87171 s x).
Proof. exact (eq_refl (term24 _87171 s x)). Qed.
Lemma lem3348812 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term33 _87171 _87182 s f g x) = (term33 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3348811 _87171 s x) (@lem3348808 _87171 _87182 f g x)). Qed.
Lemma lem3348813 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term34 _87171 _87182 s f g) = (term34 _87171 _87182 s f g).
Proof. exact (fun_ext (fun x : _87171 => @lem3348812 _87171 _87182 s f g x)). Qed.
Lemma lem3348814 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3348815 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term35 _87171 _87182 s f g) = (term35 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3348814 _87171) (@lem3348813 _87171 _87182 s f g)). Qed.
Lemma lem3348816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3348817 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term36 _87171 _87182 s f g) = (term36 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3348816) (@lem3348815 _87171 _87182 s f g)). Qed.
Lemma lem3348818 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term65 _87171 _87182 f g s) = (term65 _87171 _87182 f g s).
Proof. exact (MK_COMB (@lem3348817 _87171 _87182 s f g) (@lem3348800 _87171 _87182 f g s)). Qed.
Lemma lem3348819 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term75 _87171 _87182 g s) = (term75 _87171 _87182 g s).
Proof. exact (fun_ext (fun f : type1413 _87171 _87182 => @lem3348818 _87171 _87182 f g s)). Qed.
Lemma lem3348820 {_87171 _87182 : Type'} : (@all (_87171 -> _87182 -> Prop)) = (@all (_87171 -> _87182 -> Prop)).
Proof. exact (eq_refl (@all (_87171 -> _87182 -> Prop))). Qed.
Lemma lem3348821 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term77 _87171 _87182 g s) = (term77 _87171 _87182 g s).
Proof. exact (MK_COMB (@lem3348820 _87171 _87182) (@lem3348819 _87171 _87182 g s)). Qed.
Lemma lem3348822 {_87171 _87182 : Type'} (s : _87171 -> Prop) : (term79 _87171 _87182 s) = (term79 _87171 _87182 s).
Proof. exact (fun_ext (fun g : type1413 _87171 _87182 => @lem3348821 _87171 _87182 g s)). Qed.
Lemma lem3348823 {_87171 _87182 : Type'} : (@all (_87171 -> _87182 -> Prop)) = (@all (_87171 -> _87182 -> Prop)).
Proof. exact (eq_refl (@all (_87171 -> _87182 -> Prop))). Qed.
Lemma lem3348824 {_87171 _87182 : Type'} (s : _87171 -> Prop) : (term81 _87171 _87182 s) = (term81 _87171 _87182 s).
Proof. exact (MK_COMB (@lem3348823 _87171 _87182) (@lem3348822 _87171 _87182 s)). Qed.
Lemma lem3348825 {_87171 _87182 : Type'} : (term83 _87171 _87182) = (term83 _87171 _87182).
Proof. exact (fun_ext (fun s : _87171 -> Prop => @lem3348824 _87171 _87182 s)). Qed.
Lemma lem3348826 {_87171 : Type'} : (@all (_87171 -> Prop)) = (@all (_87171 -> Prop)).
Proof. exact (eq_refl (@all (_87171 -> Prop))). Qed.
Lemma lem3348827 {_87171 _87182 : Type'} : (term85 _87171 _87182) = (term85 _87171 _87182).
Proof. exact (MK_COMB (@lem3348826 _87171) (@lem3348825 _87171 _87182)). Qed.
Lemma lem3348906 {_87171 _87182 : Type'} : (term84 _87171 _87182) = (term85 _87171 _87182).
Proof. exact (TRANS (@lem3348764 _87171 _87182) (@lem3348827 _87171 _87182)). Qed.
Lemma lem3348907 {_87171 _87182 : Type'} : (term85 _87171 _87182) = (term84 _87171 _87182).
Proof. exact (SYM (@lem3348906 _87171 _87182)). Qed.
Lemma lem3348908 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term35 _87171 _87182 s f g.
Proof. exact (h1). Qed.
Lemma lem3348909 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term57 _87171 _87182 f s x) : term57 _87171 _87182 f s x.
Proof. exact (h1). Qed.
Lemma lem3348911 (p : Prop) : p = (term66 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3348912 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term57 _87171 _87182 g s x) = (term86 _87171 _87182 g s x).
Proof. exact (@lem3348911 (term57 _87171 _87182 g s x)). Qed.
Lemma lem3348913 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term86 _87171 _87182 g s x) = (term57 _87171 _87182 g s x).
Proof. exact (SYM (@lem3348912 _87171 _87182 g s x)). Qed.
Lemma lem3348914 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term87 _87171 _87182 g s x.
Proof. exact (h1). Qed.
Lemma lem3348922 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term29 _87171 _87182 f g x x') = (term88 _87171 _87182 f g x x').
Proof. exact (@lem17265 (f x x') (g x x')). Qed.
Lemma lem3348923 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term31 _87171 _87182 f g x) = (term89 _87171 _87182 f g x).
Proof. exact (fun_ext (fun x' : _87182 => @lem3348922 _87171 _87182 f g x x')). Qed.
Lemma lem3348924 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3348925 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term32 _87171 _87182 f g x) = (term90 _87171 _87182 f g x).
Proof. exact (MK_COMB (@lem3348924 _87182) (@lem3348923 _87171 _87182 f g x)). Qed.
Lemma lem3348927 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term91 _87171 s x) = (term91 _87171 s x).
Proof. exact (eq_refl (term91 _87171 s x)). Qed.
Lemma lem3348928 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term92 _87171 _87182 s f g x) = (term93 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3348927 _87171 s x) (@lem3348925 _87171 _87182 f g x)). Qed.
Lemma lem3348929 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term33 _87171 _87182 s f g x) = (term92 _87171 _87182 s f g x).
Proof. exact (@lem17265 (s x) (term32 _87171 _87182 f g x)). Qed.
Lemma lem3348930 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term33 _87171 _87182 s f g x) = (term93 _87171 _87182 s f g x).
Proof. exact (TRANS (@lem3348929 _87171 _87182 s f g x) (@lem3348928 _87171 _87182 s f g x)). Qed.
Lemma lem3348931 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term34 _87171 _87182 s f g) = (term94 _87171 _87182 s f g).
Proof. exact (fun_ext (fun x : _87171 => @lem3348930 _87171 _87182 s f g x)). Qed.
Lemma lem3348932 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349033 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term35 _87171 _87182 s f g) = (term95 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3348932 _87171) (@lem3348931 _87171 _87182 s f g)). Qed.
Lemma lem3349034 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term95 _87171 _87182 s f g.
Proof. exact (EQ_MP (@lem3349033 _87171 _87182 s f g) (@lem3348908 _87171 _87182 s f g h1)). Qed.
Lemma lem3349039 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term47 _87171 _87182 t f s x) = (term47 _87171 _87182 t f s x).
Proof. exact (eq_refl (term47 _87171 _87182 t f s x)). Qed.
Lemma lem3349040 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term49 _87171 _87182 t f s) = (term49 _87171 _87182 t f s).
Proof. exact (fun_ext (fun x : _87171 => @lem3349039 _87171 _87182 t f s x)). Qed.
Lemma lem3349041 {_87171 : Type'} : (@ex _87171) = (@ex _87171).
Proof. exact (eq_refl (@ex _87171)). Qed.
Lemma lem3349042 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term50 _87171 _87182 t f s) = (term50 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3349041 _87171) (@lem3349040 _87171 _87182 t f s)). Qed.
Lemma lem3349043 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3349044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3349045 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term52 _87171 _87182 t f s) = (term52 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3349044) (@lem3349042 _87171 _87182 t f s)). Qed.
Lemma lem3349046 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term54 _87171 _87182 f s t x) = (term54 _87171 _87182 f s t x).
Proof. exact (MK_COMB (@lem3349045 _87171 _87182 t f s) (@lem3349043 _87182 t x)). Qed.
Lemma lem3349047 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term56 _87171 _87182 f s x) = (term56 _87171 _87182 f s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3349046 _87171 _87182 f s t x)). Qed.
Lemma lem3349048 {_87182 : Type'} : (@ex (_87182 -> Prop)) = (@ex (_87182 -> Prop)).
Proof. exact (eq_refl (@ex (_87182 -> Prop))). Qed.
Lemma lem3349049 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term57 _87171 _87182 f s x) = (term57 _87171 _87182 f s x).
Proof. exact (MK_COMB (@lem3349048 _87182) (@lem3349047 _87171 _87182 f s x)). Qed.
Lemma lem3349132 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3349133 {_87171 : Type'} (P : _87171 -> Prop) (Q : Prop) : (term96 _87171 P Q) = (term97 _87171 P Q).
Proof. exact (@lem3349132 _87171 P Q). Qed.
Lemma lem3349134 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term98 _87171 _87182 f s t x) = (term99 _87171 _87182 f s t x).
Proof. exact (@lem3349133 _87171 (term49 _87171 _87182 t f s) (t x)). Qed.
Lemma lem3349135 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term100 _87171 _87182 t f s x) = (term47 _87171 _87182 t f s x).
Proof. exact (eq_refl (term100 _87171 _87182 t f s x)). Qed.
Lemma lem3349136 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term101 _87171 _87182 t f s) = (term49 _87171 _87182 t f s).
Proof. exact (fun_ext (fun x : _87171 => @lem3349135 _87171 _87182 t f s x)). Qed.
Lemma lem3349137 {_87171 : Type'} : (@ex _87171) = (@ex _87171).
Proof. exact (eq_refl (@ex _87171)). Qed.
Lemma lem3349138 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term102 _87171 _87182 t f s) = (term50 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3349137 _87171) (@lem3349136 _87171 _87182 t f s)). Qed.
Lemma lem3349139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3349140 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) : (term103 _87171 _87182 t f s) = (term52 _87171 _87182 t f s).
Proof. exact (MK_COMB (@lem3349139) (@lem3349138 _87171 _87182 t f s)). Qed.
Lemma lem3349141 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3349142 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term98 _87171 _87182 f s t x) = (term54 _87171 _87182 f s t x).
Proof. exact (MK_COMB (@lem3349140 _87171 _87182 t f s) (@lem3349141 _87182 t x)). Qed.
Lemma lem3349143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3349144 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term104 _87171 _87182 f s t x) = (term105 _87171 _87182 f s t x).
Proof. exact (MK_COMB (@lem3349143) (@lem3349142 _87171 _87182 f s t x)). Qed.
Lemma lem3349145 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term100 _87171 _87182 t f s x) = (term47 _87171 _87182 t f s x).
Proof. exact (eq_refl (term100 _87171 _87182 t f s x)). Qed.
Lemma lem3349146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3349147 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term106 _87171 _87182 t f s x) = (term107 _87171 _87182 t f s x).
Proof. exact (MK_COMB (@lem3349146) (@lem3349145 _87171 _87182 t f s x)). Qed.
Lemma lem3349148 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3349149 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) (t : _87182 -> Prop) (x' : _87182) : (term108 _87171 _87182 f s x t x') = (term109 _87171 _87182 f s x t x').
Proof. exact (MK_COMB (@lem3349147 _87171 _87182 t f s x) (@lem3349148 _87182 t x')). Qed.
Lemma lem3349150 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term110 _87171 _87182 f s t x) = (term111 _87171 _87182 f s t x).
Proof. exact (fun_ext (fun x' : _87171 => @lem3349149 _87171 _87182 f s x' t x)). Qed.
Lemma lem3349151 {_87171 : Type'} : (@ex _87171) = (@ex _87171).
Proof. exact (eq_refl (@ex _87171)). Qed.
Lemma lem3349152 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term99 _87171 _87182 f s t x) = (term112 _87171 _87182 f s t x).
Proof. exact (MK_COMB (@lem3349151 _87171) (@lem3349150 _87171 _87182 f s t x)). Qed.
Lemma lem3349153 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : ((term98 _87171 _87182 f s t x) = (term99 _87171 _87182 f s t x)) = ((term54 _87171 _87182 f s t x) = (term112 _87171 _87182 f s t x)).
Proof. exact (MK_COMB (@lem3349144 _87171 _87182 f s t x) (@lem3349152 _87171 _87182 f s t x)). Qed.
Lemma lem3349154 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term54 _87171 _87182 f s t x) = (term112 _87171 _87182 f s t x).
Proof. exact (EQ_MP (@lem3349153 _87171 _87182 f s t x) (@lem3349134 _87171 _87182 f s t x)). Qed.
Lemma lem3349155 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term56 _87171 _87182 f s x) = (term113 _87171 _87182 f s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3349154 _87171 _87182 f s t x)). Qed.
Lemma lem3349156 {_87182 : Type'} : (@ex (_87182 -> Prop)) = (@ex (_87182 -> Prop)).
Proof. exact (eq_refl (@ex (_87182 -> Prop))). Qed.
Lemma lem3349158 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term57 _87171 _87182 f s x) = (term114 _87171 _87182 f s x).
Proof. exact (MK_COMB (@lem3349156 _87182) (@lem3349155 _87171 _87182 f s x)). Qed.
Lemma lem3349159 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term57 _87171 _87182 f s x) = (term114 _87171 _87182 f s x).
Proof. exact (TRANS (@lem3349049 _87171 _87182 f s x) (@lem3349158 _87171 _87182 f s x)). Qed.
Lemma lem3349160 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term57 _87171 _87182 f s x) : term114 _87171 _87182 f s x.
Proof. exact (EQ_MP (@lem3349159 _87171 _87182 f s x) (@lem3348909 _87171 _87182 f s x h1)). Qed.
Lemma lem3349167 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term115 _87171 _87182 t g s x) = (term116 _87171 _87182 t g s x).
Proof. exact (@lem17045 (t = (g x)) (s x)). Qed.
Lemma lem3349168 {_87171 : Type'} (P : _87171 -> Prop) : (term117 _87171 P) = (term118 _87171 P).
Proof. exact (@lem18394 _87171 P). Qed.
Lemma lem3349169 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term119 _87171 _87182 t g s) = (term120 _87171 _87182 t g s).
Proof. exact (@lem3349168 _87171 (term49 _87171 _87182 t g s)). Qed.
Lemma lem3349170 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term100 _87171 _87182 t g s x) = (term47 _87171 _87182 t g s x).
Proof. exact (eq_refl (term100 _87171 _87182 t g s x)). Qed.
Lemma lem3349171 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3349172 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term121 _87171 _87182 t g s x) = (term115 _87171 _87182 t g s x).
Proof. exact (MK_COMB (@lem3349171) (@lem3349170 _87171 _87182 t g s x)). Qed.
Lemma lem3349173 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term121 _87171 _87182 t g s x) = (term116 _87171 _87182 t g s x).
Proof. exact (TRANS (@lem3349172 _87171 _87182 t g s x) (@lem3349167 _87171 _87182 t g s x)). Qed.
Lemma lem3349174 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term122 _87171 _87182 t g s) = (term123 _87171 _87182 t g s).
Proof. exact (fun_ext (fun x : _87171 => @lem3349173 _87171 _87182 t g s x)). Qed.
Lemma lem3349175 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349176 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term120 _87171 _87182 t g s) = (term124 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3349175 _87171) (@lem3349174 _87171 _87182 t g s)). Qed.
Lemma lem3349177 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term119 _87171 _87182 t g s) = (term124 _87171 _87182 t g s).
Proof. exact (TRANS (@lem3349169 _87171 _87182 t g s) (@lem3349176 _87171 _87182 t g s)). Qed.
Lemma lem3349178 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (term125 _87182 t x) = (term125 _87182 t x).
Proof. exact (eq_refl (term125 _87182 t x)). Qed.
Lemma lem3349179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3349180 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term126 _87171 _87182 t g s) = (term127 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3349179) (@lem3349177 _87171 _87182 t g s)). Qed.
Lemma lem3349181 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term128 _87171 _87182 g s t x) = (term129 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3349180 _87171 _87182 t g s) (@lem3349178 _87182 t x)). Qed.
Lemma lem3349182 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term130 _87171 _87182 g s t x) = (term128 _87171 _87182 g s t x).
Proof. exact (@lem17045 (term50 _87171 _87182 t g s) (t x)). Qed.
Lemma lem3349183 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term130 _87171 _87182 g s t x) = (term129 _87171 _87182 g s t x).
Proof. exact (TRANS (@lem3349182 _87171 _87182 g s t x) (@lem3349181 _87171 _87182 g s t x)). Qed.
Lemma lem3349184 {_87182 : Type'} (P : type686 _87182) : (term131 _87182 P) = (term132 _87182 P).
Proof. exact (@lem18394 (_87182 -> Prop) P). Qed.
Lemma lem3349185 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term87 _87171 _87182 g s x) = (term133 _87171 _87182 g s x).
Proof. exact (@lem3349184 _87182 (term56 _87171 _87182 g s x)). Qed.
Lemma lem3349186 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term134 _87171 _87182 g s x t) = (term54 _87171 _87182 g s t x).
Proof. exact (eq_refl (term134 _87171 _87182 g s x t)). Qed.
Lemma lem3349187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3349188 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term135 _87171 _87182 g s x t) = (term130 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3349187) (@lem3349186 _87171 _87182 g s t x)). Qed.
Lemma lem3349189 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term135 _87171 _87182 g s x t) = (term129 _87171 _87182 g s t x).
Proof. exact (TRANS (@lem3349188 _87171 _87182 g s t x) (@lem3349183 _87171 _87182 g s t x)). Qed.
Lemma lem3349190 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term136 _87171 _87182 g s x) = (term137 _87171 _87182 g s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3349189 _87171 _87182 g s t x)). Qed.
Lemma lem3349191 {_87182 : Type'} : (@all (_87182 -> Prop)) = (@all (_87182 -> Prop)).
Proof. exact (eq_refl (@all (_87182 -> Prop))). Qed.
Lemma lem3349192 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term133 _87171 _87182 g s x) = (term138 _87171 _87182 g s x).
Proof. exact (MK_COMB (@lem3349191 _87182) (@lem3349190 _87171 _87182 g s x)). Qed.
Lemma lem3349293 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term87 _87171 _87182 g s x) = (term138 _87171 _87182 g s x).
Proof. exact (TRANS (@lem3349185 _87171 _87182 g s x) (@lem3349192 _87171 _87182 g s x)). Qed.
Lemma lem3349294 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term138 _87171 _87182 g s x.
Proof. exact (EQ_MP (@lem3349293 _87171 _87182 g s x) (@lem3348914 _87171 _87182 g s x h1)). Qed.
Lemma lem3349295 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) (h1 : term112 _87171 _87182 f s t x) : term112 _87171 _87182 f s t x.
Proof. exact (h1). Qed.
Lemma lem3349296 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term109 _87171 _87182 f s x' t x.
Proof. exact (h1). Qed.
Lemma lem3349303 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349304 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) : (f x) = (@I (_87171 -> _87182 -> Prop) f x).
Proof. exact (@lem3349303 _87171 (_87182 -> Prop) f x). Qed.
Lemma lem3349305 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x : _87171) : (g x) = (@I (_87171 -> _87182 -> Prop) g x).
Proof. exact (@lem3349304 _87171 _87182 g x). Qed.
Lemma lem3349306 {_87182 : Type'} (x : _87182) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3349307 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (g x x') = (@I (_87171 -> _87182 -> Prop) g x x').
Proof. exact (MK_COMB (@lem3349305 _87171 _87182 g x) (@lem3349306 _87182 x')). Qed.
Lemma lem3349309 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349310 {_87182 : Type'} (f : _87182 -> Prop) (x : _87182) : (f x) = (@I (_87182 -> Prop) f x).
Proof. exact (@lem3349309 _87182 Prop f x). Qed.
Lemma lem3349311 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (@I (_87171 -> _87182 -> Prop) g x x') = (term139 _87171 _87182 g x x').
Proof. exact (@lem3349310 _87182 (@I (_87171 -> _87182 -> Prop) g x) x'). Qed.
Lemma lem3349313 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (g x x') = (term139 _87171 _87182 g x x').
Proof. exact (TRANS (@lem3349307 _87171 _87182 g x x') (@lem3349311 _87171 _87182 g x x')). Qed.
Lemma lem3349314 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3349321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349322 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) : (f x) = (@I (_87171 -> _87182 -> Prop) f x).
Proof. exact (@lem3349321 _87171 (_87182 -> Prop) f x). Qed.
Lemma lem3349323 {_87182 : Type'} (x : _87182) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3349324 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (f x x') = (@I (_87171 -> _87182 -> Prop) f x x').
Proof. exact (MK_COMB (@lem3349322 _87171 _87182 f x) (@lem3349323 _87182 x')). Qed.
Lemma lem3349326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349327 {_87182 : Type'} (f : _87182 -> Prop) (x : _87182) : (f x) = (@I (_87182 -> Prop) f x).
Proof. exact (@lem3349326 _87182 Prop f x). Qed.
Lemma lem3349328 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (@I (_87171 -> _87182 -> Prop) f x x') = (term139 _87171 _87182 f x x').
Proof. exact (@lem3349327 _87182 (@I (_87171 -> _87182 -> Prop) f x) x'). Qed.
Lemma lem3349330 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (f x x') = (term139 _87171 _87182 f x x').
Proof. exact (TRANS (@lem3349324 _87171 _87182 f x x') (@lem3349328 _87171 _87182 f x x')). Qed.
Lemma lem3349331 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term140 _87171 _87182 f x x') = (term141 _87171 _87182 f x x').
Proof. exact (MK_COMB (@lem3349314) (@lem3349330 _87171 _87182 f x x')). Qed.
Lemma lem3349332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3349333 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term142 _87171 _87182 f x x') = (term143 _87171 _87182 f x x').
Proof. exact (MK_COMB (@lem3349332) (@lem3349331 _87171 _87182 f x x')). Qed.
Lemma lem3349334 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term88 _87171 _87182 f g x x') = (term144 _87171 _87182 f g x x').
Proof. exact (MK_COMB (@lem3349333 _87171 _87182 f x x') (@lem3349313 _87171 _87182 g x x')). Qed.
Lemma lem3349335 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term89 _87171 _87182 f g x) = (term145 _87171 _87182 f g x).
Proof. exact (fun_ext (fun x' : _87182 => @lem3349334 _87171 _87182 f g x x')). Qed.
Lemma lem3349336 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3349337 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term90 _87171 _87182 f g x) = (term146 _87171 _87182 f g x).
Proof. exact (MK_COMB (@lem3349336 _87182) (@lem3349335 _87171 _87182 f g x)). Qed.
Lemma lem3349338 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3349343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349344 {_87171 : Type'} (f : _87171 -> Prop) (x : _87171) : (f x) = (@I (_87171 -> Prop) f x).
Proof. exact (@lem3349343 _87171 Prop f x). Qed.
Lemma lem3349346 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (s x) = (@I (_87171 -> Prop) s x).
Proof. exact (@lem3349344 _87171 s x). Qed.
Lemma lem3349347 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term125 _87171 s x) = (term147 _87171 s x).
Proof. exact (MK_COMB (@lem3349338) (@lem3349346 _87171 s x)). Qed.
Lemma lem3349348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3349349 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term91 _87171 s x) = (term148 _87171 s x).
Proof. exact (MK_COMB (@lem3349348) (@lem3349347 _87171 s x)). Qed.
Lemma lem3349350 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term93 _87171 _87182 s f g x) = (term149 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3349349 _87171 s x) (@lem3349337 _87171 _87182 f g x)). Qed.
Lemma lem3349351 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term94 _87171 _87182 s f g) = (term150 _87171 _87182 s f g).
Proof. exact (fun_ext (fun x : _87171 => @lem3349350 _87171 _87182 s f g x)). Qed.
Lemma lem3349352 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349353 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term95 _87171 _87182 s f g) = (term151 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3349352 _87171) (@lem3349351 _87171 _87182 s f g)). Qed.
Lemma lem3349354 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term151 _87171 _87182 s f g.
Proof. exact (EQ_MP (@lem3349353 _87171 _87182 s f g) (@lem3349034 _87171 _87182 s f g h1)). Qed.
Lemma lem3349355 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3349360 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349361 {_87182 : Type'} (f : _87182 -> Prop) (x : _87182) : (f x) = (@I (_87182 -> Prop) f x).
Proof. exact (@lem3349360 _87182 Prop f x). Qed.
Lemma lem3349363 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (t x) = (@I (_87182 -> Prop) t x).
Proof. exact (@lem3349361 _87182 t x). Qed.
Lemma lem3349364 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (term125 _87182 t x) = (term147 _87182 t x).
Proof. exact (MK_COMB (@lem3349355) (@lem3349363 _87182 t x)). Qed.
Lemma lem3349365 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3349370 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349371 {_87171 : Type'} (f : _87171 -> Prop) (x : _87171) : (f x) = (@I (_87171 -> Prop) f x).
Proof. exact (@lem3349370 _87171 Prop f x). Qed.
Lemma lem3349373 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (s x) = (@I (_87171 -> Prop) s x).
Proof. exact (@lem3349371 _87171 s x). Qed.
Lemma lem3349374 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term125 _87171 s x) = (term147 _87171 s x).
Proof. exact (MK_COMB (@lem3349365) (@lem3349373 _87171 s x)). Qed.
Lemma lem3349375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3349382 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349383 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) : (f x) = (@I (_87171 -> _87182 -> Prop) f x).
Proof. exact (@lem3349382 _87171 (_87182 -> Prop) f x). Qed.
Lemma lem3349385 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x : _87171) : (g x) = (@I (_87171 -> _87182 -> Prop) g x).
Proof. exact (@lem3349383 _87171 _87182 g x). Qed.
Lemma lem3349386 {_87182 : Type'} (t : _87182 -> Prop) : (@eq (_87182 -> Prop) t) = (@eq (_87182 -> Prop) t).
Proof. exact (eq_refl (@eq (_87182 -> Prop) t)). Qed.
Lemma lem3349387 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (x : _87171) : (t = (g x)) = (t = (@I (_87171 -> _87182 -> Prop) g x)).
Proof. exact (MK_COMB (@lem3349386 _87182 t) (@lem3349385 _87171 _87182 g x)). Qed.
Lemma lem3349388 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (x : _87171) : (term152 _87171 _87182 t g x) = (term153 _87171 _87182 t g x).
Proof. exact (MK_COMB (@lem3349375) (@lem3349387 _87171 _87182 t g x)). Qed.
Lemma lem3349389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3349390 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (x : _87171) : (term154 _87171 _87182 t g x) = (term155 _87171 _87182 t g x).
Proof. exact (MK_COMB (@lem3349389) (@lem3349388 _87171 _87182 t g x)). Qed.
Lemma lem3349391 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term116 _87171 _87182 t g s x) = (term156 _87171 _87182 t g s x).
Proof. exact (MK_COMB (@lem3349390 _87171 _87182 t g x) (@lem3349374 _87171 s x)). Qed.
Lemma lem3349392 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term123 _87171 _87182 t g s) = (term157 _87171 _87182 t g s).
Proof. exact (fun_ext (fun x : _87171 => @lem3349391 _87171 _87182 t g s x)). Qed.
Lemma lem3349393 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349394 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term124 _87171 _87182 t g s) = (term158 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3349393 _87171) (@lem3349392 _87171 _87182 t g s)). Qed.
Lemma lem3349395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3349396 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term127 _87171 _87182 t g s) = (term159 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3349395) (@lem3349394 _87171 _87182 t g s)). Qed.
Lemma lem3349397 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term129 _87171 _87182 g s t x) = (term160 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3349396 _87171 _87182 t g s) (@lem3349364 _87182 t x)). Qed.
Lemma lem3349398 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term137 _87171 _87182 g s x) = (term161 _87171 _87182 g s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3349397 _87171 _87182 g s t x)). Qed.
Lemma lem3349399 {_87182 : Type'} : (@all (_87182 -> Prop)) = (@all (_87182 -> Prop)).
Proof. exact (eq_refl (@all (_87182 -> Prop))). Qed.
Lemma lem3349400 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term138 _87171 _87182 g s x) = (term162 _87171 _87182 g s x).
Proof. exact (MK_COMB (@lem3349399 _87182) (@lem3349398 _87171 _87182 g s x)). Qed.
Lemma lem3349401 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term162 _87171 _87182 g s x.
Proof. exact (EQ_MP (@lem3349400 _87171 _87182 g s x) (@lem3349294 _87171 _87182 g s x h1)). Qed.
Lemma lem3349406 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349407 {_87182 : Type'} (f : _87182 -> Prop) (x : _87182) : (f x) = (@I (_87182 -> Prop) f x).
Proof. exact (@lem3349406 _87182 Prop f x). Qed.
Lemma lem3349409 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (t x) = (@I (_87182 -> Prop) t x).
Proof. exact (@lem3349407 _87182 t x). Qed.
Lemma lem3349414 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349415 {_87171 : Type'} (f : _87171 -> Prop) (x : _87171) : (f x) = (@I (_87171 -> Prop) f x).
Proof. exact (@lem3349414 _87171 Prop f x). Qed.
Lemma lem3349417 {_87171 : Type'} (s : _87171 -> Prop) (x' : _87171) : (s x') = (@I (_87171 -> Prop) s x').
Proof. exact (@lem3349415 _87171 s x'). Qed.
Lemma lem3349424 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3349425 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x : _87171) : (f x) = (@I (_87171 -> _87182 -> Prop) f x).
Proof. exact (@lem3349424 _87171 (_87182 -> Prop) f x). Qed.
Lemma lem3349427 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x' : _87171) : (f x') = (@I (_87171 -> _87182 -> Prop) f x').
Proof. exact (@lem3349425 _87171 _87182 f x'). Qed.
Lemma lem3349428 {_87182 : Type'} (t : _87182 -> Prop) : (@eq (_87182 -> Prop) t) = (@eq (_87182 -> Prop) t).
Proof. exact (eq_refl (@eq (_87182 -> Prop) t)). Qed.
Lemma lem3349429 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (x' : _87171) : (t = (f x')) = (t = (@I (_87171 -> _87182 -> Prop) f x')).
Proof. exact (MK_COMB (@lem3349428 _87182 t) (@lem3349427 _87171 _87182 f x')). Qed.
Lemma lem3349430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3349431 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (x' : _87171) : (term45 _87171 _87182 t f x') = (term163 _87171 _87182 t f x').
Proof. exact (MK_COMB (@lem3349430) (@lem3349429 _87171 _87182 t f x')). Qed.
Lemma lem3349432 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) : (term47 _87171 _87182 t f s x') = (term164 _87171 _87182 t f s x').
Proof. exact (MK_COMB (@lem3349431 _87171 _87182 t f x') (@lem3349417 _87171 s x')). Qed.
Lemma lem3349433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3349434 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) : (term107 _87171 _87182 t f s x') = (term165 _87171 _87182 t f s x').
Proof. exact (MK_COMB (@lem3349433) (@lem3349432 _87171 _87182 t f s x')). Qed.
Lemma lem3349435 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) : (term109 _87171 _87182 f s x' t x) = (term166 _87171 _87182 f s x' t x).
Proof. exact (MK_COMB (@lem3349434 _87171 _87182 t f s x') (@lem3349409 _87182 t x)). Qed.
Lemma lem3349436 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term166 _87171 _87182 f s x' t x.
Proof. exact (EQ_MP (@lem3349435 _87171 _87182 f s x' t x) (@lem3349296 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349438 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term164 _87171 _87182 t f s x'.
Proof. exact (proj1 (@lem3349436 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349442 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3349443 {_87182 : Type'} (P : Prop) (Q : _87182 -> Prop) : (term167 _87182 P Q) = (term168 _87182 P Q).
Proof. exact (@lem3349442 _87182 P Q). Qed.
Lemma lem3349444 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term169 _87171 _87182 s f g x) = (term170 _87171 _87182 s f g x).
Proof. exact (@lem3349443 _87182 (term147 _87171 s x) (term145 _87171 _87182 f g x)). Qed.
Lemma lem3349445 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term171 _87171 _87182 f g x x') = (term144 _87171 _87182 f g x x').
Proof. exact (eq_refl (term171 _87171 _87182 f g x x')). Qed.
Lemma lem3349446 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term172 _87171 _87182 f g x) = (term145 _87171 _87182 f g x).
Proof. exact (fun_ext (fun x' : _87182 => @lem3349445 _87171 _87182 f g x x')). Qed.
Lemma lem3349447 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3349448 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term173 _87171 _87182 f g x) = (term146 _87171 _87182 f g x).
Proof. exact (MK_COMB (@lem3349447 _87182) (@lem3349446 _87171 _87182 f g x)). Qed.
Lemma lem3349449 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term148 _87171 s x) = (term148 _87171 s x).
Proof. exact (eq_refl (term148 _87171 s x)). Qed.
Lemma lem3349450 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term169 _87171 _87182 s f g x) = (term149 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3349449 _87171 s x) (@lem3349448 _87171 _87182 f g x)). Qed.
Lemma lem3349451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3349452 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term174 _87171 _87182 s f g x) = (term175 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3349451) (@lem3349450 _87171 _87182 s f g x)). Qed.
Lemma lem3349453 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term171 _87171 _87182 f g x x') = (term144 _87171 _87182 f g x x').
Proof. exact (eq_refl (term171 _87171 _87182 f g x x')). Qed.
Lemma lem3349454 {_87171 : Type'} (s : _87171 -> Prop) (x : _87171) : (term148 _87171 s x) = (term148 _87171 s x).
Proof. exact (eq_refl (term148 _87171 s x)). Qed.
Lemma lem3349455 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term176 _87171 _87182 s f g x x') = (term177 _87171 _87182 s f g x x').
Proof. exact (MK_COMB (@lem3349454 _87171 s x) (@lem3349453 _87171 _87182 f g x x')). Qed.
Lemma lem3349456 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term178 _87171 _87182 s f g x) = (term179 _87171 _87182 s f g x).
Proof. exact (fun_ext (fun x' : _87182 => @lem3349455 _87171 _87182 s f g x x')). Qed.
Lemma lem3349457 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3349458 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term170 _87171 _87182 s f g x) = (term180 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3349457 _87182) (@lem3349456 _87171 _87182 s f g x)). Qed.
Lemma lem3349459 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : ((term169 _87171 _87182 s f g x) = (term170 _87171 _87182 s f g x)) = ((term149 _87171 _87182 s f g x) = (term180 _87171 _87182 s f g x)).
Proof. exact (MK_COMB (@lem3349452 _87171 _87182 s f g x) (@lem3349458 _87171 _87182 s f g x)). Qed.
Lemma lem3349460 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term149 _87171 _87182 s f g x) = (term180 _87171 _87182 s f g x).
Proof. exact (EQ_MP (@lem3349459 _87171 _87182 s f g x) (@lem3349444 _87171 _87182 s f g x)). Qed.
Lemma lem3349461 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term150 _87171 _87182 s f g) = (term181 _87171 _87182 s f g).
Proof. exact (fun_ext (fun x : _87171 => @lem3349460 _87171 _87182 s f g x)). Qed.
Lemma lem3349462 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349463 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term151 _87171 _87182 s f g) = (term182 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3349462 _87171) (@lem3349461 _87171 _87182 s f g)). Qed.
Lemma lem3349476 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) (x' : _87182) : (term177 _87171 _87182 s f g x x') = (term177 _87171 _87182 s f g x x').
Proof. exact (eq_refl (term177 _87171 _87182 s f g x x')). Qed.
Lemma lem3349477 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term179 _87171 _87182 s f g x) = (term179 _87171 _87182 s f g x).
Proof. exact (fun_ext (fun x' : _87182 => @lem3349476 _87171 _87182 s f g x x')). Qed.
Lemma lem3349478 {_87182 : Type'} : (@all _87182) = (@all _87182).
Proof. exact (eq_refl (@all _87182)). Qed.
Lemma lem3349479 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (x : _87171) : (term180 _87171 _87182 s f g x) = (term180 _87171 _87182 s f g x).
Proof. exact (MK_COMB (@lem3349478 _87182) (@lem3349477 _87171 _87182 s f g x)). Qed.
Lemma lem3349480 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term181 _87171 _87182 s f g) = (term181 _87171 _87182 s f g).
Proof. exact (fun_ext (fun x : _87171 => @lem3349479 _87171 _87182 s f g x)). Qed.
Lemma lem3349481 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349482 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term182 _87171 _87182 s f g) = (term182 _87171 _87182 s f g).
Proof. exact (MK_COMB (@lem3349481 _87171) (@lem3349480 _87171 _87182 s f g)). Qed.
Lemma lem3349483 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) : (term151 _87171 _87182 s f g) = (term182 _87171 _87182 s f g).
Proof. exact (TRANS (@lem3349463 _87171 _87182 s f g) (@lem3349482 _87171 _87182 s f g)). Qed.
Lemma lem3349484 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term182 _87171 _87182 s f g.
Proof. exact (EQ_MP (@lem3349483 _87171 _87182 s f g) (@lem3349354 _87171 _87182 s f g h1)). Qed.
Lemma lem3349486 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3349487 {_87171 : Type'} (P : _87171 -> Prop) (Q : Prop) : (term183 _87171 P Q) = (term184 _87171 P Q).
Proof. exact (@lem3349486 _87171 P Q). Qed.
Lemma lem3349488 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term185 _87171 _87182 g s t x) = (term186 _87171 _87182 g s t x).
Proof. exact (@lem3349487 _87171 (term157 _87171 _87182 t g s) (term147 _87182 t x)). Qed.
Lemma lem3349489 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term187 _87171 _87182 t g s x) = (term156 _87171 _87182 t g s x).
Proof. exact (eq_refl (term187 _87171 _87182 t g s x)). Qed.
Lemma lem3349490 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term188 _87171 _87182 t g s) = (term157 _87171 _87182 t g s).
Proof. exact (fun_ext (fun x : _87171 => @lem3349489 _87171 _87182 t g s x)). Qed.
Lemma lem3349491 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349492 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term189 _87171 _87182 t g s) = (term158 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3349491 _87171) (@lem3349490 _87171 _87182 t g s)). Qed.
Lemma lem3349493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3349494 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term190 _87171 _87182 t g s) = (term159 _87171 _87182 t g s).
Proof. exact (MK_COMB (@lem3349493) (@lem3349492 _87171 _87182 t g s)). Qed.
Lemma lem3349495 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (term147 _87182 t x) = (term147 _87182 t x).
Proof. exact (eq_refl (term147 _87182 t x)). Qed.
Lemma lem3349496 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term185 _87171 _87182 g s t x) = (term160 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3349494 _87171 _87182 t g s) (@lem3349495 _87182 t x)). Qed.
Lemma lem3349497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3349498 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term191 _87171 _87182 g s t x) = (term192 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3349497) (@lem3349496 _87171 _87182 g s t x)). Qed.
Lemma lem3349499 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term187 _87171 _87182 t g s x) = (term156 _87171 _87182 t g s x).
Proof. exact (eq_refl (term187 _87171 _87182 t g s x)). Qed.
Lemma lem3349500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3349501 {_87171 _87182 : Type'} (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) : (term193 _87171 _87182 t g s x) = (term194 _87171 _87182 t g s x).
Proof. exact (MK_COMB (@lem3349500) (@lem3349499 _87171 _87182 t g s x)). Qed.
Lemma lem3349502 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (term147 _87182 t x) = (term147 _87182 t x).
Proof. exact (eq_refl (term147 _87182 t x)). Qed.
Lemma lem3349503 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) (t : _87182 -> Prop) (x' : _87182) : (term195 _87171 _87182 g s x t x') = (term196 _87171 _87182 g s x t x').
Proof. exact (MK_COMB (@lem3349501 _87171 _87182 t g s x) (@lem3349502 _87182 t x')). Qed.
Lemma lem3349504 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term197 _87171 _87182 g s t x) = (term198 _87171 _87182 g s t x).
Proof. exact (fun_ext (fun x' : _87171 => @lem3349503 _87171 _87182 g s x' t x)). Qed.
Lemma lem3349505 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349506 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term186 _87171 _87182 g s t x) = (term199 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3349505 _87171) (@lem3349504 _87171 _87182 g s t x)). Qed.
Lemma lem3349507 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : ((term185 _87171 _87182 g s t x) = (term186 _87171 _87182 g s t x)) = ((term160 _87171 _87182 g s t x) = (term199 _87171 _87182 g s t x)).
Proof. exact (MK_COMB (@lem3349498 _87171 _87182 g s t x) (@lem3349506 _87171 _87182 g s t x)). Qed.
Lemma lem3349508 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term160 _87171 _87182 g s t x) = (term199 _87171 _87182 g s t x).
Proof. exact (EQ_MP (@lem3349507 _87171 _87182 g s t x) (@lem3349488 _87171 _87182 g s t x)). Qed.
Lemma lem3349509 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term161 _87171 _87182 g s x) = (term200 _87171 _87182 g s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3349508 _87171 _87182 g s t x)). Qed.
Lemma lem3349510 {_87182 : Type'} : (@all (_87182 -> Prop)) = (@all (_87182 -> Prop)).
Proof. exact (eq_refl (@all (_87182 -> Prop))). Qed.
Lemma lem3349511 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term162 _87171 _87182 g s x) = (term201 _87171 _87182 g s x).
Proof. exact (MK_COMB (@lem3349510 _87182) (@lem3349509 _87171 _87182 g s x)). Qed.
Lemma lem3349524 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87171) (t : _87182 -> Prop) (x' : _87182) : (term196 _87171 _87182 g s x t x') = (term196 _87171 _87182 g s x t x').
Proof. exact (eq_refl (term196 _87171 _87182 g s x t x')). Qed.
Lemma lem3349525 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term198 _87171 _87182 g s t x) = (term198 _87171 _87182 g s t x).
Proof. exact (fun_ext (fun x' : _87171 => @lem3349524 _87171 _87182 g s x' t x)). Qed.
Lemma lem3349526 {_87171 : Type'} : (@all _87171) = (@all _87171).
Proof. exact (eq_refl (@all _87171)). Qed.
Lemma lem3349527 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (t : _87182 -> Prop) (x : _87182) : (term199 _87171 _87182 g s t x) = (term199 _87171 _87182 g s t x).
Proof. exact (MK_COMB (@lem3349526 _87171) (@lem3349525 _87171 _87182 g s t x)). Qed.
Lemma lem3349528 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term200 _87171 _87182 g s x) = (term200 _87171 _87182 g s x).
Proof. exact (fun_ext (fun t : _87182 -> Prop => @lem3349527 _87171 _87182 g s t x)). Qed.
Lemma lem3349529 {_87182 : Type'} : (@all (_87182 -> Prop)) = (@all (_87182 -> Prop)).
Proof. exact (eq_refl (@all (_87182 -> Prop))). Qed.
Lemma lem3349530 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term201 _87171 _87182 g s x) = (term201 _87171 _87182 g s x).
Proof. exact (MK_COMB (@lem3349529 _87182) (@lem3349528 _87171 _87182 g s x)). Qed.
Lemma lem3349531 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) : (term162 _87171 _87182 g s x) = (term201 _87171 _87182 g s x).
Proof. exact (TRANS (@lem3349511 _87171 _87182 g s x) (@lem3349530 _87171 _87182 g s x)). Qed.
Lemma lem3349532 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term201 _87171 _87182 g s x.
Proof. exact (EQ_MP (@lem3349531 _87171 _87182 g s x) (@lem3349401 _87171 _87182 g s x h1)). Qed.
Lemma lem3349545 {_87171 _87182 : Type'} (_34908 : _87171) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term202 _87171 _87182 s f g _34908.
Proof. exact (@lem3349484 _87171 _87182 s f g h1 _34908). Qed.
Lemma lem3349546 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (_34908 : _87171) : (term202 _87171 _87182 s f g _34908) = (term180 _87171 _87182 s f g _34908).
Proof. exact (eq_refl (term202 _87171 _87182 s f g _34908)). Qed.
Lemma lem3349547 {_87171 _87182 : Type'} (_34908 : _87171) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term180 _87171 _87182 s f g _34908.
Proof. exact (EQ_MP (@lem3349546 _87171 _87182 s f g _34908) (@lem3349545 _87171 _87182 _34908 s f g h1)). Qed.
Lemma lem3349548 {_87171 _87182 : Type'} (_34908 : _87171) (_34909 : _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term203 _87171 _87182 s f g _34908 _34909.
Proof. exact (@lem3349547 _87171 _87182 _34908 s f g h1 _34909). Qed.
Lemma lem3349549 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term203 _87171 _87182 s f g _34908 _34909) = (term177 _87171 _87182 s f g _34908 _34909).
Proof. exact (eq_refl (term203 _87171 _87182 s f g _34908 _34909)). Qed.
Lemma lem3349551 {_87171 _87182 : Type'} (_34910 : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term204 _87171 _87182 g s x _34910.
Proof. exact (@lem3349532 _87171 _87182 g s x h1 _34910). Qed.
Lemma lem3349552 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34910 : _87182 -> Prop) (x : _87182) : (term204 _87171 _87182 g s x _34910) = (term199 _87171 _87182 g s _34910 x).
Proof. exact (eq_refl (term204 _87171 _87182 g s x _34910)). Qed.
Lemma lem3349553 {_87171 _87182 : Type'} (_34910 : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term199 _87171 _87182 g s _34910 x.
Proof. exact (EQ_MP (@lem3349552 _87171 _87182 g s _34910 x) (@lem3349551 _87171 _87182 _34910 g s x h1)). Qed.
Lemma lem3349554 {_87171 _87182 : Type'} (_34910 : _87182 -> Prop) (_34911 : _87171) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term205 _87171 _87182 g s _34910 x _34911.
Proof. exact (@lem3349553 _87171 _87182 _34910 g s x h1 _34911). Qed.
Lemma lem3349555 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term205 _87171 _87182 g s _34910 x _34911) = (term196 _87171 _87182 g s _34911 _34910 x).
Proof. exact (eq_refl (term205 _87171 _87182 g s _34910 x _34911)). Qed.
Lemma lem3349556 {_87171 _87182 : Type'} (_34911 : _87171) (_34910 : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term196 _87171 _87182 g s _34911 _34910 x.
Proof. exact (EQ_MP (@lem3349555 _87171 _87182 g s _34911 _34910 x) (@lem3349554 _87171 _87182 _34910 _34911 g s x h1)). Qed.
Lemma lem3349577 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term196 _87171 _87182 g s _34911 _34910 x) = (term206 _87171 _87182 g s _34911 _34910 x).
Proof. exact (@lem3348282 (term153 _87171 _87182 _34910 g _34911) (term147 _87171 s _34911) (term147 _87182 _34910 x)). Qed.
Lemma lem3349580 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : @I (_87182 -> Prop) t x.
Proof. exact (proj2 (@lem3349436 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349582 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : t = (@I (_87171 -> _87182 -> Prop) f x').
Proof. exact (proj1 (@lem3349438 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349612 {_87171 _87182 : Type'} (_34908 : _87171) (_34909 : _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term177 _87171 _87182 s f g _34908 _34909.
Proof. exact (EQ_MP (@lem3349549 _87171 _87182 s f g _34908 _34909) (@lem3349548 _87171 _87182 _34908 _34909 s f g h1)). Qed.
Lemma lem3349626 {_87171 _87182 : Type'} (_34911 : _87171) (_34910 : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term206 _87171 _87182 g s _34911 _34910 x.
Proof. exact (EQ_MP (@lem3349577 _87171 _87182 g s _34911 _34910 x) (@lem3349556 _87171 _87182 _34911 _34910 g s x h1)). Qed.
Lemma lem3349627 {_87182 : Type'} (x : _87182) : (term207 _87182 x) = (term207 _87182 x).
Proof. exact (eq_refl (term207 _87182 x)). Qed.
Lemma lem3349628 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : (term208 _87182 x t) = (term209 _87171 _87182 x f x').
Proof. exact (MK_COMB (@lem3349627 _87182 x) (@lem3349582 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349629 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x' : _87171) (x : _87182) : (term209 _87171 _87182 x f x') = (term139 _87171 _87182 f x' x).
Proof. exact (eq_refl (term209 _87171 _87182 x f x')). Qed.
Lemma lem3349630 {_87182 : Type'} (x : _87182) (t : _87182 -> Prop) : (term210 _87182 x t) = (term210 _87182 x t).
Proof. exact (eq_refl (term210 _87182 x t)). Qed.
Lemma lem3349631 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (x' : _87171) (x : _87182) : ((term208 _87182 x t) = (term209 _87171 _87182 x f x')) = ((term208 _87182 x t) = (term139 _87171 _87182 f x' x)).
Proof. exact (MK_COMB (@lem3349630 _87182 x t) (@lem3349629 _87171 _87182 f x' x)). Qed.
Lemma lem3349632 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (term208 _87182 x t) = (@I (_87182 -> Prop) t x).
Proof. exact (eq_refl (term208 _87182 x t)). Qed.
Lemma lem3349633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3349634 {_87182 : Type'} (t : _87182 -> Prop) (x : _87182) : (term210 _87182 x t) = (term211 _87182 t x).
Proof. exact (MK_COMB (@lem3349633) (@lem3349632 _87182 t x)). Qed.
Lemma lem3349635 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x' : _87171) (x : _87182) : (term139 _87171 _87182 f x' x) = (term139 _87171 _87182 f x' x).
Proof. exact (eq_refl (term139 _87171 _87182 f x' x)). Qed.
Lemma lem3349636 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (x' : _87171) (x : _87182) : ((term208 _87182 x t) = (term139 _87171 _87182 f x' x)) = ((@I (_87182 -> Prop) t x) = (term139 _87171 _87182 f x' x)).
Proof. exact (MK_COMB (@lem3349634 _87182 t x) (@lem3349635 _87171 _87182 f x' x)). Qed.
Lemma lem3349637 {_87171 _87182 : Type'} (t : _87182 -> Prop) (f : type1413 _87171 _87182) (x' : _87171) (x : _87182) : ((term208 _87182 x t) = (term209 _87171 _87182 x f x')) = ((@I (_87182 -> Prop) t x) = (term139 _87171 _87182 f x' x)).
Proof. exact (TRANS (@lem3349631 _87171 _87182 t f x' x) (@lem3349636 _87171 _87182 t f x' x)). Qed.
Lemma lem3349638 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : (@I (_87182 -> Prop) t x) = (term139 _87171 _87182 f x' x).
Proof. exact (EQ_MP (@lem3349637 _87171 _87182 t f x' x) (@lem3349628 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349718 {_87182 : Type'} (x : _87182 -> Prop) : x = x.
Proof. exact (@lem21386 (_87182 -> Prop) x). Qed.
Lemma lem3349719 {_87182 : Type'} (x : _87182 -> Prop) : x = x.
Proof. exact (@lem3349718 _87182 x). Qed.
Lemma lem3349720 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x' : _87171) : (@I (_87171 -> _87182 -> Prop) g x') = (@I (_87171 -> _87182 -> Prop) g x').
Proof. exact (@lem3349719 _87182 (@I (_87171 -> _87182 -> Prop) g x')). Qed.
Lemma lem3349721 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x' : _87171) : term212 _87171 _87182 g x'.
Proof. exact (fun h0 : term213 _87171 _87182 g x' => @lem3349720 _87171 _87182 g x'). Qed.
Lemma lem3349723 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3349724 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x' : _87171) : (term212 _87171 _87182 g x') = ((@I (_87171 -> _87182 -> Prop) g x') = (@I (_87171 -> _87182 -> Prop) g x')).
Proof. exact (@lem3349723 ((@I (_87171 -> _87182 -> Prop) g x') = (@I (_87171 -> _87182 -> Prop) g x'))). Qed.
Lemma lem3349725 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x' : _87171) : (@I (_87171 -> _87182 -> Prop) g x') = (@I (_87171 -> _87182 -> Prop) g x').
Proof. exact (EQ_MP (@lem3349724 _87171 _87182 g x') (@lem3349721 _87171 _87182 g x')). Qed.
Lemma lem3349727 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : @I (_87171 -> Prop) s x'.
Proof. exact (proj2 (@lem3349438 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349728 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term215 _87171 s x'.
Proof. exact (fun h0 : term147 _87171 s x' => @lem3349727 _87171 _87182 f s x' t x h1). Qed.
Lemma lem3349730 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3349731 {_87171 : Type'} (s : _87171 -> Prop) (x' : _87171) : (term215 _87171 s x') = (@I (_87171 -> Prop) s x').
Proof. exact (@lem3349730 (@I (_87171 -> Prop) s x')). Qed.
Lemma lem3349732 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : @I (_87171 -> Prop) s x'.
Proof. exact (EQ_MP (@lem3349731 _87171 s x') (@lem3349728 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349734 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : @I (_87171 -> Prop) s x'.
Proof. exact (proj2 (@lem3349438 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349735 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term215 _87171 s x'.
Proof. exact (fun h0 : term147 _87171 s x' => @lem3349734 _87171 _87182 f s x' t x h1). Qed.
Lemma lem3349737 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3349738 {_87171 : Type'} (s : _87171 -> Prop) (x' : _87171) : (term215 _87171 s x') = (@I (_87171 -> Prop) s x').
Proof. exact (@lem3349737 (@I (_87171 -> Prop) s x')). Qed.
Lemma lem3349739 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : @I (_87171 -> Prop) s x'.
Proof. exact (EQ_MP (@lem3349738 _87171 s x') (@lem3349735 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349741 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term139 _87171 _87182 f x' x.
Proof. exact (EQ_MP (@lem3349638 _87171 _87182 f s x' t x h1) (@lem3349580 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349742 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term216 _87171 _87182 f x' x.
Proof. exact (fun h0 : term141 _87171 _87182 f x' x => @lem3349741 _87171 _87182 f s x' t x h1). Qed.
Lemma lem3349744 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3349745 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (x' : _87171) (x : _87182) : (term216 _87171 _87182 f x' x) = (term139 _87171 _87182 f x' x).
Proof. exact (@lem3349744 (term139 _87171 _87182 f x' x)). Qed.
Lemma lem3349746 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term139 _87171 _87182 f x' x.
Proof. exact (EQ_MP (@lem3349745 _87171 _87182 f x' x) (@lem3349742 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349762 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3349763 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term144 _87171 _87182 f g _34908 _34909) = (term217 _87171 _87182 g f _34908 _34909).
Proof. exact (@lem3349762 (term139 _87171 _87182 g _34908 _34909) (term141 _87171 _87182 f _34908 _34909)). Qed.
Lemma lem3349769 {_87171 : Type'} (s : _87171 -> Prop) (_34908 : _87171) : (term148 _87171 s _34908) = (term148 _87171 s _34908).
Proof. exact (eq_refl (term148 _87171 s _34908)). Qed.
Lemma lem3349770 {_87171 _87182 : Type'} (s : _87171 -> Prop) (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term177 _87171 _87182 s f g _34908 _34909) = (term218 _87171 _87182 s g f _34908 _34909).
Proof. exact (MK_COMB (@lem3349769 _87171 s _34908) (@lem3349763 _87171 _87182 g f _34908 _34909)). Qed.
Lemma lem3349774 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3349775 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term218 _87171 _87182 s g f _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909).
Proof. exact (@lem3349774 (term139 _87171 _87182 g _34908 _34909) (term147 _87171 s _34908) (term141 _87171 _87182 f _34908 _34909)). Qed.
Lemma lem3349791 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term177 _87171 _87182 s f g _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909).
Proof. exact (TRANS (@lem3349770 _87171 _87182 s g f _34908 _34909) (@lem3349775 _87171 _87182 g s f _34908 _34909)). Qed.
Lemma lem3349792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3349793 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term220 _87171 _87182 s f g _34908 _34909) = (term221 _87171 _87182 g s f _34908 _34909).
Proof. exact (MK_COMB (@lem3349792) (@lem3349791 _87171 _87182 g s f _34908 _34909)). Qed.
Lemma lem3349809 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term219 _87171 _87182 g s f _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909).
Proof. exact (eq_refl (term219 _87171 _87182 g s f _34908 _34909)). Qed.
Lemma lem3349810 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : ((term177 _87171 _87182 s f g _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909)) = ((term219 _87171 _87182 g s f _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909)).
Proof. exact (MK_COMB (@lem3349793 _87171 _87182 g s f _34908 _34909) (@lem3349809 _87171 _87182 g s f _34908 _34909)). Qed.
Lemma lem3349812 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3349813 (x : Prop) : (x = x) = True.
Proof. exact (@lem3349812 Prop x). Qed.
Lemma lem3349814 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : ((term219 _87171 _87182 g s f _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909)) = True.
Proof. exact (@lem3349813 (term219 _87171 _87182 g s f _34908 _34909)). Qed.
Lemma lem3349815 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : ((term177 _87171 _87182 s f g _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909)) = True.
Proof. exact (TRANS (@lem3349810 _87171 _87182 g s f _34908 _34909) (@lem3349814 _87171 _87182 g s f _34908 _34909)). Qed.
Lemma lem3349816 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : True = ((term177 _87171 _87182 s f g _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909)).
Proof. exact (SYM (@lem3349815 _87171 _87182 g s f _34908 _34909)). Qed.
Lemma lem3349817 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term177 _87171 _87182 s f g _34908 _34909) = (term219 _87171 _87182 g s f _34908 _34909).
Proof. exact (EQ_MP (@lem3349816 _87171 _87182 g s f _34908 _34909) (@lem0)). Qed.
Lemma lem3349818 {_87171 _87182 : Type'} (_34908 : _87171) (_34909 : _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term219 _87171 _87182 g s f _34908 _34909.
Proof. exact (EQ_MP (@lem3349817 _87171 _87182 g s f _34908 _34909) (@lem3349612 _87171 _87182 _34908 _34909 s f g h1)). Qed.
Lemma lem3349820 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3349821 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term219 _87171 _87182 g s f _34908 _34909) = (term223 _87171 _87182 s f g _34908 _34909).
Proof. exact (@lem3349820 (term224 _87171 _87182 s f _34908 _34909) (term139 _87171 _87182 g _34908 _34909)). Qed.
Lemma lem3349823 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3349824 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term227 _87171 _87182 s f _34908 _34909) = (term228 _87171 _87182 s f _34908 _34909).
Proof. exact (@lem3349823 (term147 _87171 s _34908) (term141 _87171 _87182 f _34908 _34909)). Qed.
Lemma lem3349826 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3349827 {_87171 : Type'} (s : _87171 -> Prop) (_34908 : _87171) : (term229 _87171 s _34908) = (@I (_87171 -> Prop) s _34908).
Proof. exact (@lem3349826 (@I (_87171 -> Prop) s _34908)). Qed.
Lemma lem3349828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3349829 {_87171 : Type'} (s : _87171 -> Prop) (_34908 : _87171) : (term230 _87171 s _34908) = (term231 _87171 s _34908).
Proof. exact (MK_COMB (@lem3349828) (@lem3349827 _87171 s _34908)). Qed.
Lemma lem3349831 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3349832 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term232 _87171 _87182 f _34908 _34909) = (term139 _87171 _87182 f _34908 _34909).
Proof. exact (@lem3349831 (term139 _87171 _87182 f _34908 _34909)). Qed.
Lemma lem3349833 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term228 _87171 _87182 s f _34908 _34909) = (term233 _87171 _87182 s f _34908 _34909).
Proof. exact (MK_COMB (@lem3349829 _87171 s _34908) (@lem3349832 _87171 _87182 f _34908 _34909)). Qed.
Lemma lem3349834 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term227 _87171 _87182 s f _34908 _34909) = (term233 _87171 _87182 s f _34908 _34909).
Proof. exact (TRANS (@lem3349824 _87171 _87182 s f _34908 _34909) (@lem3349833 _87171 _87182 s f _34908 _34909)). Qed.
Lemma lem3349835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3349836 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term234 _87171 _87182 s f _34908 _34909) = (term235 _87171 _87182 s f _34908 _34909).
Proof. exact (MK_COMB (@lem3349835) (@lem3349834 _87171 _87182 s f _34908 _34909)). Qed.
Lemma lem3349837 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term139 _87171 _87182 g _34908 _34909) = (term139 _87171 _87182 g _34908 _34909).
Proof. exact (eq_refl (term139 _87171 _87182 g _34908 _34909)). Qed.
Lemma lem3349838 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term223 _87171 _87182 s f g _34908 _34909) = (term236 _87171 _87182 s f g _34908 _34909).
Proof. exact (MK_COMB (@lem3349836 _87171 _87182 s f _34908 _34909) (@lem3349837 _87171 _87182 g _34908 _34909)). Qed.
Lemma lem3349839 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (_34908 : _87171) (_34909 : _87182) : (term219 _87171 _87182 g s f _34908 _34909) = (term236 _87171 _87182 s f g _34908 _34909).
Proof. exact (TRANS (@lem3349821 _87171 _87182 s f g _34908 _34909) (@lem3349838 _87171 _87182 s f g _34908 _34909)). Qed.
Lemma lem3349841 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term109 _87171 _87182 f s x' t x) : term233 _87171 _87182 s f x' x.
Proof. exact (conj (@lem3349739 _87171 _87182 f s x' t x h1) (@lem3349746 _87171 _87182 f s x' t x h1)). Qed.
Lemma lem3349843 {_87171 _87182 : Type'} (_34908 : _87171) (_34909 : _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term236 _87171 _87182 s f g _34908 _34909.
Proof. exact (EQ_MP (@lem3349839 _87171 _87182 s f g _34908 _34909) (@lem3349818 _87171 _87182 _34908 _34909 s f g h1)). Qed.
Lemma lem3349844 {_87171 _87182 : Type'} (_34908 : _87171) (_34909 : _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term236 _87171 _87182 s f g _34908 _34909.
Proof. exact (@lem3349843 _87171 _87182 _34908 _34909 s f g h1). Qed.
Lemma lem3349845 {_87171 _87182 : Type'} (x' : _87171) (x : _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term236 _87171 _87182 s f g x' x.
Proof. exact (@lem3349844 _87171 _87182 x' x s f g h1). Qed.
Lemma lem3349848 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term109 _87171 _87182 f s x' t x) : term139 _87171 _87182 g x' x.
Proof. exact (@lem3349845 _87171 _87182 x' x s f g h1 (@lem3349841 _87171 _87182 f s x' t x h2)). Qed.
Lemma lem3349849 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term109 _87171 _87182 f s x' t x) : term216 _87171 _87182 g x' x.
Proof. exact (fun h0 : term141 _87171 _87182 g x' x => @lem3349848 _87171 _87182 g f s x' t x h1 h2). Qed.
Lemma lem3349851 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3349852 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (x' : _87171) (x : _87182) : (term216 _87171 _87182 g x' x) = (term139 _87171 _87182 g x' x).
Proof. exact (@lem3349851 (term139 _87171 _87182 g x' x)). Qed.
Lemma lem3349853 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term109 _87171 _87182 f s x' t x) : term139 _87171 _87182 g x' x.
Proof. exact (EQ_MP (@lem3349852 _87171 _87182 g x' x) (@lem3349849 _87171 _87182 g f s x' t x h1 h2)). Qed.
Lemma lem3349855 (a : Prop) (b : Prop) : (term237 a b) = (term238 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3349856 {_87171 _87182 : Type'} (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term239 _87171 _87182 s _34911 _34910 x) = (term240 _87171 _87182 s _34911 _34910 x).
Proof. exact (@lem3349855 (@I (_87171 -> Prop) s _34911) (@I (_87182 -> Prop) _34910 x)). Qed.
Lemma lem3349857 {_87171 _87182 : Type'} (_34910 : _87182 -> Prop) (g : type1413 _87171 _87182) (_34911 : _87171) : (term155 _87171 _87182 _34910 g _34911) = (term155 _87171 _87182 _34910 g _34911).
Proof. exact (eq_refl (term155 _87171 _87182 _34910 g _34911)). Qed.
Lemma lem3349858 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term206 _87171 _87182 g s _34911 _34910 x) = (term241 _87171 _87182 g s _34911 _34910 x).
Proof. exact (MK_COMB (@lem3349857 _87171 _87182 _34910 g _34911) (@lem3349856 _87171 _87182 s _34911 _34910 x)). Qed.
Lemma lem3349860 (a : Prop) (b : Prop) : (term237 a b) = (term238 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3349861 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term241 _87171 _87182 g s _34911 _34910 x) = (term242 _87171 _87182 g s _34911 _34910 x).
Proof. exact (@lem3349860 (_34910 = (@I (_87171 -> _87182 -> Prop) g _34911)) (term243 _87171 _87182 s _34911 _34910 x)). Qed.
Lemma lem3349862 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term206 _87171 _87182 g s _34911 _34910 x) = (term242 _87171 _87182 g s _34911 _34910 x).
Proof. exact (TRANS (@lem3349858 _87171 _87182 g s _34911 _34910 x) (@lem3349861 _87171 _87182 g s _34911 _34910 x)). Qed.
Lemma lem3349864 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3349865 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term242 _87171 _87182 g s _34911 _34910 x) = (term244 _87171 _87182 g s _34911 _34910 x).
Proof. exact (@lem3349864 (term245 _87171 _87182 g s _34911 _34910 x)). Qed.
Lemma lem3349866 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (_34911 : _87171) (_34910 : _87182 -> Prop) (x : _87182) : (term206 _87171 _87182 g s _34911 _34910 x) = (term244 _87171 _87182 g s _34911 _34910 x).
Proof. exact (TRANS (@lem3349862 _87171 _87182 g s _34911 _34910 x) (@lem3349865 _87171 _87182 g s _34911 _34910 x)). Qed.
Lemma lem3349868 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term109 _87171 _87182 f s x' t x) : term233 _87171 _87182 s g x' x.
Proof. exact (conj (@lem3349732 _87171 _87182 f s x' t x h2) (@lem3349853 _87171 _87182 g f s x' t x h1 h2)). Qed.
Lemma lem3349869 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term109 _87171 _87182 f s x' t x) : term246 _87171 _87182 s g x' x.
Proof. exact (conj (@lem3349725 _87171 _87182 g x') (@lem3349868 _87171 _87182 g f s x' t x h1 h2)). Qed.
Lemma lem3349871 {_87171 _87182 : Type'} (_34911 : _87171) (_34910 : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term244 _87171 _87182 g s _34911 _34910 x.
Proof. exact (EQ_MP (@lem3349866 _87171 _87182 g s _34911 _34910 x) (@lem3349626 _87171 _87182 _34911 _34910 g s x h1)). Qed.
Lemma lem3349872 {_87171 _87182 : Type'} (_34911 : _87171) (_34910 : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term244 _87171 _87182 g s _34911 _34910 x.
Proof. exact (@lem3349871 _87171 _87182 _34911 _34910 g s x h1). Qed.
Lemma lem3349873 {_87171 _87182 : Type'} (x' : _87171) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term87 _87171 _87182 g s x) : term247 _87171 _87182 s g x' x.
Proof. exact (@lem3349872 _87171 _87182 x' (@I (_87171 -> _87182 -> Prop) g x') g s x h1). Qed.
Lemma lem3349876 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term87 _87171 _87182 g s x) (h3 : term109 _87171 _87182 f s x' t x) : False.
Proof. exact (@lem3349873 _87171 _87182 x' g s x h2 (@lem3349869 _87171 _87182 g f s x' t x h1 h3)). Qed.
Lemma lem3349877 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term87 _87171 _87182 g s x) (h3 : term109 _87171 _87182 f s x' t x) : term248.
Proof. exact (fun h0 : ~ False => @lem3349876 _87171 _87182 g f s x' t x h1 h2 h3). Qed.
Lemma lem3349879 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3349880 : term248 = False.
Proof. exact (@lem3349879 False). Qed.
Lemma lem3349882 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x' : _87171) (t : _87182 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term87 _87171 _87182 g s x) (h3 : term109 _87171 _87182 f s x' t x) : False.
Proof. exact (EQ_MP (@lem3349880) (@lem3349877 _87171 _87182 g f s x' t x h1 h2 h3)). Qed.
Lemma lem3349883 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (t : _87182 -> Prop) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term112 _87171 _87182 f s t x) (h3 : term87 _87171 _87182 g s x) : False.
Proof. exact (ex_elim (@lem3349295 _87171 _87182 f s t x h2) (fun x' : _87171 => fun h0 : term111 _87171 _87182 f s t x x' => @lem3349882 _87171 _87182 g f s x' t x h1 h3 h0)). Qed.
Lemma lem3349884 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term57 _87171 _87182 f s x) (h3 : term87 _87171 _87182 g s x) : False.
Proof. exact (ex_elim (@lem3349160 _87171 _87182 f s x h2) (fun t : _87182 -> Prop => fun h0 : term113 _87171 _87182 f s x t => @lem3349883 _87171 _87182 f t g s x h1 h0 h3)). Qed.
Lemma lem3349885 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term57 _87171 _87182 f s x) (h3 : term87 _87171 _87182 g s x) : (term87 _87171 _87182 g s x) = False.
Proof. exact (prop_ext (fun h4 : term87 _87171 _87182 g s x => @lem3349884 _87171 _87182 f g s x h1 h2 h3) (fun h4 : False => @lem3348914 _87171 _87182 g s x h3)). Qed.
Lemma lem3349886 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term57 _87171 _87182 f s x) (h3 : term87 _87171 _87182 g s x) : False.
Proof. exact (EQ_MP (@lem3349885 _87171 _87182 f g s x h1 h2 h3) (@lem3348914 _87171 _87182 g s x h3)). Qed.
Lemma lem3349887 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term57 _87171 _87182 f s x) : term86 _87171 _87182 g s x.
Proof. exact (fun h0 : term87 _87171 _87182 g s x => @lem3349886 _87171 _87182 f g s x h1 h2 h0). Qed.
Lemma lem3349888 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (f : type1413 _87171 _87182) (s : _87171 -> Prop) (x : _87182) (h1 : term35 _87171 _87182 s f g) (h2 : term57 _87171 _87182 f s x) : term57 _87171 _87182 g s x.
Proof. exact (EQ_MP (@lem3348913 _87171 _87182 g s x) (@lem3349887 _87171 _87182 g f s x h1 h2)). Qed.
Lemma lem3349889 {_87171 _87182 : Type'} (x : _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term61 _87171 _87182 f g s x.
Proof. exact (fun h0 : term57 _87171 _87182 f s x => @lem3349888 _87171 _87182 g f s x h1 h0). Qed.
Lemma lem3349894 {_87171 _87182 : Type'} (s : _87171 -> Prop) (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (h1 : term35 _87171 _87182 s f g) : term64 _87171 _87182 f g s.
Proof. exact (fun x : _87182 => @lem3349889 _87171 _87182 x s f g h1). Qed.
Lemma lem3349895 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term65 _87171 _87182 f g s.
Proof. exact (fun h0 : term35 _87171 _87182 s f g => @lem3349894 _87171 _87182 s f g h0). Qed.
Lemma lem3349900 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term77 _87171 _87182 g s.
Proof. exact (fun f : type1413 _87171 _87182 => @lem3349895 _87171 _87182 f g s). Qed.
Lemma lem3349905 {_87171 _87182 : Type'} (s : _87171 -> Prop) : term81 _87171 _87182 s.
Proof. exact (fun g : type1413 _87171 _87182 => @lem3349900 _87171 _87182 g s). Qed.
Lemma lem3349910 {_87171 _87182 : Type'} : term85 _87171 _87182.
Proof. exact (fun s : _87171 -> Prop => @lem3349905 _87171 _87182 s). Qed.
Lemma lem3349911 {_87171 _87182 : Type'} : term84 _87171 _87182.
Proof. exact (EQ_MP (@lem3348907 _87171 _87182) (@lem3349910 _87171 _87182)). Qed.
Lemma lem3349912 {_87171 _87182 : Type'} (s : _87171 -> Prop) : term249 _87171 _87182 s.
Proof. exact (@lem3349911 _87171 _87182 s). Qed.
Lemma lem3349913 {_87171 _87182 : Type'} (s : _87171 -> Prop) : (term249 _87171 _87182 s) = (term80 _87171 _87182 s).
Proof. exact (eq_refl (term249 _87171 _87182 s)). Qed.
Lemma lem3349914 {_87171 _87182 : Type'} (s : _87171 -> Prop) : term80 _87171 _87182 s.
Proof. exact (EQ_MP (@lem3349913 _87171 _87182 s) (@lem3349912 _87171 _87182 s)). Qed.
Lemma lem3349915 {_87171 _87182 : Type'} (s : _87171 -> Prop) (g : type1413 _87171 _87182) : term250 _87171 _87182 s g.
Proof. exact (@lem3349914 _87171 _87182 s g). Qed.
Lemma lem3349916 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term250 _87171 _87182 s g) = (term76 _87171 _87182 g s).
Proof. exact (eq_refl (term250 _87171 _87182 s g)). Qed.
Lemma lem3349917 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term76 _87171 _87182 g s.
Proof. exact (EQ_MP (@lem3349916 _87171 _87182 g s) (@lem3349915 _87171 _87182 s g)). Qed.
Lemma lem3349918 {_87171 _87182 : Type'} (g : type1413 _87171 _87182) (s : _87171 -> Prop) (f : type1413 _87171 _87182) : term251 _87171 _87182 g s f.
Proof. exact (@lem3349917 _87171 _87182 g s f). Qed.
Lemma lem3349919 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : (term251 _87171 _87182 g s f) = (term67 _87171 _87182 f g s).
Proof. exact (eq_refl (term251 _87171 _87182 g s f)). Qed.
Lemma lem3349920 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term67 _87171 _87182 f g s.
Proof. exact (EQ_MP (@lem3349919 _87171 _87182 f g s) (@lem3349918 _87171 _87182 g s f)). Qed.
Lemma lem3349922 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term67 _87171 _87182 f g s.
Proof. exact (@lem3348532 _87171 _87182 f g s (@lem3349920 _87171 _87182 f g s)). Qed.
Lemma lem3349923 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term68 _87171 _87182 f g s) : False.
Proof. exact (@lem3349922 _87171 _87182 f g s (@lem3348516 _87171 _87182 f g s h1)). Qed.
Lemma lem3349924 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term68 _87171 _87182 f g s) : (term68 _87171 _87182 f g s) = False.
Proof. exact (prop_ext (fun h2 : term68 _87171 _87182 f g s => @lem3349923 _87171 _87182 f g s h1) (fun h2 : False => @lem3348516 _87171 _87182 f g s h1)). Qed.
Lemma lem3349925 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) (h1 : term68 _87171 _87182 f g s) : False.
Proof. exact (EQ_MP (@lem3349924 _87171 _87182 f g s h1) (@lem3348516 _87171 _87182 f g s h1)). Qed.
Lemma lem3349926 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term67 _87171 _87182 f g s.
Proof. exact (fun h0 : term68 _87171 _87182 f g s => @lem3349925 _87171 _87182 f g s h0). Qed.
Lemma lem3349927 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term65 _87171 _87182 f g s.
Proof. exact (EQ_MP (@lem3348515 _87171 _87182 f g s) (@lem3349926 _87171 _87182 f g s)). Qed.
Lemma lem3349928 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term23 _87171 _87182 f g s.
Proof. exact (EQ_MP (@lem3348511 _87171 _87182 f g s) (@lem3349927 _87171 _87182 f g s)). Qed.
Lemma lem3349929 {_87171 _87182 : Type'} (f : type1413 _87171 _87182) (g : type1413 _87171 _87182) (s : _87171 -> Prop) : term22 _87171 _87182 f g s.
Proof. exact (EQ_MP (@lem3348327 _87171 _87182 f g s) (@lem3349928 _87171 _87182 f g s)). Qed.
