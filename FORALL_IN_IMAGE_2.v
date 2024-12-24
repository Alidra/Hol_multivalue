Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_IMAGE_2_term_abbrevs.
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
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Lemma lem3388255 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3388256 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3388257 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3388256 t1) (@lem3388255 t1)). Qed.
Lemma lem3388258 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3388257 t1 t2). Qed.
Lemma lem3388259 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3388260 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3388259 t1 t2) (@lem3388258 t1 t2)). Qed.
Lemma lem3388261 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3388260 t1 t2 t3). Qed.
Lemma lem3388262 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3388263 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3388262 t1 t2 t3) (@lem3388261 t1 t2 t3)). Qed.
Lemma lem3388264 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3388263 t1 t2 t3)). Qed.
Lemma lem3388334 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term7 A B y f s) = (term8 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3388335 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term9 _88066 _88069 y f s) = (term10 _88066 _88069 y f s).
Proof. exact (@lem3388334 _88069 _88066 y f s). Qed.
Lemma lem3388336 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term9 _88066 _88069 x f s) = (term10 _88066 _88069 x f s).
Proof. exact (@lem3388335 _88066 _88069 x f s). Qed.
Lemma lem3388346 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3388347 {_88069 : Type'} (P : _88069 -> Prop) (x : _88069) : (@IN _88069 x P) = (P x).
Proof. exact (@lem3388346 _88069 P x). Qed.
Lemma lem3388348 {_88069 : Type'} (s : _88069 -> Prop) (x : _88069) : (@IN _88069 x s) = (s x).
Proof. exact (@lem3388347 _88069 s x). Qed.
Lemma lem3388349 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (x' : _88069) : (term11 _88066 _88069 x f x') = (term11 _88066 _88069 x f x').
Proof. exact (eq_refl (term11 _88066 _88069 x f x')). Qed.
Lemma lem3388350 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term12 _88066 _88069 x f x' s) = (term13 _88066 _88069 x f s x').
Proof. exact (MK_COMB (@lem3388349 _88066 _88069 x f x') (@lem3388348 _88069 s x')). Qed.
Lemma lem3388353 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term14 _88066 _88069 x f s) = (term15 _88066 _88069 x f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3388350 _88066 _88069 x f s x')). Qed.
Lemma lem3388354 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388355 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term10 _88066 _88069 x f s) = (term16 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388354 _88069) (@lem3388353 _88066 _88069 x f s)). Qed.
Lemma lem3388360 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term9 _88066 _88069 x f s) = (term16 _88066 _88069 x f s).
Proof. exact (TRANS (@lem3388336 _88066 _88069 x f s) (@lem3388355 _88066 _88069 x f s)). Qed.
Lemma lem3388361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3388362 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term17 _88066 _88069 x f s) = (term18 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388361) (@lem3388360 _88066 _88069 x f s)). Qed.
Lemma lem3388364 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term7 A B y f s) = (term8 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3388365 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term9 _88066 _88069 y f s) = (term10 _88066 _88069 y f s).
Proof. exact (@lem3388364 _88069 _88066 y f s). Qed.
Lemma lem3388375 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3388376 {_88069 : Type'} (P : _88069 -> Prop) (x : _88069) : (@IN _88069 x P) = (P x).
Proof. exact (@lem3388375 _88069 P x). Qed.
Lemma lem3388377 {_88069 : Type'} (s : _88069 -> Prop) (x : _88069) : (@IN _88069 x s) = (s x).
Proof. exact (@lem3388376 _88069 s x). Qed.
Lemma lem3388378 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (x : _88069) : (term11 _88066 _88069 y f x) = (term11 _88066 _88069 y f x).
Proof. exact (eq_refl (term11 _88066 _88069 y f x)). Qed.
Lemma lem3388379 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term12 _88066 _88069 y f x s) = (term13 _88066 _88069 y f s x).
Proof. exact (MK_COMB (@lem3388378 _88066 _88069 y f x) (@lem3388377 _88069 s x)). Qed.
Lemma lem3388382 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term14 _88066 _88069 y f s) = (term15 _88066 _88069 y f s).
Proof. exact (fun_ext (fun x : _88069 => @lem3388379 _88066 _88069 y f s x)). Qed.
Lemma lem3388383 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388384 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term10 _88066 _88069 y f s) = (term16 _88066 _88069 y f s).
Proof. exact (MK_COMB (@lem3388383 _88069) (@lem3388382 _88066 _88069 y f s)). Qed.
Lemma lem3388389 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term9 _88066 _88069 y f s) = (term16 _88066 _88069 y f s).
Proof. exact (TRANS (@lem3388365 _88066 _88069 y f s) (@lem3388384 _88066 _88069 y f s)). Qed.
Lemma lem3388390 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term19 _88066 _88069 x y f s) = (term20 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388362 _88066 _88069 x f s) (@lem3388389 _88066 _88069 y f s)). Qed.
Lemma lem3388393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3388394 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term21 _88066 _88069 x y f s) = (term22 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388393) (@lem3388390 _88066 _88069 x y f s)). Qed.
Lemma lem3388395 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3388396 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term23 _88066 _88069 f s P x y) = (term24 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3388394 _88066 _88069 x y f s) (@lem3388395 _88066 P x y)). Qed.
Lemma lem3388399 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term25 _88066 _88069 f s P x) = (term26 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3388396 _88066 _88069 f s P x y)). Qed.
Lemma lem3388400 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3388401 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term27 _88066 _88069 f s P x) = (term28 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3388400 _88066) (@lem3388399 _88066 _88069 f s P x)). Qed.
Lemma lem3388406 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term29 _88066 _88069 f s P) = (term30 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3388401 _88066 _88069 f s P x)). Qed.
Lemma lem3388407 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3388408 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term31 _88066 _88069 f s P) = (term32 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388407 _88066) (@lem3388406 _88066 _88069 f s P)). Qed.
Lemma lem3388413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3388414 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term33 _88066 _88069 f s P) = (term34 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388413) (@lem3388408 _88066 _88069 f s P)). Qed.
Lemma lem3388428 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3388429 {_88069 : Type'} (P : _88069 -> Prop) (x : _88069) : (@IN _88069 x P) = (P x).
Proof. exact (@lem3388428 _88069 P x). Qed.
Lemma lem3388430 {_88069 : Type'} (s : _88069 -> Prop) (x : _88069) : (@IN _88069 x s) = (s x).
Proof. exact (@lem3388429 _88069 s x). Qed.
Lemma lem3388431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3388432 {_88069 : Type'} (s : _88069 -> Prop) (x : _88069) : (term35 _88069 x s) = (term36 _88069 s x).
Proof. exact (MK_COMB (@lem3388431) (@lem3388430 _88069 s x)). Qed.
Lemma lem3388434 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3388435 {_88069 : Type'} (P : _88069 -> Prop) (x : _88069) : (@IN _88069 x P) = (P x).
Proof. exact (@lem3388434 _88069 P x). Qed.
Lemma lem3388436 {_88069 : Type'} (s : _88069 -> Prop) (y : _88069) : (@IN _88069 y s) = (s y).
Proof. exact (@lem3388435 _88069 s y). Qed.
Lemma lem3388437 {_88069 : Type'} (x : _88069) (s : _88069 -> Prop) (y : _88069) : (term37 _88069 x y s) = (term38 _88069 x s y).
Proof. exact (MK_COMB (@lem3388432 _88069 s x) (@lem3388436 _88069 s y)). Qed.
Lemma lem3388440 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3388441 {_88069 : Type'} (x : _88069) (s : _88069 -> Prop) (y : _88069) : (term39 _88069 x y s) = (term40 _88069 x s y).
Proof. exact (MK_COMB (@lem3388440) (@lem3388437 _88069 x s y)). Qed.
Lemma lem3388442 {_88066 _88069 : Type'} (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term41 _88066 _88069 P x f y) = (term41 _88066 _88069 P x f y).
Proof. exact (eq_refl (term41 _88066 _88069 P x f y)). Qed.
Lemma lem3388443 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term42 _88066 _88069 s P x f y) = (term43 _88066 _88069 s P x f y).
Proof. exact (MK_COMB (@lem3388441 _88069 x s y) (@lem3388442 _88066 _88069 P x f y)). Qed.
Lemma lem3388446 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term44 _88066 _88069 s P x f) = (term45 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3388443 _88066 _88069 s P x f y)). Qed.
Lemma lem3388447 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388448 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term46 _88066 _88069 s P x f) = (term47 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3388447 _88069) (@lem3388446 _88066 _88069 s P x f)). Qed.
Lemma lem3388453 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term48 _88066 _88069 s P f) = (term49 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3388448 _88066 _88069 s P x f)). Qed.
Lemma lem3388454 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388455 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term50 _88066 _88069 s P f) = (term51 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388454 _88069) (@lem3388453 _88066 _88069 s P f)). Qed.
Lemma lem3388460 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term31 _88066 _88069 f s P) = (term50 _88066 _88069 s P f)) = ((term32 _88066 _88069 f s P) = (term51 _88066 _88069 s P f)).
Proof. exact (MK_COMB (@lem3388414 _88066 _88069 f s P) (@lem3388455 _88066 _88069 s P f)). Qed.
Lemma lem3388463 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) : (term52 _88066 _88069 P f) = (term53 _88066 _88069 P f).
Proof. exact (fun_ext (fun s : _88069 -> Prop => @lem3388460 _88066 _88069 s P f)). Qed.
Lemma lem3388464 {_88069 : Type'} : (@all (_88069 -> Prop)) = (@all (_88069 -> Prop)).
Proof. exact (eq_refl (@all (_88069 -> Prop))). Qed.
Lemma lem3388465 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) : (term54 _88066 _88069 P f) = (term55 _88066 _88069 P f).
Proof. exact (MK_COMB (@lem3388464 _88069) (@lem3388463 _88066 _88069 P f)). Qed.
Lemma lem3388470 {_88066 _88069 : Type'} (f : _88069 -> _88066) : (term56 _88066 _88069 f) = (term57 _88066 _88069 f).
Proof. exact (fun_ext (fun P : type1402 _88066 => @lem3388465 _88066 _88069 P f)). Qed.
Lemma lem3388471 {_88066 : Type'} : (@all (_88066 -> _88066 -> Prop)) = (@all (_88066 -> _88066 -> Prop)).
Proof. exact (eq_refl (@all (_88066 -> _88066 -> Prop))). Qed.
Lemma lem3388472 {_88066 _88069 : Type'} (f : _88069 -> _88066) : (term58 _88066 _88069 f) = (term59 _88066 _88069 f).
Proof. exact (MK_COMB (@lem3388471 _88066) (@lem3388470 _88066 _88069 f)). Qed.
Lemma lem3388477 {_88066 _88069 : Type'} : (term60 _88066 _88069) = (term61 _88066 _88069).
Proof. exact (fun_ext (fun f : _88069 -> _88066 => @lem3388472 _88066 _88069 f)). Qed.
Lemma lem3388478 {_88066 _88069 : Type'} : (@all (_88069 -> _88066)) = (@all (_88069 -> _88066)).
Proof. exact (eq_refl (@all (_88069 -> _88066))). Qed.
Lemma lem3388479 {_88066 _88069 : Type'} : (term62 _88066 _88069) = (term63 _88066 _88069).
Proof. exact (MK_COMB (@lem3388478 _88066 _88069) (@lem3388477 _88066 _88069)). Qed.
Lemma lem3388484 {_88066 _88069 : Type'} : (term63 _88066 _88069) = (term62 _88066 _88069).
Proof. exact (SYM (@lem3388479 _88066 _88069)). Qed.
Lemma lem3388486 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3388487 {_88066 _88069 : Type'} : (term63 _88066 _88069) = (term65 _88066 _88069).
Proof. exact (@lem3388486 (term63 _88066 _88069)). Qed.
Lemma lem3388488 {_88066 _88069 : Type'} : (term65 _88066 _88069) = (term63 _88066 _88069).
Proof. exact (SYM (@lem3388487 _88066 _88069)). Qed.
Lemma lem3388489 {_88066 _88069 : Type'} (h1 : term66 _88066 _88069) : term66 _88066 _88069.
Proof. exact (h1). Qed.
Lemma lem3388492 {_88066 _88069 : Type'} (h1 : term65 _88066 _88069) : term65 _88066 _88069.
Proof. exact (h1). Qed.
Lemma lem3388493 {_88066 _88069 : Type'} : term67 _88066 _88069.
Proof. exact (fun h0 : term65 _88066 _88069 => @lem3388492 _88066 _88069 h0). Qed.
Lemma lem3388494 {_88066 _88069 : Type'} (h1 : term67 _88066 _88069) : term67 _88066 _88069.
Proof. exact (h1). Qed.
Lemma lem3388495 {_88066 _88069 : Type'} (h1 : term65 _88066 _88069) : term65 _88066 _88069.
Proof. exact (h1). Qed.
Lemma lem3388496 {_88066 _88069 : Type'} (h1 : term65 _88066 _88069) (h2 : term67 _88066 _88069) : term65 _88066 _88069.
Proof. exact (@lem3388494 _88066 _88069 h2 (@lem3388495 _88066 _88069 h1)). Qed.
Lemma lem3388497 {_88066 _88069 : Type'} (h1 : term65 _88066 _88069) : term68 _88066 _88069.
Proof. exact (fun h0 : term67 _88066 _88069 => @lem3388496 _88066 _88069 h1 h0). Qed.
Lemma lem3388498 {_88066 _88069 : Type'} (h1 : term67 _88066 _88069) : term67 _88066 _88069.
Proof. exact (h1). Qed.
Lemma lem3388499 {_88066 _88069 : Type'} (h1 : term65 _88066 _88069) (h2 : term67 _88066 _88069) : term65 _88066 _88069.
Proof. exact (@lem3388497 _88066 _88069 h1 (@lem3388498 _88066 _88069 h2)). Qed.
Lemma lem3388500 {_88066 _88069 : Type'} (h1 : term67 _88066 _88069) : term67 _88066 _88069.
Proof. exact (fun h0 : term65 _88066 _88069 => @lem3388499 _88066 _88069 h0 h1). Qed.
Lemma lem3388501 {_88066 _88069 : Type'} : term69 _88066 _88069.
Proof. exact (fun h0 : term67 _88066 _88069 => @lem3388500 _88066 _88069 h0). Qed.
Lemma lem3388504 {_88066 _88069 : Type'} : term67 _88066 _88069.
Proof. exact (@lem3388501 _88066 _88069 (@lem3388493 _88066 _88069)). Qed.
Lemma lem3388505 {_88066 _88069 : Type'} : term67 _88066 _88069.
Proof. exact (@lem3388504 _88066 _88069). Qed.
Lemma lem3388507 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3388508 {_88066 _88069 : Type'} : (term65 _88066 _88069) = (term70 _88066 _88069).
Proof. exact (@lem3388507 (term66 _88066 _88069)). Qed.
Lemma lem3388510 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3388511 {_88066 _88069 : Type'} : (term70 _88066 _88069) = (term63 _88066 _88069).
Proof. exact (@lem3388510 (term63 _88066 _88069)). Qed.
Lemma lem3388620 {_88066 _88069 : Type'} : (term65 _88066 _88069) = (term63 _88066 _88069).
Proof. exact (TRANS (@lem3388508 _88066 _88069) (@lem3388511 _88066 _88069)). Qed.
Lemma lem3388629 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term43 _88066 _88069 s P x f y) = (term43 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term43 _88066 _88069 s P x f y)). Qed.
Lemma lem3388630 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term45 _88066 _88069 s P x f) = (term45 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3388629 _88066 _88069 s P x f y)). Qed.
Lemma lem3388631 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388632 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term47 _88066 _88069 s P x f) = (term47 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3388631 _88069) (@lem3388630 _88066 _88069 s P x f)). Qed.
Lemma lem3388633 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term49 _88066 _88069 s P f) = (term49 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3388632 _88066 _88069 s P x f)). Qed.
Lemma lem3388634 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388635 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term51 _88066 _88069 s P f) = (term51 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388634 _88069) (@lem3388633 _88066 _88069 s P f)). Qed.
Lemma lem3388636 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3388641 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term13 _88066 _88069 y f s x) = (term13 _88066 _88069 y f s x).
Proof. exact (eq_refl (term13 _88066 _88069 y f s x)). Qed.
Lemma lem3388642 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term15 _88066 _88069 y f s) = (term15 _88066 _88069 y f s).
Proof. exact (fun_ext (fun x : _88069 => @lem3388641 _88066 _88069 y f s x)). Qed.
Lemma lem3388643 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388644 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term16 _88066 _88069 y f s) = (term16 _88066 _88069 y f s).
Proof. exact (MK_COMB (@lem3388643 _88069) (@lem3388642 _88066 _88069 y f s)). Qed.
Lemma lem3388649 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term13 _88066 _88069 x f s x') = (term13 _88066 _88069 x f s x').
Proof. exact (eq_refl (term13 _88066 _88069 x f s x')). Qed.
Lemma lem3388650 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term15 _88066 _88069 x f s) = (term15 _88066 _88069 x f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3388649 _88066 _88069 x f s x')). Qed.
Lemma lem3388651 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388652 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term16 _88066 _88069 x f s) = (term16 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388651 _88069) (@lem3388650 _88066 _88069 x f s)). Qed.
Lemma lem3388653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3388654 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term18 _88066 _88069 x f s) = (term18 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388653) (@lem3388652 _88066 _88069 x f s)). Qed.
Lemma lem3388655 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term20 _88066 _88069 x y f s) = (term20 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388654 _88066 _88069 x f s) (@lem3388644 _88066 _88069 y f s)). Qed.
Lemma lem3388656 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3388657 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term22 _88066 _88069 x y f s) = (term22 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388656) (@lem3388655 _88066 _88069 x y f s)). Qed.
Lemma lem3388658 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term24 _88066 _88069 f s P x y) = (term24 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3388657 _88066 _88069 x y f s) (@lem3388636 _88066 P x y)). Qed.
Lemma lem3388659 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term26 _88066 _88069 f s P x) = (term26 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3388658 _88066 _88069 f s P x y)). Qed.
Lemma lem3388660 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3388661 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term28 _88066 _88069 f s P x) = (term28 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3388660 _88066) (@lem3388659 _88066 _88069 f s P x)). Qed.
Lemma lem3388662 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term30 _88066 _88069 f s P) = (term30 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3388661 _88066 _88069 f s P x)). Qed.
Lemma lem3388663 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3388664 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term32 _88066 _88069 f s P) = (term32 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388663 _88066) (@lem3388662 _88066 _88069 f s P)). Qed.
Lemma lem3388665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3388666 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term34 _88066 _88069 f s P) = (term34 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388665) (@lem3388664 _88066 _88069 f s P)). Qed.
Lemma lem3388667 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term32 _88066 _88069 f s P) = (term51 _88066 _88069 s P f)) = ((term32 _88066 _88069 f s P) = (term51 _88066 _88069 s P f)).
Proof. exact (MK_COMB (@lem3388666 _88066 _88069 f s P) (@lem3388635 _88066 _88069 s P f)). Qed.
Lemma lem3388668 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) : (term53 _88066 _88069 P f) = (term53 _88066 _88069 P f).
Proof. exact (fun_ext (fun s : _88069 -> Prop => @lem3388667 _88066 _88069 s P f)). Qed.
Lemma lem3388669 {_88069 : Type'} : (@all (_88069 -> Prop)) = (@all (_88069 -> Prop)).
Proof. exact (eq_refl (@all (_88069 -> Prop))). Qed.
Lemma lem3388670 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) : (term55 _88066 _88069 P f) = (term55 _88066 _88069 P f).
Proof. exact (MK_COMB (@lem3388669 _88069) (@lem3388668 _88066 _88069 P f)). Qed.
Lemma lem3388671 {_88066 _88069 : Type'} (f : _88069 -> _88066) : (term57 _88066 _88069 f) = (term57 _88066 _88069 f).
Proof. exact (fun_ext (fun P : type1402 _88066 => @lem3388670 _88066 _88069 P f)). Qed.
Lemma lem3388672 {_88066 : Type'} : (@all (_88066 -> _88066 -> Prop)) = (@all (_88066 -> _88066 -> Prop)).
Proof. exact (eq_refl (@all (_88066 -> _88066 -> Prop))). Qed.
Lemma lem3388673 {_88066 _88069 : Type'} (f : _88069 -> _88066) : (term59 _88066 _88069 f) = (term59 _88066 _88069 f).
Proof. exact (MK_COMB (@lem3388672 _88066) (@lem3388671 _88066 _88069 f)). Qed.
Lemma lem3388674 {_88066 _88069 : Type'} : (term61 _88066 _88069) = (term61 _88066 _88069).
Proof. exact (fun_ext (fun f : _88069 -> _88066 => @lem3388673 _88066 _88069 f)). Qed.
Lemma lem3388675 {_88066 _88069 : Type'} : (@all (_88069 -> _88066)) = (@all (_88069 -> _88066)).
Proof. exact (eq_refl (@all (_88069 -> _88066))). Qed.
Lemma lem3388676 {_88066 _88069 : Type'} : (term63 _88066 _88069) = (term63 _88066 _88069).
Proof. exact (MK_COMB (@lem3388675 _88066 _88069) (@lem3388674 _88066 _88069)). Qed.
Lemma lem3388745 {_88066 _88069 : Type'} : (term65 _88066 _88069) = (term63 _88066 _88069).
Proof. exact (TRANS (@lem3388620 _88066 _88069) (@lem3388676 _88066 _88069)). Qed.
Lemma lem3388746 {_88066 _88069 : Type'} : (term63 _88066 _88069) = (term65 _88066 _88069).
Proof. exact (SYM (@lem3388745 _88066 _88069)). Qed.
Lemma lem3388748 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3388749 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term32 _88066 _88069 f s P) = (term51 _88066 _88069 s P f)) = (term72 _88066 _88069 s P f).
Proof. exact (@lem3388748 ((term32 _88066 _88069 f s P) = (term51 _88066 _88069 s P f))). Qed.
Lemma lem3388750 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term72 _88066 _88069 s P f) = ((term32 _88066 _88069 f s P) = (term51 _88066 _88069 s P f)).
Proof. exact (SYM (@lem3388749 _88066 _88069 s P f)). Qed.
Lemma lem3388751 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term73 _88066 _88069 s P f) : term73 _88066 _88069 s P f.
Proof. exact (h1). Qed.
Lemma lem3388760 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term74 _88066 _88069 x f s x') = (term75 _88066 _88069 x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3388763 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term13 _88066 _88069 x f s x') = (term13 _88066 _88069 x f s x').
Proof. exact (eq_refl (term13 _88066 _88069 x f s x')). Qed.
Lemma lem3388764 {_88069 : Type'} (P : _88069 -> Prop) : (term76 _88069 P) = (term77 _88069 P).
Proof. exact (@lem18394 _88069 P). Qed.
Lemma lem3388765 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term78 _88066 _88069 x f s) = (term79 _88066 _88069 x f s).
Proof. exact (@lem3388764 _88069 (term15 _88066 _88069 x f s)). Qed.
Lemma lem3388766 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term80 _88066 _88069 x f s x') = (term13 _88066 _88069 x f s x').
Proof. exact (eq_refl (term80 _88066 _88069 x f s x')). Qed.
Lemma lem3388767 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3388768 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term81 _88066 _88069 x f s x') = (term74 _88066 _88069 x f s x').
Proof. exact (MK_COMB (@lem3388767) (@lem3388766 _88066 _88069 x f s x')). Qed.
Lemma lem3388769 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term81 _88066 _88069 x f s x') = (term75 _88066 _88069 x f s x').
Proof. exact (TRANS (@lem3388768 _88066 _88069 x f s x') (@lem3388760 _88066 _88069 x f s x')). Qed.
Lemma lem3388770 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term82 _88066 _88069 x f s) = (term83 _88066 _88069 x f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3388769 _88066 _88069 x f s x')). Qed.
Lemma lem3388771 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388772 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term79 _88066 _88069 x f s) = (term84 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388771 _88069) (@lem3388770 _88066 _88069 x f s)). Qed.
Lemma lem3388773 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term78 _88066 _88069 x f s) = (term84 _88066 _88069 x f s).
Proof. exact (TRANS (@lem3388765 _88066 _88069 x f s) (@lem3388772 _88066 _88069 x f s)). Qed.
Lemma lem3388774 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term15 _88066 _88069 x f s) = (term15 _88066 _88069 x f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3388763 _88066 _88069 x f s x')). Qed.
Lemma lem3388775 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388776 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term16 _88066 _88069 x f s) = (term16 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388775 _88069) (@lem3388774 _88066 _88069 x f s)). Qed.
Lemma lem3388785 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term74 _88066 _88069 y f s x) = (term75 _88066 _88069 y f s x).
Proof. exact (@lem17045 (y = (f x)) (s x)). Qed.
Lemma lem3388788 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term13 _88066 _88069 y f s x) = (term13 _88066 _88069 y f s x).
Proof. exact (eq_refl (term13 _88066 _88069 y f s x)). Qed.
Lemma lem3388789 {_88069 : Type'} (P : _88069 -> Prop) : (term76 _88069 P) = (term77 _88069 P).
Proof. exact (@lem18394 _88069 P). Qed.
Lemma lem3388790 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term78 _88066 _88069 y f s) = (term79 _88066 _88069 y f s).
Proof. exact (@lem3388789 _88069 (term15 _88066 _88069 y f s)). Qed.
Lemma lem3388791 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term80 _88066 _88069 y f s x) = (term13 _88066 _88069 y f s x).
Proof. exact (eq_refl (term80 _88066 _88069 y f s x)). Qed.
Lemma lem3388792 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3388793 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term81 _88066 _88069 y f s x) = (term74 _88066 _88069 y f s x).
Proof. exact (MK_COMB (@lem3388792) (@lem3388791 _88066 _88069 y f s x)). Qed.
Lemma lem3388794 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term81 _88066 _88069 y f s x) = (term75 _88066 _88069 y f s x).
Proof. exact (TRANS (@lem3388793 _88066 _88069 y f s x) (@lem3388785 _88066 _88069 y f s x)). Qed.
Lemma lem3388795 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term82 _88066 _88069 y f s) = (term83 _88066 _88069 y f s).
Proof. exact (fun_ext (fun x : _88069 => @lem3388794 _88066 _88069 y f s x)). Qed.
Lemma lem3388796 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388797 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term79 _88066 _88069 y f s) = (term84 _88066 _88069 y f s).
Proof. exact (MK_COMB (@lem3388796 _88069) (@lem3388795 _88066 _88069 y f s)). Qed.
Lemma lem3388798 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term78 _88066 _88069 y f s) = (term84 _88066 _88069 y f s).
Proof. exact (TRANS (@lem3388790 _88066 _88069 y f s) (@lem3388797 _88066 _88069 y f s)). Qed.
Lemma lem3388799 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term15 _88066 _88069 y f s) = (term15 _88066 _88069 y f s).
Proof. exact (fun_ext (fun x : _88069 => @lem3388788 _88066 _88069 y f s x)). Qed.
Lemma lem3388800 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388801 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term16 _88066 _88069 y f s) = (term16 _88066 _88069 y f s).
Proof. exact (MK_COMB (@lem3388800 _88069) (@lem3388799 _88066 _88069 y f s)). Qed.
Lemma lem3388802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3388803 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term85 _88066 _88069 x f s) = (term86 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388802) (@lem3388773 _88066 _88069 x f s)). Qed.
Lemma lem3388804 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term87 _88066 _88069 x y f s) = (term88 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388803 _88066 _88069 x f s) (@lem3388798 _88066 _88069 y f s)). Qed.
Lemma lem3388805 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term89 _88066 _88069 x y f s) = (term87 _88066 _88069 x y f s).
Proof. exact (@lem17045 (term16 _88066 _88069 x f s) (term16 _88066 _88069 y f s)). Qed.
Lemma lem3388806 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term89 _88066 _88069 x y f s) = (term88 _88066 _88069 x y f s).
Proof. exact (TRANS (@lem3388805 _88066 _88069 x y f s) (@lem3388804 _88066 _88069 x y f s)). Qed.
Lemma lem3388807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3388808 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term18 _88066 _88069 x f s) = (term18 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3388807) (@lem3388776 _88066 _88069 x f s)). Qed.
Lemma lem3388809 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term20 _88066 _88069 x y f s) = (term20 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388808 _88066 _88069 x f s) (@lem3388801 _88066 _88069 y f s)). Qed.
Lemma lem3388810 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (term90 _88066 P x y) = (term90 _88066 P x y).
Proof. exact (eq_refl (term90 _88066 P x y)). Qed.
Lemma lem3388811 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3388812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3388813 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term91 _88066 _88069 x y f s) = (term91 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388812) (@lem3388809 _88066 _88069 x y f s)). Qed.
Lemma lem3388814 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term92 _88066 _88069 f s P x y) = (term92 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3388813 _88066 _88069 x y f s) (@lem3388810 _88066 P x y)). Qed.
Lemma lem3388815 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term93 _88066 _88069 f s P x y) = (term92 _88066 _88069 f s P x y).
Proof. exact (@lem17362 (term20 _88066 _88069 x y f s) (P x y)). Qed.
Lemma lem3388816 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term93 _88066 _88069 f s P x y) = (term92 _88066 _88069 f s P x y).
Proof. exact (TRANS (@lem3388815 _88066 _88069 f s P x y) (@lem3388814 _88066 _88069 f s P x y)). Qed.
Lemma lem3388817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3388818 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term94 _88066 _88069 x y f s) = (term95 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3388817) (@lem3388806 _88066 _88069 x y f s)). Qed.
Lemma lem3388819 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term96 _88066 _88069 f s P x y) = (term97 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3388818 _88066 _88069 x y f s) (@lem3388811 _88066 P x y)). Qed.
Lemma lem3388820 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term24 _88066 _88069 f s P x y) = (term96 _88066 _88069 f s P x y).
Proof. exact (@lem17265 (term20 _88066 _88069 x y f s) (P x y)). Qed.
Lemma lem3388821 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term24 _88066 _88069 f s P x y) = (term97 _88066 _88069 f s P x y).
Proof. exact (TRANS (@lem3388820 _88066 _88069 f s P x y) (@lem3388819 _88066 _88069 f s P x y)). Qed.
Lemma lem3388822 {_88066 : Type'} (P : _88066 -> Prop) : (term98 _88066 P) = (term99 _88066 P).
Proof. exact (@lem18392 _88066 P). Qed.
Lemma lem3388823 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term100 _88066 _88069 f s P x) = (term101 _88066 _88069 f s P x).
Proof. exact (@lem3388822 _88066 (term26 _88066 _88069 f s P x)). Qed.
Lemma lem3388824 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term102 _88066 _88069 f s P x y) = (term24 _88066 _88069 f s P x y).
Proof. exact (eq_refl (term102 _88066 _88069 f s P x y)). Qed.
Lemma lem3388825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3388826 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term103 _88066 _88069 f s P x y) = (term93 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3388825) (@lem3388824 _88066 _88069 f s P x y)). Qed.
Lemma lem3388827 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term103 _88066 _88069 f s P x y) = (term92 _88066 _88069 f s P x y).
Proof. exact (TRANS (@lem3388826 _88066 _88069 f s P x y) (@lem3388816 _88066 _88069 f s P x y)). Qed.
Lemma lem3388828 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term104 _88066 _88069 f s P x) = (term105 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3388827 _88066 _88069 f s P x y)). Qed.
Lemma lem3388829 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3388830 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term101 _88066 _88069 f s P x) = (term106 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3388829 _88066) (@lem3388828 _88066 _88069 f s P x)). Qed.
Lemma lem3388831 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term100 _88066 _88069 f s P x) = (term106 _88066 _88069 f s P x).
Proof. exact (TRANS (@lem3388823 _88066 _88069 f s P x) (@lem3388830 _88066 _88069 f s P x)). Qed.
Lemma lem3388832 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term26 _88066 _88069 f s P x) = (term107 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3388821 _88066 _88069 f s P x y)). Qed.
Lemma lem3388833 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3388834 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term28 _88066 _88069 f s P x) = (term108 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3388833 _88066) (@lem3388832 _88066 _88069 f s P x)). Qed.
Lemma lem3388835 {_88066 : Type'} (P : _88066 -> Prop) : (term98 _88066 P) = (term99 _88066 P).
Proof. exact (@lem18392 _88066 P). Qed.
Lemma lem3388836 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term109 _88066 _88069 f s P) = (term110 _88066 _88069 f s P).
Proof. exact (@lem3388835 _88066 (term30 _88066 _88069 f s P)). Qed.
Lemma lem3388837 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term111 _88066 _88069 f s P x) = (term28 _88066 _88069 f s P x).
Proof. exact (eq_refl (term111 _88066 _88069 f s P x)). Qed.
Lemma lem3388838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3388839 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term112 _88066 _88069 f s P x) = (term100 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3388838) (@lem3388837 _88066 _88069 f s P x)). Qed.
Lemma lem3388840 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term112 _88066 _88069 f s P x) = (term106 _88066 _88069 f s P x).
Proof. exact (TRANS (@lem3388839 _88066 _88069 f s P x) (@lem3388831 _88066 _88069 f s P x)). Qed.
Lemma lem3388841 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term113 _88066 _88069 f s P) = (term114 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3388840 _88066 _88069 f s P x)). Qed.
Lemma lem3388842 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3388843 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term110 _88066 _88069 f s P) = (term115 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388842 _88066) (@lem3388841 _88066 _88069 f s P)). Qed.
Lemma lem3388844 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term109 _88066 _88069 f s P) = (term115 _88066 _88069 f s P).
Proof. exact (TRANS (@lem3388836 _88066 _88069 f s P) (@lem3388843 _88066 _88069 f s P)). Qed.
Lemma lem3388845 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term30 _88066 _88069 f s P) = (term116 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3388834 _88066 _88069 f s P x)). Qed.
Lemma lem3388846 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3388847 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term32 _88066 _88069 f s P) = (term117 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388846 _88066) (@lem3388845 _88066 _88069 f s P)). Qed.
Lemma lem3388856 {_88069 : Type'} (x : _88069) (s : _88069 -> Prop) (y : _88069) : (term118 _88069 x s y) = (term119 _88069 x s y).
Proof. exact (@lem17045 (s x) (s y)). Qed.
Lemma lem3388861 {_88066 _88069 : Type'} (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term41 _88066 _88069 P x f y) = (term41 _88066 _88069 P x f y).
Proof. exact (eq_refl (term41 _88066 _88069 P x f y)). Qed.
Lemma lem3388866 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term120 _88066 _88069 s P x f y) = (term121 _88066 _88069 s P x f y).
Proof. exact (@lem17362 (term38 _88069 x s y) (term41 _88066 _88069 P x f y)). Qed.
Lemma lem3388867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3388868 {_88069 : Type'} (x : _88069) (s : _88069 -> Prop) (y : _88069) : (term122 _88069 x s y) = (term123 _88069 x s y).
Proof. exact (MK_COMB (@lem3388867) (@lem3388856 _88069 x s y)). Qed.
Lemma lem3388869 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term124 _88066 _88069 s P x f y) = (term125 _88066 _88069 s P x f y).
Proof. exact (MK_COMB (@lem3388868 _88069 x s y) (@lem3388861 _88066 _88069 P x f y)). Qed.
Lemma lem3388870 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term43 _88066 _88069 s P x f y) = (term124 _88066 _88069 s P x f y).
Proof. exact (@lem17265 (term38 _88069 x s y) (term41 _88066 _88069 P x f y)). Qed.
Lemma lem3388871 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term43 _88066 _88069 s P x f y) = (term125 _88066 _88069 s P x f y).
Proof. exact (TRANS (@lem3388870 _88066 _88069 s P x f y) (@lem3388869 _88066 _88069 s P x f y)). Qed.
Lemma lem3388872 {_88069 : Type'} (P : _88069 -> Prop) : (term98 _88069 P) = (term99 _88069 P).
Proof. exact (@lem18392 _88069 P). Qed.
Lemma lem3388873 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term126 _88066 _88069 s P x f) = (term127 _88066 _88069 s P x f).
Proof. exact (@lem3388872 _88069 (term45 _88066 _88069 s P x f)). Qed.
Lemma lem3388874 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term128 _88066 _88069 s P x f y) = (term43 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term128 _88066 _88069 s P x f y)). Qed.
Lemma lem3388875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3388876 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term129 _88066 _88069 s P x f y) = (term120 _88066 _88069 s P x f y).
Proof. exact (MK_COMB (@lem3388875) (@lem3388874 _88066 _88069 s P x f y)). Qed.
Lemma lem3388877 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term129 _88066 _88069 s P x f y) = (term121 _88066 _88069 s P x f y).
Proof. exact (TRANS (@lem3388876 _88066 _88069 s P x f y) (@lem3388866 _88066 _88069 s P x f y)). Qed.
Lemma lem3388878 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term130 _88066 _88069 s P x f) = (term131 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3388877 _88066 _88069 s P x f y)). Qed.
Lemma lem3388879 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388880 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term127 _88066 _88069 s P x f) = (term132 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3388879 _88069) (@lem3388878 _88066 _88069 s P x f)). Qed.
Lemma lem3388881 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term126 _88066 _88069 s P x f) = (term132 _88066 _88069 s P x f).
Proof. exact (TRANS (@lem3388873 _88066 _88069 s P x f) (@lem3388880 _88066 _88069 s P x f)). Qed.
Lemma lem3388882 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term45 _88066 _88069 s P x f) = (term133 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3388871 _88066 _88069 s P x f y)). Qed.
Lemma lem3388883 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388884 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term47 _88066 _88069 s P x f) = (term134 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3388883 _88069) (@lem3388882 _88066 _88069 s P x f)). Qed.
Lemma lem3388885 {_88069 : Type'} (P : _88069 -> Prop) : (term98 _88069 P) = (term99 _88069 P).
Proof. exact (@lem18392 _88069 P). Qed.
Lemma lem3388886 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term135 _88066 _88069 s P f) = (term136 _88066 _88069 s P f).
Proof. exact (@lem3388885 _88069 (term49 _88066 _88069 s P f)). Qed.
Lemma lem3388887 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term137 _88066 _88069 s P f x) = (term47 _88066 _88069 s P x f).
Proof. exact (eq_refl (term137 _88066 _88069 s P f x)). Qed.
Lemma lem3388888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3388889 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term138 _88066 _88069 s P f x) = (term126 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3388888) (@lem3388887 _88066 _88069 s P x f)). Qed.
Lemma lem3388890 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term138 _88066 _88069 s P f x) = (term132 _88066 _88069 s P x f).
Proof. exact (TRANS (@lem3388889 _88066 _88069 s P x f) (@lem3388881 _88066 _88069 s P x f)). Qed.
Lemma lem3388891 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term139 _88066 _88069 s P f) = (term140 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3388890 _88066 _88069 s P x f)). Qed.
Lemma lem3388892 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3388893 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term136 _88066 _88069 s P f) = (term141 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388892 _88069) (@lem3388891 _88066 _88069 s P f)). Qed.
Lemma lem3388894 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term135 _88066 _88069 s P f) = (term141 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3388886 _88066 _88069 s P f) (@lem3388893 _88066 _88069 s P f)). Qed.
Lemma lem3388895 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term49 _88066 _88069 s P f) = (term142 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3388884 _88066 _88069 s P x f)). Qed.
Lemma lem3388896 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3388897 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term51 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388896 _88069) (@lem3388895 _88066 _88069 s P f)). Qed.
Lemma lem3388898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3388899 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term144 _88066 _88069 f s P) = (term145 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388898) (@lem3388844 _88066 _88069 f s P)). Qed.
Lemma lem3388900 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term146 _88066 _88069 s P f) = (term147 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388899 _88066 _88069 f s P) (@lem3388897 _88066 _88069 s P f)). Qed.
Lemma lem3388901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3388902 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term148 _88066 _88069 f s P) = (term149 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3388901) (@lem3388847 _88066 _88069 f s P)). Qed.
Lemma lem3388903 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term150 _88066 _88069 s P f) = (term151 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388902 _88066 _88069 f s P) (@lem3388894 _88066 _88069 s P f)). Qed.
Lemma lem3388904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3388905 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term152 _88066 _88069 s P f) = (term153 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388904) (@lem3388903 _88066 _88069 s P f)). Qed.
Lemma lem3388906 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term154 _88066 _88069 s P f) = (term155 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3388905 _88066 _88069 s P f) (@lem3388900 _88066 _88069 s P f)). Qed.
Lemma lem3388907 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term73 _88066 _88069 s P f) = (term154 _88066 _88069 s P f).
Proof. exact (@lem17646 (term32 _88066 _88069 f s P) (term51 _88066 _88069 s P f)). Qed.
Lemma lem3388908 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term73 _88066 _88069 s P f) = (term155 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3388907 _88066 _88069 s P f) (@lem3388906 _88066 _88069 s P f)). Qed.
Lemma lem3389279 {A : Type'} (P : Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3389280 {_88069 : Type'} (P : Prop) (Q : _88069 -> Prop) : (term156 _88069 P Q) = (term157 _88069 P Q).
Proof. exact (@lem3389279 _88069 P Q). Qed.
Lemma lem3389281 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term158 _88066 _88069 s P f) = (term159 _88066 _88069 s P f).
Proof. exact (@lem3389280 _88069 (term117 _88066 _88069 f s P) (term140 _88066 _88069 s P f)). Qed.
Lemma lem3389282 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term160 _88066 _88069 s P f x) = (term132 _88066 _88069 s P x f).
Proof. exact (eq_refl (term160 _88066 _88069 s P f x)). Qed.
Lemma lem3389283 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term161 _88066 _88069 s P f) = (term140 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3389282 _88066 _88069 s P x f)). Qed.
Lemma lem3389284 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389285 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term162 _88066 _88069 s P f) = (term141 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389284 _88069) (@lem3389283 _88066 _88069 s P f)). Qed.
Lemma lem3389286 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term149 _88066 _88069 f s P) = (term149 _88066 _88069 f s P).
Proof. exact (eq_refl (term149 _88066 _88069 f s P)). Qed.
Lemma lem3389287 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term158 _88066 _88069 s P f) = (term151 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389286 _88066 _88069 f s P) (@lem3389285 _88066 _88069 s P f)). Qed.
Lemma lem3389288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389289 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term163 _88066 _88069 s P f) = (term164 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389288) (@lem3389287 _88066 _88069 s P f)). Qed.
Lemma lem3389290 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term160 _88066 _88069 s P f x) = (term132 _88066 _88069 s P x f).
Proof. exact (eq_refl (term160 _88066 _88069 s P f x)). Qed.
Lemma lem3389291 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term149 _88066 _88069 f s P) = (term149 _88066 _88069 f s P).
Proof. exact (eq_refl (term149 _88066 _88069 f s P)). Qed.
Lemma lem3389292 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term165 _88066 _88069 s P f x) = (term166 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389291 _88066 _88069 f s P) (@lem3389290 _88066 _88069 s P x f)). Qed.
Lemma lem3389293 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term167 _88066 _88069 s P f) = (term168 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3389292 _88066 _88069 s P x f)). Qed.
Lemma lem3389294 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389295 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term159 _88066 _88069 s P f) = (term169 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389294 _88069) (@lem3389293 _88066 _88069 s P f)). Qed.
Lemma lem3389296 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term158 _88066 _88069 s P f) = (term159 _88066 _88069 s P f)) = ((term151 _88066 _88069 s P f) = (term169 _88066 _88069 s P f)).
Proof. exact (MK_COMB (@lem3389289 _88066 _88069 s P f) (@lem3389295 _88066 _88069 s P f)). Qed.
Lemma lem3389297 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term151 _88066 _88069 s P f) = (term169 _88066 _88069 s P f).
Proof. exact (EQ_MP (@lem3389296 _88066 _88069 s P f) (@lem3389281 _88066 _88069 s P f)). Qed.
Lemma lem3389299 {A : Type'} (P : Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3389300 {_88069 : Type'} (P : Prop) (Q : _88069 -> Prop) : (term156 _88069 P Q) = (term157 _88069 P Q).
Proof. exact (@lem3389299 _88069 P Q). Qed.
Lemma lem3389301 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term170 _88066 _88069 s P x f) = (term171 _88066 _88069 s P x f).
Proof. exact (@lem3389300 _88069 (term117 _88066 _88069 f s P) (term131 _88066 _88069 s P x f)). Qed.
Lemma lem3389302 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term172 _88066 _88069 s P x f y) = (term121 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term172 _88066 _88069 s P x f y)). Qed.
Lemma lem3389303 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term173 _88066 _88069 s P x f) = (term131 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3389302 _88066 _88069 s P x f y)). Qed.
Lemma lem3389304 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389305 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term174 _88066 _88069 s P x f) = (term132 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389304 _88069) (@lem3389303 _88066 _88069 s P x f)). Qed.
Lemma lem3389306 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term149 _88066 _88069 f s P) = (term149 _88066 _88069 f s P).
Proof. exact (eq_refl (term149 _88066 _88069 f s P)). Qed.
Lemma lem3389307 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term170 _88066 _88069 s P x f) = (term166 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389306 _88066 _88069 f s P) (@lem3389305 _88066 _88069 s P x f)). Qed.
Lemma lem3389308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389309 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term175 _88066 _88069 s P x f) = (term176 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389308) (@lem3389307 _88066 _88069 s P x f)). Qed.
Lemma lem3389310 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term172 _88066 _88069 s P x f y) = (term121 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term172 _88066 _88069 s P x f y)). Qed.
Lemma lem3389311 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term149 _88066 _88069 f s P) = (term149 _88066 _88069 f s P).
Proof. exact (eq_refl (term149 _88066 _88069 f s P)). Qed.
Lemma lem3389312 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term177 _88066 _88069 s P x f y) = (term178 _88066 _88069 s P x f y).
Proof. exact (MK_COMB (@lem3389311 _88066 _88069 f s P) (@lem3389310 _88066 _88069 s P x f y)). Qed.
Lemma lem3389313 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term179 _88066 _88069 s P x f) = (term180 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3389312 _88066 _88069 s P x f y)). Qed.
Lemma lem3389314 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389315 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term171 _88066 _88069 s P x f) = (term181 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389314 _88069) (@lem3389313 _88066 _88069 s P x f)). Qed.
Lemma lem3389316 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : ((term170 _88066 _88069 s P x f) = (term171 _88066 _88069 s P x f)) = ((term166 _88066 _88069 s P x f) = (term181 _88066 _88069 s P x f)).
Proof. exact (MK_COMB (@lem3389309 _88066 _88069 s P x f) (@lem3389315 _88066 _88069 s P x f)). Qed.
Lemma lem3389317 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term166 _88066 _88069 s P x f) = (term181 _88066 _88069 s P x f).
Proof. exact (EQ_MP (@lem3389316 _88066 _88069 s P x f) (@lem3389301 _88066 _88069 s P x f)). Qed.
Lemma lem3389318 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term168 _88066 _88069 s P f) = (term182 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3389317 _88066 _88069 s P x f)). Qed.
Lemma lem3389319 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389320 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term169 _88066 _88069 s P f) = (term183 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389319 _88069) (@lem3389318 _88066 _88069 s P f)). Qed.
Lemma lem3389321 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term151 _88066 _88069 s P f) = (term183 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3389297 _88066 _88069 s P f) (@lem3389320 _88066 _88069 s P f)). Qed.
Lemma lem3389322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389323 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term153 _88066 _88069 s P f) = (term184 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389322) (@lem3389321 _88066 _88069 s P f)). Qed.
Lemma lem3389325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3389326 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term185 _88069 P Q) = (term186 _88069 P Q).
Proof. exact (@lem3389325 _88069 P Q). Qed.
Lemma lem3389327 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term187 _88066 _88069 x y f s) = (term188 _88066 _88069 x y f s).
Proof. exact (@lem3389326 _88069 (term15 _88066 _88069 x f s) (term16 _88066 _88069 y f s)). Qed.
Lemma lem3389328 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term80 _88066 _88069 x f s x') = (term13 _88066 _88069 x f s x').
Proof. exact (eq_refl (term80 _88066 _88069 x f s x')). Qed.
Lemma lem3389329 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term189 _88066 _88069 x f s) = (term15 _88066 _88069 x f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389328 _88066 _88069 x f s x')). Qed.
Lemma lem3389330 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389331 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term190 _88066 _88069 x f s) = (term16 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3389330 _88069) (@lem3389329 _88066 _88069 x f s)). Qed.
Lemma lem3389332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389333 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term191 _88066 _88069 x f s) = (term18 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3389332) (@lem3389331 _88066 _88069 x f s)). Qed.
Lemma lem3389334 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term16 _88066 _88069 y f s) = (term16 _88066 _88069 y f s).
Proof. exact (eq_refl (term16 _88066 _88069 y f s)). Qed.
Lemma lem3389335 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term187 _88066 _88069 x y f s) = (term20 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389333 _88066 _88069 x f s) (@lem3389334 _88066 _88069 y f s)). Qed.
Lemma lem3389336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389337 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term192 _88066 _88069 x y f s) = (term193 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389336) (@lem3389335 _88066 _88069 x y f s)). Qed.
Lemma lem3389338 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term80 _88066 _88069 x f s x') = (term13 _88066 _88069 x f s x').
Proof. exact (eq_refl (term80 _88066 _88069 x f s x')). Qed.
Lemma lem3389339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389340 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term194 _88066 _88069 x f s x') = (term195 _88066 _88069 x f s x').
Proof. exact (MK_COMB (@lem3389339) (@lem3389338 _88066 _88069 x f s x')). Qed.
Lemma lem3389341 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term16 _88066 _88069 y f s) = (term16 _88066 _88069 y f s).
Proof. exact (eq_refl (term16 _88066 _88069 y f s)). Qed.
Lemma lem3389342 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term196 _88066 _88069 x x' y f s) = (term197 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389340 _88066 _88069 x f s x') (@lem3389341 _88066 _88069 y f s)). Qed.
Lemma lem3389343 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term198 _88066 _88069 x y f s) = (term199 _88066 _88069 x y f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389342 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389344 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389345 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term188 _88066 _88069 x y f s) = (term200 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389344 _88069) (@lem3389343 _88066 _88069 x y f s)). Qed.
Lemma lem3389346 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : ((term187 _88066 _88069 x y f s) = (term188 _88066 _88069 x y f s)) = ((term20 _88066 _88069 x y f s) = (term200 _88066 _88069 x y f s)).
Proof. exact (MK_COMB (@lem3389337 _88066 _88069 x y f s) (@lem3389345 _88066 _88069 x y f s)). Qed.
Lemma lem3389347 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term20 _88066 _88069 x y f s) = (term200 _88066 _88069 x y f s).
Proof. exact (EQ_MP (@lem3389346 _88066 _88069 x y f s) (@lem3389327 _88066 _88069 x y f s)). Qed.
Lemma lem3389349 {A : Type'} (P : Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3389350 {_88069 : Type'} (P : Prop) (Q : _88069 -> Prop) : (term156 _88069 P Q) = (term157 _88069 P Q).
Proof. exact (@lem3389349 _88069 P Q). Qed.
Lemma lem3389351 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term201 _88066 _88069 x x' y f s) = (term202 _88066 _88069 x x' y f s).
Proof. exact (@lem3389350 _88069 (term13 _88066 _88069 x f s x') (term15 _88066 _88069 y f s)). Qed.
Lemma lem3389352 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term80 _88066 _88069 y f s x) = (term13 _88066 _88069 y f s x).
Proof. exact (eq_refl (term80 _88066 _88069 y f s x)). Qed.
Lemma lem3389353 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term189 _88066 _88069 y f s) = (term15 _88066 _88069 y f s).
Proof. exact (fun_ext (fun x : _88069 => @lem3389352 _88066 _88069 y f s x)). Qed.
Lemma lem3389354 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389355 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term190 _88066 _88069 y f s) = (term16 _88066 _88069 y f s).
Proof. exact (MK_COMB (@lem3389354 _88069) (@lem3389353 _88066 _88069 y f s)). Qed.
Lemma lem3389356 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term195 _88066 _88069 x f s x') = (term195 _88066 _88069 x f s x').
Proof. exact (eq_refl (term195 _88066 _88069 x f s x')). Qed.
Lemma lem3389357 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term201 _88066 _88069 x x' y f s) = (term197 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389356 _88066 _88069 x f s x') (@lem3389355 _88066 _88069 y f s)). Qed.
Lemma lem3389358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389359 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term203 _88066 _88069 x x' y f s) = (term204 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389358) (@lem3389357 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389360 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term80 _88066 _88069 y f s x') = (term13 _88066 _88069 y f s x').
Proof. exact (eq_refl (term80 _88066 _88069 y f s x')). Qed.
Lemma lem3389361 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term195 _88066 _88069 x f s x') = (term195 _88066 _88069 x f s x').
Proof. exact (eq_refl (term195 _88066 _88069 x f s x')). Qed.
Lemma lem3389362 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term205 _88066 _88069 x x' y f s x'') = (term206 _88066 _88069 x x' y f s x'').
Proof. exact (MK_COMB (@lem3389361 _88066 _88069 x f s x') (@lem3389360 _88066 _88069 y f s x'')). Qed.
Lemma lem3389363 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term207 _88066 _88069 x x' y f s) = (term208 _88066 _88069 x x' y f s).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389362 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389364 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389365 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term202 _88066 _88069 x x' y f s) = (term209 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389364 _88069) (@lem3389363 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389366 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : ((term201 _88066 _88069 x x' y f s) = (term202 _88066 _88069 x x' y f s)) = ((term197 _88066 _88069 x x' y f s) = (term209 _88066 _88069 x x' y f s)).
Proof. exact (MK_COMB (@lem3389359 _88066 _88069 x x' y f s) (@lem3389365 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389367 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term197 _88066 _88069 x x' y f s) = (term209 _88066 _88069 x x' y f s).
Proof. exact (EQ_MP (@lem3389366 _88066 _88069 x x' y f s) (@lem3389351 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389368 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term199 _88066 _88069 x y f s) = (term210 _88066 _88069 x y f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389367 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389369 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389370 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term200 _88066 _88069 x y f s) = (term211 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389369 _88069) (@lem3389368 _88066 _88069 x y f s)). Qed.
Lemma lem3389371 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term20 _88066 _88069 x y f s) = (term211 _88066 _88069 x y f s).
Proof. exact (TRANS (@lem3389347 _88066 _88069 x y f s) (@lem3389370 _88066 _88069 x y f s)). Qed.
Lemma lem3389372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389373 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term91 _88066 _88069 x y f s) = (term212 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389372) (@lem3389371 _88066 _88069 x y f s)). Qed.
Lemma lem3389374 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (term90 _88066 P x y) = (term90 _88066 P x y).
Proof. exact (eq_refl (term90 _88066 P x y)). Qed.
Lemma lem3389375 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term92 _88066 _88069 f s P x y) = (term213 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389373 _88066 _88069 x y f s) (@lem3389374 _88066 P x y)). Qed.
Lemma lem3389377 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3389378 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term185 _88069 P Q) = (term186 _88069 P Q).
Proof. exact (@lem3389377 _88069 P Q). Qed.
Lemma lem3389379 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term214 _88066 _88069 f s P x y) = (term215 _88066 _88069 f s P x y).
Proof. exact (@lem3389378 _88069 (term210 _88066 _88069 x y f s) (term90 _88066 P x y)). Qed.
Lemma lem3389380 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term216 _88066 _88069 x y f s x') = (term209 _88066 _88069 x x' y f s).
Proof. exact (eq_refl (term216 _88066 _88069 x y f s x')). Qed.
Lemma lem3389381 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term217 _88066 _88069 x y f s) = (term210 _88066 _88069 x y f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389380 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389382 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389383 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term218 _88066 _88069 x y f s) = (term211 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389382 _88069) (@lem3389381 _88066 _88069 x y f s)). Qed.
Lemma lem3389384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389385 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term219 _88066 _88069 x y f s) = (term212 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389384) (@lem3389383 _88066 _88069 x y f s)). Qed.
Lemma lem3389386 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (term90 _88066 P x y) = (term90 _88066 P x y).
Proof. exact (eq_refl (term90 _88066 P x y)). Qed.
Lemma lem3389387 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term214 _88066 _88069 f s P x y) = (term213 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389385 _88066 _88069 x y f s) (@lem3389386 _88066 P x y)). Qed.
Lemma lem3389388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389389 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term220 _88066 _88069 f s P x y) = (term221 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389388) (@lem3389387 _88066 _88069 f s P x y)). Qed.
Lemma lem3389390 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term216 _88066 _88069 x y f s x') = (term209 _88066 _88069 x x' y f s).
Proof. exact (eq_refl (term216 _88066 _88069 x y f s x')). Qed.
Lemma lem3389391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389392 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term222 _88066 _88069 x y f s x') = (term223 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389391) (@lem3389390 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389393 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (term90 _88066 P x y) = (term90 _88066 P x y).
Proof. exact (eq_refl (term90 _88066 P x y)). Qed.
Lemma lem3389394 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term224 _88066 _88069 f s x P x' y) = (term225 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389392 _88066 _88069 x' x y f s) (@lem3389393 _88066 P x' y)). Qed.
Lemma lem3389395 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term226 _88066 _88069 f s P x y) = (term227 _88066 _88069 f s P x y).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389394 _88066 _88069 x' f s P x y)). Qed.
Lemma lem3389396 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389397 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term215 _88066 _88069 f s P x y) = (term228 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389396 _88069) (@lem3389395 _88066 _88069 f s P x y)). Qed.
Lemma lem3389398 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : ((term214 _88066 _88069 f s P x y) = (term215 _88066 _88069 f s P x y)) = ((term213 _88066 _88069 f s P x y) = (term228 _88066 _88069 f s P x y)).
Proof. exact (MK_COMB (@lem3389389 _88066 _88069 f s P x y) (@lem3389397 _88066 _88069 f s P x y)). Qed.
Lemma lem3389399 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term213 _88066 _88069 f s P x y) = (term228 _88066 _88069 f s P x y).
Proof. exact (EQ_MP (@lem3389398 _88066 _88069 f s P x y) (@lem3389379 _88066 _88069 f s P x y)). Qed.
Lemma lem3389401 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3389402 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term185 _88069 P Q) = (term186 _88069 P Q).
Proof. exact (@lem3389401 _88069 P Q). Qed.
Lemma lem3389403 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term229 _88066 _88069 x f s P x' y) = (term230 _88066 _88069 x f s P x' y).
Proof. exact (@lem3389402 _88069 (term208 _88066 _88069 x' x y f s) (term90 _88066 P x' y)). Qed.
Lemma lem3389404 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term231 _88066 _88069 x x' y f s x'') = (term206 _88066 _88069 x x' y f s x'').
Proof. exact (eq_refl (term231 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389405 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term232 _88066 _88069 x x' y f s) = (term208 _88066 _88069 x x' y f s).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389404 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389406 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389407 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term233 _88066 _88069 x x' y f s) = (term209 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389406 _88069) (@lem3389405 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389409 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term234 _88066 _88069 x x' y f s) = (term223 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389408) (@lem3389407 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389410 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (term90 _88066 P x y) = (term90 _88066 P x y).
Proof. exact (eq_refl (term90 _88066 P x y)). Qed.
Lemma lem3389411 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term229 _88066 _88069 x f s P x' y) = (term225 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389409 _88066 _88069 x' x y f s) (@lem3389410 _88066 P x' y)). Qed.
Lemma lem3389412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389413 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term235 _88066 _88069 x f s P x' y) = (term236 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389412) (@lem3389411 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389414 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term231 _88066 _88069 x x' y f s x'') = (term206 _88066 _88069 x x' y f s x'').
Proof. exact (eq_refl (term231 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389416 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term237 _88066 _88069 x x' y f s x'') = (term238 _88066 _88069 x x' y f s x'').
Proof. exact (MK_COMB (@lem3389415) (@lem3389414 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389417 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (term90 _88066 P x y) = (term90 _88066 P x y).
Proof. exact (eq_refl (term90 _88066 P x y)). Qed.
Lemma lem3389418 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) (P : type1402 _88066) (x'' : _88066) (y : _88066) : (term239 _88066 _88069 x f s x' P x'' y) = (term240 _88066 _88069 x f s x' P x'' y).
Proof. exact (MK_COMB (@lem3389416 _88066 _88069 x'' x y f s x') (@lem3389417 _88066 P x'' y)). Qed.
Lemma lem3389419 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term241 _88066 _88069 x f s P x' y) = (term242 _88066 _88069 x f s P x' y).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389418 _88066 _88069 x f s x'' P x' y)). Qed.
Lemma lem3389420 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389421 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term230 _88066 _88069 x f s P x' y) = (term243 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389420 _88069) (@lem3389419 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389422 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : ((term229 _88066 _88069 x f s P x' y) = (term230 _88066 _88069 x f s P x' y)) = ((term225 _88066 _88069 x f s P x' y) = (term243 _88066 _88069 x f s P x' y)).
Proof. exact (MK_COMB (@lem3389413 _88066 _88069 x f s P x' y) (@lem3389421 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389423 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term225 _88066 _88069 x f s P x' y) = (term243 _88066 _88069 x f s P x' y).
Proof. exact (EQ_MP (@lem3389422 _88066 _88069 x f s P x' y) (@lem3389403 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389424 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term227 _88066 _88069 f s P x y) = (term244 _88066 _88069 f s P x y).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389423 _88066 _88069 x' f s P x y)). Qed.
Lemma lem3389425 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389426 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term228 _88066 _88069 f s P x y) = (term245 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389425 _88069) (@lem3389424 _88066 _88069 f s P x y)). Qed.
Lemma lem3389427 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term213 _88066 _88069 f s P x y) = (term245 _88066 _88069 f s P x y).
Proof. exact (TRANS (@lem3389399 _88066 _88069 f s P x y) (@lem3389426 _88066 _88069 f s P x y)). Qed.
Lemma lem3389428 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term92 _88066 _88069 f s P x y) = (term245 _88066 _88069 f s P x y).
Proof. exact (TRANS (@lem3389375 _88066 _88069 f s P x y) (@lem3389427 _88066 _88069 f s P x y)). Qed.
Lemma lem3389429 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term105 _88066 _88069 f s P x) = (term246 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3389428 _88066 _88069 f s P x y)). Qed.
Lemma lem3389430 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389431 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term106 _88066 _88069 f s P x) = (term247 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3389430 _88066) (@lem3389429 _88066 _88069 f s P x)). Qed.
Lemma lem3389432 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term114 _88066 _88069 f s P) = (term248 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3389431 _88066 _88069 f s P x)). Qed.
Lemma lem3389433 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389434 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term115 _88066 _88069 f s P) = (term249 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3389433 _88066) (@lem3389432 _88066 _88069 f s P)). Qed.
Lemma lem3389435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389436 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term145 _88066 _88069 f s P) = (term250 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3389435) (@lem3389434 _88066 _88069 f s P)). Qed.
Lemma lem3389437 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389438 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term147 _88066 _88069 s P f) = (term251 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389436 _88066 _88069 f s P) (@lem3389437 _88066 _88069 s P f)). Qed.
Lemma lem3389440 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3389441 {_88066 : Type'} (P : _88066 -> Prop) (Q : Prop) : (term185 _88066 P Q) = (term186 _88066 P Q).
Proof. exact (@lem3389440 _88066 P Q). Qed.
Lemma lem3389442 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term252 _88066 _88069 s P f) = (term253 _88066 _88069 s P f).
Proof. exact (@lem3389441 _88066 (term248 _88066 _88069 f s P) (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389443 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term254 _88066 _88069 f s P x) = (term247 _88066 _88069 f s P x).
Proof. exact (eq_refl (term254 _88066 _88069 f s P x)). Qed.
Lemma lem3389444 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term255 _88066 _88069 f s P) = (term248 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3389443 _88066 _88069 f s P x)). Qed.
Lemma lem3389445 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389446 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term256 _88066 _88069 f s P) = (term249 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3389445 _88066) (@lem3389444 _88066 _88069 f s P)). Qed.
Lemma lem3389447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389448 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term257 _88066 _88069 f s P) = (term250 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3389447) (@lem3389446 _88066 _88069 f s P)). Qed.
Lemma lem3389449 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389450 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term252 _88066 _88069 s P f) = (term251 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389448 _88066 _88069 f s P) (@lem3389449 _88066 _88069 s P f)). Qed.
Lemma lem3389451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389452 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term258 _88066 _88069 s P f) = (term259 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389451) (@lem3389450 _88066 _88069 s P f)). Qed.
Lemma lem3389453 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term254 _88066 _88069 f s P x) = (term247 _88066 _88069 f s P x).
Proof. exact (eq_refl (term254 _88066 _88069 f s P x)). Qed.
Lemma lem3389454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389455 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term260 _88066 _88069 f s P x) = (term261 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3389454) (@lem3389453 _88066 _88069 f s P x)). Qed.
Lemma lem3389456 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389457 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term262 _88066 _88069 x s P f) = (term263 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389455 _88066 _88069 f s P x) (@lem3389456 _88066 _88069 s P f)). Qed.
Lemma lem3389458 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term264 _88066 _88069 s P f) = (term265 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88066 => @lem3389457 _88066 _88069 x s P f)). Qed.
Lemma lem3389459 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389460 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term253 _88066 _88069 s P f) = (term266 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389459 _88066) (@lem3389458 _88066 _88069 s P f)). Qed.
Lemma lem3389461 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term252 _88066 _88069 s P f) = (term253 _88066 _88069 s P f)) = ((term251 _88066 _88069 s P f) = (term266 _88066 _88069 s P f)).
Proof. exact (MK_COMB (@lem3389452 _88066 _88069 s P f) (@lem3389460 _88066 _88069 s P f)). Qed.
Lemma lem3389462 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term251 _88066 _88069 s P f) = (term266 _88066 _88069 s P f).
Proof. exact (EQ_MP (@lem3389461 _88066 _88069 s P f) (@lem3389442 _88066 _88069 s P f)). Qed.
Lemma lem3389464 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3389465 {_88066 : Type'} (P : _88066 -> Prop) (Q : Prop) : (term185 _88066 P Q) = (term186 _88066 P Q).
Proof. exact (@lem3389464 _88066 P Q). Qed.
Lemma lem3389466 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term267 _88066 _88069 x s P f) = (term268 _88066 _88069 x s P f).
Proof. exact (@lem3389465 _88066 (term246 _88066 _88069 f s P x) (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389467 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term269 _88066 _88069 f s P x y) = (term245 _88066 _88069 f s P x y).
Proof. exact (eq_refl (term269 _88066 _88069 f s P x y)). Qed.
Lemma lem3389468 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term270 _88066 _88069 f s P x) = (term246 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3389467 _88066 _88069 f s P x y)). Qed.
Lemma lem3389469 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389470 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term271 _88066 _88069 f s P x) = (term247 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3389469 _88066) (@lem3389468 _88066 _88069 f s P x)). Qed.
Lemma lem3389471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389472 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term272 _88066 _88069 f s P x) = (term261 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3389471) (@lem3389470 _88066 _88069 f s P x)). Qed.
Lemma lem3389473 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389474 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term267 _88066 _88069 x s P f) = (term263 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389472 _88066 _88069 f s P x) (@lem3389473 _88066 _88069 s P f)). Qed.
Lemma lem3389475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389476 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term273 _88066 _88069 x s P f) = (term274 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389475) (@lem3389474 _88066 _88069 x s P f)). Qed.
Lemma lem3389477 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term269 _88066 _88069 f s P x y) = (term245 _88066 _88069 f s P x y).
Proof. exact (eq_refl (term269 _88066 _88069 f s P x y)). Qed.
Lemma lem3389478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389479 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term275 _88066 _88069 f s P x y) = (term276 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389478) (@lem3389477 _88066 _88069 f s P x y)). Qed.
Lemma lem3389480 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389481 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term277 _88066 _88069 x y s P f) = (term278 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389479 _88066 _88069 f s P x y) (@lem3389480 _88066 _88069 s P f)). Qed.
Lemma lem3389482 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term279 _88066 _88069 x s P f) = (term280 _88066 _88069 x s P f).
Proof. exact (fun_ext (fun y : _88066 => @lem3389481 _88066 _88069 x y s P f)). Qed.
Lemma lem3389483 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389484 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term268 _88066 _88069 x s P f) = (term281 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389483 _88066) (@lem3389482 _88066 _88069 x s P f)). Qed.
Lemma lem3389485 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term267 _88066 _88069 x s P f) = (term268 _88066 _88069 x s P f)) = ((term263 _88066 _88069 x s P f) = (term281 _88066 _88069 x s P f)).
Proof. exact (MK_COMB (@lem3389476 _88066 _88069 x s P f) (@lem3389484 _88066 _88069 x s P f)). Qed.
Lemma lem3389486 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term263 _88066 _88069 x s P f) = (term281 _88066 _88069 x s P f).
Proof. exact (EQ_MP (@lem3389485 _88066 _88069 x s P f) (@lem3389466 _88066 _88069 x s P f)). Qed.
Lemma lem3389488 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3389489 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term185 _88069 P Q) = (term186 _88069 P Q).
Proof. exact (@lem3389488 _88069 P Q). Qed.
Lemma lem3389490 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term282 _88066 _88069 x y s P f) = (term283 _88066 _88069 x y s P f).
Proof. exact (@lem3389489 _88069 (term244 _88066 _88069 f s P x y) (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389491 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term284 _88066 _88069 f s P x' y x) = (term243 _88066 _88069 x f s P x' y).
Proof. exact (eq_refl (term284 _88066 _88069 f s P x' y x)). Qed.
Lemma lem3389492 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term285 _88066 _88069 f s P x y) = (term244 _88066 _88069 f s P x y).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389491 _88066 _88069 x' f s P x y)). Qed.
Lemma lem3389493 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389494 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term286 _88066 _88069 f s P x y) = (term245 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389493 _88069) (@lem3389492 _88066 _88069 f s P x y)). Qed.
Lemma lem3389495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389496 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term287 _88066 _88069 f s P x y) = (term276 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389495) (@lem3389494 _88066 _88069 f s P x y)). Qed.
Lemma lem3389497 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389498 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term282 _88066 _88069 x y s P f) = (term278 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389496 _88066 _88069 f s P x y) (@lem3389497 _88066 _88069 s P f)). Qed.
Lemma lem3389499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389500 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term288 _88066 _88069 x y s P f) = (term289 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389499) (@lem3389498 _88066 _88069 x y s P f)). Qed.
Lemma lem3389501 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term284 _88066 _88069 f s P x' y x) = (term243 _88066 _88069 x f s P x' y).
Proof. exact (eq_refl (term284 _88066 _88069 f s P x' y x)). Qed.
Lemma lem3389502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389503 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term290 _88066 _88069 f s P x' y x) = (term291 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389502) (@lem3389501 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389504 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389505 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term292 _88066 _88069 x' y x s P f) = (term293 _88066 _88069 x x' y s P f).
Proof. exact (MK_COMB (@lem3389503 _88066 _88069 x f s P x' y) (@lem3389504 _88066 _88069 s P f)). Qed.
Lemma lem3389506 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term294 _88066 _88069 x y s P f) = (term295 _88066 _88069 x y s P f).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389505 _88066 _88069 x' x y s P f)). Qed.
Lemma lem3389507 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389508 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term283 _88066 _88069 x y s P f) = (term296 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389507 _88069) (@lem3389506 _88066 _88069 x y s P f)). Qed.
Lemma lem3389509 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term282 _88066 _88069 x y s P f) = (term283 _88066 _88069 x y s P f)) = ((term278 _88066 _88069 x y s P f) = (term296 _88066 _88069 x y s P f)).
Proof. exact (MK_COMB (@lem3389500 _88066 _88069 x y s P f) (@lem3389508 _88066 _88069 x y s P f)). Qed.
Lemma lem3389510 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term278 _88066 _88069 x y s P f) = (term296 _88066 _88069 x y s P f).
Proof. exact (EQ_MP (@lem3389509 _88066 _88069 x y s P f) (@lem3389490 _88066 _88069 x y s P f)). Qed.
Lemma lem3389512 {A : Type'} (P : A -> Prop) (Q : Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3389513 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term185 _88069 P Q) = (term186 _88069 P Q).
Proof. exact (@lem3389512 _88069 P Q). Qed.
Lemma lem3389514 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term297 _88066 _88069 x x' y s P f) = (term298 _88066 _88069 x x' y s P f).
Proof. exact (@lem3389513 _88069 (term242 _88066 _88069 x f s P x' y) (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389515 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) (P : type1402 _88066) (x'' : _88066) (y : _88066) : (term299 _88066 _88069 x f s P x'' y x') = (term240 _88066 _88069 x f s x' P x'' y).
Proof. exact (eq_refl (term299 _88066 _88069 x f s P x'' y x')). Qed.
Lemma lem3389516 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term300 _88066 _88069 x f s P x' y) = (term242 _88066 _88069 x f s P x' y).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389515 _88066 _88069 x f s x'' P x' y)). Qed.
Lemma lem3389517 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389518 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term301 _88066 _88069 x f s P x' y) = (term243 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389517 _88069) (@lem3389516 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389520 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term302 _88066 _88069 x f s P x' y) = (term291 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389519) (@lem3389518 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389521 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389522 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term297 _88066 _88069 x x' y s P f) = (term293 _88066 _88069 x x' y s P f).
Proof. exact (MK_COMB (@lem3389520 _88066 _88069 x f s P x' y) (@lem3389521 _88066 _88069 s P f)). Qed.
Lemma lem3389523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389524 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term303 _88066 _88069 x x' y s P f) = (term304 _88066 _88069 x x' y s P f).
Proof. exact (MK_COMB (@lem3389523) (@lem3389522 _88066 _88069 x x' y s P f)). Qed.
Lemma lem3389525 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) (P : type1402 _88066) (x'' : _88066) (y : _88066) : (term299 _88066 _88069 x f s P x'' y x') = (term240 _88066 _88069 x f s x' P x'' y).
Proof. exact (eq_refl (term299 _88066 _88069 x f s P x'' y x')). Qed.
Lemma lem3389526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389527 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) (P : type1402 _88066) (x'' : _88066) (y : _88066) : (term305 _88066 _88069 x f s P x'' y x') = (term306 _88066 _88069 x f s x' P x'' y).
Proof. exact (MK_COMB (@lem3389526) (@lem3389525 _88066 _88069 x f s x' P x'' y)). Qed.
Lemma lem3389528 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (eq_refl (term143 _88066 _88069 s P f)). Qed.
Lemma lem3389529 {_88066 _88069 : Type'} (x : _88069) (x' : _88069) (x'' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term307 _88066 _88069 x x'' y x' s P f) = (term308 _88066 _88069 x x' x'' y s P f).
Proof. exact (MK_COMB (@lem3389527 _88066 _88069 x f s x' P x'' y) (@lem3389528 _88066 _88069 s P f)). Qed.
Lemma lem3389530 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term309 _88066 _88069 x x' y s P f) = (term310 _88066 _88069 x x' y s P f).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389529 _88066 _88069 x x'' x' y s P f)). Qed.
Lemma lem3389531 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389532 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term298 _88066 _88069 x x' y s P f) = (term311 _88066 _88069 x x' y s P f).
Proof. exact (MK_COMB (@lem3389531 _88069) (@lem3389530 _88066 _88069 x x' y s P f)). Qed.
Lemma lem3389533 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term297 _88066 _88069 x x' y s P f) = (term298 _88066 _88069 x x' y s P f)) = ((term293 _88066 _88069 x x' y s P f) = (term311 _88066 _88069 x x' y s P f)).
Proof. exact (MK_COMB (@lem3389524 _88066 _88069 x x' y s P f) (@lem3389532 _88066 _88069 x x' y s P f)). Qed.
Lemma lem3389534 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term293 _88066 _88069 x x' y s P f) = (term311 _88066 _88069 x x' y s P f).
Proof. exact (EQ_MP (@lem3389533 _88066 _88069 x x' y s P f) (@lem3389514 _88066 _88069 x x' y s P f)). Qed.
Lemma lem3389535 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term295 _88066 _88069 x y s P f) = (term312 _88066 _88069 x y s P f).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389534 _88066 _88069 x' x y s P f)). Qed.
Lemma lem3389536 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389537 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term296 _88066 _88069 x y s P f) = (term313 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389536 _88069) (@lem3389535 _88066 _88069 x y s P f)). Qed.
Lemma lem3389538 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term278 _88066 _88069 x y s P f) = (term313 _88066 _88069 x y s P f).
Proof. exact (TRANS (@lem3389510 _88066 _88069 x y s P f) (@lem3389537 _88066 _88069 x y s P f)). Qed.
Lemma lem3389539 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term280 _88066 _88069 x s P f) = (term314 _88066 _88069 x s P f).
Proof. exact (fun_ext (fun y : _88066 => @lem3389538 _88066 _88069 x y s P f)). Qed.
Lemma lem3389540 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389541 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term281 _88066 _88069 x s P f) = (term315 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389540 _88066) (@lem3389539 _88066 _88069 x s P f)). Qed.
Lemma lem3389542 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term263 _88066 _88069 x s P f) = (term315 _88066 _88069 x s P f).
Proof. exact (TRANS (@lem3389486 _88066 _88069 x s P f) (@lem3389541 _88066 _88069 x s P f)). Qed.
Lemma lem3389543 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term265 _88066 _88069 s P f) = (term316 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88066 => @lem3389542 _88066 _88069 x s P f)). Qed.
Lemma lem3389544 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389545 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term266 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389544 _88066) (@lem3389543 _88066 _88069 s P f)). Qed.
Lemma lem3389546 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term251 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3389462 _88066 _88069 s P f) (@lem3389545 _88066 _88069 s P f)). Qed.
Lemma lem3389547 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term147 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3389438 _88066 _88069 s P f) (@lem3389546 _88066 _88069 s P f)). Qed.
Lemma lem3389548 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term155 _88066 _88069 s P f) = (term318 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389323 _88066 _88069 s P f) (@lem3389547 _88066 _88069 s P f)). Qed.
Lemma lem3389552 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3389553 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term319 _88069 P Q) = (term320 _88069 P Q).
Proof. exact (@lem3389552 _88069 P Q). Qed.
Lemma lem3389554 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term321 _88066 _88069 s P f) = (term322 _88066 _88069 s P f).
Proof. exact (@lem3389553 _88069 (term182 _88066 _88069 s P f) (term317 _88066 _88069 s P f)). Qed.
Lemma lem3389555 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term323 _88066 _88069 s P f x) = (term181 _88066 _88069 s P x f).
Proof. exact (eq_refl (term323 _88066 _88069 s P f x)). Qed.
Lemma lem3389556 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term324 _88066 _88069 s P f) = (term182 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3389555 _88066 _88069 s P x f)). Qed.
Lemma lem3389557 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389558 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term325 _88066 _88069 s P f) = (term183 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389557 _88069) (@lem3389556 _88066 _88069 s P f)). Qed.
Lemma lem3389559 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389560 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term326 _88066 _88069 s P f) = (term184 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389559) (@lem3389558 _88066 _88069 s P f)). Qed.
Lemma lem3389561 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term317 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (eq_refl (term317 _88066 _88069 s P f)). Qed.
Lemma lem3389562 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term321 _88066 _88069 s P f) = (term318 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389560 _88066 _88069 s P f) (@lem3389561 _88066 _88069 s P f)). Qed.
Lemma lem3389563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389564 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term327 _88066 _88069 s P f) = (term328 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389563) (@lem3389562 _88066 _88069 s P f)). Qed.
Lemma lem3389565 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term323 _88066 _88069 s P f x) = (term181 _88066 _88069 s P x f).
Proof. exact (eq_refl (term323 _88066 _88069 s P f x)). Qed.
Lemma lem3389566 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389567 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term329 _88066 _88069 s P f x) = (term330 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389566) (@lem3389565 _88066 _88069 s P x f)). Qed.
Lemma lem3389568 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term317 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (eq_refl (term317 _88066 _88069 s P f)). Qed.
Lemma lem3389569 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term331 _88066 _88069 x s P f) = (term332 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389567 _88066 _88069 s P x f) (@lem3389568 _88066 _88069 s P f)). Qed.
Lemma lem3389570 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term333 _88066 _88069 s P f) = (term334 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3389569 _88066 _88069 x s P f)). Qed.
Lemma lem3389571 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389572 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term322 _88066 _88069 s P f) = (term335 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389571 _88069) (@lem3389570 _88066 _88069 s P f)). Qed.
Lemma lem3389573 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term321 _88066 _88069 s P f) = (term322 _88066 _88069 s P f)) = ((term318 _88066 _88069 s P f) = (term335 _88066 _88069 s P f)).
Proof. exact (MK_COMB (@lem3389564 _88066 _88069 s P f) (@lem3389572 _88066 _88069 s P f)). Qed.
Lemma lem3389574 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term318 _88066 _88069 s P f) = (term335 _88066 _88069 s P f).
Proof. exact (EQ_MP (@lem3389573 _88066 _88069 s P f) (@lem3389554 _88066 _88069 s P f)). Qed.
Lemma lem3389578 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3389579 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term319 _88069 P Q) = (term320 _88069 P Q).
Proof. exact (@lem3389578 _88069 P Q). Qed.
Lemma lem3389580 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term336 _88066 _88069 x s P f) = (term337 _88066 _88069 x s P f).
Proof. exact (@lem3389579 _88069 (term180 _88066 _88069 s P x f) (term317 _88066 _88069 s P f)). Qed.
Lemma lem3389581 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term338 _88066 _88069 s P x f y) = (term178 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term338 _88066 _88069 s P x f y)). Qed.
Lemma lem3389582 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term339 _88066 _88069 s P x f) = (term180 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3389581 _88066 _88069 s P x f y)). Qed.
Lemma lem3389583 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389584 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term340 _88066 _88069 s P x f) = (term181 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389583 _88069) (@lem3389582 _88066 _88069 s P x f)). Qed.
Lemma lem3389585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389586 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term341 _88066 _88069 s P x f) = (term330 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389585) (@lem3389584 _88066 _88069 s P x f)). Qed.
Lemma lem3389587 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term317 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (eq_refl (term317 _88066 _88069 s P f)). Qed.
Lemma lem3389588 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term336 _88066 _88069 x s P f) = (term332 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389586 _88066 _88069 s P x f) (@lem3389587 _88066 _88069 s P f)). Qed.
Lemma lem3389589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389590 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term342 _88066 _88069 x s P f) = (term343 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389589) (@lem3389588 _88066 _88069 x s P f)). Qed.
Lemma lem3389591 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term338 _88066 _88069 s P x f y) = (term178 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term338 _88066 _88069 s P x f y)). Qed.
Lemma lem3389592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389593 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term344 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (MK_COMB (@lem3389592) (@lem3389591 _88066 _88069 s P x f y)). Qed.
Lemma lem3389594 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term317 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (eq_refl (term317 _88066 _88069 s P f)). Qed.
Lemma lem3389595 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term346 _88066 _88069 x y s P f) = (term347 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389593 _88066 _88069 s P x f y) (@lem3389594 _88066 _88069 s P f)). Qed.
Lemma lem3389596 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term348 _88066 _88069 x s P f) = (term349 _88066 _88069 x s P f).
Proof. exact (fun_ext (fun y : _88069 => @lem3389595 _88066 _88069 x y s P f)). Qed.
Lemma lem3389597 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389598 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term337 _88066 _88069 x s P f) = (term350 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389597 _88069) (@lem3389596 _88066 _88069 x s P f)). Qed.
Lemma lem3389599 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term336 _88066 _88069 x s P f) = (term337 _88066 _88069 x s P f)) = ((term332 _88066 _88069 x s P f) = (term350 _88066 _88069 x s P f)).
Proof. exact (MK_COMB (@lem3389590 _88066 _88069 x s P f) (@lem3389598 _88066 _88069 x s P f)). Qed.
Lemma lem3389600 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term332 _88066 _88069 x s P f) = (term350 _88066 _88069 x s P f).
Proof. exact (EQ_MP (@lem3389599 _88066 _88069 x s P f) (@lem3389580 _88066 _88069 x s P f)). Qed.
Lemma lem3389602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3389603 {_88066 : Type'} (P : Prop) (Q : _88066 -> Prop) : (term351 _88066 P Q) = (term352 _88066 P Q).
Proof. exact (@lem3389602 _88066 P Q). Qed.
Lemma lem3389604 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term353 _88066 _88069 x y s P f) = (term354 _88066 _88069 x y s P f).
Proof. exact (@lem3389603 _88066 (term178 _88066 _88069 s P x f y) (term316 _88066 _88069 s P f)). Qed.
Lemma lem3389605 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term355 _88066 _88069 s P f x) = (term315 _88066 _88069 x s P f).
Proof. exact (eq_refl (term355 _88066 _88069 s P f x)). Qed.
Lemma lem3389606 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term356 _88066 _88069 s P f) = (term316 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88066 => @lem3389605 _88066 _88069 x s P f)). Qed.
Lemma lem3389607 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389608 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term357 _88066 _88069 s P f) = (term317 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389607 _88066) (@lem3389606 _88066 _88069 s P f)). Qed.
Lemma lem3389609 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389610 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term353 _88066 _88069 x y s P f) = (term347 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389609 _88066 _88069 s P x f y) (@lem3389608 _88066 _88069 s P f)). Qed.
Lemma lem3389611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389612 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term358 _88066 _88069 x y s P f) = (term359 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389611) (@lem3389610 _88066 _88069 x y s P f)). Qed.
Lemma lem3389613 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term355 _88066 _88069 s P f x) = (term315 _88066 _88069 x s P f).
Proof. exact (eq_refl (term355 _88066 _88069 s P f x)). Qed.
Lemma lem3389614 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389615 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term360 _88066 _88069 x y s P f x') = (term361 _88066 _88069 x y x' s P f).
Proof. exact (MK_COMB (@lem3389614 _88066 _88069 s P x f y) (@lem3389613 _88066 _88069 x' s P f)). Qed.
Lemma lem3389616 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term362 _88066 _88069 x y s P f) = (term363 _88066 _88069 x y s P f).
Proof. exact (fun_ext (fun x' : _88066 => @lem3389615 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389617 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389618 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term354 _88066 _88069 x y s P f) = (term364 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389617 _88066) (@lem3389616 _88066 _88069 x y s P f)). Qed.
Lemma lem3389619 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term353 _88066 _88069 x y s P f) = (term354 _88066 _88069 x y s P f)) = ((term347 _88066 _88069 x y s P f) = (term364 _88066 _88069 x y s P f)).
Proof. exact (MK_COMB (@lem3389612 _88066 _88069 x y s P f) (@lem3389618 _88066 _88069 x y s P f)). Qed.
Lemma lem3389620 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term347 _88066 _88069 x y s P f) = (term364 _88066 _88069 x y s P f).
Proof. exact (EQ_MP (@lem3389619 _88066 _88069 x y s P f) (@lem3389604 _88066 _88069 x y s P f)). Qed.
Lemma lem3389622 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3389623 {_88066 : Type'} (P : Prop) (Q : _88066 -> Prop) : (term351 _88066 P Q) = (term352 _88066 P Q).
Proof. exact (@lem3389622 _88066 P Q). Qed.
Lemma lem3389624 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term365 _88066 _88069 x y x' s P f) = (term366 _88066 _88069 x y x' s P f).
Proof. exact (@lem3389623 _88066 (term178 _88066 _88069 s P x f y) (term314 _88066 _88069 x' s P f)). Qed.
Lemma lem3389625 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term367 _88066 _88069 x s P f y) = (term313 _88066 _88069 x y s P f).
Proof. exact (eq_refl (term367 _88066 _88069 x s P f y)). Qed.
Lemma lem3389626 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term368 _88066 _88069 x s P f) = (term314 _88066 _88069 x s P f).
Proof. exact (fun_ext (fun y : _88066 => @lem3389625 _88066 _88069 x y s P f)). Qed.
Lemma lem3389627 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389628 {_88066 _88069 : Type'} (x : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term369 _88066 _88069 x s P f) = (term315 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389627 _88066) (@lem3389626 _88066 _88069 x s P f)). Qed.
Lemma lem3389629 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389630 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term365 _88066 _88069 x y x' s P f) = (term361 _88066 _88069 x y x' s P f).
Proof. exact (MK_COMB (@lem3389629 _88066 _88069 s P x f y) (@lem3389628 _88066 _88069 x' s P f)). Qed.
Lemma lem3389631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389632 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term370 _88066 _88069 x y x' s P f) = (term371 _88066 _88069 x y x' s P f).
Proof. exact (MK_COMB (@lem3389631) (@lem3389630 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389633 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term367 _88066 _88069 x s P f y) = (term313 _88066 _88069 x y s P f).
Proof. exact (eq_refl (term367 _88066 _88069 x s P f y)). Qed.
Lemma lem3389634 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389635 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term372 _88066 _88069 x y x' s P f y') = (term373 _88066 _88069 x y x' y' s P f).
Proof. exact (MK_COMB (@lem3389634 _88066 _88069 s P x f y) (@lem3389633 _88066 _88069 x' y' s P f)). Qed.
Lemma lem3389636 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term374 _88066 _88069 x y x' s P f) = (term375 _88066 _88069 x y x' s P f).
Proof. exact (fun_ext (fun y' : _88066 => @lem3389635 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389637 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389638 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term366 _88066 _88069 x y x' s P f) = (term376 _88066 _88069 x y x' s P f).
Proof. exact (MK_COMB (@lem3389637 _88066) (@lem3389636 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389639 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term365 _88066 _88069 x y x' s P f) = (term366 _88066 _88069 x y x' s P f)) = ((term361 _88066 _88069 x y x' s P f) = (term376 _88066 _88069 x y x' s P f)).
Proof. exact (MK_COMB (@lem3389632 _88066 _88069 x y x' s P f) (@lem3389638 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389640 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term361 _88066 _88069 x y x' s P f) = (term376 _88066 _88069 x y x' s P f).
Proof. exact (EQ_MP (@lem3389639 _88066 _88069 x y x' s P f) (@lem3389624 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3389643 {_88069 : Type'} (P : Prop) (Q : _88069 -> Prop) : (term351 _88069 P Q) = (term352 _88069 P Q).
Proof. exact (@lem3389642 _88069 P Q). Qed.
Lemma lem3389644 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term377 _88066 _88069 x y x' y' s P f) = (term378 _88066 _88069 x y x' y' s P f).
Proof. exact (@lem3389643 _88069 (term178 _88066 _88069 s P x f y) (term312 _88066 _88069 x' y' s P f)). Qed.
Lemma lem3389645 {_88066 _88069 : Type'} (x : _88069) (x' : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term379 _88066 _88069 x' y s P f x) = (term311 _88066 _88069 x x' y s P f).
Proof. exact (eq_refl (term379 _88066 _88069 x' y s P f x)). Qed.
Lemma lem3389646 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term380 _88066 _88069 x y s P f) = (term312 _88066 _88069 x y s P f).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389645 _88066 _88069 x' x y s P f)). Qed.
Lemma lem3389647 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389648 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term381 _88066 _88069 x y s P f) = (term313 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389647 _88069) (@lem3389646 _88066 _88069 x y s P f)). Qed.
Lemma lem3389649 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389650 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term377 _88066 _88069 x y x' y' s P f) = (term373 _88066 _88069 x y x' y' s P f).
Proof. exact (MK_COMB (@lem3389649 _88066 _88069 s P x f y) (@lem3389648 _88066 _88069 x' y' s P f)). Qed.
Lemma lem3389651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389652 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term382 _88066 _88069 x y x' y' s P f) = (term383 _88066 _88069 x y x' y' s P f).
Proof. exact (MK_COMB (@lem3389651) (@lem3389650 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389653 {_88066 _88069 : Type'} (x' : _88069) (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term379 _88066 _88069 x y s P f x') = (term311 _88066 _88069 x' x y s P f).
Proof. exact (eq_refl (term379 _88066 _88069 x y s P f x')). Qed.
Lemma lem3389654 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389655 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term384 _88066 _88069 x y x'' y' s P f x') = (term385 _88066 _88069 x y x' x'' y' s P f).
Proof. exact (MK_COMB (@lem3389654 _88066 _88069 s P x f y) (@lem3389653 _88066 _88069 x' x'' y' s P f)). Qed.
Lemma lem3389656 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term386 _88066 _88069 x y x' y' s P f) = (term387 _88066 _88069 x y x' y' s P f).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389655 _88066 _88069 x y x'' x' y' s P f)). Qed.
Lemma lem3389657 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389658 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term378 _88066 _88069 x y x' y' s P f) = (term388 _88066 _88069 x y x' y' s P f).
Proof. exact (MK_COMB (@lem3389657 _88069) (@lem3389656 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389659 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term377 _88066 _88069 x y x' y' s P f) = (term378 _88066 _88069 x y x' y' s P f)) = ((term373 _88066 _88069 x y x' y' s P f) = (term388 _88066 _88069 x y x' y' s P f)).
Proof. exact (MK_COMB (@lem3389652 _88066 _88069 x y x' y' s P f) (@lem3389658 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389660 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term373 _88066 _88069 x y x' y' s P f) = (term388 _88066 _88069 x y x' y' s P f).
Proof. exact (EQ_MP (@lem3389659 _88066 _88069 x y x' y' s P f) (@lem3389644 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389662 {A : Type'} (P : Prop) (Q : A -> Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3389663 {_88069 : Type'} (P : Prop) (Q : _88069 -> Prop) : (term351 _88069 P Q) = (term352 _88069 P Q).
Proof. exact (@lem3389662 _88069 P Q). Qed.
Lemma lem3389664 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term389 _88066 _88069 x y x' x'' y' s P f) = (term390 _88066 _88069 x y x' x'' y' s P f).
Proof. exact (@lem3389663 _88069 (term178 _88066 _88069 s P x f y) (term310 _88066 _88069 x' x'' y' s P f)). Qed.
Lemma lem3389665 {_88066 _88069 : Type'} (x' : _88069) (x'' : _88069) (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term391 _88066 _88069 x' x y s P f x'') = (term308 _88066 _88069 x' x'' x y s P f).
Proof. exact (eq_refl (term391 _88066 _88069 x' x y s P f x'')). Qed.
Lemma lem3389666 {_88066 _88069 : Type'} (x' : _88069) (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term392 _88066 _88069 x' x y s P f) = (term310 _88066 _88069 x' x y s P f).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389665 _88066 _88069 x' x'' x y s P f)). Qed.
Lemma lem3389667 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389668 {_88066 _88069 : Type'} (x' : _88069) (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term393 _88066 _88069 x' x y s P f) = (term311 _88066 _88069 x' x y s P f).
Proof. exact (MK_COMB (@lem3389667 _88069) (@lem3389666 _88066 _88069 x' x y s P f)). Qed.
Lemma lem3389669 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389670 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term389 _88066 _88069 x y x' x'' y' s P f) = (term385 _88066 _88069 x y x' x'' y' s P f).
Proof. exact (MK_COMB (@lem3389669 _88066 _88069 s P x f y) (@lem3389668 _88066 _88069 x' x'' y' s P f)). Qed.
Lemma lem3389671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389672 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term394 _88066 _88069 x y x' x'' y' s P f) = (term395 _88066 _88069 x y x' x'' y' s P f).
Proof. exact (MK_COMB (@lem3389671) (@lem3389670 _88066 _88069 x y x' x'' y' s P f)). Qed.
Lemma lem3389673 {_88066 _88069 : Type'} (x' : _88069) (x'' : _88069) (x : _88066) (y : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term391 _88066 _88069 x' x y s P f x'') = (term308 _88066 _88069 x' x'' x y s P f).
Proof. exact (eq_refl (term391 _88066 _88069 x' x y s P f x'')). Qed.
Lemma lem3389674 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term345 _88066 _88069 s P x f y)). Qed.
Lemma lem3389675 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88069) (x''' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term396 _88066 _88069 x y x' x''' y' s P f x'') = (term397 _88066 _88069 x y x' x'' x''' y' s P f).
Proof. exact (MK_COMB (@lem3389674 _88066 _88069 s P x f y) (@lem3389673 _88066 _88069 x' x'' x''' y' s P f)). Qed.
Lemma lem3389676 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term398 _88066 _88069 x y x' x'' y' s P f) = (term399 _88066 _88069 x y x' x'' y' s P f).
Proof. exact (fun_ext (fun x''' : _88069 => @lem3389675 _88066 _88069 x y x' x''' x'' y' s P f)). Qed.
Lemma lem3389677 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389678 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term390 _88066 _88069 x y x' x'' y' s P f) = (term400 _88066 _88069 x y x' x'' y' s P f).
Proof. exact (MK_COMB (@lem3389677 _88069) (@lem3389676 _88066 _88069 x y x' x'' y' s P f)). Qed.
Lemma lem3389679 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : ((term389 _88066 _88069 x y x' x'' y' s P f) = (term390 _88066 _88069 x y x' x'' y' s P f)) = ((term385 _88066 _88069 x y x' x'' y' s P f) = (term400 _88066 _88069 x y x' x'' y' s P f)).
Proof. exact (MK_COMB (@lem3389672 _88066 _88069 x y x' x'' y' s P f) (@lem3389678 _88066 _88069 x y x' x'' y' s P f)). Qed.
Lemma lem3389680 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88069) (x'' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term385 _88066 _88069 x y x' x'' y' s P f) = (term400 _88066 _88069 x y x' x'' y' s P f).
Proof. exact (EQ_MP (@lem3389679 _88066 _88069 x y x' x'' y' s P f) (@lem3389664 _88066 _88069 x y x' x'' y' s P f)). Qed.
Lemma lem3389681 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term387 _88066 _88069 x y x' y' s P f) = (term401 _88066 _88069 x y x' y' s P f).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389680 _88066 _88069 x y x'' x' y' s P f)). Qed.
Lemma lem3389682 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389683 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term388 _88066 _88069 x y x' y' s P f) = (term402 _88066 _88069 x y x' y' s P f).
Proof. exact (MK_COMB (@lem3389682 _88069) (@lem3389681 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389684 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term373 _88066 _88069 x y x' y' s P f) = (term402 _88066 _88069 x y x' y' s P f).
Proof. exact (TRANS (@lem3389660 _88066 _88069 x y x' y' s P f) (@lem3389683 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389685 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term375 _88066 _88069 x y x' s P f) = (term403 _88066 _88069 x y x' s P f).
Proof. exact (fun_ext (fun y' : _88066 => @lem3389684 _88066 _88069 x y x' y' s P f)). Qed.
Lemma lem3389686 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389687 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term376 _88066 _88069 x y x' s P f) = (term404 _88066 _88069 x y x' s P f).
Proof. exact (MK_COMB (@lem3389686 _88066) (@lem3389685 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389688 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term361 _88066 _88069 x y x' s P f) = (term404 _88066 _88069 x y x' s P f).
Proof. exact (TRANS (@lem3389640 _88066 _88069 x y x' s P f) (@lem3389687 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389689 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term363 _88066 _88069 x y s P f) = (term405 _88066 _88069 x y s P f).
Proof. exact (fun_ext (fun x' : _88066 => @lem3389688 _88066 _88069 x y x' s P f)). Qed.
Lemma lem3389690 {_88066 : Type'} : (@ex _88066) = (@ex _88066).
Proof. exact (eq_refl (@ex _88066)). Qed.
Lemma lem3389691 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term364 _88066 _88069 x y s P f) = (term406 _88066 _88069 x y s P f).
Proof. exact (MK_COMB (@lem3389690 _88066) (@lem3389689 _88066 _88069 x y s P f)). Qed.
Lemma lem3389692 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term347 _88066 _88069 x y s P f) = (term406 _88066 _88069 x y s P f).
Proof. exact (TRANS (@lem3389620 _88066 _88069 x y s P f) (@lem3389691 _88066 _88069 x y s P f)). Qed.
Lemma lem3389693 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term349 _88066 _88069 x s P f) = (term407 _88066 _88069 x s P f).
Proof. exact (fun_ext (fun y : _88069 => @lem3389692 _88066 _88069 x y s P f)). Qed.
Lemma lem3389694 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389695 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term350 _88066 _88069 x s P f) = (term408 _88066 _88069 x s P f).
Proof. exact (MK_COMB (@lem3389694 _88069) (@lem3389693 _88066 _88069 x s P f)). Qed.
Lemma lem3389696 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term332 _88066 _88069 x s P f) = (term408 _88066 _88069 x s P f).
Proof. exact (TRANS (@lem3389600 _88066 _88069 x s P f) (@lem3389695 _88066 _88069 x s P f)). Qed.
Lemma lem3389697 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term334 _88066 _88069 s P f) = (term409 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3389696 _88066 _88069 x s P f)). Qed.
Lemma lem3389698 {_88069 : Type'} : (@ex _88069) = (@ex _88069).
Proof. exact (eq_refl (@ex _88069)). Qed.
Lemma lem3389699 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term335 _88066 _88069 s P f) = (term410 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389698 _88069) (@lem3389697 _88066 _88069 s P f)). Qed.
Lemma lem3389700 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term318 _88066 _88069 s P f) = (term410 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3389574 _88066 _88069 s P f) (@lem3389699 _88066 _88069 s P f)). Qed.
Lemma lem3389702 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term155 _88066 _88069 s P f) = (term410 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3389548 _88066 _88069 s P f) (@lem3389700 _88066 _88069 s P f)). Qed.
Lemma lem3389703 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term73 _88066 _88069 s P f) = (term410 _88066 _88069 s P f).
Proof. exact (TRANS (@lem3388908 _88066 _88069 s P f) (@lem3389702 _88066 _88069 s P f)). Qed.
Lemma lem3389704 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term73 _88066 _88069 s P f) : term410 _88066 _88069 s P f.
Proof. exact (EQ_MP (@lem3389703 _88066 _88069 s P f) (@lem3388751 _88066 _88069 s P f h1)). Qed.
Lemma lem3389705 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term408 _88066 _88069 x s P f) : term408 _88066 _88069 x s P f.
Proof. exact (h1). Qed.
Lemma lem3389706 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term406 _88066 _88069 x y s P f) : term406 _88066 _88069 x y s P f.
Proof. exact (h1). Qed.
Lemma lem3389707 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term404 _88066 _88069 x y x' s P f) : term404 _88066 _88069 x y x' s P f.
Proof. exact (h1). Qed.
Lemma lem3389708 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term402 _88066 _88069 x y x' y' s P f) : term402 _88066 _88069 x y x' y' s P f.
Proof. exact (h1). Qed.
Lemma lem3389709 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term400 _88066 _88069 x y x'' x' y' s P f) : term400 _88066 _88069 x y x'' x' y' s P f.
Proof. exact (h1). Qed.
Lemma lem3389710 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term397 _88066 _88069 x y x'' x''' x' y' s P f) : term397 _88066 _88069 x y x'' x''' x' y' s P f.
Proof. exact (h1). Qed.
Lemma lem3389735 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term125 _88066 _88069 s P x f y) = (term125 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term125 _88066 _88069 s P x f y)). Qed.
Lemma lem3389736 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term133 _88066 _88069 s P x f) = (term133 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3389735 _88066 _88069 s P x f y)). Qed.
Lemma lem3389737 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389738 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term134 _88066 _88069 s P x f) = (term134 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3389737 _88069) (@lem3389736 _88066 _88069 s P x f)). Qed.
Lemma lem3389739 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term142 _88066 _88069 s P f) = (term142 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3389738 _88066 _88069 s P x f)). Qed.
Lemma lem3389740 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389741 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3389740 _88069) (@lem3389739 _88066 _88069 s P f)). Qed.
Lemma lem3389782 {_88066 _88069 : Type'} (x'' : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (x''' : _88069) (P : type1402 _88066) (x' : _88066) (y' : _88066) : (term306 _88066 _88069 x'' f s x''' P x' y') = (term306 _88066 _88069 x'' f s x''' P x' y').
Proof. exact (eq_refl (term306 _88066 _88069 x'' f s x''' P x' y')). Qed.
Lemma lem3389783 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term308 _88066 _88069 x'' x''' x' y' s P f) = (term308 _88066 _88069 x'' x''' x' y' s P f).
Proof. exact (MK_COMB (@lem3389782 _88066 _88069 x'' f s x''' P x' y') (@lem3389741 _88066 _88069 s P f)). Qed.
Lemma lem3389806 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term121 _88066 _88069 s P x f y) = (term121 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term121 _88066 _88069 s P x f y)). Qed.
Lemma lem3389811 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3389828 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term75 _88066 _88069 y f s x) = (term75 _88066 _88069 y f s x).
Proof. exact (eq_refl (term75 _88066 _88069 y f s x)). Qed.
Lemma lem3389829 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term83 _88066 _88069 y f s) = (term83 _88066 _88069 y f s).
Proof. exact (fun_ext (fun x : _88069 => @lem3389828 _88066 _88069 y f s x)). Qed.
Lemma lem3389830 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389831 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term84 _88066 _88069 y f s) = (term84 _88066 _88069 y f s).
Proof. exact (MK_COMB (@lem3389830 _88069) (@lem3389829 _88066 _88069 y f s)). Qed.
Lemma lem3389848 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term75 _88066 _88069 x f s x') = (term75 _88066 _88069 x f s x').
Proof. exact (eq_refl (term75 _88066 _88069 x f s x')). Qed.
Lemma lem3389849 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term83 _88066 _88069 x f s) = (term83 _88066 _88069 x f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389848 _88066 _88069 x f s x')). Qed.
Lemma lem3389850 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389851 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term84 _88066 _88069 x f s) = (term84 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3389850 _88069) (@lem3389849 _88066 _88069 x f s)). Qed.
Lemma lem3389852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389853 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term86 _88066 _88069 x f s) = (term86 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3389852) (@lem3389851 _88066 _88069 x f s)). Qed.
Lemma lem3389854 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term88 _88066 _88069 x y f s) = (term88 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389853 _88066 _88069 x f s) (@lem3389831 _88066 _88069 y f s)). Qed.
Lemma lem3389855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389856 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term95 _88066 _88069 x y f s) = (term95 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389855) (@lem3389854 _88066 _88069 x y f s)). Qed.
Lemma lem3389857 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term97 _88066 _88069 f s P x y) = (term97 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389856 _88066 _88069 x y f s) (@lem3389811 _88066 P x y)). Qed.
Lemma lem3389858 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term107 _88066 _88069 f s P x) = (term107 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3389857 _88066 _88069 f s P x y)). Qed.
Lemma lem3389859 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3389860 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term108 _88066 _88069 f s P x) = (term108 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3389859 _88066) (@lem3389858 _88066 _88069 f s P x)). Qed.
Lemma lem3389861 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term116 _88066 _88069 f s P) = (term116 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3389860 _88066 _88069 f s P x)). Qed.
Lemma lem3389862 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3389863 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term117 _88066 _88069 f s P) = (term117 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3389862 _88066) (@lem3389861 _88066 _88069 f s P)). Qed.
Lemma lem3389864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3389865 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term149 _88066 _88069 f s P) = (term149 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3389864) (@lem3389863 _88066 _88069 f s P)). Qed.
Lemma lem3389866 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term178 _88066 _88069 s P x f y) = (term178 _88066 _88069 s P x f y).
Proof. exact (MK_COMB (@lem3389865 _88066 _88069 f s P) (@lem3389806 _88066 _88069 s P x f y)). Qed.
Lemma lem3389867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389868 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term345 _88066 _88069 s P x f y) = (term345 _88066 _88069 s P x f y).
Proof. exact (MK_COMB (@lem3389867) (@lem3389866 _88066 _88069 s P x f y)). Qed.
Lemma lem3389869 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term397 _88066 _88069 x y x'' x''' x' y' s P f) = (term397 _88066 _88069 x y x'' x''' x' y' s P f).
Proof. exact (MK_COMB (@lem3389868 _88066 _88069 s P x f y) (@lem3389783 _88066 _88069 x'' x''' x' y' s P f)). Qed.
Lemma lem3389870 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term397 _88066 _88069 x y x'' x''' x' y' s P f) : term397 _88066 _88069 x y x'' x''' x' y' s P f.
Proof. exact (EQ_MP (@lem3389869 _88066 _88069 x y x'' x''' x' y' s P f) (@lem3389710 _88066 _88069 x y x'' x''' x' y' s P f h1)). Qed.
Lemma lem3389871 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term178 _88066 _88069 s P x f y.
Proof. exact (h1). Qed.
Lemma lem3389872 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term308 _88066 _88069 x'' x''' x' y' s P f.
Proof. exact (h1). Qed.
Lemma lem3389873 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term121 _88066 _88069 s P x f y.
Proof. exact (proj2 (@lem3389871 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3389874 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term117 _88066 _88069 f s P.
Proof. exact (proj1 (@lem3389871 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3389876 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term38 _88069 x s y.
Proof. exact (proj1 (@lem3389873 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3389879 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term143 _88066 _88069 s P f.
Proof. exact (proj2 (@lem3389872 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3389880 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term240 _88066 _88069 x'' f s x''' P x' y'.
Proof. exact (proj1 (@lem3389872 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3389882 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term206 _88066 _88069 x' x'' y' f s x'''.
Proof. exact (proj1 (@lem3389880 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3389883 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term13 _88066 _88069 y' f s x'''.
Proof. exact (proj2 (@lem3389882 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3389884 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term13 _88066 _88069 x' f s x''.
Proof. exact (proj1 (@lem3389882 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3389890 {A : Type'} (P : A -> Prop) (Q : Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3389891 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term411 _88069 P Q) = (term412 _88069 P Q).
Proof. exact (@lem3389890 _88069 P Q). Qed.
Lemma lem3389892 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term413 _88066 _88069 x y f s) = (term414 _88066 _88069 x y f s).
Proof. exact (@lem3389891 _88069 (term83 _88066 _88069 x f s) (term84 _88066 _88069 y f s)). Qed.
Lemma lem3389893 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term415 _88066 _88069 x f s x') = (term75 _88066 _88069 x f s x').
Proof. exact (eq_refl (term415 _88066 _88069 x f s x')). Qed.
Lemma lem3389894 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term416 _88066 _88069 x f s) = (term83 _88066 _88069 x f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389893 _88066 _88069 x f s x')). Qed.
Lemma lem3389895 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389896 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term417 _88066 _88069 x f s) = (term84 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3389895 _88069) (@lem3389894 _88066 _88069 x f s)). Qed.
Lemma lem3389897 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389898 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term418 _88066 _88069 x f s) = (term86 _88066 _88069 x f s).
Proof. exact (MK_COMB (@lem3389897) (@lem3389896 _88066 _88069 x f s)). Qed.
Lemma lem3389899 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term84 _88066 _88069 y f s) = (term84 _88066 _88069 y f s).
Proof. exact (eq_refl (term84 _88066 _88069 y f s)). Qed.
Lemma lem3389900 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term413 _88066 _88069 x y f s) = (term88 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389898 _88066 _88069 x f s) (@lem3389899 _88066 _88069 y f s)). Qed.
Lemma lem3389901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389902 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term419 _88066 _88069 x y f s) = (term420 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389901) (@lem3389900 _88066 _88069 x y f s)). Qed.
Lemma lem3389903 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term415 _88066 _88069 x f s x') = (term75 _88066 _88069 x f s x').
Proof. exact (eq_refl (term415 _88066 _88069 x f s x')). Qed.
Lemma lem3389904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389905 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term421 _88066 _88069 x f s x') = (term422 _88066 _88069 x f s x').
Proof. exact (MK_COMB (@lem3389904) (@lem3389903 _88066 _88069 x f s x')). Qed.
Lemma lem3389906 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term84 _88066 _88069 y f s) = (term84 _88066 _88069 y f s).
Proof. exact (eq_refl (term84 _88066 _88069 y f s)). Qed.
Lemma lem3389907 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term423 _88066 _88069 x x' y f s) = (term424 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389905 _88066 _88069 x f s x') (@lem3389906 _88066 _88069 y f s)). Qed.
Lemma lem3389908 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term425 _88066 _88069 x y f s) = (term426 _88066 _88069 x y f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389907 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389909 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389910 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term414 _88066 _88069 x y f s) = (term427 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389909 _88069) (@lem3389908 _88066 _88069 x y f s)). Qed.
Lemma lem3389911 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : ((term413 _88066 _88069 x y f s) = (term414 _88066 _88069 x y f s)) = ((term88 _88066 _88069 x y f s) = (term427 _88066 _88069 x y f s)).
Proof. exact (MK_COMB (@lem3389902 _88066 _88069 x y f s) (@lem3389910 _88066 _88069 x y f s)). Qed.
Lemma lem3389912 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term88 _88066 _88069 x y f s) = (term427 _88066 _88069 x y f s).
Proof. exact (EQ_MP (@lem3389911 _88066 _88069 x y f s) (@lem3389892 _88066 _88069 x y f s)). Qed.
Lemma lem3389914 {A : Type'} (P : Prop) (Q : A -> Prop) : (term428 A P Q) = (term429 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3389915 {_88069 : Type'} (P : Prop) (Q : _88069 -> Prop) : (term428 _88069 P Q) = (term429 _88069 P Q).
Proof. exact (@lem3389914 _88069 P Q). Qed.
Lemma lem3389916 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term430 _88066 _88069 x x' y f s) = (term431 _88066 _88069 x x' y f s).
Proof. exact (@lem3389915 _88069 (term75 _88066 _88069 x f s x') (term83 _88066 _88069 y f s)). Qed.
Lemma lem3389917 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x : _88069) : (term415 _88066 _88069 y f s x) = (term75 _88066 _88069 y f s x).
Proof. exact (eq_refl (term415 _88066 _88069 y f s x)). Qed.
Lemma lem3389918 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term416 _88066 _88069 y f s) = (term83 _88066 _88069 y f s).
Proof. exact (fun_ext (fun x : _88069 => @lem3389917 _88066 _88069 y f s x)). Qed.
Lemma lem3389919 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389920 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term417 _88066 _88069 y f s) = (term84 _88066 _88069 y f s).
Proof. exact (MK_COMB (@lem3389919 _88069) (@lem3389918 _88066 _88069 y f s)). Qed.
Lemma lem3389921 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term422 _88066 _88069 x f s x') = (term422 _88066 _88069 x f s x').
Proof. exact (eq_refl (term422 _88066 _88069 x f s x')). Qed.
Lemma lem3389922 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term430 _88066 _88069 x x' y f s) = (term424 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389921 _88066 _88069 x f s x') (@lem3389920 _88066 _88069 y f s)). Qed.
Lemma lem3389923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389924 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term432 _88066 _88069 x x' y f s) = (term433 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389923) (@lem3389922 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389925 {_88066 _88069 : Type'} (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term415 _88066 _88069 y f s x') = (term75 _88066 _88069 y f s x').
Proof. exact (eq_refl (term415 _88066 _88069 y f s x')). Qed.
Lemma lem3389926 {_88066 _88069 : Type'} (x : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) : (term422 _88066 _88069 x f s x') = (term422 _88066 _88069 x f s x').
Proof. exact (eq_refl (term422 _88066 _88069 x f s x')). Qed.
Lemma lem3389927 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term434 _88066 _88069 x x' y f s x'') = (term435 _88066 _88069 x x' y f s x'').
Proof. exact (MK_COMB (@lem3389926 _88066 _88069 x f s x') (@lem3389925 _88066 _88069 y f s x'')). Qed.
Lemma lem3389928 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term436 _88066 _88069 x x' y f s) = (term437 _88066 _88069 x x' y f s).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389927 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389929 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389930 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term431 _88066 _88069 x x' y f s) = (term438 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389929 _88069) (@lem3389928 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389931 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : ((term430 _88066 _88069 x x' y f s) = (term431 _88066 _88069 x x' y f s)) = ((term424 _88066 _88069 x x' y f s) = (term438 _88066 _88069 x x' y f s)).
Proof. exact (MK_COMB (@lem3389924 _88066 _88069 x x' y f s) (@lem3389930 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389932 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term424 _88066 _88069 x x' y f s) = (term438 _88066 _88069 x x' y f s).
Proof. exact (EQ_MP (@lem3389931 _88066 _88069 x x' y f s) (@lem3389916 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389933 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term426 _88066 _88069 x y f s) = (term439 _88066 _88069 x y f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389932 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389934 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389935 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term427 _88066 _88069 x y f s) = (term440 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389934 _88069) (@lem3389933 _88066 _88069 x y f s)). Qed.
Lemma lem3389936 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term88 _88066 _88069 x y f s) = (term440 _88066 _88069 x y f s).
Proof. exact (TRANS (@lem3389912 _88066 _88069 x y f s) (@lem3389935 _88066 _88069 x y f s)). Qed.
Lemma lem3389937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389938 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term95 _88066 _88069 x y f s) = (term441 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389937) (@lem3389936 _88066 _88069 x y f s)). Qed.
Lemma lem3389939 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3389940 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term97 _88066 _88069 f s P x y) = (term442 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389938 _88066 _88069 x y f s) (@lem3389939 _88066 P x y)). Qed.
Lemma lem3389942 {A : Type'} (P : A -> Prop) (Q : Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3389943 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term411 _88069 P Q) = (term412 _88069 P Q).
Proof. exact (@lem3389942 _88069 P Q). Qed.
Lemma lem3389944 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term443 _88066 _88069 f s P x y) = (term444 _88066 _88069 f s P x y).
Proof. exact (@lem3389943 _88069 (term439 _88066 _88069 x y f s) (P x y)). Qed.
Lemma lem3389945 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term445 _88066 _88069 x y f s x') = (term438 _88066 _88069 x x' y f s).
Proof. exact (eq_refl (term445 _88066 _88069 x y f s x')). Qed.
Lemma lem3389946 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term446 _88066 _88069 x y f s) = (term439 _88066 _88069 x y f s).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389945 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389947 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389948 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term447 _88066 _88069 x y f s) = (term440 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389947 _88069) (@lem3389946 _88066 _88069 x y f s)). Qed.
Lemma lem3389949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389950 {_88066 _88069 : Type'} (x : _88066) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term448 _88066 _88069 x y f s) = (term441 _88066 _88069 x y f s).
Proof. exact (MK_COMB (@lem3389949) (@lem3389948 _88066 _88069 x y f s)). Qed.
Lemma lem3389951 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3389952 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term443 _88066 _88069 f s P x y) = (term442 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389950 _88066 _88069 x y f s) (@lem3389951 _88066 P x y)). Qed.
Lemma lem3389953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389954 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term449 _88066 _88069 f s P x y) = (term450 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389953) (@lem3389952 _88066 _88069 f s P x y)). Qed.
Lemma lem3389955 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term445 _88066 _88069 x y f s x') = (term438 _88066 _88069 x x' y f s).
Proof. exact (eq_refl (term445 _88066 _88069 x y f s x')). Qed.
Lemma lem3389956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389957 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term451 _88066 _88069 x y f s x') = (term452 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389956) (@lem3389955 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389958 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3389959 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term453 _88066 _88069 f s x P x' y) = (term454 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389957 _88066 _88069 x' x y f s) (@lem3389958 _88066 P x' y)). Qed.
Lemma lem3389960 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term455 _88066 _88069 f s P x y) = (term456 _88066 _88069 f s P x y).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389959 _88066 _88069 x' f s P x y)). Qed.
Lemma lem3389961 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389962 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term444 _88066 _88069 f s P x y) = (term457 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389961 _88069) (@lem3389960 _88066 _88069 f s P x y)). Qed.
Lemma lem3389963 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : ((term443 _88066 _88069 f s P x y) = (term444 _88066 _88069 f s P x y)) = ((term442 _88066 _88069 f s P x y) = (term457 _88066 _88069 f s P x y)).
Proof. exact (MK_COMB (@lem3389954 _88066 _88069 f s P x y) (@lem3389962 _88066 _88069 f s P x y)). Qed.
Lemma lem3389964 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term442 _88066 _88069 f s P x y) = (term457 _88066 _88069 f s P x y).
Proof. exact (EQ_MP (@lem3389963 _88066 _88069 f s P x y) (@lem3389944 _88066 _88069 f s P x y)). Qed.
Lemma lem3389966 {A : Type'} (P : A -> Prop) (Q : Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3389967 {_88069 : Type'} (P : _88069 -> Prop) (Q : Prop) : (term411 _88069 P Q) = (term412 _88069 P Q).
Proof. exact (@lem3389966 _88069 P Q). Qed.
Lemma lem3389968 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term458 _88066 _88069 x f s P x' y) = (term459 _88066 _88069 x f s P x' y).
Proof. exact (@lem3389967 _88069 (term437 _88066 _88069 x' x y f s) (P x' y)). Qed.
Lemma lem3389969 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term460 _88066 _88069 x x' y f s x'') = (term435 _88066 _88069 x x' y f s x'').
Proof. exact (eq_refl (term460 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389970 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term461 _88066 _88069 x x' y f s) = (term437 _88066 _88069 x x' y f s).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389969 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389971 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389972 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term462 _88066 _88069 x x' y f s) = (term438 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389971 _88069) (@lem3389970 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389974 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) : (term463 _88066 _88069 x x' y f s) = (term452 _88066 _88069 x x' y f s).
Proof. exact (MK_COMB (@lem3389973) (@lem3389972 _88066 _88069 x x' y f s)). Qed.
Lemma lem3389975 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3389976 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term458 _88066 _88069 x f s P x' y) = (term454 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389974 _88066 _88069 x' x y f s) (@lem3389975 _88066 P x' y)). Qed.
Lemma lem3389977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3389978 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term464 _88066 _88069 x f s P x' y) = (term465 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389977) (@lem3389976 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389979 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term460 _88066 _88069 x x' y f s x'') = (term435 _88066 _88069 x x' y f s x'').
Proof. exact (eq_refl (term460 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389980 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3389981 {_88066 _88069 : Type'} (x : _88066) (x' : _88069) (y : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (x'' : _88069) : (term466 _88066 _88069 x x' y f s x'') = (term467 _88066 _88069 x x' y f s x'').
Proof. exact (MK_COMB (@lem3389980) (@lem3389979 _88066 _88069 x x' y f s x'')). Qed.
Lemma lem3389982 {_88066 : Type'} (P : type1402 _88066) (x : _88066) (y : _88066) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3389983 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) (P : type1402 _88066) (x'' : _88066) (y : _88066) : (term468 _88066 _88069 x f s x' P x'' y) = (term469 _88066 _88069 x f s x' P x'' y).
Proof. exact (MK_COMB (@lem3389981 _88066 _88069 x'' x y f s x') (@lem3389982 _88066 P x'' y)). Qed.
Lemma lem3389984 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term470 _88066 _88069 x f s P x' y) = (term471 _88066 _88069 x f s P x' y).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3389983 _88066 _88069 x f s x'' P x' y)). Qed.
Lemma lem3389985 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389986 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term459 _88066 _88069 x f s P x' y) = (term472 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3389985 _88069) (@lem3389984 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389987 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : ((term458 _88066 _88069 x f s P x' y) = (term459 _88066 _88069 x f s P x' y)) = ((term454 _88066 _88069 x f s P x' y) = (term472 _88066 _88069 x f s P x' y)).
Proof. exact (MK_COMB (@lem3389978 _88066 _88069 x f s P x' y) (@lem3389986 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389988 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term454 _88066 _88069 x f s P x' y) = (term472 _88066 _88069 x f s P x' y).
Proof. exact (EQ_MP (@lem3389987 _88066 _88069 x f s P x' y) (@lem3389968 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3389989 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term456 _88066 _88069 f s P x y) = (term473 _88066 _88069 f s P x y).
Proof. exact (fun_ext (fun x' : _88069 => @lem3389988 _88066 _88069 x' f s P x y)). Qed.
Lemma lem3389990 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3389991 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term457 _88066 _88069 f s P x y) = (term474 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3389990 _88069) (@lem3389989 _88066 _88069 f s P x y)). Qed.
Lemma lem3389992 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term442 _88066 _88069 f s P x y) = (term474 _88066 _88069 f s P x y).
Proof. exact (TRANS (@lem3389964 _88066 _88069 f s P x y) (@lem3389991 _88066 _88069 f s P x y)). Qed.
Lemma lem3389993 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term97 _88066 _88069 f s P x y) = (term474 _88066 _88069 f s P x y).
Proof. exact (TRANS (@lem3389940 _88066 _88069 f s P x y) (@lem3389992 _88066 _88069 f s P x y)). Qed.
Lemma lem3389994 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term107 _88066 _88069 f s P x) = (term475 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3389993 _88066 _88069 f s P x y)). Qed.
Lemma lem3389995 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3389996 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term108 _88066 _88069 f s P x) = (term476 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3389995 _88066) (@lem3389994 _88066 _88069 f s P x)). Qed.
Lemma lem3389997 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term116 _88066 _88069 f s P) = (term477 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3389996 _88066 _88069 f s P x)). Qed.
Lemma lem3389998 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3389999 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term117 _88066 _88069 f s P) = (term478 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3389998 _88066) (@lem3389997 _88066 _88069 f s P)). Qed.
Lemma lem3390024 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (x' : _88069) (P : type1402 _88066) (x'' : _88066) (y : _88066) : (term469 _88066 _88069 x f s x' P x'' y) = (term469 _88066 _88069 x f s x' P x'' y).
Proof. exact (eq_refl (term469 _88066 _88069 x f s x' P x'' y)). Qed.
Lemma lem3390025 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term471 _88066 _88069 x f s P x' y) = (term471 _88066 _88069 x f s P x' y).
Proof. exact (fun_ext (fun x'' : _88069 => @lem3390024 _88066 _88069 x f s x'' P x' y)). Qed.
Lemma lem3390026 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3390027 {_88066 _88069 : Type'} (x : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x' : _88066) (y : _88066) : (term472 _88066 _88069 x f s P x' y) = (term472 _88066 _88069 x f s P x' y).
Proof. exact (MK_COMB (@lem3390026 _88069) (@lem3390025 _88066 _88069 x f s P x' y)). Qed.
Lemma lem3390028 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term473 _88066 _88069 f s P x y) = (term473 _88066 _88069 f s P x y).
Proof. exact (fun_ext (fun x' : _88069 => @lem3390027 _88066 _88069 x' f s P x y)). Qed.
Lemma lem3390029 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3390030 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) (y : _88066) : (term474 _88066 _88069 f s P x y) = (term474 _88066 _88069 f s P x y).
Proof. exact (MK_COMB (@lem3390029 _88069) (@lem3390028 _88066 _88069 f s P x y)). Qed.
Lemma lem3390031 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term475 _88066 _88069 f s P x) = (term475 _88066 _88069 f s P x).
Proof. exact (fun_ext (fun y : _88066 => @lem3390030 _88066 _88069 f s P x y)). Qed.
Lemma lem3390032 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3390033 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88066) : (term476 _88066 _88069 f s P x) = (term476 _88066 _88069 f s P x).
Proof. exact (MK_COMB (@lem3390032 _88066) (@lem3390031 _88066 _88069 f s P x)). Qed.
Lemma lem3390034 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term477 _88066 _88069 f s P) = (term477 _88066 _88069 f s P).
Proof. exact (fun_ext (fun x : _88066 => @lem3390033 _88066 _88069 f s P x)). Qed.
Lemma lem3390035 {_88066 : Type'} : (@all _88066) = (@all _88066).
Proof. exact (eq_refl (@all _88066)). Qed.
Lemma lem3390036 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term478 _88066 _88069 f s P) = (term478 _88066 _88069 f s P).
Proof. exact (MK_COMB (@lem3390035 _88066) (@lem3390034 _88066 _88069 f s P)). Qed.
Lemma lem3390037 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) : (term117 _88066 _88069 f s P) = (term478 _88066 _88069 f s P).
Proof. exact (TRANS (@lem3389999 _88066 _88069 f s P) (@lem3390036 _88066 _88069 f s P)). Qed.
Lemma lem3390038 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term478 _88066 _88069 f s P.
Proof. exact (EQ_MP (@lem3390037 _88066 _88069 f s P) (@lem3389874 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390064 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term125 _88066 _88069 s P x f y) = (term125 _88066 _88069 s P x f y).
Proof. exact (eq_refl (term125 _88066 _88069 s P x f y)). Qed.
Lemma lem3390065 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term133 _88066 _88069 s P x f) = (term133 _88066 _88069 s P x f).
Proof. exact (fun_ext (fun y : _88069 => @lem3390064 _88066 _88069 s P x f y)). Qed.
Lemma lem3390066 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3390067 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) : (term134 _88066 _88069 s P x f) = (term134 _88066 _88069 s P x f).
Proof. exact (MK_COMB (@lem3390066 _88069) (@lem3390065 _88066 _88069 s P x f)). Qed.
Lemma lem3390068 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term142 _88066 _88069 s P f) = (term142 _88066 _88069 s P f).
Proof. exact (fun_ext (fun x : _88069 => @lem3390067 _88066 _88069 s P x f)). Qed.
Lemma lem3390069 {_88069 : Type'} : (@all _88069) = (@all _88069).
Proof. exact (eq_refl (@all _88069)). Qed.
Lemma lem3390071 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term143 _88066 _88069 s P f) = (term143 _88066 _88069 s P f).
Proof. exact (MK_COMB (@lem3390069 _88069) (@lem3390068 _88066 _88069 s P f)). Qed.
Lemma lem3390072 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term143 _88066 _88069 s P f.
Proof. exact (EQ_MP (@lem3390071 _88066 _88069 s P f) (@lem3389879 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390093 {_88066 _88069 : Type'} (_35602 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term479 _88066 _88069 f s P _35602.
Proof. exact (@lem3390038 _88066 _88069 s P x f y h1 _35602). Qed.
Lemma lem3390094 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (_35602 : _88066) : (term479 _88066 _88069 f s P _35602) = (term476 _88066 _88069 f s P _35602).
Proof. exact (eq_refl (term479 _88066 _88069 f s P _35602)). Qed.
Lemma lem3390095 {_88066 _88069 : Type'} (_35602 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term476 _88066 _88069 f s P _35602.
Proof. exact (EQ_MP (@lem3390094 _88066 _88069 f s P _35602) (@lem3390093 _88066 _88069 _35602 s P x f y h1)). Qed.
Lemma lem3390096 {_88066 _88069 : Type'} (_35602 : _88066) (_35603 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term480 _88066 _88069 f s P _35602 _35603.
Proof. exact (@lem3390095 _88066 _88069 _35602 s P x f y h1 _35603). Qed.
Lemma lem3390097 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term480 _88066 _88069 f s P _35602 _35603) = (term474 _88066 _88069 f s P _35602 _35603).
Proof. exact (eq_refl (term480 _88066 _88069 f s P _35602 _35603)). Qed.
Lemma lem3390098 {_88066 _88069 : Type'} (_35602 : _88066) (_35603 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term474 _88066 _88069 f s P _35602 _35603.
Proof. exact (EQ_MP (@lem3390097 _88066 _88069 f s P _35602 _35603) (@lem3390096 _88066 _88069 _35602 _35603 s P x f y h1)). Qed.
Lemma lem3390099 {_88066 _88069 : Type'} (_35602 : _88066) (_35603 : _88066) (_35604 : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term481 _88066 _88069 f s P _35602 _35603 _35604.
Proof. exact (@lem3390098 _88066 _88069 _35602 _35603 s P x f y h1 _35604). Qed.
Lemma lem3390100 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term481 _88066 _88069 f s P _35602 _35603 _35604) = (term472 _88066 _88069 _35604 f s P _35602 _35603).
Proof. exact (eq_refl (term481 _88066 _88069 f s P _35602 _35603 _35604)). Qed.
Lemma lem3390101 {_88066 _88069 : Type'} (_35604 : _88069) (_35602 : _88066) (_35603 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term472 _88066 _88069 _35604 f s P _35602 _35603.
Proof. exact (EQ_MP (@lem3390100 _88066 _88069 _35604 f s P _35602 _35603) (@lem3390099 _88066 _88069 _35602 _35603 _35604 s P x f y h1)). Qed.
Lemma lem3390102 {_88066 _88069 : Type'} (_35604 : _88069) (_35602 : _88066) (_35603 : _88066) (_35605 : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term482 _88066 _88069 _35604 f s P _35602 _35603 _35605.
Proof. exact (@lem3390101 _88066 _88069 _35604 _35602 _35603 s P x f y h1 _35605). Qed.
Lemma lem3390103 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term482 _88066 _88069 _35604 f s P _35602 _35603 _35605) = (term469 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (eq_refl (term482 _88066 _88069 _35604 f s P _35602 _35603 _35605)). Qed.
Lemma lem3390104 {_88066 _88069 : Type'} (_35604 : _88069) (_35605 : _88069) (_35602 : _88066) (_35603 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term469 _88066 _88069 _35604 f s _35605 P _35602 _35603.
Proof. exact (EQ_MP (@lem3390103 _88066 _88069 _35604 f s _35605 P _35602 _35603) (@lem3390102 _88066 _88069 _35604 _35602 _35603 _35605 s P x f y h1)). Qed.
Lemma lem3390105 {_88066 _88069 : Type'} (_35606 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term483 _88066 _88069 s P f _35606.
Proof. exact (@lem3390072 _88066 _88069 x'' x''' x' y' s P f h1 _35606). Qed.
Lemma lem3390106 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) : (term483 _88066 _88069 s P f _35606) = (term134 _88066 _88069 s P _35606 f).
Proof. exact (eq_refl (term483 _88066 _88069 s P f _35606)). Qed.
Lemma lem3390107 {_88066 _88069 : Type'} (_35606 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term134 _88066 _88069 s P _35606 f.
Proof. exact (EQ_MP (@lem3390106 _88066 _88069 s P _35606 f) (@lem3390105 _88066 _88069 _35606 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390108 {_88066 _88069 : Type'} (_35606 : _88069) (_35607 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term484 _88066 _88069 s P _35606 f _35607.
Proof. exact (@lem3390107 _88066 _88069 _35606 x'' x''' x' y' s P f h1 _35607). Qed.
Lemma lem3390109 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (_35607 : _88069) : (term484 _88066 _88069 s P _35606 f _35607) = (term125 _88066 _88069 s P _35606 f _35607).
Proof. exact (eq_refl (term484 _88066 _88069 s P _35606 f _35607)). Qed.
Lemma lem3390110 {_88066 _88069 : Type'} (_35606 : _88069) (_35607 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term125 _88066 _88069 s P _35606 f _35607.
Proof. exact (EQ_MP (@lem3390109 _88066 _88069 s P _35606 f _35607) (@lem3390108 _88066 _88069 _35606 _35607 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390114 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term469 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term485 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (@lem3388264 (term75 _88066 _88069 _35602 f s _35604) (term75 _88066 _88069 _35603 f s _35605) (P _35602 _35603)). Qed.
Lemma lem3390121 {_88066 _88069 : Type'} (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term486 _88066 _88069 f s _35605 P _35602 _35603) = (term487 _88066 _88069 f s _35605 P _35602 _35603).
Proof. exact (@lem3388264 (term488 _88066 _88069 _35603 f _35605) (term489 _88069 s _35605) (P _35602 _35603)). Qed.
Lemma lem3390122 {_88066 _88069 : Type'} (_35602 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35604 : _88069) : (term422 _88066 _88069 _35602 f s _35604) = (term422 _88066 _88069 _35602 f s _35604).
Proof. exact (eq_refl (term422 _88066 _88069 _35602 f s _35604)). Qed.
Lemma lem3390123 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term485 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term490 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (MK_COMB (@lem3390122 _88066 _88069 _35602 f s _35604) (@lem3390121 _88066 _88069 f s _35605 P _35602 _35603)). Qed.
Lemma lem3390130 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term490 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term491 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (@lem3388264 (term488 _88066 _88069 _35602 f _35604) (term489 _88069 s _35604) (term487 _88066 _88069 f s _35605 P _35602 _35603)). Qed.
Lemma lem3390131 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term485 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term491 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (TRANS (@lem3390123 _88066 _88069 _35604 f s _35605 P _35602 _35603) (@lem3390130 _88066 _88069 _35604 f s _35605 P _35602 _35603)). Qed.
Lemma lem3390133 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term469 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term491 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (TRANS (@lem3390114 _88066 _88069 _35604 f s _35605 P _35602 _35603) (@lem3390131 _88066 _88069 _35604 f s _35605 P _35602 _35603)). Qed.
Lemma lem3390134 {_88066 _88069 : Type'} (_35604 : _88069) (_35605 : _88069) (_35602 : _88066) (_35603 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term491 _88066 _88069 _35604 f s _35605 P _35602 _35603.
Proof. exact (EQ_MP (@lem3390133 _88066 _88069 _35604 f s _35605 P _35602 _35603) (@lem3390104 _88066 _88069 _35604 _35605 _35602 _35603 s P x f y h1)). Qed.
Lemma lem3390136 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term492 _88066 _88069 P x f y.
Proof. exact (proj2 (@lem3389873 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390151 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (_35607 : _88069) : (term125 _88066 _88069 s P _35606 f _35607) = (term493 _88066 _88069 s P _35606 f _35607).
Proof. exact (@lem3388264 (term489 _88069 s _35606) (term489 _88069 s _35607) (term41 _88066 _88069 P _35606 f _35607)). Qed.
Lemma lem3390154 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term90 _88066 P x' y'.
Proof. exact (proj2 (@lem3389880 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390160 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : x' = (f x'').
Proof. exact (proj1 (@lem3389884 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390191 {_88066 : Type'} (P : type1402 _88066) (y' : _88066) : (term494 _88066 P y') = (term494 _88066 P y').
Proof. exact (eq_refl (term494 _88066 P y')). Qed.
Lemma lem3390192 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : (term495 _88066 P y' x') = (term496 _88066 _88069 P y' f x'').
Proof. exact (MK_COMB (@lem3390191 _88066 P y') (@lem3390160 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390193 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : (term496 _88066 _88069 P y' f x'') = (term497 _88066 _88069 P f x'' y').
Proof. exact (eq_refl (term496 _88066 _88069 P y' f x'')). Qed.
Lemma lem3390194 {_88066 : Type'} (P : type1402 _88066) (y' : _88066) (x' : _88066) : (term498 _88066 P y' x') = (term498 _88066 P y' x').
Proof. exact (eq_refl (term498 _88066 P y' x')). Qed.
Lemma lem3390195 {_88066 _88069 : Type'} (x' : _88066) (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : ((term495 _88066 P y' x') = (term496 _88066 _88069 P y' f x'')) = ((term495 _88066 P y' x') = (term497 _88066 _88069 P f x'' y')).
Proof. exact (MK_COMB (@lem3390194 _88066 P y' x') (@lem3390193 _88066 _88069 P f x'' y')). Qed.
Lemma lem3390196 {_88066 : Type'} (P : type1402 _88066) (x' : _88066) (y' : _88066) : (term495 _88066 P y' x') = (term90 _88066 P x' y').
Proof. exact (eq_refl (term495 _88066 P y' x')). Qed.
Lemma lem3390197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3390198 {_88066 : Type'} (P : type1402 _88066) (x' : _88066) (y' : _88066) : (term498 _88066 P y' x') = (term499 _88066 P x' y').
Proof. exact (MK_COMB (@lem3390197) (@lem3390196 _88066 P x' y')). Qed.
Lemma lem3390199 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : (term497 _88066 _88069 P f x'' y') = (term497 _88066 _88069 P f x'' y').
Proof. exact (eq_refl (term497 _88066 _88069 P f x'' y')). Qed.
Lemma lem3390200 {_88066 _88069 : Type'} (x' : _88066) (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : ((term495 _88066 P y' x') = (term497 _88066 _88069 P f x'' y')) = ((term90 _88066 P x' y') = (term497 _88066 _88069 P f x'' y')).
Proof. exact (MK_COMB (@lem3390198 _88066 P x' y') (@lem3390199 _88066 _88069 P f x'' y')). Qed.
Lemma lem3390201 {_88066 _88069 : Type'} (x' : _88066) (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : ((term495 _88066 P y' x') = (term496 _88066 _88069 P y' f x'')) = ((term90 _88066 P x' y') = (term497 _88066 _88069 P f x'' y')).
Proof. exact (TRANS (@lem3390195 _88066 _88069 x' P f x'' y') (@lem3390200 _88066 _88069 x' P f x'' y')). Qed.
Lemma lem3390202 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : (term90 _88066 P x' y') = (term497 _88066 _88069 P f x'' y').
Proof. exact (EQ_MP (@lem3390201 _88066 _88069 x' P f x'' y') (@lem3390192 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390203 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term497 _88066 _88069 P f x'' y'.
Proof. exact (EQ_MP (@lem3390202 _88066 _88069 x'' x''' x' y' s P f h1) (@lem3390154 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390217 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : y' = (f x''').
Proof. exact (proj1 (@lem3389883 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390273 {_88066 _88069 : Type'} (_35606 : _88069) (_35607 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term493 _88066 _88069 s P _35606 f _35607.
Proof. exact (EQ_MP (@lem3390151 _88066 _88069 s P _35606 f _35607) (@lem3390110 _88066 _88069 _35606 _35607 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390274 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) : (term500 _88066 _88069 P f x'') = (term500 _88066 _88069 P f x'').
Proof. exact (eq_refl (term500 _88066 _88069 P f x'')). Qed.
Lemma lem3390275 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : (term501 _88066 _88069 P f x'' y') = (term502 _88066 _88069 P x'' f x''').
Proof. exact (MK_COMB (@lem3390274 _88066 _88069 P f x'') (@lem3390217 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390276 {_88066 _88069 : Type'} (P : type1402 _88066) (x'' : _88069) (f : _88069 -> _88066) (x''' : _88069) : (term502 _88066 _88069 P x'' f x''') = (term492 _88066 _88069 P x'' f x''').
Proof. exact (eq_refl (term502 _88066 _88069 P x'' f x''')). Qed.
Lemma lem3390277 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : (term503 _88066 _88069 P f x'' y') = (term503 _88066 _88069 P f x'' y').
Proof. exact (eq_refl (term503 _88066 _88069 P f x'' y')). Qed.
Lemma lem3390278 {_88066 _88069 : Type'} (y' : _88066) (P : type1402 _88066) (x'' : _88069) (f : _88069 -> _88066) (x''' : _88069) : ((term501 _88066 _88069 P f x'' y') = (term502 _88066 _88069 P x'' f x''')) = ((term501 _88066 _88069 P f x'' y') = (term492 _88066 _88069 P x'' f x''')).
Proof. exact (MK_COMB (@lem3390277 _88066 _88069 P f x'' y') (@lem3390276 _88066 _88069 P x'' f x''')). Qed.
Lemma lem3390279 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : (term501 _88066 _88069 P f x'' y') = (term497 _88066 _88069 P f x'' y').
Proof. exact (eq_refl (term501 _88066 _88069 P f x'' y')). Qed.
Lemma lem3390280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3390281 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (x'' : _88069) (y' : _88066) : (term503 _88066 _88069 P f x'' y') = (term504 _88066 _88069 P f x'' y').
Proof. exact (MK_COMB (@lem3390280) (@lem3390279 _88066 _88069 P f x'' y')). Qed.
Lemma lem3390282 {_88066 _88069 : Type'} (P : type1402 _88066) (x'' : _88069) (f : _88069 -> _88066) (x''' : _88069) : (term492 _88066 _88069 P x'' f x''') = (term492 _88066 _88069 P x'' f x''').
Proof. exact (eq_refl (term492 _88066 _88069 P x'' f x''')). Qed.
Lemma lem3390283 {_88066 _88069 : Type'} (y' : _88066) (P : type1402 _88066) (x'' : _88069) (f : _88069 -> _88066) (x''' : _88069) : ((term501 _88066 _88069 P f x'' y') = (term492 _88066 _88069 P x'' f x''')) = ((term497 _88066 _88069 P f x'' y') = (term492 _88066 _88069 P x'' f x''')).
Proof. exact (MK_COMB (@lem3390281 _88066 _88069 P f x'' y') (@lem3390282 _88066 _88069 P x'' f x''')). Qed.
Lemma lem3390284 {_88066 _88069 : Type'} (y' : _88066) (P : type1402 _88066) (x'' : _88069) (f : _88069 -> _88066) (x''' : _88069) : ((term501 _88066 _88069 P f x'' y') = (term502 _88066 _88069 P x'' f x''')) = ((term497 _88066 _88069 P f x'' y') = (term492 _88066 _88069 P x'' f x''')).
Proof. exact (TRANS (@lem3390278 _88066 _88069 y' P x'' f x''') (@lem3390283 _88066 _88069 y' P x'' f x''')). Qed.
Lemma lem3390285 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : (term497 _88066 _88069 P f x'' y') = (term492 _88066 _88069 P x'' f x''').
Proof. exact (EQ_MP (@lem3390284 _88066 _88069 y' P x'' f x''') (@lem3390275 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390286 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term492 _88066 _88069 P x'' f x'''.
Proof. exact (EQ_MP (@lem3390285 _88066 _88069 x'' x''' x' y' s P f h1) (@lem3390203 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390359 {_88066 : Type'} (x : _88066) : x = x.
Proof. exact (@lem21386 _88066 x). Qed.
Lemma lem3390360 {_88066 : Type'} (x : _88066) : x = x.
Proof. exact (@lem3390359 _88066 x). Qed.
Lemma lem3390361 {_88066 _88069 : Type'} (f : _88069 -> _88066) (x : _88069) : (f x) = (f x).
Proof. exact (@lem3390360 _88066 (f x)). Qed.
Lemma lem3390362 {_88066 _88069 : Type'} (f : _88069 -> _88066) (x : _88069) : term505 _88066 _88069 f x.
Proof. exact (fun h0 : term506 _88066 _88069 f x => @lem3390361 _88066 _88069 f x). Qed.
Lemma lem3390364 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390365 {_88066 _88069 : Type'} (f : _88069 -> _88066) (x : _88069) : (term505 _88066 _88069 f x) = ((f x) = (f x)).
Proof. exact (@lem3390364 ((f x) = (f x))). Qed.
Lemma lem3390366 {_88066 _88069 : Type'} (f : _88069 -> _88066) (x : _88069) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3390365 _88066 _88069 f x) (@lem3390362 _88066 _88069 f x)). Qed.
Lemma lem3390368 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : s x.
Proof. exact (proj1 (@lem3389876 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390369 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term508 _88069 s x.
Proof. exact (fun h0 : term489 _88069 s x => @lem3390368 _88066 _88069 s P x f y h1). Qed.
Lemma lem3390371 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390372 {_88069 : Type'} (s : _88069 -> Prop) (x : _88069) : (term508 _88069 s x) = (s x).
Proof. exact (@lem3390371 (s x)). Qed.
Lemma lem3390373 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : s x.
Proof. exact (EQ_MP (@lem3390372 _88069 s x) (@lem3390369 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390375 {_88066 : Type'} (x : _88066) : x = x.
Proof. exact (@lem21386 _88066 x). Qed.
Lemma lem3390376 {_88066 : Type'} (x : _88066) : x = x.
Proof. exact (@lem3390375 _88066 x). Qed.
Lemma lem3390377 {_88066 _88069 : Type'} (f : _88069 -> _88066) (y : _88069) : (f y) = (f y).
Proof. exact (@lem3390376 _88066 (f y)). Qed.
Lemma lem3390378 {_88066 _88069 : Type'} (f : _88069 -> _88066) (y : _88069) : term505 _88066 _88069 f y.
Proof. exact (fun h0 : term506 _88066 _88069 f y => @lem3390377 _88066 _88069 f y). Qed.
Lemma lem3390380 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390381 {_88066 _88069 : Type'} (f : _88069 -> _88066) (y : _88069) : (term505 _88066 _88069 f y) = ((f y) = (f y)).
Proof. exact (@lem3390380 ((f y) = (f y))). Qed.
Lemma lem3390382 {_88066 _88069 : Type'} (f : _88069 -> _88066) (y : _88069) : (f y) = (f y).
Proof. exact (EQ_MP (@lem3390381 _88066 _88069 f y) (@lem3390378 _88066 _88069 f y)). Qed.
Lemma lem3390384 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : s y.
Proof. exact (proj2 (@lem3389876 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390385 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term508 _88069 s y.
Proof. exact (fun h0 : term489 _88069 s y => @lem3390384 _88066 _88069 s P x f y h1). Qed.
Lemma lem3390387 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390388 {_88069 : Type'} (s : _88069 -> Prop) (y : _88069) : (term508 _88069 s y) = (s y).
Proof. exact (@lem3390387 (s y)). Qed.
Lemma lem3390389 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : s y.
Proof. exact (EQ_MP (@lem3390388 _88069 s y) (@lem3390385 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390395 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390396 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term491 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term509 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (@lem3390395 (term489 _88069 s _35604) (term488 _88066 _88069 _35602 f _35604) (term487 _88066 _88069 f s _35605 P _35602 _35603)). Qed.
Lemma lem3390422 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390423 {_88066 _88069 : Type'} (s : _88069 -> Prop) (f : _88069 -> _88066) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term487 _88066 _88069 f s _35605 P _35602 _35603) = (term510 _88066 _88069 s f _35605 P _35602 _35603).
Proof. exact (@lem3390422 (term489 _88069 s _35605) (term488 _88066 _88069 _35603 f _35605) (P _35602 _35603)). Qed.
Lemma lem3390437 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3390438 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term511 _88066 _88069 f _35605 P _35602 _35603) = (term512 _88066 _88069 P _35602 _35603 f _35605).
Proof. exact (@lem3390437 (P _35602 _35603) (term488 _88066 _88069 _35603 f _35605)). Qed.
Lemma lem3390446 {_88069 : Type'} (s : _88069 -> Prop) (_35605 : _88069) : (term513 _88069 s _35605) = (term513 _88069 s _35605).
Proof. exact (eq_refl (term513 _88069 s _35605)). Qed.
Lemma lem3390447 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term510 _88066 _88069 s f _35605 P _35602 _35603) = (term514 _88066 _88069 s P _35602 _35603 f _35605).
Proof. exact (MK_COMB (@lem3390446 _88069 s _35605) (@lem3390438 _88066 _88069 P _35602 _35603 f _35605)). Qed.
Lemma lem3390451 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390452 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (s : _88069 -> Prop) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term514 _88066 _88069 s P _35602 _35603 f _35605) = (term515 _88066 _88069 P _35602 s _35603 f _35605).
Proof. exact (@lem3390451 (P _35602 _35603) (term489 _88069 s _35605) (term488 _88066 _88069 _35603 f _35605)). Qed.
Lemma lem3390470 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (s : _88069 -> Prop) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term510 _88066 _88069 s f _35605 P _35602 _35603) = (term515 _88066 _88069 P _35602 s _35603 f _35605).
Proof. exact (TRANS (@lem3390447 _88066 _88069 s P _35602 _35603 f _35605) (@lem3390452 _88066 _88069 P _35602 s _35603 f _35605)). Qed.
Lemma lem3390471 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (s : _88069 -> Prop) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term487 _88066 _88069 f s _35605 P _35602 _35603) = (term515 _88066 _88069 P _35602 s _35603 f _35605).
Proof. exact (TRANS (@lem3390423 _88066 _88069 s f _35605 P _35602 _35603) (@lem3390470 _88066 _88069 P _35602 s _35603 f _35605)). Qed.
Lemma lem3390472 {_88066 _88069 : Type'} (_35602 : _88066) (f : _88069 -> _88066) (_35604 : _88069) : (term516 _88066 _88069 _35602 f _35604) = (term516 _88066 _88069 _35602 f _35604).
Proof. exact (eq_refl (term516 _88066 _88069 _35602 f _35604)). Qed.
Lemma lem3390473 {_88066 _88069 : Type'} (_35604 : _88069) (P : type1402 _88066) (_35602 : _88066) (s : _88069 -> Prop) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term517 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term518 _88066 _88069 _35604 P _35602 s _35603 f _35605).
Proof. exact (MK_COMB (@lem3390472 _88066 _88069 _35602 f _35604) (@lem3390471 _88066 _88069 P _35602 s _35603 f _35605)). Qed.
Lemma lem3390477 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390478 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35604 : _88069) (s : _88069 -> Prop) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term518 _88066 _88069 _35604 P _35602 s _35603 f _35605) = (term519 _88066 _88069 P _35602 _35604 s _35603 f _35605).
Proof. exact (@lem3390477 (P _35602 _35603) (term488 _88066 _88069 _35602 f _35604) (term520 _88066 _88069 s _35603 f _35605)). Qed.
Lemma lem3390492 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390493 {_88066 _88069 : Type'} (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term521 _88066 _88069 _35602 _35604 s _35603 f _35605) = (term522 _88066 _88069 s _35602 _35604 _35603 f _35605).
Proof. exact (@lem3390492 (term489 _88069 s _35605) (term488 _88066 _88069 _35602 f _35604) (term488 _88066 _88069 _35603 f _35605)). Qed.
Lemma lem3390513 {_88066 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term523 _88066 P _35602 _35603) = (term523 _88066 P _35602 _35603).
Proof. exact (eq_refl (term523 _88066 P _35602 _35603)). Qed.
Lemma lem3390514 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term519 _88066 _88069 P _35602 _35604 s _35603 f _35605) = (term524 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (MK_COMB (@lem3390513 _88066 P _35602 _35603) (@lem3390493 _88066 _88069 s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390525 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term518 _88066 _88069 _35604 P _35602 s _35603 f _35605) = (term524 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (TRANS (@lem3390478 _88066 _88069 P _35602 _35604 s _35603 f _35605) (@lem3390514 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390526 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term517 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term524 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (TRANS (@lem3390473 _88066 _88069 _35604 P _35602 s _35603 f _35605) (@lem3390525 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390527 {_88069 : Type'} (s : _88069 -> Prop) (_35604 : _88069) : (term513 _88069 s _35604) = (term513 _88069 s _35604).
Proof. exact (eq_refl (term513 _88069 s _35604)). Qed.
Lemma lem3390528 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term509 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term525 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (MK_COMB (@lem3390527 _88069 s _35604) (@lem3390526 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390532 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390533 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term525 _88066 _88069 P s _35602 _35604 _35603 f _35605) = (term526 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (@lem3390532 (P _35602 _35603) (term489 _88069 s _35604) (term522 _88066 _88069 s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390573 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term509 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term526 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (TRANS (@lem3390528 _88066 _88069 P s _35602 _35604 _35603 f _35605) (@lem3390533 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390574 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term491 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term526 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (TRANS (@lem3390396 _88066 _88069 _35604 f s _35605 P _35602 _35603) (@lem3390573 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3390576 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term527 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term528 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (MK_COMB (@lem3390575) (@lem3390574 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390590 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390591 {_88066 _88069 : Type'} (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term529 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term530 _88066 _88069 _35602 _35604 _35603 f s _35605).
Proof. exact (@lem3390590 (term489 _88069 s _35604) (term488 _88066 _88069 _35602 f _35604) (term75 _88066 _88069 _35603 f s _35605)). Qed.
Lemma lem3390617 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3390618 {_88066 _88069 : Type'} (s : _88069 -> Prop) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term75 _88066 _88069 _35603 f s _35605) = (term520 _88066 _88069 s _35603 f _35605).
Proof. exact (@lem3390617 (term489 _88069 s _35605) (term488 _88066 _88069 _35603 f _35605)). Qed.
Lemma lem3390626 {_88066 _88069 : Type'} (_35602 : _88066) (f : _88069 -> _88066) (_35604 : _88069) : (term516 _88066 _88069 _35602 f _35604) = (term516 _88066 _88069 _35602 f _35604).
Proof. exact (eq_refl (term516 _88066 _88069 _35602 f _35604)). Qed.
Lemma lem3390627 {_88066 _88069 : Type'} (_35602 : _88066) (_35604 : _88069) (s : _88069 -> Prop) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term531 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term521 _88066 _88069 _35602 _35604 s _35603 f _35605).
Proof. exact (MK_COMB (@lem3390626 _88066 _88069 _35602 f _35604) (@lem3390618 _88066 _88069 s _35603 f _35605)). Qed.
Lemma lem3390631 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390632 {_88066 _88069 : Type'} (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term521 _88066 _88069 _35602 _35604 s _35603 f _35605) = (term522 _88066 _88069 s _35602 _35604 _35603 f _35605).
Proof. exact (@lem3390631 (term489 _88069 s _35605) (term488 _88066 _88069 _35602 f _35604) (term488 _88066 _88069 _35603 f _35605)). Qed.
Lemma lem3390652 {_88066 _88069 : Type'} (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term531 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term522 _88066 _88069 s _35602 _35604 _35603 f _35605).
Proof. exact (TRANS (@lem3390627 _88066 _88069 _35602 _35604 s _35603 f _35605) (@lem3390632 _88066 _88069 s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390653 {_88069 : Type'} (s : _88069 -> Prop) (_35604 : _88069) : (term513 _88069 s _35604) = (term513 _88069 s _35604).
Proof. exact (eq_refl (term513 _88069 s _35604)). Qed.
Lemma lem3390654 {_88066 _88069 : Type'} (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term530 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term532 _88066 _88069 s _35602 _35604 _35603 f _35605).
Proof. exact (MK_COMB (@lem3390653 _88069 s _35604) (@lem3390652 _88066 _88069 s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390665 {_88066 _88069 : Type'} (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term529 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term532 _88066 _88069 s _35602 _35604 _35603 f _35605).
Proof. exact (TRANS (@lem3390591 _88066 _88069 _35602 _35604 _35603 f s _35605) (@lem3390654 _88066 _88069 s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390666 {_88066 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term523 _88066 P _35602 _35603) = (term523 _88066 P _35602 _35603).
Proof. exact (eq_refl (term523 _88066 P _35602 _35603)). Qed.
Lemma lem3390667 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term533 _88066 _88069 P _35602 _35604 _35603 f s _35605) = (term526 _88066 _88069 P s _35602 _35604 _35603 f _35605).
Proof. exact (MK_COMB (@lem3390666 _88066 P _35602 _35603) (@lem3390665 _88066 _88069 s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390678 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : ((term491 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term533 _88066 _88069 P _35602 _35604 _35603 f s _35605)) = ((term526 _88066 _88069 P s _35602 _35604 _35603 f _35605) = (term526 _88066 _88069 P s _35602 _35604 _35603 f _35605)).
Proof. exact (MK_COMB (@lem3390576 _88066 _88069 P s _35602 _35604 _35603 f _35605) (@lem3390667 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390680 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3390681 (x : Prop) : (x = x) = True.
Proof. exact (@lem3390680 Prop x). Qed.
Lemma lem3390682 {_88066 _88069 : Type'} (P : type1402 _88066) (s : _88069 -> Prop) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : ((term526 _88066 _88069 P s _35602 _35604 _35603 f _35605) = (term526 _88066 _88069 P s _35602 _35604 _35603 f _35605)) = True.
Proof. exact (@lem3390681 (term526 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390683 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : ((term491 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term533 _88066 _88069 P _35602 _35604 _35603 f s _35605)) = True.
Proof. exact (TRANS (@lem3390678 _88066 _88069 P s _35602 _35604 _35603 f _35605) (@lem3390682 _88066 _88069 P s _35602 _35604 _35603 f _35605)). Qed.
Lemma lem3390684 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : True = ((term491 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term533 _88066 _88069 P _35602 _35604 _35603 f s _35605)).
Proof. exact (SYM (@lem3390683 _88066 _88069 P _35602 _35604 _35603 f s _35605)). Qed.
Lemma lem3390685 {_88066 _88069 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term491 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term533 _88066 _88069 P _35602 _35604 _35603 f s _35605).
Proof. exact (EQ_MP (@lem3390684 _88066 _88069 P _35602 _35604 _35603 f s _35605) (@lem0)). Qed.
Lemma lem3390686 {_88066 _88069 : Type'} (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (_35605 : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term533 _88066 _88069 P _35602 _35604 _35603 f s _35605.
Proof. exact (EQ_MP (@lem3390685 _88066 _88069 P _35602 _35604 _35603 f s _35605) (@lem3390134 _88066 _88069 _35604 _35605 _35602 _35603 s P x f y h1)). Qed.
Lemma lem3390688 (b : Prop) (a : Prop) : (a \/ b) = (term534 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3390689 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term533 _88066 _88069 P _35602 _35604 _35603 f s _35605) = (term535 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (@lem3390688 (term529 _88066 _88069 _35602 _35604 _35603 f s _35605) (P _35602 _35603)). Qed.
Lemma lem3390691 (a : Prop) (b : Prop) : (term536 a b) = (term537 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3390692 {_88066 _88069 : Type'} (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term538 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term539 _88066 _88069 _35602 _35604 _35603 f s _35605).
Proof. exact (@lem3390691 (term488 _88066 _88069 _35602 f _35604) (term540 _88066 _88069 _35604 _35603 f s _35605)). Qed.
Lemma lem3390694 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3390695 {_88066 _88069 : Type'} (_35602 : _88066) (f : _88069 -> _88066) (_35604 : _88069) : (term541 _88066 _88069 _35602 f _35604) = (_35602 = (f _35604)).
Proof. exact (@lem3390694 (_35602 = (f _35604))). Qed.
Lemma lem3390696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3390697 {_88066 _88069 : Type'} (_35602 : _88066) (f : _88069 -> _88066) (_35604 : _88069) : (term542 _88066 _88069 _35602 f _35604) = (term11 _88066 _88069 _35602 f _35604).
Proof. exact (MK_COMB (@lem3390696) (@lem3390695 _88066 _88069 _35602 f _35604)). Qed.
Lemma lem3390699 (a : Prop) (b : Prop) : (term536 a b) = (term537 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3390700 {_88066 _88069 : Type'} (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term543 _88066 _88069 _35604 _35603 f s _35605) = (term544 _88066 _88069 _35604 _35603 f s _35605).
Proof. exact (@lem3390699 (term489 _88069 s _35604) (term75 _88066 _88069 _35603 f s _35605)). Qed.
Lemma lem3390702 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3390703 {_88069 : Type'} (s : _88069 -> Prop) (_35604 : _88069) : (term545 _88069 s _35604) = (s _35604).
Proof. exact (@lem3390702 (s _35604)). Qed.
Lemma lem3390704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3390705 {_88069 : Type'} (s : _88069 -> Prop) (_35604 : _88069) : (term546 _88069 s _35604) = (term36 _88069 s _35604).
Proof. exact (MK_COMB (@lem3390704) (@lem3390703 _88069 s _35604)). Qed.
Lemma lem3390707 (a : Prop) (b : Prop) : (term536 a b) = (term537 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3390708 {_88066 _88069 : Type'} (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term547 _88066 _88069 _35603 f s _35605) = (term548 _88066 _88069 _35603 f s _35605).
Proof. exact (@lem3390707 (term488 _88066 _88069 _35603 f _35605) (term489 _88069 s _35605)). Qed.
Lemma lem3390710 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3390711 {_88066 _88069 : Type'} (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term541 _88066 _88069 _35603 f _35605) = (_35603 = (f _35605)).
Proof. exact (@lem3390710 (_35603 = (f _35605))). Qed.
Lemma lem3390712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3390713 {_88066 _88069 : Type'} (_35603 : _88066) (f : _88069 -> _88066) (_35605 : _88069) : (term542 _88066 _88069 _35603 f _35605) = (term11 _88066 _88069 _35603 f _35605).
Proof. exact (MK_COMB (@lem3390712) (@lem3390711 _88066 _88069 _35603 f _35605)). Qed.
Lemma lem3390715 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3390716 {_88069 : Type'} (s : _88069 -> Prop) (_35605 : _88069) : (term545 _88069 s _35605) = (s _35605).
Proof. exact (@lem3390715 (s _35605)). Qed.
Lemma lem3390717 {_88066 _88069 : Type'} (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term548 _88066 _88069 _35603 f s _35605) = (term13 _88066 _88069 _35603 f s _35605).
Proof. exact (MK_COMB (@lem3390713 _88066 _88069 _35603 f _35605) (@lem3390716 _88069 s _35605)). Qed.
Lemma lem3390718 {_88066 _88069 : Type'} (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term547 _88066 _88069 _35603 f s _35605) = (term13 _88066 _88069 _35603 f s _35605).
Proof. exact (TRANS (@lem3390708 _88066 _88069 _35603 f s _35605) (@lem3390717 _88066 _88069 _35603 f s _35605)). Qed.
Lemma lem3390719 {_88066 _88069 : Type'} (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term544 _88066 _88069 _35604 _35603 f s _35605) = (term549 _88066 _88069 _35604 _35603 f s _35605).
Proof. exact (MK_COMB (@lem3390705 _88069 s _35604) (@lem3390718 _88066 _88069 _35603 f s _35605)). Qed.
Lemma lem3390720 {_88066 _88069 : Type'} (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term543 _88066 _88069 _35604 _35603 f s _35605) = (term549 _88066 _88069 _35604 _35603 f s _35605).
Proof. exact (TRANS (@lem3390700 _88066 _88069 _35604 _35603 f s _35605) (@lem3390719 _88066 _88069 _35604 _35603 f s _35605)). Qed.
Lemma lem3390721 {_88066 _88069 : Type'} (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term539 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term550 _88066 _88069 _35602 _35604 _35603 f s _35605).
Proof. exact (MK_COMB (@lem3390697 _88066 _88069 _35602 f _35604) (@lem3390720 _88066 _88069 _35604 _35603 f s _35605)). Qed.
Lemma lem3390722 {_88066 _88069 : Type'} (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term538 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term550 _88066 _88069 _35602 _35604 _35603 f s _35605).
Proof. exact (TRANS (@lem3390692 _88066 _88069 _35602 _35604 _35603 f s _35605) (@lem3390721 _88066 _88069 _35602 _35604 _35603 f s _35605)). Qed.
Lemma lem3390723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3390724 {_88066 _88069 : Type'} (_35602 : _88066) (_35604 : _88069) (_35603 : _88066) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) : (term551 _88066 _88069 _35602 _35604 _35603 f s _35605) = (term552 _88066 _88069 _35602 _35604 _35603 f s _35605).
Proof. exact (MK_COMB (@lem3390723) (@lem3390722 _88066 _88069 _35602 _35604 _35603 f s _35605)). Qed.
Lemma lem3390725 {_88066 : Type'} (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (P _35602 _35603) = (P _35602 _35603).
Proof. exact (eq_refl (P _35602 _35603)). Qed.
Lemma lem3390726 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term535 _88066 _88069 _35604 f s _35605 P _35602 _35603) = (term553 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (MK_COMB (@lem3390724 _88066 _88069 _35602 _35604 _35603 f s _35605) (@lem3390725 _88066 P _35602 _35603)). Qed.
Lemma lem3390727 {_88066 _88069 : Type'} (_35604 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35605 : _88069) (P : type1402 _88066) (_35602 : _88066) (_35603 : _88066) : (term533 _88066 _88069 P _35602 _35604 _35603 f s _35605) = (term553 _88066 _88069 _35604 f s _35605 P _35602 _35603).
Proof. exact (TRANS (@lem3390689 _88066 _88069 _35604 f s _35605 P _35602 _35603) (@lem3390726 _88066 _88069 _35604 f s _35605 P _35602 _35603)). Qed.
Lemma lem3390729 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term554 _88066 _88069 f s y.
Proof. exact (conj (@lem3390382 _88066 _88069 f y) (@lem3390389 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390730 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term555 _88066 _88069 x f s y.
Proof. exact (conj (@lem3390373 _88066 _88069 s P x f y h1) (@lem3390729 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390731 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term556 _88066 _88069 x f s y.
Proof. exact (conj (@lem3390366 _88066 _88069 f x) (@lem3390730 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390733 {_88066 _88069 : Type'} (_35604 : _88069) (_35605 : _88069) (_35602 : _88066) (_35603 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term553 _88066 _88069 _35604 f s _35605 P _35602 _35603.
Proof. exact (EQ_MP (@lem3390727 _88066 _88069 _35604 f s _35605 P _35602 _35603) (@lem3390686 _88066 _88069 _35602 _35604 _35603 _35605 s P x f y h1)). Qed.
Lemma lem3390734 {_88066 _88069 : Type'} (_35604 : _88069) (_35605 : _88069) (_35602 : _88066) (_35603 : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term553 _88066 _88069 _35604 f s _35605 P _35602 _35603.
Proof. exact (@lem3390733 _88066 _88069 _35604 _35605 _35602 _35603 s P x f y h1). Qed.
Lemma lem3390735 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term557 _88066 _88069 s P x f y.
Proof. exact (@lem3390734 _88066 _88069 x y (f x) (f y) s P x f y h1). Qed.
Lemma lem3390738 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term41 _88066 _88069 P x f y.
Proof. exact (@lem3390735 _88066 _88069 s P x f y h1 (@lem3390731 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390739 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term558 _88066 _88069 P x f y.
Proof. exact (fun h0 : term492 _88066 _88069 P x f y => @lem3390738 _88066 _88069 s P x f y h1). Qed.
Lemma lem3390741 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390742 {_88066 _88069 : Type'} (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term558 _88066 _88069 P x f y) = (term41 _88066 _88069 P x f y).
Proof. exact (@lem3390741 (term41 _88066 _88069 P x f y)). Qed.
Lemma lem3390743 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term41 _88066 _88069 P x f y.
Proof. exact (EQ_MP (@lem3390742 _88066 _88069 P x f y) (@lem3390739 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390746 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3390748 {_88066 _88069 : Type'} (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) : (term492 _88066 _88069 P x f y) = (term559 _88066 _88069 P x f y).
Proof. exact (@lem3390746 (term41 _88066 _88069 P x f y)). Qed.
Lemma lem3390751 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term559 _88066 _88069 P x f y.
Proof. exact (EQ_MP (@lem3390748 _88066 _88069 P x f y) (@lem3390136 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390754 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : False.
Proof. exact (@lem3390751 _88066 _88069 s P x f y h1 (@lem3390743 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390755 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : term560.
Proof. exact (fun h0 : ~ False => @lem3390754 _88066 _88069 s P x f y h1). Qed.
Lemma lem3390757 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390758 : term560 = False.
Proof. exact (@lem3390757 False). Qed.
Lemma lem3390759 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (x : _88069) (f : _88069 -> _88066) (y : _88069) (h1 : term178 _88066 _88069 s P x f y) : False.
Proof. exact (EQ_MP (@lem3390758) (@lem3390755 _88066 _88069 s P x f y h1)). Qed.
Lemma lem3390761 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : s x''.
Proof. exact (proj2 (@lem3389884 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390762 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term508 _88069 s x''.
Proof. exact (fun h0 : term489 _88069 s x'' => @lem3390761 _88066 _88069 x'' x''' x' y' s P f h1). Qed.
Lemma lem3390764 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390765 {_88069 : Type'} (s : _88069 -> Prop) (x'' : _88069) : (term508 _88069 s x'') = (s x'').
Proof. exact (@lem3390764 (s x'')). Qed.
Lemma lem3390766 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : s x''.
Proof. exact (EQ_MP (@lem3390765 _88069 s x'') (@lem3390762 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390768 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : s x'''.
Proof. exact (proj2 (@lem3389883 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390769 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term508 _88069 s x'''.
Proof. exact (fun h0 : term489 _88069 s x''' => @lem3390768 _88066 _88069 x'' x''' x' y' s P f h1). Qed.
Lemma lem3390771 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390772 {_88069 : Type'} (s : _88069 -> Prop) (x''' : _88069) : (term508 _88069 s x''') = (s x''').
Proof. exact (@lem3390771 (s x''')). Qed.
Lemma lem3390773 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : s x'''.
Proof. exact (EQ_MP (@lem3390772 _88069 s x''') (@lem3390769 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390789 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3390790 {_88066 _88069 : Type'} (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35607 : _88069) : (term561 _88066 _88069 s P _35606 f _35607) = (term562 _88066 _88069 P _35606 f s _35607).
Proof. exact (@lem3390789 (term41 _88066 _88069 P _35606 f _35607) (term489 _88069 s _35607)). Qed.
Lemma lem3390796 {_88069 : Type'} (s : _88069 -> Prop) (_35606 : _88069) : (term513 _88069 s _35606) = (term513 _88069 s _35606).
Proof. exact (eq_refl (term513 _88069 s _35606)). Qed.
Lemma lem3390797 {_88066 _88069 : Type'} (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (s : _88069 -> Prop) (_35607 : _88069) : (term493 _88066 _88069 s P _35606 f _35607) = (term563 _88066 _88069 P _35606 f s _35607).
Proof. exact (MK_COMB (@lem3390796 _88069 s _35606) (@lem3390790 _88066 _88069 P _35606 f s _35607)). Qed.
Lemma lem3390801 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3390802 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term563 _88066 _88069 P _35606 f s _35607) = (term564 _88066 _88069 P f _35606 s _35607).
Proof. exact (@lem3390801 (term41 _88066 _88069 P _35606 f _35607) (term489 _88069 s _35606) (term489 _88069 s _35607)). Qed.
Lemma lem3390818 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term493 _88066 _88069 s P _35606 f _35607) = (term564 _88066 _88069 P f _35606 s _35607).
Proof. exact (TRANS (@lem3390797 _88066 _88069 P _35606 f s _35607) (@lem3390802 _88066 _88069 P f _35606 s _35607)). Qed.
Lemma lem3390819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3390820 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term565 _88066 _88069 s P _35606 f _35607) = (term566 _88066 _88069 P f _35606 s _35607).
Proof. exact (MK_COMB (@lem3390819) (@lem3390818 _88066 _88069 P f _35606 s _35607)). Qed.
Lemma lem3390836 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term564 _88066 _88069 P f _35606 s _35607) = (term564 _88066 _88069 P f _35606 s _35607).
Proof. exact (eq_refl (term564 _88066 _88069 P f _35606 s _35607)). Qed.
Lemma lem3390837 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : ((term493 _88066 _88069 s P _35606 f _35607) = (term564 _88066 _88069 P f _35606 s _35607)) = ((term564 _88066 _88069 P f _35606 s _35607) = (term564 _88066 _88069 P f _35606 s _35607)).
Proof. exact (MK_COMB (@lem3390820 _88066 _88069 P f _35606 s _35607) (@lem3390836 _88066 _88069 P f _35606 s _35607)). Qed.
Lemma lem3390839 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3390840 (x : Prop) : (x = x) = True.
Proof. exact (@lem3390839 Prop x). Qed.
Lemma lem3390841 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : ((term564 _88066 _88069 P f _35606 s _35607) = (term564 _88066 _88069 P f _35606 s _35607)) = True.
Proof. exact (@lem3390840 (term564 _88066 _88069 P f _35606 s _35607)). Qed.
Lemma lem3390842 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : ((term493 _88066 _88069 s P _35606 f _35607) = (term564 _88066 _88069 P f _35606 s _35607)) = True.
Proof. exact (TRANS (@lem3390837 _88066 _88069 P f _35606 s _35607) (@lem3390841 _88066 _88069 P f _35606 s _35607)). Qed.
Lemma lem3390843 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : True = ((term493 _88066 _88069 s P _35606 f _35607) = (term564 _88066 _88069 P f _35606 s _35607)).
Proof. exact (SYM (@lem3390842 _88066 _88069 P f _35606 s _35607)). Qed.
Lemma lem3390844 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term493 _88066 _88069 s P _35606 f _35607) = (term564 _88066 _88069 P f _35606 s _35607).
Proof. exact (EQ_MP (@lem3390843 _88066 _88069 P f _35606 s _35607) (@lem0)). Qed.
Lemma lem3390845 {_88066 _88069 : Type'} (_35606 : _88069) (_35607 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term564 _88066 _88069 P f _35606 s _35607.
Proof. exact (EQ_MP (@lem3390844 _88066 _88069 P f _35606 s _35607) (@lem3390273 _88066 _88069 _35606 _35607 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390847 (b : Prop) (a : Prop) : (a \/ b) = (term534 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3390848 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (_35607 : _88069) : (term564 _88066 _88069 P f _35606 s _35607) = (term567 _88066 _88069 s P _35606 f _35607).
Proof. exact (@lem3390847 (term119 _88069 _35606 s _35607) (term41 _88066 _88069 P _35606 f _35607)). Qed.
Lemma lem3390850 (a : Prop) (b : Prop) : (term536 a b) = (term537 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3390851 {_88069 : Type'} (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term568 _88069 _35606 s _35607) = (term569 _88069 _35606 s _35607).
Proof. exact (@lem3390850 (term489 _88069 s _35606) (term489 _88069 s _35607)). Qed.
Lemma lem3390853 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3390854 {_88069 : Type'} (s : _88069 -> Prop) (_35606 : _88069) : (term545 _88069 s _35606) = (s _35606).
Proof. exact (@lem3390853 (s _35606)). Qed.
Lemma lem3390855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3390856 {_88069 : Type'} (s : _88069 -> Prop) (_35606 : _88069) : (term546 _88069 s _35606) = (term36 _88069 s _35606).
Proof. exact (MK_COMB (@lem3390855) (@lem3390854 _88069 s _35606)). Qed.
Lemma lem3390858 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3390859 {_88069 : Type'} (s : _88069 -> Prop) (_35607 : _88069) : (term545 _88069 s _35607) = (s _35607).
Proof. exact (@lem3390858 (s _35607)). Qed.
Lemma lem3390860 {_88069 : Type'} (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term569 _88069 _35606 s _35607) = (term38 _88069 _35606 s _35607).
Proof. exact (MK_COMB (@lem3390856 _88069 s _35606) (@lem3390859 _88069 s _35607)). Qed.
Lemma lem3390861 {_88069 : Type'} (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term568 _88069 _35606 s _35607) = (term38 _88069 _35606 s _35607).
Proof. exact (TRANS (@lem3390851 _88069 _35606 s _35607) (@lem3390860 _88069 _35606 s _35607)). Qed.
Lemma lem3390862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3390863 {_88069 : Type'} (_35606 : _88069) (s : _88069 -> Prop) (_35607 : _88069) : (term570 _88069 _35606 s _35607) = (term40 _88069 _35606 s _35607).
Proof. exact (MK_COMB (@lem3390862) (@lem3390861 _88069 _35606 s _35607)). Qed.
Lemma lem3390864 {_88066 _88069 : Type'} (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (_35607 : _88069) : (term41 _88066 _88069 P _35606 f _35607) = (term41 _88066 _88069 P _35606 f _35607).
Proof. exact (eq_refl (term41 _88066 _88069 P _35606 f _35607)). Qed.
Lemma lem3390865 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (_35607 : _88069) : (term567 _88066 _88069 s P _35606 f _35607) = (term43 _88066 _88069 s P _35606 f _35607).
Proof. exact (MK_COMB (@lem3390863 _88069 _35606 s _35607) (@lem3390864 _88066 _88069 P _35606 f _35607)). Qed.
Lemma lem3390866 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (_35606 : _88069) (f : _88069 -> _88066) (_35607 : _88069) : (term564 _88066 _88069 P f _35606 s _35607) = (term43 _88066 _88069 s P _35606 f _35607).
Proof. exact (TRANS (@lem3390848 _88066 _88069 s P _35606 f _35607) (@lem3390865 _88066 _88069 s P _35606 f _35607)). Qed.
Lemma lem3390868 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term38 _88069 x'' s x'''.
Proof. exact (conj (@lem3390766 _88066 _88069 x'' x''' x' y' s P f h1) (@lem3390773 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390870 {_88066 _88069 : Type'} (_35606 : _88069) (_35607 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term43 _88066 _88069 s P _35606 f _35607.
Proof. exact (EQ_MP (@lem3390866 _88066 _88069 s P _35606 f _35607) (@lem3390845 _88066 _88069 _35606 _35607 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390871 {_88066 _88069 : Type'} (_35606 : _88069) (_35607 : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term43 _88066 _88069 s P _35606 f _35607.
Proof. exact (@lem3390870 _88066 _88069 _35606 _35607 x'' x''' x' y' s P f h1). Qed.
Lemma lem3390872 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term43 _88066 _88069 s P x'' f x'''.
Proof. exact (@lem3390871 _88066 _88069 x'' x''' x'' x''' x' y' s P f h1). Qed.
Lemma lem3390875 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term41 _88066 _88069 P x'' f x'''.
Proof. exact (@lem3390872 _88066 _88069 x'' x''' x' y' s P f h1 (@lem3390868 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390876 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term558 _88066 _88069 P x'' f x'''.
Proof. exact (fun h0 : term492 _88066 _88069 P x'' f x''' => @lem3390875 _88066 _88069 x'' x''' x' y' s P f h1). Qed.
Lemma lem3390878 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390879 {_88066 _88069 : Type'} (P : type1402 _88066) (x'' : _88069) (f : _88069 -> _88066) (x''' : _88069) : (term558 _88066 _88069 P x'' f x''') = (term41 _88066 _88069 P x'' f x''').
Proof. exact (@lem3390878 (term41 _88066 _88069 P x'' f x''')). Qed.
Lemma lem3390880 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term41 _88066 _88069 P x'' f x'''.
Proof. exact (EQ_MP (@lem3390879 _88066 _88069 P x'' f x''') (@lem3390876 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390883 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3390885 {_88066 _88069 : Type'} (P : type1402 _88066) (x'' : _88069) (f : _88069 -> _88066) (x''' : _88069) : (term492 _88066 _88069 P x'' f x''') = (term559 _88066 _88069 P x'' f x''').
Proof. exact (@lem3390883 (term41 _88066 _88069 P x'' f x''')). Qed.
Lemma lem3390888 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term559 _88066 _88069 P x'' f x'''.
Proof. exact (EQ_MP (@lem3390885 _88066 _88069 P x'' f x''') (@lem3390286 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390891 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : False.
Proof. exact (@lem3390888 _88066 _88069 x'' x''' x' y' s P f h1 (@lem3390880 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390892 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : term560.
Proof. exact (fun h0 : ~ False => @lem3390891 _88066 _88069 x'' x''' x' y' s P f h1). Qed.
Lemma lem3390894 (p : Prop) : (term507 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3390895 : term560 = False.
Proof. exact (@lem3390894 False). Qed.
Lemma lem3390898 {_88066 _88069 : Type'} (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term308 _88066 _88069 x'' x''' x' y' s P f) : False.
Proof. exact (EQ_MP (@lem3390895) (@lem3390892 _88066 _88069 x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390899 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term397 _88066 _88069 x y x'' x''' x' y' s P f) : False.
Proof. exact (or_elim (@lem3389870 _88066 _88069 x y x'' x''' x' y' s P f h1) (fun h0 : term178 _88066 _88069 s P x f y => @lem3390759 _88066 _88069 s P x f y h0) (fun h0 : term308 _88066 _88069 x'' x''' x' y' s P f => @lem3390898 _88066 _88069 x'' x''' x' y' s P f h0)). Qed.
Lemma lem3390900 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term397 _88066 _88069 x y x'' x''' x' y' s P f) : (term397 _88066 _88069 x y x'' x''' x' y' s P f) = False.
Proof. exact (prop_ext (fun h2 : term397 _88066 _88069 x y x'' x''' x' y' s P f => @lem3390899 _88066 _88069 x y x'' x''' x' y' s P f h1) (fun h2 : False => @lem3389870 _88066 _88069 x y x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390901 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x''' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term397 _88066 _88069 x y x'' x''' x' y' s P f) : False.
Proof. exact (EQ_MP (@lem3390900 _88066 _88069 x y x'' x''' x' y' s P f h1) (@lem3389870 _88066 _88069 x y x'' x''' x' y' s P f h1)). Qed.
Lemma lem3390902 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x'' : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term400 _88066 _88069 x y x'' x' y' s P f) : False.
Proof. exact (ex_elim (@lem3389709 _88066 _88069 x y x'' x' y' s P f h1) (fun x''' : _88069 => fun h0 : term399 _88066 _88069 x y x'' x' y' s P f x''' => @lem3390901 _88066 _88069 x y x'' x''' x' y' s P f h0)). Qed.
Lemma lem3390903 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (y' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term402 _88066 _88069 x y x' y' s P f) : False.
Proof. exact (ex_elim (@lem3389708 _88066 _88069 x y x' y' s P f h1) (fun x'' : _88069 => fun h0 : term401 _88066 _88069 x y x' y' s P f x'' => @lem3390902 _88066 _88069 x y x'' x' y' s P f h0)). Qed.
Lemma lem3390904 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (x' : _88066) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term404 _88066 _88069 x y x' s P f) : False.
Proof. exact (ex_elim (@lem3389707 _88066 _88069 x y x' s P f h1) (fun y' : _88066 => fun h0 : term403 _88066 _88069 x y x' s P f y' => @lem3390903 _88066 _88069 x y x' y' s P f h0)). Qed.
Lemma lem3390905 {_88066 _88069 : Type'} (x : _88069) (y : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term406 _88066 _88069 x y s P f) : False.
Proof. exact (ex_elim (@lem3389706 _88066 _88069 x y s P f h1) (fun x' : _88066 => fun h0 : term405 _88066 _88069 x y s P f x' => @lem3390904 _88066 _88069 x y x' s P f h0)). Qed.
Lemma lem3390906 {_88066 _88069 : Type'} (x : _88069) (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term408 _88066 _88069 x s P f) : False.
Proof. exact (ex_elim (@lem3389705 _88066 _88069 x s P f h1) (fun y : _88069 => fun h0 : term407 _88066 _88069 x s P f y => @lem3390905 _88066 _88069 x y s P f h0)). Qed.
Lemma lem3390907 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term73 _88066 _88069 s P f) : False.
Proof. exact (ex_elim (@lem3389704 _88066 _88069 s P f h1) (fun x : _88069 => fun h0 : term409 _88066 _88069 s P f x => @lem3390906 _88066 _88069 x s P f h0)). Qed.
Lemma lem3390908 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term73 _88066 _88069 s P f) : (term73 _88066 _88069 s P f) = False.
Proof. exact (prop_ext (fun h2 : term73 _88066 _88069 s P f => @lem3390907 _88066 _88069 s P f h1) (fun h2 : False => @lem3388751 _88066 _88069 s P f h1)). Qed.
Lemma lem3390909 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) (h1 : term73 _88066 _88069 s P f) : False.
Proof. exact (EQ_MP (@lem3390908 _88066 _88069 s P f h1) (@lem3388751 _88066 _88069 s P f h1)). Qed.
Lemma lem3390910 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : term72 _88066 _88069 s P f.
Proof. exact (fun h0 : term73 _88066 _88069 s P f => @lem3390909 _88066 _88069 s P f h0). Qed.
Lemma lem3390911 {_88066 _88069 : Type'} (s : _88069 -> Prop) (P : type1402 _88066) (f : _88069 -> _88066) : (term32 _88066 _88069 f s P) = (term51 _88066 _88069 s P f).
Proof. exact (EQ_MP (@lem3388750 _88066 _88069 s P f) (@lem3390910 _88066 _88069 s P f)). Qed.
Lemma lem3390916 {_88066 _88069 : Type'} (P : type1402 _88066) (f : _88069 -> _88066) : term55 _88066 _88069 P f.
Proof. exact (fun s : _88069 -> Prop => @lem3390911 _88066 _88069 s P f). Qed.
Lemma lem3390921 {_88066 _88069 : Type'} (f : _88069 -> _88066) : term59 _88066 _88069 f.
Proof. exact (fun P : type1402 _88066 => @lem3390916 _88066 _88069 P f). Qed.
Lemma lem3390926 {_88066 _88069 : Type'} : term63 _88066 _88069.
Proof. exact (fun f : _88069 -> _88066 => @lem3390921 _88066 _88069 f). Qed.
Lemma lem3390927 {_88066 _88069 : Type'} : term65 _88066 _88069.
Proof. exact (EQ_MP (@lem3388746 _88066 _88069) (@lem3390926 _88066 _88069)). Qed.
Lemma lem3390929 {_88066 _88069 : Type'} : term65 _88066 _88069.
Proof. exact (@lem3388505 _88066 _88069 (@lem3390927 _88066 _88069)). Qed.
Lemma lem3390930 {_88066 _88069 : Type'} (h1 : term66 _88066 _88069) : False.
Proof. exact (@lem3390929 _88066 _88069 (@lem3388489 _88066 _88069 h1)). Qed.
Lemma lem3390931 {_88066 _88069 : Type'} (h1 : term66 _88066 _88069) : (term66 _88066 _88069) = False.
Proof. exact (prop_ext (fun h2 : term66 _88066 _88069 => @lem3390930 _88066 _88069 h1) (fun h2 : False => @lem3388489 _88066 _88069 h1)). Qed.
Lemma lem3390932 {_88066 _88069 : Type'} (h1 : term66 _88066 _88069) : False.
Proof. exact (EQ_MP (@lem3390931 _88066 _88069 h1) (@lem3388489 _88066 _88069 h1)). Qed.
Lemma lem3390933 {_88066 _88069 : Type'} : term65 _88066 _88069.
Proof. exact (fun h0 : term66 _88066 _88069 => @lem3390932 _88066 _88069 h0). Qed.
Lemma lem3390934 {_88066 _88069 : Type'} : term63 _88066 _88069.
Proof. exact (EQ_MP (@lem3388488 _88066 _88069) (@lem3390933 _88066 _88069)). Qed.
Lemma lem3390936 {_88066 _88069 : Type'} : term62 _88066 _88069.
Proof. exact (EQ_MP (@lem3388484 _88066 _88069) (@lem3390934 _88066 _88069)). Qed.
