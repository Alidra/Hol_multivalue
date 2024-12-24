Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FUN_IN_IMAGE_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm18394_spec.
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
Lemma lem3397344 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3397345 {_88224 : Type'} (P : _88224 -> Prop) (x : _88224) : (@IN _88224 x P) = (P x).
Proof. exact (@lem3397344 _88224 P x). Qed.
Lemma lem3397346 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) : (@IN _88224 x s) = (s x).
Proof. exact (@lem3397345 _88224 s x). Qed.
Lemma lem3397347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3397348 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) : (term0 _88224 x s) = (term1 _88224 s x).
Proof. exact (MK_COMB (@lem3397347) (@lem3397346 _88224 s x)). Qed.
Lemma lem3397350 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term2 A B y f s) = (term3 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3397351 {_88224 _88228 : Type'} (y : _88228) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term2 _88224 _88228 y f s) = (term3 _88224 _88228 y f s).
Proof. exact (@lem3397350 _88224 _88228 y f s). Qed.
Lemma lem3397352 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term4 _88224 _88228 x f s) = (term5 _88224 _88228 x f s).
Proof. exact (@lem3397351 _88224 _88228 (f x) f s). Qed.
Lemma lem3397362 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3397363 {_88224 : Type'} (P : _88224 -> Prop) (x : _88224) : (@IN _88224 x P) = (P x).
Proof. exact (@lem3397362 _88224 P x). Qed.
Lemma lem3397364 {_88224 : Type'} (s : _88224 -> Prop) (x' : _88224) : (@IN _88224 x' s) = (s x').
Proof. exact (@lem3397363 _88224 s x'). Qed.
Lemma lem3397365 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (x' : _88224) : (term6 _88224 _88228 x f x') = (term6 _88224 _88228 x f x').
Proof. exact (eq_refl (term6 _88224 _88228 x f x')). Qed.
Lemma lem3397366 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term7 _88224 _88228 x f x' s) = (term8 _88224 _88228 x f s x').
Proof. exact (MK_COMB (@lem3397365 _88224 _88228 x f x') (@lem3397364 _88224 s x')). Qed.
Lemma lem3397369 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term9 _88224 _88228 x f s) = (term10 _88224 _88228 x f s).
Proof. exact (fun_ext (fun x' : _88224 => @lem3397366 _88224 _88228 x f s x')). Qed.
Lemma lem3397370 {_88224 : Type'} : (@ex _88224) = (@ex _88224).
Proof. exact (eq_refl (@ex _88224)). Qed.
Lemma lem3397371 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term5 _88224 _88228 x f s) = (term11 _88224 _88228 x f s).
Proof. exact (MK_COMB (@lem3397370 _88224) (@lem3397369 _88224 _88228 x f s)). Qed.
Lemma lem3397376 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term4 _88224 _88228 x f s) = (term11 _88224 _88228 x f s).
Proof. exact (TRANS (@lem3397352 _88224 _88228 x f s) (@lem3397371 _88224 _88228 x f s)). Qed.
Lemma lem3397377 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term12 _88224 _88228 x f s) = (term13 _88224 _88228 x f s).
Proof. exact (MK_COMB (@lem3397348 _88224 s x) (@lem3397376 _88224 _88228 x f s)). Qed.
Lemma lem3397380 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) : (term14 _88224 _88228 f s) = (term15 _88224 _88228 f s).
Proof. exact (fun_ext (fun x : _88224 => @lem3397377 _88224 _88228 x f s)). Qed.
Lemma lem3397381 {_88224 : Type'} : (@all _88224) = (@all _88224).
Proof. exact (eq_refl (@all _88224)). Qed.
Lemma lem3397382 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) : (term16 _88224 _88228 f s) = (term17 _88224 _88228 f s).
Proof. exact (MK_COMB (@lem3397381 _88224) (@lem3397380 _88224 _88228 f s)). Qed.
Lemma lem3397387 {_88224 _88228 : Type'} (f : _88224 -> _88228) : (term18 _88224 _88228 f) = (term19 _88224 _88228 f).
Proof. exact (fun_ext (fun s : _88224 -> Prop => @lem3397382 _88224 _88228 f s)). Qed.
Lemma lem3397388 {_88224 : Type'} : (@all (_88224 -> Prop)) = (@all (_88224 -> Prop)).
Proof. exact (eq_refl (@all (_88224 -> Prop))). Qed.
Lemma lem3397389 {_88224 _88228 : Type'} (f : _88224 -> _88228) : (term20 _88224 _88228 f) = (term21 _88224 _88228 f).
Proof. exact (MK_COMB (@lem3397388 _88224) (@lem3397387 _88224 _88228 f)). Qed.
Lemma lem3397394 {_88224 _88228 : Type'} : (term22 _88224 _88228) = (term23 _88224 _88228).
Proof. exact (fun_ext (fun f : _88224 -> _88228 => @lem3397389 _88224 _88228 f)). Qed.
Lemma lem3397395 {_88224 _88228 : Type'} : (@all (_88224 -> _88228)) = (@all (_88224 -> _88228)).
Proof. exact (eq_refl (@all (_88224 -> _88228))). Qed.
Lemma lem3397396 {_88224 _88228 : Type'} : (term24 _88224 _88228) = (term25 _88224 _88228).
Proof. exact (MK_COMB (@lem3397395 _88224 _88228) (@lem3397394 _88224 _88228)). Qed.
Lemma lem3397401 {_88224 _88228 : Type'} : (term25 _88224 _88228) = (term24 _88224 _88228).
Proof. exact (SYM (@lem3397396 _88224 _88228)). Qed.
Lemma lem3397403 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3397404 {_88224 _88228 : Type'} : (term25 _88224 _88228) = (term27 _88224 _88228).
Proof. exact (@lem3397403 (term25 _88224 _88228)). Qed.
Lemma lem3397405 {_88224 _88228 : Type'} : (term27 _88224 _88228) = (term25 _88224 _88228).
Proof. exact (SYM (@lem3397404 _88224 _88228)). Qed.
Lemma lem3397406 {_88224 _88228 : Type'} (h1 : term28 _88224 _88228) : term28 _88224 _88228.
Proof. exact (h1). Qed.
Lemma lem3397409 {_88224 _88228 : Type'} (h1 : term27 _88224 _88228) : term27 _88224 _88228.
Proof. exact (h1). Qed.
Lemma lem3397410 {_88224 _88228 : Type'} : term29 _88224 _88228.
Proof. exact (fun h0 : term27 _88224 _88228 => @lem3397409 _88224 _88228 h0). Qed.
Lemma lem3397411 {_88224 _88228 : Type'} (h1 : term29 _88224 _88228) : term29 _88224 _88228.
Proof. exact (h1). Qed.
Lemma lem3397412 {_88224 _88228 : Type'} (h1 : term27 _88224 _88228) : term27 _88224 _88228.
Proof. exact (h1). Qed.
Lemma lem3397413 {_88224 _88228 : Type'} (h1 : term27 _88224 _88228) (h2 : term29 _88224 _88228) : term27 _88224 _88228.
Proof. exact (@lem3397411 _88224 _88228 h2 (@lem3397412 _88224 _88228 h1)). Qed.
Lemma lem3397414 {_88224 _88228 : Type'} (h1 : term27 _88224 _88228) : term30 _88224 _88228.
Proof. exact (fun h0 : term29 _88224 _88228 => @lem3397413 _88224 _88228 h1 h0). Qed.
Lemma lem3397415 {_88224 _88228 : Type'} (h1 : term29 _88224 _88228) : term29 _88224 _88228.
Proof. exact (h1). Qed.
Lemma lem3397416 {_88224 _88228 : Type'} (h1 : term27 _88224 _88228) (h2 : term29 _88224 _88228) : term27 _88224 _88228.
Proof. exact (@lem3397414 _88224 _88228 h1 (@lem3397415 _88224 _88228 h2)). Qed.
Lemma lem3397417 {_88224 _88228 : Type'} (h1 : term29 _88224 _88228) : term29 _88224 _88228.
Proof. exact (fun h0 : term27 _88224 _88228 => @lem3397416 _88224 _88228 h0 h1). Qed.
Lemma lem3397418 {_88224 _88228 : Type'} : term31 _88224 _88228.
Proof. exact (fun h0 : term29 _88224 _88228 => @lem3397417 _88224 _88228 h0). Qed.
Lemma lem3397421 {_88224 _88228 : Type'} : term29 _88224 _88228.
Proof. exact (@lem3397418 _88224 _88228 (@lem3397410 _88224 _88228)). Qed.
Lemma lem3397422 {_88224 _88228 : Type'} : term29 _88224 _88228.
Proof. exact (@lem3397421 _88224 _88228). Qed.
Lemma lem3397424 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3397425 {_88224 _88228 : Type'} : (term27 _88224 _88228) = (term32 _88224 _88228).
Proof. exact (@lem3397424 (term28 _88224 _88228)). Qed.
Lemma lem3397427 (t : Prop) : (term33 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3397428 {_88224 _88228 : Type'} : (term32 _88224 _88228) = (term25 _88224 _88228).
Proof. exact (@lem3397427 (term25 _88224 _88228)). Qed.
Lemma lem3397481 {_88224 _88228 : Type'} : (term27 _88224 _88228) = (term25 _88224 _88228).
Proof. exact (TRANS (@lem3397425 _88224 _88228) (@lem3397428 _88224 _88228)). Qed.
Lemma lem3397486 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term8 _88224 _88228 x f s x') = (term8 _88224 _88228 x f s x').
Proof. exact (eq_refl (term8 _88224 _88228 x f s x')). Qed.
Lemma lem3397487 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term10 _88224 _88228 x f s) = (term10 _88224 _88228 x f s).
Proof. exact (fun_ext (fun x' : _88224 => @lem3397486 _88224 _88228 x f s x')). Qed.
Lemma lem3397488 {_88224 : Type'} : (@ex _88224) = (@ex _88224).
Proof. exact (eq_refl (@ex _88224)). Qed.
Lemma lem3397489 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term11 _88224 _88228 x f s) = (term11 _88224 _88228 x f s).
Proof. exact (MK_COMB (@lem3397488 _88224) (@lem3397487 _88224 _88228 x f s)). Qed.
Lemma lem3397492 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) : (term1 _88224 s x) = (term1 _88224 s x).
Proof. exact (eq_refl (term1 _88224 s x)). Qed.
Lemma lem3397493 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term13 _88224 _88228 x f s) = (term13 _88224 _88228 x f s).
Proof. exact (MK_COMB (@lem3397492 _88224 s x) (@lem3397489 _88224 _88228 x f s)). Qed.
Lemma lem3397494 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) : (term15 _88224 _88228 f s) = (term15 _88224 _88228 f s).
Proof. exact (fun_ext (fun x : _88224 => @lem3397493 _88224 _88228 x f s)). Qed.
Lemma lem3397495 {_88224 : Type'} : (@all _88224) = (@all _88224).
Proof. exact (eq_refl (@all _88224)). Qed.
Lemma lem3397496 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) : (term17 _88224 _88228 f s) = (term17 _88224 _88228 f s).
Proof. exact (MK_COMB (@lem3397495 _88224) (@lem3397494 _88224 _88228 f s)). Qed.
Lemma lem3397497 {_88224 _88228 : Type'} (f : _88224 -> _88228) : (term19 _88224 _88228 f) = (term19 _88224 _88228 f).
Proof. exact (fun_ext (fun s : _88224 -> Prop => @lem3397496 _88224 _88228 f s)). Qed.
Lemma lem3397498 {_88224 : Type'} : (@all (_88224 -> Prop)) = (@all (_88224 -> Prop)).
Proof. exact (eq_refl (@all (_88224 -> Prop))). Qed.
Lemma lem3397499 {_88224 _88228 : Type'} (f : _88224 -> _88228) : (term21 _88224 _88228 f) = (term21 _88224 _88228 f).
Proof. exact (MK_COMB (@lem3397498 _88224) (@lem3397497 _88224 _88228 f)). Qed.
Lemma lem3397500 {_88224 _88228 : Type'} : (term23 _88224 _88228) = (term23 _88224 _88228).
Proof. exact (fun_ext (fun f : _88224 -> _88228 => @lem3397499 _88224 _88228 f)). Qed.
Lemma lem3397501 {_88224 _88228 : Type'} : (@all (_88224 -> _88228)) = (@all (_88224 -> _88228)).
Proof. exact (eq_refl (@all (_88224 -> _88228))). Qed.
Lemma lem3397502 {_88224 _88228 : Type'} : (term25 _88224 _88228) = (term25 _88224 _88228).
Proof. exact (MK_COMB (@lem3397501 _88224 _88228) (@lem3397500 _88224 _88228)). Qed.
Lemma lem3397533 {_88224 _88228 : Type'} : (term27 _88224 _88228) = (term25 _88224 _88228).
Proof. exact (TRANS (@lem3397481 _88224 _88228) (@lem3397502 _88224 _88228)). Qed.
Lemma lem3397534 {_88224 _88228 : Type'} : (term25 _88224 _88228) = (term27 _88224 _88228).
Proof. exact (SYM (@lem3397533 _88224 _88228)). Qed.
Lemma lem3397537 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3397538 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term11 _88224 _88228 x f s) = (term34 _88224 _88228 x f s).
Proof. exact (@lem3397537 (term11 _88224 _88228 x f s)). Qed.
Lemma lem3397539 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term34 _88224 _88228 x f s) = (term11 _88224 _88228 x f s).
Proof. exact (SYM (@lem3397538 _88224 _88228 x f s)). Qed.
Lemma lem3397540 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term35 _88224 _88228 x f s.
Proof. exact (h1). Qed.
Lemma lem3397546 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3397553 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term36 _88224 _88228 x f s x') = (term37 _88224 _88228 x f s x').
Proof. exact (@lem17045 ((f x) = (f x')) (s x')). Qed.
Lemma lem3397554 {_88224 : Type'} (P : _88224 -> Prop) : (term38 _88224 P) = (term39 _88224 P).
Proof. exact (@lem18394 _88224 P). Qed.
Lemma lem3397555 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term35 _88224 _88228 x f s) = (term40 _88224 _88228 x f s).
Proof. exact (@lem3397554 _88224 (term10 _88224 _88228 x f s)). Qed.
Lemma lem3397556 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term41 _88224 _88228 x f s x') = (term8 _88224 _88228 x f s x').
Proof. exact (eq_refl (term41 _88224 _88228 x f s x')). Qed.
Lemma lem3397557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3397558 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term42 _88224 _88228 x f s x') = (term36 _88224 _88228 x f s x').
Proof. exact (MK_COMB (@lem3397557) (@lem3397556 _88224 _88228 x f s x')). Qed.
Lemma lem3397559 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term42 _88224 _88228 x f s x') = (term37 _88224 _88228 x f s x').
Proof. exact (TRANS (@lem3397558 _88224 _88228 x f s x') (@lem3397553 _88224 _88228 x f s x')). Qed.
Lemma lem3397560 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term43 _88224 _88228 x f s) = (term44 _88224 _88228 x f s).
Proof. exact (fun_ext (fun x' : _88224 => @lem3397559 _88224 _88228 x f s x')). Qed.
Lemma lem3397561 {_88224 : Type'} : (@all _88224) = (@all _88224).
Proof. exact (eq_refl (@all _88224)). Qed.
Lemma lem3397562 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term40 _88224 _88228 x f s) = (term45 _88224 _88228 x f s).
Proof. exact (MK_COMB (@lem3397561 _88224) (@lem3397560 _88224 _88228 x f s)). Qed.
Lemma lem3397615 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term35 _88224 _88228 x f s) = (term45 _88224 _88228 x f s).
Proof. exact (TRANS (@lem3397555 _88224 _88228 x f s) (@lem3397562 _88224 _88228 x f s)). Qed.
Lemma lem3397616 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term45 _88224 _88228 x f s.
Proof. exact (EQ_MP (@lem3397615 _88224 _88228 x f s) (@lem3397540 _88224 _88228 x f s h1)). Qed.
Lemma lem3397620 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3397639 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term37 _88224 _88228 x f s x') = (term37 _88224 _88228 x f s x').
Proof. exact (eq_refl (term37 _88224 _88228 x f s x')). Qed.
Lemma lem3397640 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term44 _88224 _88228 x f s) = (term44 _88224 _88228 x f s).
Proof. exact (fun_ext (fun x' : _88224 => @lem3397639 _88224 _88228 x f s x')). Qed.
Lemma lem3397641 {_88224 : Type'} : (@all _88224) = (@all _88224).
Proof. exact (eq_refl (@all _88224)). Qed.
Lemma lem3397642 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term45 _88224 _88228 x f s) = (term45 _88224 _88228 x f s).
Proof. exact (MK_COMB (@lem3397641 _88224) (@lem3397640 _88224 _88228 x f s)). Qed.
Lemma lem3397643 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term45 _88224 _88228 x f s.
Proof. exact (EQ_MP (@lem3397642 _88224 _88228 x f s) (@lem3397616 _88224 _88228 x f s h1)). Qed.
Lemma lem3397647 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3397655 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (x' : _88224) : (term37 _88224 _88228 x f s x') = (term37 _88224 _88228 x f s x').
Proof. exact (eq_refl (term37 _88224 _88228 x f s x')). Qed.
Lemma lem3397656 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term44 _88224 _88228 x f s) = (term44 _88224 _88228 x f s).
Proof. exact (fun_ext (fun x' : _88224 => @lem3397655 _88224 _88228 x f s x')). Qed.
Lemma lem3397657 {_88224 : Type'} : (@all _88224) = (@all _88224).
Proof. exact (eq_refl (@all _88224)). Qed.
Lemma lem3397659 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : (term45 _88224 _88228 x f s) = (term45 _88224 _88228 x f s).
Proof. exact (MK_COMB (@lem3397657 _88224) (@lem3397656 _88224 _88228 x f s)). Qed.
Lemma lem3397660 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term45 _88224 _88228 x f s.
Proof. exact (EQ_MP (@lem3397659 _88224 _88228 x f s) (@lem3397643 _88224 _88228 x f s h1)). Qed.
Lemma lem3397661 {_88224 _88228 : Type'} (_35798 : _88224) (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term46 _88224 _88228 x f s _35798.
Proof. exact (@lem3397660 _88224 _88228 x f s h1 _35798). Qed.
Lemma lem3397662 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (_35798 : _88224) : (term46 _88224 _88228 x f s _35798) = (term37 _88224 _88228 x f s _35798).
Proof. exact (eq_refl (term46 _88224 _88228 x f s _35798)). Qed.
Lemma lem3397665 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3397671 {_88224 _88228 : Type'} (_35798 : _88224) (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term37 _88224 _88228 x f s _35798.
Proof. exact (EQ_MP (@lem3397662 _88224 _88228 x f s _35798) (@lem3397661 _88224 _88228 _35798 x f s h1)). Qed.
Lemma lem3397697 {_88228 : Type'} (x : _88228) : x = x.
Proof. exact (@lem21386 _88228 x). Qed.
Lemma lem3397698 {_88228 : Type'} (x : _88228) : x = x.
Proof. exact (@lem3397697 _88228 x). Qed.
Lemma lem3397699 {_88224 _88228 : Type'} (f : _88224 -> _88228) (x : _88224) : (f x) = (f x).
Proof. exact (@lem3397698 _88228 (f x)). Qed.
Lemma lem3397700 {_88224 _88228 : Type'} (f : _88224 -> _88228) (x : _88224) : term47 _88224 _88228 f x.
Proof. exact (fun h0 : term48 _88224 _88228 f x => @lem3397699 _88224 _88228 f x). Qed.
Lemma lem3397702 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397703 {_88224 _88228 : Type'} (f : _88224 -> _88228) (x : _88224) : (term47 _88224 _88228 f x) = ((f x) = (f x)).
Proof. exact (@lem3397702 ((f x) = (f x))). Qed.
Lemma lem3397704 {_88224 _88228 : Type'} (f : _88224 -> _88228) (x : _88224) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3397703 _88224 _88228 f x) (@lem3397700 _88224 _88228 f x)). Qed.
Lemma lem3397706 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3397707 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) (h1 : s x) : term50 _88224 s x.
Proof. exact (fun h0 : term51 _88224 s x => @lem3397706 _88224 s x h1). Qed.
Lemma lem3397709 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397710 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) : (term50 _88224 s x) = (s x).
Proof. exact (@lem3397709 (s x)). Qed.
Lemma lem3397711 {_88224 : Type'} (s : _88224 -> Prop) (x : _88224) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3397710 _88224 s x) (@lem3397707 _88224 s x h1)). Qed.
Lemma lem3397713 (a : Prop) (b : Prop) : (term52 a b) = (term53 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3397714 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (_35798 : _88224) : (term37 _88224 _88228 x f s _35798) = (term36 _88224 _88228 x f s _35798).
Proof. exact (@lem3397713 ((f x) = (f _35798)) (s _35798)). Qed.
Lemma lem3397716 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3397717 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (_35798 : _88224) : (term36 _88224 _88228 x f s _35798) = (term54 _88224 _88228 x f s _35798).
Proof. exact (@lem3397716 (term8 _88224 _88228 x f s _35798)). Qed.
Lemma lem3397718 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (_35798 : _88224) : (term37 _88224 _88228 x f s _35798) = (term54 _88224 _88228 x f s _35798).
Proof. exact (TRANS (@lem3397714 _88224 _88228 x f s _35798) (@lem3397717 _88224 _88228 x f s _35798)). Qed.
Lemma lem3397720 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : s x) : term55 _88224 _88228 f s x.
Proof. exact (conj (@lem3397704 _88224 _88228 f x) (@lem3397711 _88224 s x h1)). Qed.
Lemma lem3397722 {_88224 _88228 : Type'} (_35798 : _88224) (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term54 _88224 _88228 x f s _35798.
Proof. exact (EQ_MP (@lem3397718 _88224 _88228 x f s _35798) (@lem3397671 _88224 _88228 _35798 x f s h1)). Qed.
Lemma lem3397723 {_88224 _88228 : Type'} (_35798 : _88224) (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term54 _88224 _88228 x f s _35798.
Proof. exact (@lem3397722 _88224 _88228 _35798 x f s h1). Qed.
Lemma lem3397724 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) (h1 : term35 _88224 _88228 x f s) : term56 _88224 _88228 f s x.
Proof. exact (@lem3397723 _88224 _88228 x x f s h1). Qed.
Lemma lem3397727 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (@lem3397724 _88224 _88228 x f s h1 (@lem3397720 _88224 _88228 f s x h2)). Qed.
Lemma lem3397728 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : term57.
Proof. exact (fun h0 : ~ False => @lem3397727 _88224 _88228 f s x h1 h2). Qed.
Lemma lem3397730 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397731 : term57 = False.
Proof. exact (@lem3397730 False). Qed.
Lemma lem3397732 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3397731) (@lem3397728 _88224 _88228 f s x h1 h2)). Qed.
Lemma lem3397733 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3397732 _88224 _88228 f s x h1 h2) (fun h3 : False => @lem3397665 _88224 s x h2)). Qed.
Lemma lem3397734 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3397733 _88224 _88228 f s x h1 h2) (@lem3397665 _88224 s x h2)). Qed.
Lemma lem3397735 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3397734 _88224 _88228 f s x h1 h2) (fun h3 : False => @lem3397647 _88224 s x h2)). Qed.
Lemma lem3397736 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3397735 _88224 _88228 f s x h1 h2) (@lem3397647 _88224 s x h2)). Qed.
Lemma lem3397737 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3397736 _88224 _88228 f s x h1 h2) (fun h3 : False => @lem3397647 _88224 s x h2)). Qed.
Lemma lem3397738 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3397737 _88224 _88228 f s x h1 h2) (@lem3397647 _88224 s x h2)). Qed.
Lemma lem3397739 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3397738 _88224 _88228 f s x h1 h2) (fun h3 : False => @lem3397620 _88224 s x h2)). Qed.
Lemma lem3397740 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3397739 _88224 _88228 f s x h1 h2) (@lem3397620 _88224 s x h2)). Qed.
Lemma lem3397741 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3397740 _88224 _88228 f s x h1 h2) (fun h3 : False => @lem3397546 _88224 s x h2)). Qed.
Lemma lem3397742 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3397741 _88224 _88228 f s x h1 h2) (@lem3397546 _88224 s x h2)). Qed.
Lemma lem3397743 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : (term35 _88224 _88228 x f s) = False.
Proof. exact (prop_ext (fun h3 : term35 _88224 _88228 x f s => @lem3397742 _88224 _88228 f s x h1 h2) (fun h3 : False => @lem3397540 _88224 _88228 x f s h1)). Qed.
Lemma lem3397744 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : term35 _88224 _88228 x f s) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3397743 _88224 _88228 f s x h1 h2) (@lem3397540 _88224 _88228 x f s h1)). Qed.
Lemma lem3397745 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : s x) : term34 _88224 _88228 x f s.
Proof. exact (fun h0 : term35 _88224 _88228 x f s => @lem3397744 _88224 _88228 f s x h0 h1). Qed.
Lemma lem3397746 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) (x : _88224) (h1 : s x) : term11 _88224 _88228 x f s.
Proof. exact (EQ_MP (@lem3397539 _88224 _88228 x f s) (@lem3397745 _88224 _88228 f s x h1)). Qed.
Lemma lem3397747 {_88224 _88228 : Type'} (x : _88224) (f : _88224 -> _88228) (s : _88224 -> Prop) : term13 _88224 _88228 x f s.
Proof. exact (fun h0 : s x => @lem3397746 _88224 _88228 f s x h0). Qed.
Lemma lem3397752 {_88224 _88228 : Type'} (f : _88224 -> _88228) (s : _88224 -> Prop) : term17 _88224 _88228 f s.
Proof. exact (fun x : _88224 => @lem3397747 _88224 _88228 x f s). Qed.
Lemma lem3397757 {_88224 _88228 : Type'} (f : _88224 -> _88228) : term21 _88224 _88228 f.
Proof. exact (fun s : _88224 -> Prop => @lem3397752 _88224 _88228 f s). Qed.
Lemma lem3397762 {_88224 _88228 : Type'} : term25 _88224 _88228.
Proof. exact (fun f : _88224 -> _88228 => @lem3397757 _88224 _88228 f). Qed.
Lemma lem3397763 {_88224 _88228 : Type'} : term27 _88224 _88228.
Proof. exact (EQ_MP (@lem3397534 _88224 _88228) (@lem3397762 _88224 _88228)). Qed.
Lemma lem3397765 {_88224 _88228 : Type'} : term27 _88224 _88228.
Proof. exact (@lem3397422 _88224 _88228 (@lem3397763 _88224 _88228)). Qed.
Lemma lem3397766 {_88224 _88228 : Type'} (h1 : term28 _88224 _88228) : False.
Proof. exact (@lem3397765 _88224 _88228 (@lem3397406 _88224 _88228 h1)). Qed.
Lemma lem3397767 {_88224 _88228 : Type'} (h1 : term28 _88224 _88228) : (term28 _88224 _88228) = False.
Proof. exact (prop_ext (fun h2 : term28 _88224 _88228 => @lem3397766 _88224 _88228 h1) (fun h2 : False => @lem3397406 _88224 _88228 h1)). Qed.
Lemma lem3397768 {_88224 _88228 : Type'} (h1 : term28 _88224 _88228) : False.
Proof. exact (EQ_MP (@lem3397767 _88224 _88228 h1) (@lem3397406 _88224 _88228 h1)). Qed.
Lemma lem3397769 {_88224 _88228 : Type'} : term27 _88224 _88228.
Proof. exact (fun h0 : term28 _88224 _88228 => @lem3397768 _88224 _88228 h0). Qed.
Lemma lem3397770 {_88224 _88228 : Type'} : term25 _88224 _88228.
Proof. exact (EQ_MP (@lem3397405 _88224 _88228) (@lem3397769 _88224 _88228)). Qed.
Lemma lem3397772 {_88224 _88228 : Type'} : term24 _88224 _88228.
Proof. exact (EQ_MP (@lem3397401 _88224 _88228) (@lem3397770 _88224 _88228)). Qed.
