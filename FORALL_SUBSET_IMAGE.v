Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_SUBSET_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUBSET_IMAGE_spec.
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
Lemma lem3647317 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3647318 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3647319 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3647318 t1) (@lem3647317 t1)). Qed.
Lemma lem3647320 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3647319 t1 t2). Qed.
Lemma lem3647321 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3647322 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3647321 t1 t2) (@lem3647320 t1 t2)). Qed.
Lemma lem3647323 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3647322 t1 t2 t3). Qed.
Lemma lem3647324 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3647325 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3647324 t1 t2 t3) (@lem3647323 t1 t2 t3)). Qed.
Lemma lem3647326 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3647325 t1 t2 t3)). Qed.
Lemma lem3647327 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem3645951 A B f). Qed.
Lemma lem3647328 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem3647329 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (EQ_MP (@lem3647328 A B f) (@lem3647327 A B f)). Qed.
Lemma lem3647330 {A B : Type'} (f : A -> B) (s : B -> Prop) : term9 A B f s.
Proof. exact (@lem3647329 A B f s). Qed.
Lemma lem3647331 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term9 A B f s) = (term10 A B s f).
Proof. exact (eq_refl (term9 A B f s)). Qed.
Lemma lem3647332 {A B : Type'} (s : B -> Prop) (f : A -> B) : term10 A B s f.
Proof. exact (EQ_MP (@lem3647331 A B s f) (@lem3647330 A B f s)). Qed.
Lemma lem3647333 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term11 A B s f t.
Proof. exact (@lem3647332 A B s f t). Qed.
Lemma lem3647334 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term11 A B s f t) = ((term12 A B s f t) = (term13 A B t s f)).
Proof. exact (eq_refl (term11 A B s f t)). Qed.
Lemma lem3647357 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term12 A B s f t) = (term13 A B t s f).
Proof. exact (EQ_MP (@lem3647334 A B t s f) (@lem3647333 A B s f t)). Qed.
Lemma lem3647358 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93424 -> Prop) (f : _93408 -> _93424) : (term12 _93408 _93424 s f t) = (term13 _93408 _93424 t s f).
Proof. exact (@lem3647357 _93408 _93424 t s f). Qed.
Lemma lem3647359 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term12 _93408 _93424 t f s) = (term13 _93408 _93424 s t f).
Proof. exact (@lem3647358 _93408 _93424 s t f). Qed.
Lemma lem3647368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3647369 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term14 _93408 _93424 t f s) = (term15 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647368) (@lem3647359 _93408 _93424 s t f)). Qed.
Lemma lem3647370 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3647371 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term16 _93408 _93424 f s P t) = (term17 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3647369 _93408 _93424 s t f) (@lem3647370 _93424 P t)). Qed.
Lemma lem3647374 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term18 _93408 _93424 f s P) = (term19 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3647371 _93408 _93424 s f P t)). Qed.
Lemma lem3647375 {_93424 : Type'} : (@all (_93424 -> Prop)) = (@all (_93424 -> Prop)).
Proof. exact (eq_refl (@all (_93424 -> Prop))). Qed.
Lemma lem3647376 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term20 _93408 _93424 f s P) = (term21 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647375 _93424) (@lem3647374 _93408 _93424 s f P)). Qed.
Lemma lem3647381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3647382 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term22 _93408 _93424 f s P) = (term23 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647381) (@lem3647376 _93408 _93424 s f P)). Qed.
Lemma lem3647389 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term24 _93408 _93424 s P f) = (term24 _93408 _93424 s P f).
Proof. exact (eq_refl (term24 _93408 _93424 s P f)). Qed.
Lemma lem3647390 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term20 _93408 _93424 f s P) = (term24 _93408 _93424 s P f)) = ((term21 _93408 _93424 s f P) = (term24 _93408 _93424 s P f)).
Proof. exact (MK_COMB (@lem3647382 _93408 _93424 s f P) (@lem3647389 _93408 _93424 s P f)). Qed.
Lemma lem3647393 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) : (term25 _93408 _93424 P f) = (term26 _93408 _93424 P f).
Proof. exact (fun_ext (fun s : _93408 -> Prop => @lem3647390 _93408 _93424 s P f)). Qed.
Lemma lem3647394 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3647395 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) : (term27 _93408 _93424 P f) = (term28 _93408 _93424 P f).
Proof. exact (MK_COMB (@lem3647394 _93408) (@lem3647393 _93408 _93424 P f)). Qed.
Lemma lem3647400 {_93408 _93424 : Type'} (P : type686 _93424) : (term29 _93408 _93424 P) = (term30 _93408 _93424 P).
Proof. exact (fun_ext (fun f : _93408 -> _93424 => @lem3647395 _93408 _93424 P f)). Qed.
Lemma lem3647401 {_93408 _93424 : Type'} : (@all (_93408 -> _93424)) = (@all (_93408 -> _93424)).
Proof. exact (eq_refl (@all (_93408 -> _93424))). Qed.
Lemma lem3647402 {_93408 _93424 : Type'} (P : type686 _93424) : (term31 _93408 _93424 P) = (term32 _93408 _93424 P).
Proof. exact (MK_COMB (@lem3647401 _93408 _93424) (@lem3647400 _93408 _93424 P)). Qed.
Lemma lem3647407 {_93408 _93424 : Type'} : (term33 _93408 _93424) = (term34 _93408 _93424).
Proof. exact (fun_ext (fun P : type686 _93424 => @lem3647402 _93408 _93424 P)). Qed.
Lemma lem3647408 {_93424 : Type'} : (@all ((_93424 -> Prop) -> Prop)) = (@all ((_93424 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93424 -> Prop) -> Prop))). Qed.
Lemma lem3647409 {_93408 _93424 : Type'} : (term35 _93408 _93424) = (term36 _93408 _93424).
Proof. exact (MK_COMB (@lem3647408 _93424) (@lem3647407 _93408 _93424)). Qed.
Lemma lem3647414 {_93408 _93424 : Type'} : (term36 _93408 _93424) = (term35 _93408 _93424).
Proof. exact (SYM (@lem3647409 _93408 _93424)). Qed.
Lemma lem3647416 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3647417 {_93408 _93424 : Type'} : (term36 _93408 _93424) = (term38 _93408 _93424).
Proof. exact (@lem3647416 (term36 _93408 _93424)). Qed.
Lemma lem3647418 {_93408 _93424 : Type'} : (term38 _93408 _93424) = (term36 _93408 _93424).
Proof. exact (SYM (@lem3647417 _93408 _93424)). Qed.
Lemma lem3647419 {_93408 _93424 : Type'} (h1 : term39 _93408 _93424) : term39 _93408 _93424.
Proof. exact (h1). Qed.
Lemma lem3647422 {_93408 _93424 : Type'} (h1 : term38 _93408 _93424) : term38 _93408 _93424.
Proof. exact (h1). Qed.
Lemma lem3647423 {_93408 _93424 : Type'} : term40 _93408 _93424.
Proof. exact (fun h0 : term38 _93408 _93424 => @lem3647422 _93408 _93424 h0). Qed.
Lemma lem3647424 {_93408 _93424 : Type'} (h1 : term40 _93408 _93424) : term40 _93408 _93424.
Proof. exact (h1). Qed.
Lemma lem3647425 {_93408 _93424 : Type'} (h1 : term38 _93408 _93424) : term38 _93408 _93424.
Proof. exact (h1). Qed.
Lemma lem3647426 {_93408 _93424 : Type'} (h1 : term38 _93408 _93424) (h2 : term40 _93408 _93424) : term38 _93408 _93424.
Proof. exact (@lem3647424 _93408 _93424 h2 (@lem3647425 _93408 _93424 h1)). Qed.
Lemma lem3647427 {_93408 _93424 : Type'} (h1 : term38 _93408 _93424) : term41 _93408 _93424.
Proof. exact (fun h0 : term40 _93408 _93424 => @lem3647426 _93408 _93424 h1 h0). Qed.
Lemma lem3647428 {_93408 _93424 : Type'} (h1 : term40 _93408 _93424) : term40 _93408 _93424.
Proof. exact (h1). Qed.
Lemma lem3647429 {_93408 _93424 : Type'} (h1 : term38 _93408 _93424) (h2 : term40 _93408 _93424) : term38 _93408 _93424.
Proof. exact (@lem3647427 _93408 _93424 h1 (@lem3647428 _93408 _93424 h2)). Qed.
Lemma lem3647430 {_93408 _93424 : Type'} (h1 : term40 _93408 _93424) : term40 _93408 _93424.
Proof. exact (fun h0 : term38 _93408 _93424 => @lem3647429 _93408 _93424 h0 h1). Qed.
Lemma lem3647431 {_93408 _93424 : Type'} : term42 _93408 _93424.
Proof. exact (fun h0 : term40 _93408 _93424 => @lem3647430 _93408 _93424 h0). Qed.
Lemma lem3647434 {_93408 _93424 : Type'} : term40 _93408 _93424.
Proof. exact (@lem3647431 _93408 _93424 (@lem3647423 _93408 _93424)). Qed.
Lemma lem3647435 {_93408 _93424 : Type'} : term40 _93408 _93424.
Proof. exact (@lem3647434 _93408 _93424). Qed.
Lemma lem3647437 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3647438 {_93408 _93424 : Type'} : (term38 _93408 _93424) = (term43 _93408 _93424).
Proof. exact (@lem3647437 (term39 _93408 _93424)). Qed.
Lemma lem3647440 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3647441 {_93408 _93424 : Type'} : (term43 _93408 _93424) = (term36 _93408 _93424).
Proof. exact (@lem3647440 (term36 _93408 _93424)). Qed.
Lemma lem3647520 {_93408 _93424 : Type'} : (term38 _93408 _93424) = (term36 _93408 _93424).
Proof. exact (TRANS (@lem3647438 _93408 _93424) (@lem3647441 _93408 _93424)). Qed.
Lemma lem3647525 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term45 _93408 _93424 s P f t) = (term45 _93408 _93424 s P f t).
Proof. exact (eq_refl (term45 _93408 _93424 s P f t)). Qed.
Lemma lem3647526 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term46 _93408 _93424 s P f) = (term46 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3647525 _93408 _93424 s P f t)). Qed.
Lemma lem3647527 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3647528 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term24 _93408 _93424 s P f) = (term24 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647527 _93408) (@lem3647526 _93408 _93424 s P f)). Qed.
Lemma lem3647529 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3647534 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term47 _93408 _93424 s t f u) = (term47 _93408 _93424 s t f u).
Proof. exact (eq_refl (term47 _93408 _93424 s t f u)). Qed.
Lemma lem3647535 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term48 _93408 _93424 s t f) = (term48 _93408 _93424 s t f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3647534 _93408 _93424 s t f u)). Qed.
Lemma lem3647536 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3647537 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term13 _93408 _93424 s t f) = (term13 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647536 _93408) (@lem3647535 _93408 _93424 s t f)). Qed.
Lemma lem3647538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3647539 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term15 _93408 _93424 s t f) = (term15 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647538) (@lem3647537 _93408 _93424 s t f)). Qed.
Lemma lem3647540 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term17 _93408 _93424 s f P t) = (term17 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3647539 _93408 _93424 s t f) (@lem3647529 _93424 P t)). Qed.
Lemma lem3647541 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term19 _93408 _93424 s f P) = (term19 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3647540 _93408 _93424 s f P t)). Qed.
Lemma lem3647542 {_93424 : Type'} : (@all (_93424 -> Prop)) = (@all (_93424 -> Prop)).
Proof. exact (eq_refl (@all (_93424 -> Prop))). Qed.
Lemma lem3647543 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term21 _93408 _93424 s f P) = (term21 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647542 _93424) (@lem3647541 _93408 _93424 s f P)). Qed.
Lemma lem3647544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3647545 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term23 _93408 _93424 s f P) = (term23 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647544) (@lem3647543 _93408 _93424 s f P)). Qed.
Lemma lem3647546 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term21 _93408 _93424 s f P) = (term24 _93408 _93424 s P f)) = ((term21 _93408 _93424 s f P) = (term24 _93408 _93424 s P f)).
Proof. exact (MK_COMB (@lem3647545 _93408 _93424 s f P) (@lem3647528 _93408 _93424 s P f)). Qed.
Lemma lem3647547 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) : (term26 _93408 _93424 P f) = (term26 _93408 _93424 P f).
Proof. exact (fun_ext (fun s : _93408 -> Prop => @lem3647546 _93408 _93424 s P f)). Qed.
Lemma lem3647548 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3647549 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) : (term28 _93408 _93424 P f) = (term28 _93408 _93424 P f).
Proof. exact (MK_COMB (@lem3647548 _93408) (@lem3647547 _93408 _93424 P f)). Qed.
Lemma lem3647550 {_93408 _93424 : Type'} (P : type686 _93424) : (term30 _93408 _93424 P) = (term30 _93408 _93424 P).
Proof. exact (fun_ext (fun f : _93408 -> _93424 => @lem3647549 _93408 _93424 P f)). Qed.
Lemma lem3647551 {_93408 _93424 : Type'} : (@all (_93408 -> _93424)) = (@all (_93408 -> _93424)).
Proof. exact (eq_refl (@all (_93408 -> _93424))). Qed.
Lemma lem3647552 {_93408 _93424 : Type'} (P : type686 _93424) : (term32 _93408 _93424 P) = (term32 _93408 _93424 P).
Proof. exact (MK_COMB (@lem3647551 _93408 _93424) (@lem3647550 _93408 _93424 P)). Qed.
Lemma lem3647553 {_93408 _93424 : Type'} : (term34 _93408 _93424) = (term34 _93408 _93424).
Proof. exact (fun_ext (fun P : type686 _93424 => @lem3647552 _93408 _93424 P)). Qed.
Lemma lem3647554 {_93424 : Type'} : (@all ((_93424 -> Prop) -> Prop)) = (@all ((_93424 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93424 -> Prop) -> Prop))). Qed.
Lemma lem3647555 {_93408 _93424 : Type'} : (term36 _93408 _93424) = (term36 _93408 _93424).
Proof. exact (MK_COMB (@lem3647554 _93424) (@lem3647553 _93408 _93424)). Qed.
Lemma lem3647600 {_93408 _93424 : Type'} : (term38 _93408 _93424) = (term36 _93408 _93424).
Proof. exact (TRANS (@lem3647520 _93408 _93424) (@lem3647555 _93408 _93424)). Qed.
Lemma lem3647601 {_93408 _93424 : Type'} : (term36 _93408 _93424) = (term38 _93408 _93424).
Proof. exact (SYM (@lem3647600 _93408 _93424)). Qed.
Lemma lem3647603 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3647604 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term21 _93408 _93424 s f P) = (term24 _93408 _93424 s P f)) = (term49 _93408 _93424 s P f).
Proof. exact (@lem3647603 ((term21 _93408 _93424 s f P) = (term24 _93408 _93424 s P f))). Qed.
Lemma lem3647605 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term49 _93408 _93424 s P f) = ((term21 _93408 _93424 s f P) = (term24 _93408 _93424 s P f)).
Proof. exact (SYM (@lem3647604 _93408 _93424 s P f)). Qed.
Lemma lem3647606 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term50 _93408 _93424 s P f) : term50 _93408 _93424 s P f.
Proof. exact (h1). Qed.
Lemma lem3647615 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term51 _93408 _93424 s t f u) = (term52 _93408 _93424 s t f u).
Proof. exact (@lem17045 (@SUBSET _93408 u s) (t = (@IMAGE _93408 _93424 f u))). Qed.
Lemma lem3647618 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term47 _93408 _93424 s t f u) = (term47 _93408 _93424 s t f u).
Proof. exact (eq_refl (term47 _93408 _93424 s t f u)). Qed.
Lemma lem3647619 {_93408 : Type'} (P : type686 _93408) : (term53 _93408 P) = (term54 _93408 P).
Proof. exact (@lem18394 (_93408 -> Prop) P). Qed.
Lemma lem3647620 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term55 _93408 _93424 s t f) = (term56 _93408 _93424 s t f).
Proof. exact (@lem3647619 _93408 (term48 _93408 _93424 s t f)). Qed.
Lemma lem3647621 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term57 _93408 _93424 s t f u) = (term47 _93408 _93424 s t f u).
Proof. exact (eq_refl (term57 _93408 _93424 s t f u)). Qed.
Lemma lem3647622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3647623 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term58 _93408 _93424 s t f u) = (term51 _93408 _93424 s t f u).
Proof. exact (MK_COMB (@lem3647622) (@lem3647621 _93408 _93424 s t f u)). Qed.
Lemma lem3647624 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term58 _93408 _93424 s t f u) = (term52 _93408 _93424 s t f u).
Proof. exact (TRANS (@lem3647623 _93408 _93424 s t f u) (@lem3647615 _93408 _93424 s t f u)). Qed.
Lemma lem3647625 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term59 _93408 _93424 s t f) = (term60 _93408 _93424 s t f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3647624 _93408 _93424 s t f u)). Qed.
Lemma lem3647626 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3647627 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term56 _93408 _93424 s t f) = (term61 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647626 _93408) (@lem3647625 _93408 _93424 s t f)). Qed.
Lemma lem3647628 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term55 _93408 _93424 s t f) = (term61 _93408 _93424 s t f).
Proof. exact (TRANS (@lem3647620 _93408 _93424 s t f) (@lem3647627 _93408 _93424 s t f)). Qed.
Lemma lem3647629 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term48 _93408 _93424 s t f) = (term48 _93408 _93424 s t f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3647618 _93408 _93424 s t f u)). Qed.
Lemma lem3647630 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3647631 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term13 _93408 _93424 s t f) = (term13 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647630 _93408) (@lem3647629 _93408 _93424 s t f)). Qed.
Lemma lem3647632 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (term62 _93424 P t) = (term62 _93424 P t).
Proof. exact (eq_refl (term62 _93424 P t)). Qed.
Lemma lem3647633 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3647634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3647635 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term63 _93408 _93424 s t f) = (term63 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647634) (@lem3647631 _93408 _93424 s t f)). Qed.
Lemma lem3647636 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term64 _93408 _93424 s f P t) = (term64 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3647635 _93408 _93424 s t f) (@lem3647632 _93424 P t)). Qed.
Lemma lem3647637 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term65 _93408 _93424 s f P t) = (term64 _93408 _93424 s f P t).
Proof. exact (@lem17362 (term13 _93408 _93424 s t f) (P t)). Qed.
Lemma lem3647638 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term65 _93408 _93424 s f P t) = (term64 _93408 _93424 s f P t).
Proof. exact (TRANS (@lem3647637 _93408 _93424 s f P t) (@lem3647636 _93408 _93424 s f P t)). Qed.
Lemma lem3647639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3647640 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term66 _93408 _93424 s t f) = (term67 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647639) (@lem3647628 _93408 _93424 s t f)). Qed.
Lemma lem3647641 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term68 _93408 _93424 s f P t) = (term69 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3647640 _93408 _93424 s t f) (@lem3647633 _93424 P t)). Qed.
Lemma lem3647642 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term17 _93408 _93424 s f P t) = (term68 _93408 _93424 s f P t).
Proof. exact (@lem17265 (term13 _93408 _93424 s t f) (P t)). Qed.
Lemma lem3647643 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term17 _93408 _93424 s f P t) = (term69 _93408 _93424 s f P t).
Proof. exact (TRANS (@lem3647642 _93408 _93424 s f P t) (@lem3647641 _93408 _93424 s f P t)). Qed.
Lemma lem3647644 {_93424 : Type'} (P : type686 _93424) : (term70 _93424 P) = (term71 _93424 P).
Proof. exact (@lem18392 (_93424 -> Prop) P). Qed.
Lemma lem3647645 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term72 _93408 _93424 s f P) = (term73 _93408 _93424 s f P).
Proof. exact (@lem3647644 _93424 (term19 _93408 _93424 s f P)). Qed.
Lemma lem3647646 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term74 _93408 _93424 s f P t) = (term17 _93408 _93424 s f P t).
Proof. exact (eq_refl (term74 _93408 _93424 s f P t)). Qed.
Lemma lem3647647 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3647648 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term75 _93408 _93424 s f P t) = (term65 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3647647) (@lem3647646 _93408 _93424 s f P t)). Qed.
Lemma lem3647649 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term75 _93408 _93424 s f P t) = (term64 _93408 _93424 s f P t).
Proof. exact (TRANS (@lem3647648 _93408 _93424 s f P t) (@lem3647638 _93408 _93424 s f P t)). Qed.
Lemma lem3647650 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term76 _93408 _93424 s f P) = (term77 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3647649 _93408 _93424 s f P t)). Qed.
Lemma lem3647651 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3647652 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term73 _93408 _93424 s f P) = (term78 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647651 _93424) (@lem3647650 _93408 _93424 s f P)). Qed.
Lemma lem3647653 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term72 _93408 _93424 s f P) = (term78 _93408 _93424 s f P).
Proof. exact (TRANS (@lem3647645 _93408 _93424 s f P) (@lem3647652 _93408 _93424 s f P)). Qed.
Lemma lem3647654 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term19 _93408 _93424 s f P) = (term79 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3647643 _93408 _93424 s f P t)). Qed.
Lemma lem3647655 {_93424 : Type'} : (@all (_93424 -> Prop)) = (@all (_93424 -> Prop)).
Proof. exact (eq_refl (@all (_93424 -> Prop))). Qed.
Lemma lem3647656 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term21 _93408 _93424 s f P) = (term80 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647655 _93424) (@lem3647654 _93408 _93424 s f P)). Qed.
Lemma lem3647665 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term81 _93408 _93424 s P f t) = (term82 _93408 _93424 s P f t).
Proof. exact (@lem17362 (@SUBSET _93408 t s) (term83 _93408 _93424 P f t)). Qed.
Lemma lem3647670 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term45 _93408 _93424 s P f t) = (term84 _93408 _93424 s P f t).
Proof. exact (@lem17265 (@SUBSET _93408 t s) (term83 _93408 _93424 P f t)). Qed.
Lemma lem3647671 {_93408 : Type'} (P : type686 _93408) : (term70 _93408 P) = (term71 _93408 P).
Proof. exact (@lem18392 (_93408 -> Prop) P). Qed.
Lemma lem3647672 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term85 _93408 _93424 s P f) = (term86 _93408 _93424 s P f).
Proof. exact (@lem3647671 _93408 (term46 _93408 _93424 s P f)). Qed.
Lemma lem3647673 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term87 _93408 _93424 s P f t) = (term45 _93408 _93424 s P f t).
Proof. exact (eq_refl (term87 _93408 _93424 s P f t)). Qed.
Lemma lem3647674 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3647675 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term88 _93408 _93424 s P f t) = (term81 _93408 _93424 s P f t).
Proof. exact (MK_COMB (@lem3647674) (@lem3647673 _93408 _93424 s P f t)). Qed.
Lemma lem3647676 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term88 _93408 _93424 s P f t) = (term82 _93408 _93424 s P f t).
Proof. exact (TRANS (@lem3647675 _93408 _93424 s P f t) (@lem3647665 _93408 _93424 s P f t)). Qed.
Lemma lem3647677 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term89 _93408 _93424 s P f) = (term90 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3647676 _93408 _93424 s P f t)). Qed.
Lemma lem3647678 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3647679 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term86 _93408 _93424 s P f) = (term91 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647678 _93408) (@lem3647677 _93408 _93424 s P f)). Qed.
Lemma lem3647680 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term85 _93408 _93424 s P f) = (term91 _93408 _93424 s P f).
Proof. exact (TRANS (@lem3647672 _93408 _93424 s P f) (@lem3647679 _93408 _93424 s P f)). Qed.
Lemma lem3647681 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term46 _93408 _93424 s P f) = (term92 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3647670 _93408 _93424 s P f t)). Qed.
Lemma lem3647682 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3647683 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term24 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647682 _93408) (@lem3647681 _93408 _93424 s P f)). Qed.
Lemma lem3647684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3647685 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term94 _93408 _93424 s f P) = (term95 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647684) (@lem3647653 _93408 _93424 s f P)). Qed.
Lemma lem3647686 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term96 _93408 _93424 s P f) = (term97 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647685 _93408 _93424 s f P) (@lem3647683 _93408 _93424 s P f)). Qed.
Lemma lem3647687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3647688 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term98 _93408 _93424 s f P) = (term99 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3647687) (@lem3647656 _93408 _93424 s f P)). Qed.
Lemma lem3647689 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term100 _93408 _93424 s P f) = (term101 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647688 _93408 _93424 s f P) (@lem3647680 _93408 _93424 s P f)). Qed.
Lemma lem3647690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3647691 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term102 _93408 _93424 s P f) = (term103 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647690) (@lem3647689 _93408 _93424 s P f)). Qed.
Lemma lem3647692 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term104 _93408 _93424 s P f) = (term105 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647691 _93408 _93424 s P f) (@lem3647686 _93408 _93424 s P f)). Qed.
Lemma lem3647693 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term50 _93408 _93424 s P f) = (term104 _93408 _93424 s P f).
Proof. exact (@lem17646 (term21 _93408 _93424 s f P) (term24 _93408 _93424 s P f)). Qed.
Lemma lem3647694 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term50 _93408 _93424 s P f) = (term105 _93408 _93424 s P f).
Proof. exact (TRANS (@lem3647693 _93408 _93424 s P f) (@lem3647692 _93408 _93424 s P f)). Qed.
Lemma lem3647969 {A : Type'} (P : Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3647970 {_93408 : Type'} (P : Prop) (Q : type686 _93408) : (term108 _93408 P Q) = (term109 _93408 P Q).
Proof. exact (@lem3647969 (_93408 -> Prop) P Q). Qed.
Lemma lem3647971 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term110 _93408 _93424 s P f) = (term111 _93408 _93424 s P f).
Proof. exact (@lem3647970 _93408 (term80 _93408 _93424 s f P) (term90 _93408 _93424 s P f)). Qed.
Lemma lem3647972 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term112 _93408 _93424 s P f t) = (term82 _93408 _93424 s P f t).
Proof. exact (eq_refl (term112 _93408 _93424 s P f t)). Qed.
Lemma lem3647973 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term113 _93408 _93424 s P f) = (term90 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3647972 _93408 _93424 s P f t)). Qed.
Lemma lem3647974 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3647975 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term114 _93408 _93424 s P f) = (term91 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647974 _93408) (@lem3647973 _93408 _93424 s P f)). Qed.
Lemma lem3647976 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term99 _93408 _93424 s f P) = (term99 _93408 _93424 s f P).
Proof. exact (eq_refl (term99 _93408 _93424 s f P)). Qed.
Lemma lem3647977 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term110 _93408 _93424 s P f) = (term101 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647976 _93408 _93424 s f P) (@lem3647975 _93408 _93424 s P f)). Qed.
Lemma lem3647978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3647979 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term115 _93408 _93424 s P f) = (term116 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647978) (@lem3647977 _93408 _93424 s P f)). Qed.
Lemma lem3647980 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term112 _93408 _93424 s P f t) = (term82 _93408 _93424 s P f t).
Proof. exact (eq_refl (term112 _93408 _93424 s P f t)). Qed.
Lemma lem3647981 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term99 _93408 _93424 s f P) = (term99 _93408 _93424 s f P).
Proof. exact (eq_refl (term99 _93408 _93424 s f P)). Qed.
Lemma lem3647982 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term117 _93408 _93424 s P f t) = (term118 _93408 _93424 s P f t).
Proof. exact (MK_COMB (@lem3647981 _93408 _93424 s f P) (@lem3647980 _93408 _93424 s P f t)). Qed.
Lemma lem3647983 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term119 _93408 _93424 s P f) = (term120 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3647982 _93408 _93424 s P f t)). Qed.
Lemma lem3647984 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3647985 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term111 _93408 _93424 s P f) = (term121 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647984 _93408) (@lem3647983 _93408 _93424 s P f)). Qed.
Lemma lem3647986 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term110 _93408 _93424 s P f) = (term111 _93408 _93424 s P f)) = ((term101 _93408 _93424 s P f) = (term121 _93408 _93424 s P f)).
Proof. exact (MK_COMB (@lem3647979 _93408 _93424 s P f) (@lem3647985 _93408 _93424 s P f)). Qed.
Lemma lem3647987 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term101 _93408 _93424 s P f) = (term121 _93408 _93424 s P f).
Proof. exact (EQ_MP (@lem3647986 _93408 _93424 s P f) (@lem3647971 _93408 _93424 s P f)). Qed.
Lemma lem3647988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3647989 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term103 _93408 _93424 s P f) = (term122 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647988) (@lem3647987 _93408 _93424 s P f)). Qed.
Lemma lem3647991 {A : Type'} (P : A -> Prop) (Q : Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3647992 {_93408 : Type'} (P : type686 _93408) (Q : Prop) : (term125 _93408 P Q) = (term126 _93408 P Q).
Proof. exact (@lem3647991 (_93408 -> Prop) P Q). Qed.
Lemma lem3647993 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term127 _93408 _93424 s f P t) = (term128 _93408 _93424 s f P t).
Proof. exact (@lem3647992 _93408 (term48 _93408 _93424 s t f) (term62 _93424 P t)). Qed.
Lemma lem3647994 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term57 _93408 _93424 s t f u) = (term47 _93408 _93424 s t f u).
Proof. exact (eq_refl (term57 _93408 _93424 s t f u)). Qed.
Lemma lem3647995 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term129 _93408 _93424 s t f) = (term48 _93408 _93424 s t f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3647994 _93408 _93424 s t f u)). Qed.
Lemma lem3647996 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3647997 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term130 _93408 _93424 s t f) = (term13 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647996 _93408) (@lem3647995 _93408 _93424 s t f)). Qed.
Lemma lem3647998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3647999 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term131 _93408 _93424 s t f) = (term63 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3647998) (@lem3647997 _93408 _93424 s t f)). Qed.
Lemma lem3648000 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (term62 _93424 P t) = (term62 _93424 P t).
Proof. exact (eq_refl (term62 _93424 P t)). Qed.
Lemma lem3648001 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term127 _93408 _93424 s f P t) = (term64 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3647999 _93408 _93424 s t f) (@lem3648000 _93424 P t)). Qed.
Lemma lem3648002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648003 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term132 _93408 _93424 s f P t) = (term133 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648002) (@lem3648001 _93408 _93424 s f P t)). Qed.
Lemma lem3648004 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term57 _93408 _93424 s t f u) = (term47 _93408 _93424 s t f u).
Proof. exact (eq_refl (term57 _93408 _93424 s t f u)). Qed.
Lemma lem3648005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648006 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term134 _93408 _93424 s t f u) = (term135 _93408 _93424 s t f u).
Proof. exact (MK_COMB (@lem3648005) (@lem3648004 _93408 _93424 s t f u)). Qed.
Lemma lem3648007 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (term62 _93424 P t) = (term62 _93424 P t).
Proof. exact (eq_refl (term62 _93424 P t)). Qed.
Lemma lem3648008 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) (P : type686 _93424) (t : _93424 -> Prop) : (term136 _93408 _93424 s f u P t) = (term137 _93408 _93424 s f u P t).
Proof. exact (MK_COMB (@lem3648006 _93408 _93424 s t f u) (@lem3648007 _93424 P t)). Qed.
Lemma lem3648009 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term138 _93408 _93424 s f P t) = (term139 _93408 _93424 s f P t).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648008 _93408 _93424 s f u P t)). Qed.
Lemma lem3648010 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648011 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term128 _93408 _93424 s f P t) = (term140 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648010 _93408) (@lem3648009 _93408 _93424 s f P t)). Qed.
Lemma lem3648012 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : ((term127 _93408 _93424 s f P t) = (term128 _93408 _93424 s f P t)) = ((term64 _93408 _93424 s f P t) = (term140 _93408 _93424 s f P t)).
Proof. exact (MK_COMB (@lem3648003 _93408 _93424 s f P t) (@lem3648011 _93408 _93424 s f P t)). Qed.
Lemma lem3648013 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term64 _93408 _93424 s f P t) = (term140 _93408 _93424 s f P t).
Proof. exact (EQ_MP (@lem3648012 _93408 _93424 s f P t) (@lem3647993 _93408 _93424 s f P t)). Qed.
Lemma lem3648014 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term77 _93408 _93424 s f P) = (term141 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648013 _93408 _93424 s f P t)). Qed.
Lemma lem3648015 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3648016 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term78 _93408 _93424 s f P) = (term142 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648015 _93424) (@lem3648014 _93408 _93424 s f P)). Qed.
Lemma lem3648017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648018 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term95 _93408 _93424 s f P) = (term143 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648017) (@lem3648016 _93408 _93424 s f P)). Qed.
Lemma lem3648019 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term93 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (eq_refl (term93 _93408 _93424 s P f)). Qed.
Lemma lem3648020 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term97 _93408 _93424 s P f) = (term144 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648018 _93408 _93424 s f P) (@lem3648019 _93408 _93424 s P f)). Qed.
Lemma lem3648022 {A : Type'} (P : A -> Prop) (Q : Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3648023 {_93424 : Type'} (P : type686 _93424) (Q : Prop) : (term125 _93424 P Q) = (term126 _93424 P Q).
Proof. exact (@lem3648022 (_93424 -> Prop) P Q). Qed.
Lemma lem3648024 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term145 _93408 _93424 s P f) = (term146 _93408 _93424 s P f).
Proof. exact (@lem3648023 _93424 (term141 _93408 _93424 s f P) (term93 _93408 _93424 s P f)). Qed.
Lemma lem3648025 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term147 _93408 _93424 s f P t) = (term140 _93408 _93424 s f P t).
Proof. exact (eq_refl (term147 _93408 _93424 s f P t)). Qed.
Lemma lem3648026 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term148 _93408 _93424 s f P) = (term141 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648025 _93408 _93424 s f P t)). Qed.
Lemma lem3648027 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3648028 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term149 _93408 _93424 s f P) = (term142 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648027 _93424) (@lem3648026 _93408 _93424 s f P)). Qed.
Lemma lem3648029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648030 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term150 _93408 _93424 s f P) = (term143 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648029) (@lem3648028 _93408 _93424 s f P)). Qed.
Lemma lem3648031 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term93 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (eq_refl (term93 _93408 _93424 s P f)). Qed.
Lemma lem3648032 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term145 _93408 _93424 s P f) = (term144 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648030 _93408 _93424 s f P) (@lem3648031 _93408 _93424 s P f)). Qed.
Lemma lem3648033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648034 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term151 _93408 _93424 s P f) = (term152 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648033) (@lem3648032 _93408 _93424 s P f)). Qed.
Lemma lem3648035 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term147 _93408 _93424 s f P t) = (term140 _93408 _93424 s f P t).
Proof. exact (eq_refl (term147 _93408 _93424 s f P t)). Qed.
Lemma lem3648036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648037 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term153 _93408 _93424 s f P t) = (term154 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648036) (@lem3648035 _93408 _93424 s f P t)). Qed.
Lemma lem3648038 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term93 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (eq_refl (term93 _93408 _93424 s P f)). Qed.
Lemma lem3648039 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term155 _93408 _93424 t s P f) = (term156 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648037 _93408 _93424 s f P t) (@lem3648038 _93408 _93424 s P f)). Qed.
Lemma lem3648040 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term157 _93408 _93424 s P f) = (term158 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648039 _93408 _93424 t s P f)). Qed.
Lemma lem3648041 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3648042 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term146 _93408 _93424 s P f) = (term159 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648041 _93424) (@lem3648040 _93408 _93424 s P f)). Qed.
Lemma lem3648043 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term145 _93408 _93424 s P f) = (term146 _93408 _93424 s P f)) = ((term144 _93408 _93424 s P f) = (term159 _93408 _93424 s P f)).
Proof. exact (MK_COMB (@lem3648034 _93408 _93424 s P f) (@lem3648042 _93408 _93424 s P f)). Qed.
Lemma lem3648044 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term144 _93408 _93424 s P f) = (term159 _93408 _93424 s P f).
Proof. exact (EQ_MP (@lem3648043 _93408 _93424 s P f) (@lem3648024 _93408 _93424 s P f)). Qed.
Lemma lem3648046 {A : Type'} (P : A -> Prop) (Q : Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3648047 {_93408 : Type'} (P : type686 _93408) (Q : Prop) : (term125 _93408 P Q) = (term126 _93408 P Q).
Proof. exact (@lem3648046 (_93408 -> Prop) P Q). Qed.
Lemma lem3648048 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term160 _93408 _93424 t s P f) = (term161 _93408 _93424 t s P f).
Proof. exact (@lem3648047 _93408 (term139 _93408 _93424 s f P t) (term93 _93408 _93424 s P f)). Qed.
Lemma lem3648049 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) (P : type686 _93424) (t : _93424 -> Prop) : (term162 _93408 _93424 s f P t u) = (term137 _93408 _93424 s f u P t).
Proof. exact (eq_refl (term162 _93408 _93424 s f P t u)). Qed.
Lemma lem3648050 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term163 _93408 _93424 s f P t) = (term139 _93408 _93424 s f P t).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648049 _93408 _93424 s f u P t)). Qed.
Lemma lem3648051 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648052 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term164 _93408 _93424 s f P t) = (term140 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648051 _93408) (@lem3648050 _93408 _93424 s f P t)). Qed.
Lemma lem3648053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648054 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term165 _93408 _93424 s f P t) = (term154 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648053) (@lem3648052 _93408 _93424 s f P t)). Qed.
Lemma lem3648055 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term93 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (eq_refl (term93 _93408 _93424 s P f)). Qed.
Lemma lem3648056 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term160 _93408 _93424 t s P f) = (term156 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648054 _93408 _93424 s f P t) (@lem3648055 _93408 _93424 s P f)). Qed.
Lemma lem3648057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648058 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term166 _93408 _93424 t s P f) = (term167 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648057) (@lem3648056 _93408 _93424 t s P f)). Qed.
Lemma lem3648059 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) (P : type686 _93424) (t : _93424 -> Prop) : (term162 _93408 _93424 s f P t u) = (term137 _93408 _93424 s f u P t).
Proof. exact (eq_refl (term162 _93408 _93424 s f P t u)). Qed.
Lemma lem3648060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648061 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) (P : type686 _93424) (t : _93424 -> Prop) : (term168 _93408 _93424 s f P t u) = (term169 _93408 _93424 s f u P t).
Proof. exact (MK_COMB (@lem3648060) (@lem3648059 _93408 _93424 s f u P t)). Qed.
Lemma lem3648062 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term93 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (eq_refl (term93 _93408 _93424 s P f)). Qed.
Lemma lem3648063 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term170 _93408 _93424 t u s P f) = (term171 _93408 _93424 u t s P f).
Proof. exact (MK_COMB (@lem3648061 _93408 _93424 s f u P t) (@lem3648062 _93408 _93424 s P f)). Qed.
Lemma lem3648064 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term172 _93408 _93424 t s P f) = (term173 _93408 _93424 t s P f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648063 _93408 _93424 u t s P f)). Qed.
Lemma lem3648065 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648066 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term161 _93408 _93424 t s P f) = (term174 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648065 _93408) (@lem3648064 _93408 _93424 t s P f)). Qed.
Lemma lem3648067 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term160 _93408 _93424 t s P f) = (term161 _93408 _93424 t s P f)) = ((term156 _93408 _93424 t s P f) = (term174 _93408 _93424 t s P f)).
Proof. exact (MK_COMB (@lem3648058 _93408 _93424 t s P f) (@lem3648066 _93408 _93424 t s P f)). Qed.
Lemma lem3648068 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term156 _93408 _93424 t s P f) = (term174 _93408 _93424 t s P f).
Proof. exact (EQ_MP (@lem3648067 _93408 _93424 t s P f) (@lem3648048 _93408 _93424 t s P f)). Qed.
Lemma lem3648069 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term158 _93408 _93424 s P f) = (term175 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648068 _93408 _93424 t s P f)). Qed.
Lemma lem3648070 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3648071 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term159 _93408 _93424 s P f) = (term176 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648070 _93424) (@lem3648069 _93408 _93424 s P f)). Qed.
Lemma lem3648072 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term144 _93408 _93424 s P f) = (term176 _93408 _93424 s P f).
Proof. exact (TRANS (@lem3648044 _93408 _93424 s P f) (@lem3648071 _93408 _93424 s P f)). Qed.
Lemma lem3648073 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term97 _93408 _93424 s P f) = (term176 _93408 _93424 s P f).
Proof. exact (TRANS (@lem3648020 _93408 _93424 s P f) (@lem3648072 _93408 _93424 s P f)). Qed.
Lemma lem3648074 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term105 _93408 _93424 s P f) = (term177 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3647989 _93408 _93424 s P f) (@lem3648073 _93408 _93424 s P f)). Qed.
Lemma lem3648078 {A : Type'} (P : A -> Prop) (Q : Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3648079 {_93408 : Type'} (P : type686 _93408) (Q : Prop) : (term180 _93408 P Q) = (term181 _93408 P Q).
Proof. exact (@lem3648078 (_93408 -> Prop) P Q). Qed.
Lemma lem3648080 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term182 _93408 _93424 s P f) = (term183 _93408 _93424 s P f).
Proof. exact (@lem3648079 _93408 (term120 _93408 _93424 s P f) (term176 _93408 _93424 s P f)). Qed.
Lemma lem3648081 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term184 _93408 _93424 s P f t) = (term118 _93408 _93424 s P f t).
Proof. exact (eq_refl (term184 _93408 _93424 s P f t)). Qed.
Lemma lem3648082 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term185 _93408 _93424 s P f) = (term120 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3648081 _93408 _93424 s P f t)). Qed.
Lemma lem3648083 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648084 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term186 _93408 _93424 s P f) = (term121 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648083 _93408) (@lem3648082 _93408 _93424 s P f)). Qed.
Lemma lem3648085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3648086 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term187 _93408 _93424 s P f) = (term122 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648085) (@lem3648084 _93408 _93424 s P f)). Qed.
Lemma lem3648087 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term176 _93408 _93424 s P f) = (term176 _93408 _93424 s P f).
Proof. exact (eq_refl (term176 _93408 _93424 s P f)). Qed.
Lemma lem3648088 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term182 _93408 _93424 s P f) = (term177 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648086 _93408 _93424 s P f) (@lem3648087 _93408 _93424 s P f)). Qed.
Lemma lem3648089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648090 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term188 _93408 _93424 s P f) = (term189 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648089) (@lem3648088 _93408 _93424 s P f)). Qed.
Lemma lem3648091 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term184 _93408 _93424 s P f t) = (term118 _93408 _93424 s P f t).
Proof. exact (eq_refl (term184 _93408 _93424 s P f t)). Qed.
Lemma lem3648092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3648093 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term190 _93408 _93424 s P f t) = (term191 _93408 _93424 s P f t).
Proof. exact (MK_COMB (@lem3648092) (@lem3648091 _93408 _93424 s P f t)). Qed.
Lemma lem3648094 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term176 _93408 _93424 s P f) = (term176 _93408 _93424 s P f).
Proof. exact (eq_refl (term176 _93408 _93424 s P f)). Qed.
Lemma lem3648095 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term192 _93408 _93424 t s P f) = (term193 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648093 _93408 _93424 s P f t) (@lem3648094 _93408 _93424 s P f)). Qed.
Lemma lem3648096 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term194 _93408 _93424 s P f) = (term195 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3648095 _93408 _93424 t s P f)). Qed.
Lemma lem3648097 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648098 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term183 _93408 _93424 s P f) = (term196 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648097 _93408) (@lem3648096 _93408 _93424 s P f)). Qed.
Lemma lem3648099 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term182 _93408 _93424 s P f) = (term183 _93408 _93424 s P f)) = ((term177 _93408 _93424 s P f) = (term196 _93408 _93424 s P f)).
Proof. exact (MK_COMB (@lem3648090 _93408 _93424 s P f) (@lem3648098 _93408 _93424 s P f)). Qed.
Lemma lem3648100 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term177 _93408 _93424 s P f) = (term196 _93408 _93424 s P f).
Proof. exact (EQ_MP (@lem3648099 _93408 _93424 s P f) (@lem3648080 _93408 _93424 s P f)). Qed.
Lemma lem3648102 {A : Type'} (P : Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3648103 {_93424 : Type'} (P : Prop) (Q : type686 _93424) : (term199 _93424 P Q) = (term200 _93424 P Q).
Proof. exact (@lem3648102 (_93424 -> Prop) P Q). Qed.
Lemma lem3648104 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term201 _93408 _93424 t s P f) = (term202 _93408 _93424 t s P f).
Proof. exact (@lem3648103 _93424 (term118 _93408 _93424 s P f t) (term175 _93408 _93424 s P f)). Qed.
Lemma lem3648105 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term203 _93408 _93424 s P f t) = (term174 _93408 _93424 t s P f).
Proof. exact (eq_refl (term203 _93408 _93424 s P f t)). Qed.
Lemma lem3648106 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term204 _93408 _93424 s P f) = (term175 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648105 _93408 _93424 t s P f)). Qed.
Lemma lem3648107 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3648108 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term205 _93408 _93424 s P f) = (term176 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648107 _93424) (@lem3648106 _93408 _93424 s P f)). Qed.
Lemma lem3648109 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term191 _93408 _93424 s P f t) = (term191 _93408 _93424 s P f t).
Proof. exact (eq_refl (term191 _93408 _93424 s P f t)). Qed.
Lemma lem3648110 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term201 _93408 _93424 t s P f) = (term193 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648109 _93408 _93424 s P f t) (@lem3648108 _93408 _93424 s P f)). Qed.
Lemma lem3648111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648112 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term206 _93408 _93424 t s P f) = (term207 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648111) (@lem3648110 _93408 _93424 t s P f)). Qed.
Lemma lem3648113 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term203 _93408 _93424 s P f t) = (term174 _93408 _93424 t s P f).
Proof. exact (eq_refl (term203 _93408 _93424 s P f t)). Qed.
Lemma lem3648114 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term191 _93408 _93424 s P f t) = (term191 _93408 _93424 s P f t).
Proof. exact (eq_refl (term191 _93408 _93424 s P f t)). Qed.
Lemma lem3648115 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term208 _93408 _93424 t s P f t') = (term209 _93408 _93424 t t' s P f).
Proof. exact (MK_COMB (@lem3648114 _93408 _93424 s P f t) (@lem3648113 _93408 _93424 t' s P f)). Qed.
Lemma lem3648116 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term210 _93408 _93424 t s P f) = (term211 _93408 _93424 t s P f).
Proof. exact (fun_ext (fun t' : _93424 -> Prop => @lem3648115 _93408 _93424 t t' s P f)). Qed.
Lemma lem3648117 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3648118 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term202 _93408 _93424 t s P f) = (term212 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648117 _93424) (@lem3648116 _93408 _93424 t s P f)). Qed.
Lemma lem3648119 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term201 _93408 _93424 t s P f) = (term202 _93408 _93424 t s P f)) = ((term193 _93408 _93424 t s P f) = (term212 _93408 _93424 t s P f)).
Proof. exact (MK_COMB (@lem3648112 _93408 _93424 t s P f) (@lem3648118 _93408 _93424 t s P f)). Qed.
Lemma lem3648120 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term193 _93408 _93424 t s P f) = (term212 _93408 _93424 t s P f).
Proof. exact (EQ_MP (@lem3648119 _93408 _93424 t s P f) (@lem3648104 _93408 _93424 t s P f)). Qed.
Lemma lem3648122 {A : Type'} (P : Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3648123 {_93408 : Type'} (P : Prop) (Q : type686 _93408) : (term199 _93408 P Q) = (term200 _93408 P Q).
Proof. exact (@lem3648122 (_93408 -> Prop) P Q). Qed.
Lemma lem3648124 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term213 _93408 _93424 t t' s P f) = (term214 _93408 _93424 t t' s P f).
Proof. exact (@lem3648123 _93408 (term118 _93408 _93424 s P f t) (term173 _93408 _93424 t' s P f)). Qed.
Lemma lem3648125 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term215 _93408 _93424 t s P f u) = (term171 _93408 _93424 u t s P f).
Proof. exact (eq_refl (term215 _93408 _93424 t s P f u)). Qed.
Lemma lem3648126 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term216 _93408 _93424 t s P f) = (term173 _93408 _93424 t s P f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648125 _93408 _93424 u t s P f)). Qed.
Lemma lem3648127 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648128 {_93408 _93424 : Type'} (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term217 _93408 _93424 t s P f) = (term174 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648127 _93408) (@lem3648126 _93408 _93424 t s P f)). Qed.
Lemma lem3648129 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term191 _93408 _93424 s P f t) = (term191 _93408 _93424 s P f t).
Proof. exact (eq_refl (term191 _93408 _93424 s P f t)). Qed.
Lemma lem3648130 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term213 _93408 _93424 t t' s P f) = (term209 _93408 _93424 t t' s P f).
Proof. exact (MK_COMB (@lem3648129 _93408 _93424 s P f t) (@lem3648128 _93408 _93424 t' s P f)). Qed.
Lemma lem3648131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648132 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term218 _93408 _93424 t t' s P f) = (term219 _93408 _93424 t t' s P f).
Proof. exact (MK_COMB (@lem3648131) (@lem3648130 _93408 _93424 t t' s P f)). Qed.
Lemma lem3648133 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term215 _93408 _93424 t s P f u) = (term171 _93408 _93424 u t s P f).
Proof. exact (eq_refl (term215 _93408 _93424 t s P f u)). Qed.
Lemma lem3648134 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term191 _93408 _93424 s P f t) = (term191 _93408 _93424 s P f t).
Proof. exact (eq_refl (term191 _93408 _93424 s P f t)). Qed.
Lemma lem3648135 {_93408 _93424 : Type'} (t : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term220 _93408 _93424 t t' s P f u) = (term221 _93408 _93424 t u t' s P f).
Proof. exact (MK_COMB (@lem3648134 _93408 _93424 s P f t) (@lem3648133 _93408 _93424 u t' s P f)). Qed.
Lemma lem3648136 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term222 _93408 _93424 t t' s P f) = (term223 _93408 _93424 t t' s P f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648135 _93408 _93424 t u t' s P f)). Qed.
Lemma lem3648137 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648138 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term214 _93408 _93424 t t' s P f) = (term224 _93408 _93424 t t' s P f).
Proof. exact (MK_COMB (@lem3648137 _93408) (@lem3648136 _93408 _93424 t t' s P f)). Qed.
Lemma lem3648139 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : ((term213 _93408 _93424 t t' s P f) = (term214 _93408 _93424 t t' s P f)) = ((term209 _93408 _93424 t t' s P f) = (term224 _93408 _93424 t t' s P f)).
Proof. exact (MK_COMB (@lem3648132 _93408 _93424 t t' s P f) (@lem3648138 _93408 _93424 t t' s P f)). Qed.
Lemma lem3648140 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term209 _93408 _93424 t t' s P f) = (term224 _93408 _93424 t t' s P f).
Proof. exact (EQ_MP (@lem3648139 _93408 _93424 t t' s P f) (@lem3648124 _93408 _93424 t t' s P f)). Qed.
Lemma lem3648141 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term211 _93408 _93424 t s P f) = (term225 _93408 _93424 t s P f).
Proof. exact (fun_ext (fun t' : _93424 -> Prop => @lem3648140 _93408 _93424 t t' s P f)). Qed.
Lemma lem3648142 {_93424 : Type'} : (@ex (_93424 -> Prop)) = (@ex (_93424 -> Prop)).
Proof. exact (eq_refl (@ex (_93424 -> Prop))). Qed.
Lemma lem3648143 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term212 _93408 _93424 t s P f) = (term226 _93408 _93424 t s P f).
Proof. exact (MK_COMB (@lem3648142 _93424) (@lem3648141 _93408 _93424 t s P f)). Qed.
Lemma lem3648144 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term193 _93408 _93424 t s P f) = (term226 _93408 _93424 t s P f).
Proof. exact (TRANS (@lem3648120 _93408 _93424 t s P f) (@lem3648143 _93408 _93424 t s P f)). Qed.
Lemma lem3648145 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term195 _93408 _93424 s P f) = (term227 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3648144 _93408 _93424 t s P f)). Qed.
Lemma lem3648146 {_93408 : Type'} : (@ex (_93408 -> Prop)) = (@ex (_93408 -> Prop)).
Proof. exact (eq_refl (@ex (_93408 -> Prop))). Qed.
Lemma lem3648147 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term196 _93408 _93424 s P f) = (term228 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648146 _93408) (@lem3648145 _93408 _93424 s P f)). Qed.
Lemma lem3648148 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term177 _93408 _93424 s P f) = (term228 _93408 _93424 s P f).
Proof. exact (TRANS (@lem3648100 _93408 _93424 s P f) (@lem3648147 _93408 _93424 s P f)). Qed.
Lemma lem3648150 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term105 _93408 _93424 s P f) = (term228 _93408 _93424 s P f).
Proof. exact (TRANS (@lem3648074 _93408 _93424 s P f) (@lem3648148 _93408 _93424 s P f)). Qed.
Lemma lem3648151 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term50 _93408 _93424 s P f) = (term228 _93408 _93424 s P f).
Proof. exact (TRANS (@lem3647694 _93408 _93424 s P f) (@lem3648150 _93408 _93424 s P f)). Qed.
Lemma lem3648152 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term50 _93408 _93424 s P f) : term228 _93408 _93424 s P f.
Proof. exact (EQ_MP (@lem3648151 _93408 _93424 s P f) (@lem3647606 _93408 _93424 s P f h1)). Qed.
Lemma lem3648153 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term226 _93408 _93424 t s P f) : term226 _93408 _93424 t s P f.
Proof. exact (h1). Qed.
Lemma lem3648154 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term224 _93408 _93424 t t' s P f) : term224 _93408 _93424 t t' s P f.
Proof. exact (h1). Qed.
Lemma lem3648155 {_93408 _93424 : Type'} (t : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term221 _93408 _93424 t u t' s P f) : term221 _93408 _93424 t u t' s P f.
Proof. exact (h1). Qed.
Lemma lem3648172 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term84 _93408 _93424 s P f t) = (term84 _93408 _93424 s P f t).
Proof. exact (eq_refl (term84 _93408 _93424 s P f t)). Qed.
Lemma lem3648173 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term92 _93408 _93424 s P f) = (term92 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3648172 _93408 _93424 s P f t)). Qed.
Lemma lem3648174 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3648175 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term93 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648174 _93408) (@lem3648173 _93408 _93424 s P f)). Qed.
Lemma lem3648202 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) (P : type686 _93424) (t' : _93424 -> Prop) : (term169 _93408 _93424 s f u P t') = (term169 _93408 _93424 s f u P t').
Proof. exact (eq_refl (term169 _93408 _93424 s f u P t')). Qed.
Lemma lem3648203 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term171 _93408 _93424 u t' s P f) = (term171 _93408 _93424 u t' s P f).
Proof. exact (MK_COMB (@lem3648202 _93408 _93424 s f u P t') (@lem3648175 _93408 _93424 s P f)). Qed.
Lemma lem3648220 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term82 _93408 _93424 s P f t) = (term82 _93408 _93424 s P f t).
Proof. exact (eq_refl (term82 _93408 _93424 s P f t)). Qed.
Lemma lem3648223 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3648244 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term52 _93408 _93424 s t f u) = (term52 _93408 _93424 s t f u).
Proof. exact (eq_refl (term52 _93408 _93424 s t f u)). Qed.
Lemma lem3648245 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term60 _93408 _93424 s t f) = (term60 _93408 _93424 s t f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648244 _93408 _93424 s t f u)). Qed.
Lemma lem3648246 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3648247 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term61 _93408 _93424 s t f) = (term61 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3648246 _93408) (@lem3648245 _93408 _93424 s t f)). Qed.
Lemma lem3648248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3648249 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term67 _93408 _93424 s t f) = (term67 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3648248) (@lem3648247 _93408 _93424 s t f)). Qed.
Lemma lem3648250 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term69 _93408 _93424 s f P t) = (term69 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648249 _93408 _93424 s t f) (@lem3648223 _93424 P t)). Qed.
Lemma lem3648251 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term79 _93408 _93424 s f P) = (term79 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648250 _93408 _93424 s f P t)). Qed.
Lemma lem3648252 {_93424 : Type'} : (@all (_93424 -> Prop)) = (@all (_93424 -> Prop)).
Proof. exact (eq_refl (@all (_93424 -> Prop))). Qed.
Lemma lem3648253 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term80 _93408 _93424 s f P) = (term80 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648252 _93424) (@lem3648251 _93408 _93424 s f P)). Qed.
Lemma lem3648254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648255 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term99 _93408 _93424 s f P) = (term99 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648254) (@lem3648253 _93408 _93424 s f P)). Qed.
Lemma lem3648256 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term118 _93408 _93424 s P f t) = (term118 _93408 _93424 s P f t).
Proof. exact (MK_COMB (@lem3648255 _93408 _93424 s f P) (@lem3648220 _93408 _93424 s P f t)). Qed.
Lemma lem3648257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3648258 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term191 _93408 _93424 s P f t) = (term191 _93408 _93424 s P f t).
Proof. exact (MK_COMB (@lem3648257) (@lem3648256 _93408 _93424 s P f t)). Qed.
Lemma lem3648259 {_93408 _93424 : Type'} (t : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term221 _93408 _93424 t u t' s P f) = (term221 _93408 _93424 t u t' s P f).
Proof. exact (MK_COMB (@lem3648258 _93408 _93424 s P f t) (@lem3648203 _93408 _93424 u t' s P f)). Qed.
Lemma lem3648260 {_93408 _93424 : Type'} (t : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term221 _93408 _93424 t u t' s P f) : term221 _93408 _93424 t u t' s P f.
Proof. exact (EQ_MP (@lem3648259 _93408 _93424 t u t' s P f) (@lem3648155 _93408 _93424 t u t' s P f h1)). Qed.
Lemma lem3648261 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term118 _93408 _93424 s P f t.
Proof. exact (h1). Qed.
Lemma lem3648262 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term171 _93408 _93424 u t' s P f.
Proof. exact (h1). Qed.
Lemma lem3648263 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term82 _93408 _93424 s P f t.
Proof. exact (proj2 (@lem3648261 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648264 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term80 _93408 _93424 s f P.
Proof. exact (proj1 (@lem3648261 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648267 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term93 _93408 _93424 s P f.
Proof. exact (proj2 (@lem3648262 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648268 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term137 _93408 _93424 s f u P t'.
Proof. exact (proj1 (@lem3648262 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648270 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term47 _93408 _93424 s t' f u.
Proof. exact (proj1 (@lem3648268 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648274 {A : Type'} (P : A -> Prop) (Q : Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3648275 {_93408 : Type'} (P : type686 _93408) (Q : Prop) : (term231 _93408 P Q) = (term232 _93408 P Q).
Proof. exact (@lem3648274 (_93408 -> Prop) P Q). Qed.
Lemma lem3648276 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term233 _93408 _93424 s f P t) = (term234 _93408 _93424 s f P t).
Proof. exact (@lem3648275 _93408 (term60 _93408 _93424 s t f) (P t)). Qed.
Lemma lem3648277 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term235 _93408 _93424 s t f u) = (term52 _93408 _93424 s t f u).
Proof. exact (eq_refl (term235 _93408 _93424 s t f u)). Qed.
Lemma lem3648278 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term236 _93408 _93424 s t f) = (term60 _93408 _93424 s t f).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648277 _93408 _93424 s t f u)). Qed.
Lemma lem3648279 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3648280 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term237 _93408 _93424 s t f) = (term61 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3648279 _93408) (@lem3648278 _93408 _93424 s t f)). Qed.
Lemma lem3648281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3648282 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) : (term238 _93408 _93424 s t f) = (term67 _93408 _93424 s t f).
Proof. exact (MK_COMB (@lem3648281) (@lem3648280 _93408 _93424 s t f)). Qed.
Lemma lem3648283 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3648284 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term233 _93408 _93424 s f P t) = (term69 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648282 _93408 _93424 s t f) (@lem3648283 _93424 P t)). Qed.
Lemma lem3648285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648286 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term239 _93408 _93424 s f P t) = (term240 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648285) (@lem3648284 _93408 _93424 s f P t)). Qed.
Lemma lem3648287 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term235 _93408 _93424 s t f u) = (term52 _93408 _93424 s t f u).
Proof. exact (eq_refl (term235 _93408 _93424 s t f u)). Qed.
Lemma lem3648288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3648289 {_93408 _93424 : Type'} (s : _93408 -> Prop) (t : _93424 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term241 _93408 _93424 s t f u) = (term242 _93408 _93424 s t f u).
Proof. exact (MK_COMB (@lem3648288) (@lem3648287 _93408 _93424 s t f u)). Qed.
Lemma lem3648290 {_93424 : Type'} (P : type686 _93424) (t : _93424 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3648291 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) (P : type686 _93424) (t : _93424 -> Prop) : (term243 _93408 _93424 s f u P t) = (term244 _93408 _93424 s f u P t).
Proof. exact (MK_COMB (@lem3648289 _93408 _93424 s t f u) (@lem3648290 _93424 P t)). Qed.
Lemma lem3648292 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term245 _93408 _93424 s f P t) = (term246 _93408 _93424 s f P t).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648291 _93408 _93424 s f u P t)). Qed.
Lemma lem3648293 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3648294 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term234 _93408 _93424 s f P t) = (term247 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648293 _93408) (@lem3648292 _93408 _93424 s f P t)). Qed.
Lemma lem3648295 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : ((term233 _93408 _93424 s f P t) = (term234 _93408 _93424 s f P t)) = ((term69 _93408 _93424 s f P t) = (term247 _93408 _93424 s f P t)).
Proof. exact (MK_COMB (@lem3648286 _93408 _93424 s f P t) (@lem3648294 _93408 _93424 s f P t)). Qed.
Lemma lem3648296 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term69 _93408 _93424 s f P t) = (term247 _93408 _93424 s f P t).
Proof. exact (EQ_MP (@lem3648295 _93408 _93424 s f P t) (@lem3648276 _93408 _93424 s f P t)). Qed.
Lemma lem3648297 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term79 _93408 _93424 s f P) = (term248 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648296 _93408 _93424 s f P t)). Qed.
Lemma lem3648298 {_93424 : Type'} : (@all (_93424 -> Prop)) = (@all (_93424 -> Prop)).
Proof. exact (eq_refl (@all (_93424 -> Prop))). Qed.
Lemma lem3648299 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term80 _93408 _93424 s f P) = (term249 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648298 _93424) (@lem3648297 _93408 _93424 s f P)). Qed.
Lemma lem3648312 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (u : _93408 -> Prop) (P : type686 _93424) (t : _93424 -> Prop) : (term244 _93408 _93424 s f u P t) = (term244 _93408 _93424 s f u P t).
Proof. exact (eq_refl (term244 _93408 _93424 s f u P t)). Qed.
Lemma lem3648313 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term246 _93408 _93424 s f P t) = (term246 _93408 _93424 s f P t).
Proof. exact (fun_ext (fun u : _93408 -> Prop => @lem3648312 _93408 _93424 s f u P t)). Qed.
Lemma lem3648314 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3648315 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (t : _93424 -> Prop) : (term247 _93408 _93424 s f P t) = (term247 _93408 _93424 s f P t).
Proof. exact (MK_COMB (@lem3648314 _93408) (@lem3648313 _93408 _93424 s f P t)). Qed.
Lemma lem3648316 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term248 _93408 _93424 s f P) = (term248 _93408 _93424 s f P).
Proof. exact (fun_ext (fun t : _93424 -> Prop => @lem3648315 _93408 _93424 s f P t)). Qed.
Lemma lem3648317 {_93424 : Type'} : (@all (_93424 -> Prop)) = (@all (_93424 -> Prop)).
Proof. exact (eq_refl (@all (_93424 -> Prop))). Qed.
Lemma lem3648318 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term249 _93408 _93424 s f P) = (term249 _93408 _93424 s f P).
Proof. exact (MK_COMB (@lem3648317 _93424) (@lem3648316 _93408 _93424 s f P)). Qed.
Lemma lem3648319 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) : (term80 _93408 _93424 s f P) = (term249 _93408 _93424 s f P).
Proof. exact (TRANS (@lem3648299 _93408 _93424 s f P) (@lem3648318 _93408 _93424 s f P)). Qed.
Lemma lem3648320 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term249 _93408 _93424 s f P.
Proof. exact (EQ_MP (@lem3648319 _93408 _93424 s f P) (@lem3648264 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648336 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term84 _93408 _93424 s P f t) = (term84 _93408 _93424 s P f t).
Proof. exact (eq_refl (term84 _93408 _93424 s P f t)). Qed.
Lemma lem3648337 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term92 _93408 _93424 s P f) = (term92 _93408 _93424 s P f).
Proof. exact (fun_ext (fun t : _93408 -> Prop => @lem3648336 _93408 _93424 s P f t)). Qed.
Lemma lem3648338 {_93408 : Type'} : (@all (_93408 -> Prop)) = (@all (_93408 -> Prop)).
Proof. exact (eq_refl (@all (_93408 -> Prop))). Qed.
Lemma lem3648340 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term93 _93408 _93424 s P f) = (term93 _93408 _93424 s P f).
Proof. exact (MK_COMB (@lem3648338 _93408) (@lem3648337 _93408 _93424 s P f)). Qed.
Lemma lem3648341 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term93 _93408 _93424 s P f.
Proof. exact (EQ_MP (@lem3648340 _93408 _93424 s P f) (@lem3648267 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648354 {_93408 _93424 : Type'} (_40028 : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term250 _93408 _93424 s f P _40028.
Proof. exact (@lem3648320 _93408 _93424 s P f t h1 _40028). Qed.
Lemma lem3648355 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (P : type686 _93424) (_40028 : _93424 -> Prop) : (term250 _93408 _93424 s f P _40028) = (term247 _93408 _93424 s f P _40028).
Proof. exact (eq_refl (term250 _93408 _93424 s f P _40028)). Qed.
Lemma lem3648356 {_93408 _93424 : Type'} (_40028 : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term247 _93408 _93424 s f P _40028.
Proof. exact (EQ_MP (@lem3648355 _93408 _93424 s f P _40028) (@lem3648354 _93408 _93424 _40028 s P f t h1)). Qed.
Lemma lem3648357 {_93408 _93424 : Type'} (_40028 : _93424 -> Prop) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term251 _93408 _93424 s f P _40028 _40029.
Proof. exact (@lem3648356 _93408 _93424 _40028 s P f t h1 _40029). Qed.
Lemma lem3648358 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (P : type686 _93424) (_40028 : _93424 -> Prop) : (term251 _93408 _93424 s f P _40028 _40029) = (term244 _93408 _93424 s f _40029 P _40028).
Proof. exact (eq_refl (term251 _93408 _93424 s f P _40028 _40029)). Qed.
Lemma lem3648359 {_93408 _93424 : Type'} (_40029 : _93408 -> Prop) (_40028 : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term244 _93408 _93424 s f _40029 P _40028.
Proof. exact (EQ_MP (@lem3648358 _93408 _93424 s f _40029 P _40028) (@lem3648357 _93408 _93424 _40028 _40029 s P f t h1)). Qed.
Lemma lem3648360 {_93408 _93424 : Type'} (_40030 : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term252 _93408 _93424 s P f _40030.
Proof. exact (@lem3648341 _93408 _93424 u t' s P f h1 _40030). Qed.
Lemma lem3648361 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) : (term252 _93408 _93424 s P f _40030) = (term84 _93408 _93424 s P f _40030).
Proof. exact (eq_refl (term252 _93408 _93424 s P f _40030)). Qed.
Lemma lem3648373 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (P : type686 _93424) (_40028 : _93424 -> Prop) : (term244 _93408 _93424 s f _40029 P _40028) = (term253 _93408 _93424 s f _40029 P _40028).
Proof. exact (@lem3647326 (term254 _93408 _40029 s) (term255 _93408 _93424 _40028 f _40029) (P _40028)). Qed.
Lemma lem3648374 {_93408 _93424 : Type'} (_40029 : _93408 -> Prop) (_40028 : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term253 _93408 _93424 s f _40029 P _40028.
Proof. exact (EQ_MP (@lem3648373 _93408 _93424 s f _40029 P _40028) (@lem3648359 _93408 _93424 _40029 _40028 s P f t h1)). Qed.
Lemma lem3648378 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term256 _93408 _93424 P f t.
Proof. exact (proj2 (@lem3648263 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648386 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term62 _93424 P t'.
Proof. exact (proj2 (@lem3648268 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648390 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : t' = (@IMAGE _93408 _93424 f u).
Proof. exact (proj2 (@lem3648270 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648418 {_93408 _93424 : Type'} (_40030 : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term84 _93408 _93424 s P f _40030.
Proof. exact (EQ_MP (@lem3648361 _93408 _93424 s P f _40030) (@lem3648360 _93408 _93424 _40030 u t' s P f h1)). Qed.
Lemma lem3648419 {_93424 : Type'} (P : type686 _93424) : (term257 _93424 P) = (term257 _93424 P).
Proof. exact (eq_refl (term257 _93424 P)). Qed.
Lemma lem3648420 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : (term258 _93424 P t') = (term259 _93408 _93424 P f u).
Proof. exact (MK_COMB (@lem3648419 _93424 P) (@lem3648390 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648421 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term259 _93408 _93424 P f u) = (term256 _93408 _93424 P f u).
Proof. exact (eq_refl (term259 _93408 _93424 P f u)). Qed.
Lemma lem3648422 {_93424 : Type'} (P : type686 _93424) (t' : _93424 -> Prop) : (term260 _93424 P t') = (term260 _93424 P t').
Proof. exact (eq_refl (term260 _93424 P t')). Qed.
Lemma lem3648423 {_93408 _93424 : Type'} (t' : _93424 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (u : _93408 -> Prop) : ((term258 _93424 P t') = (term259 _93408 _93424 P f u)) = ((term258 _93424 P t') = (term256 _93408 _93424 P f u)).
Proof. exact (MK_COMB (@lem3648422 _93424 P t') (@lem3648421 _93408 _93424 P f u)). Qed.
Lemma lem3648424 {_93424 : Type'} (P : type686 _93424) (t' : _93424 -> Prop) : (term258 _93424 P t') = (term62 _93424 P t').
Proof. exact (eq_refl (term258 _93424 P t')). Qed.
Lemma lem3648425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648426 {_93424 : Type'} (P : type686 _93424) (t' : _93424 -> Prop) : (term260 _93424 P t') = (term261 _93424 P t').
Proof. exact (MK_COMB (@lem3648425) (@lem3648424 _93424 P t')). Qed.
Lemma lem3648427 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term256 _93408 _93424 P f u) = (term256 _93408 _93424 P f u).
Proof. exact (eq_refl (term256 _93408 _93424 P f u)). Qed.
Lemma lem3648428 {_93408 _93424 : Type'} (t' : _93424 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (u : _93408 -> Prop) : ((term258 _93424 P t') = (term256 _93408 _93424 P f u)) = ((term62 _93424 P t') = (term256 _93408 _93424 P f u)).
Proof. exact (MK_COMB (@lem3648426 _93424 P t') (@lem3648427 _93408 _93424 P f u)). Qed.
Lemma lem3648429 {_93408 _93424 : Type'} (t' : _93424 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (u : _93408 -> Prop) : ((term258 _93424 P t') = (term259 _93408 _93424 P f u)) = ((term62 _93424 P t') = (term256 _93408 _93424 P f u)).
Proof. exact (TRANS (@lem3648423 _93408 _93424 t' P f u) (@lem3648428 _93408 _93424 t' P f u)). Qed.
Lemma lem3648430 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : (term62 _93424 P t') = (term256 _93408 _93424 P f u).
Proof. exact (EQ_MP (@lem3648429 _93408 _93424 t' P f u) (@lem3648420 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648431 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term256 _93408 _93424 P f u.
Proof. exact (EQ_MP (@lem3648430 _93408 _93424 u t' s P f h1) (@lem3648386 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648499 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : @SUBSET _93408 t s.
Proof. exact (proj1 (@lem3648263 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648500 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term262 _93408 t s.
Proof. exact (fun h0 : term254 _93408 t s => @lem3648499 _93408 _93424 s P f t h1). Qed.
Lemma lem3648502 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3648503 {_93408 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) : (term262 _93408 t s) = (@SUBSET _93408 t s).
Proof. exact (@lem3648502 (@SUBSET _93408 t s)). Qed.
Lemma lem3648504 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : @SUBSET _93408 t s.
Proof. exact (EQ_MP (@lem3648503 _93408 t s) (@lem3648500 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648506 {_93424 : Type'} (x : _93424 -> Prop) : x = x.
Proof. exact (@lem21386 (_93424 -> Prop) x). Qed.
Lemma lem3648507 {_93424 : Type'} (x : _93424 -> Prop) : x = x.
Proof. exact (@lem3648506 _93424 x). Qed.
Lemma lem3648508 {_93408 _93424 : Type'} (f : _93408 -> _93424) (t : _93408 -> Prop) : (@IMAGE _93408 _93424 f t) = (@IMAGE _93408 _93424 f t).
Proof. exact (@lem3648507 _93424 (@IMAGE _93408 _93424 f t)). Qed.
Lemma lem3648509 {_93408 _93424 : Type'} (f : _93408 -> _93424) (t : _93408 -> Prop) : term264 _93408 _93424 f t.
Proof. exact (fun h0 : term265 _93408 _93424 f t => @lem3648508 _93408 _93424 f t). Qed.
Lemma lem3648511 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3648512 {_93408 _93424 : Type'} (f : _93408 -> _93424) (t : _93408 -> Prop) : (term264 _93408 _93424 f t) = ((@IMAGE _93408 _93424 f t) = (@IMAGE _93408 _93424 f t)).
Proof. exact (@lem3648511 ((@IMAGE _93408 _93424 f t) = (@IMAGE _93408 _93424 f t))). Qed.
Lemma lem3648513 {_93408 _93424 : Type'} (f : _93408 -> _93424) (t : _93408 -> Prop) : (@IMAGE _93408 _93424 f t) = (@IMAGE _93408 _93424 f t).
Proof. exact (EQ_MP (@lem3648512 _93408 _93424 f t) (@lem3648509 _93408 _93424 f t)). Qed.
Lemma lem3648519 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3648520 {_93408 _93424 : Type'} (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (_40028 : _93424 -> Prop) : (term253 _93408 _93424 s f _40029 P _40028) = (term266 _93408 _93424 f _40029 s P _40028).
Proof. exact (@lem3648519 (term255 _93408 _93424 _40028 f _40029) (term254 _93408 _40029 s) (P _40028)). Qed.
Lemma lem3648536 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3648537 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term267 _93408 _93424 _40029 s P _40028) = (term268 _93408 _93424 P _40028 _40029 s).
Proof. exact (@lem3648536 (P _40028) (term254 _93408 _40029 s)). Qed.
Lemma lem3648543 {_93408 _93424 : Type'} (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : (term269 _93408 _93424 _40028 f _40029) = (term269 _93408 _93424 _40028 f _40029).
Proof. exact (eq_refl (term269 _93408 _93424 _40028 f _40029)). Qed.
Lemma lem3648544 {_93408 _93424 : Type'} (f : _93408 -> _93424) (P : type686 _93424) (_40028 : _93424 -> Prop) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term266 _93408 _93424 f _40029 s P _40028) = (term270 _93408 _93424 f P _40028 _40029 s).
Proof. exact (MK_COMB (@lem3648543 _93408 _93424 _40028 f _40029) (@lem3648537 _93408 _93424 P _40028 _40029 s)). Qed.
Lemma lem3648548 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3648549 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term270 _93408 _93424 f P _40028 _40029 s) = (term271 _93408 _93424 P _40028 f _40029 s).
Proof. exact (@lem3648548 (P _40028) (term255 _93408 _93424 _40028 f _40029) (term254 _93408 _40029 s)). Qed.
Lemma lem3648567 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term266 _93408 _93424 f _40029 s P _40028) = (term271 _93408 _93424 P _40028 f _40029 s).
Proof. exact (TRANS (@lem3648544 _93408 _93424 f P _40028 _40029 s) (@lem3648549 _93408 _93424 P _40028 f _40029 s)). Qed.
Lemma lem3648568 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term253 _93408 _93424 s f _40029 P _40028) = (term271 _93408 _93424 P _40028 f _40029 s).
Proof. exact (TRANS (@lem3648520 _93408 _93424 f _40029 s P _40028) (@lem3648567 _93408 _93424 P _40028 f _40029 s)). Qed.
Lemma lem3648569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648570 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term272 _93408 _93424 s f _40029 P _40028) = (term273 _93408 _93424 P _40028 f _40029 s).
Proof. exact (MK_COMB (@lem3648569) (@lem3648568 _93408 _93424 P _40028 f _40029 s)). Qed.
Lemma lem3648584 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3648585 {_93408 _93424 : Type'} (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term52 _93408 _93424 s _40028 f _40029) = (term274 _93408 _93424 _40028 f _40029 s).
Proof. exact (@lem3648584 (term255 _93408 _93424 _40028 f _40029) (term254 _93408 _40029 s)). Qed.
Lemma lem3648593 {_93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) : (term275 _93424 P _40028) = (term275 _93424 P _40028).
Proof. exact (eq_refl (term275 _93424 P _40028)). Qed.
Lemma lem3648594 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term276 _93408 _93424 P s _40028 f _40029) = (term271 _93408 _93424 P _40028 f _40029 s).
Proof. exact (MK_COMB (@lem3648593 _93424 P _40028) (@lem3648585 _93408 _93424 _40028 f _40029 s)). Qed.
Lemma lem3648605 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : ((term253 _93408 _93424 s f _40029 P _40028) = (term276 _93408 _93424 P s _40028 f _40029)) = ((term271 _93408 _93424 P _40028 f _40029 s) = (term271 _93408 _93424 P _40028 f _40029 s)).
Proof. exact (MK_COMB (@lem3648570 _93408 _93424 P _40028 f _40029 s) (@lem3648594 _93408 _93424 P _40028 f _40029 s)). Qed.
Lemma lem3648607 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3648608 (x : Prop) : (x = x) = True.
Proof. exact (@lem3648607 Prop x). Qed.
Lemma lem3648609 {_93408 _93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : ((term271 _93408 _93424 P _40028 f _40029 s) = (term271 _93408 _93424 P _40028 f _40029 s)) = True.
Proof. exact (@lem3648608 (term271 _93408 _93424 P _40028 f _40029 s)). Qed.
Lemma lem3648610 {_93408 _93424 : Type'} (P : type686 _93424) (s : _93408 -> Prop) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : ((term253 _93408 _93424 s f _40029 P _40028) = (term276 _93408 _93424 P s _40028 f _40029)) = True.
Proof. exact (TRANS (@lem3648605 _93408 _93424 P _40028 f _40029 s) (@lem3648609 _93408 _93424 P _40028 f _40029 s)). Qed.
Lemma lem3648611 {_93408 _93424 : Type'} (P : type686 _93424) (s : _93408 -> Prop) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : True = ((term253 _93408 _93424 s f _40029 P _40028) = (term276 _93408 _93424 P s _40028 f _40029)).
Proof. exact (SYM (@lem3648610 _93408 _93424 P s _40028 f _40029)). Qed.
Lemma lem3648612 {_93408 _93424 : Type'} (P : type686 _93424) (s : _93408 -> Prop) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : (term253 _93408 _93424 s f _40029 P _40028) = (term276 _93408 _93424 P s _40028 f _40029).
Proof. exact (EQ_MP (@lem3648611 _93408 _93424 P s _40028 f _40029) (@lem0)). Qed.
Lemma lem3648613 {_93408 _93424 : Type'} (_40028 : _93424 -> Prop) (_40029 : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term276 _93408 _93424 P s _40028 f _40029.
Proof. exact (EQ_MP (@lem3648612 _93408 _93424 P s _40028 f _40029) (@lem3648374 _93408 _93424 _40029 _40028 s P f t h1)). Qed.
Lemma lem3648615 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3648616 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (P : type686 _93424) (_40028 : _93424 -> Prop) : (term276 _93408 _93424 P s _40028 f _40029) = (term278 _93408 _93424 s f _40029 P _40028).
Proof. exact (@lem3648615 (term52 _93408 _93424 s _40028 f _40029) (P _40028)). Qed.
Lemma lem3648618 (a : Prop) (b : Prop) : (term279 a b) = (term280 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3648619 {_93408 _93424 : Type'} (s : _93408 -> Prop) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : (term281 _93408 _93424 s _40028 f _40029) = (term282 _93408 _93424 s _40028 f _40029).
Proof. exact (@lem3648618 (term254 _93408 _40029 s) (term255 _93408 _93424 _40028 f _40029)). Qed.
Lemma lem3648621 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3648622 {_93408 : Type'} (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term283 _93408 _40029 s) = (@SUBSET _93408 _40029 s).
Proof. exact (@lem3648621 (@SUBSET _93408 _40029 s)). Qed.
Lemma lem3648623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3648624 {_93408 : Type'} (_40029 : _93408 -> Prop) (s : _93408 -> Prop) : (term284 _93408 _40029 s) = (term285 _93408 _40029 s).
Proof. exact (MK_COMB (@lem3648623) (@lem3648622 _93408 _40029 s)). Qed.
Lemma lem3648626 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3648627 {_93408 _93424 : Type'} (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : (term286 _93408 _93424 _40028 f _40029) = (_40028 = (@IMAGE _93408 _93424 f _40029)).
Proof. exact (@lem3648626 (_40028 = (@IMAGE _93408 _93424 f _40029))). Qed.
Lemma lem3648628 {_93408 _93424 : Type'} (s : _93408 -> Prop) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : (term282 _93408 _93424 s _40028 f _40029) = (term47 _93408 _93424 s _40028 f _40029).
Proof. exact (MK_COMB (@lem3648624 _93408 _40029 s) (@lem3648627 _93408 _93424 _40028 f _40029)). Qed.
Lemma lem3648629 {_93408 _93424 : Type'} (s : _93408 -> Prop) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : (term281 _93408 _93424 s _40028 f _40029) = (term47 _93408 _93424 s _40028 f _40029).
Proof. exact (TRANS (@lem3648619 _93408 _93424 s _40028 f _40029) (@lem3648628 _93408 _93424 s _40028 f _40029)). Qed.
Lemma lem3648630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3648631 {_93408 _93424 : Type'} (s : _93408 -> Prop) (_40028 : _93424 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) : (term287 _93408 _93424 s _40028 f _40029) = (term288 _93408 _93424 s _40028 f _40029).
Proof. exact (MK_COMB (@lem3648630) (@lem3648629 _93408 _93424 s _40028 f _40029)). Qed.
Lemma lem3648632 {_93424 : Type'} (P : type686 _93424) (_40028 : _93424 -> Prop) : (P _40028) = (P _40028).
Proof. exact (eq_refl (P _40028)). Qed.
Lemma lem3648633 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (P : type686 _93424) (_40028 : _93424 -> Prop) : (term278 _93408 _93424 s f _40029 P _40028) = (term289 _93408 _93424 s f _40029 P _40028).
Proof. exact (MK_COMB (@lem3648631 _93408 _93424 s _40028 f _40029) (@lem3648632 _93424 P _40028)). Qed.
Lemma lem3648634 {_93408 _93424 : Type'} (s : _93408 -> Prop) (f : _93408 -> _93424) (_40029 : _93408 -> Prop) (P : type686 _93424) (_40028 : _93424 -> Prop) : (term276 _93408 _93424 P s _40028 f _40029) = (term289 _93408 _93424 s f _40029 P _40028).
Proof. exact (TRANS (@lem3648616 _93408 _93424 s f _40029 P _40028) (@lem3648633 _93408 _93424 s f _40029 P _40028)). Qed.
Lemma lem3648636 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term290 _93408 _93424 s f t.
Proof. exact (conj (@lem3648504 _93408 _93424 s P f t h1) (@lem3648513 _93408 _93424 f t)). Qed.
Lemma lem3648638 {_93408 _93424 : Type'} (_40029 : _93408 -> Prop) (_40028 : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term289 _93408 _93424 s f _40029 P _40028.
Proof. exact (EQ_MP (@lem3648634 _93408 _93424 s f _40029 P _40028) (@lem3648613 _93408 _93424 _40028 _40029 s P f t h1)). Qed.
Lemma lem3648639 {_93408 _93424 : Type'} (_40029 : _93408 -> Prop) (_40028 : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term289 _93408 _93424 s f _40029 P _40028.
Proof. exact (@lem3648638 _93408 _93424 _40029 _40028 s P f t h1). Qed.
Lemma lem3648640 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term291 _93408 _93424 s P f t.
Proof. exact (@lem3648639 _93408 _93424 t (@IMAGE _93408 _93424 f t) s P f t h1). Qed.
Lemma lem3648643 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term83 _93408 _93424 P f t.
Proof. exact (@lem3648640 _93408 _93424 s P f t h1 (@lem3648636 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648644 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term292 _93408 _93424 P f t.
Proof. exact (fun h0 : term256 _93408 _93424 P f t => @lem3648643 _93408 _93424 s P f t h1). Qed.
Lemma lem3648646 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3648647 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term292 _93408 _93424 P f t) = (term83 _93408 _93424 P f t).
Proof. exact (@lem3648646 (term83 _93408 _93424 P f t)). Qed.
Lemma lem3648648 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term83 _93408 _93424 P f t.
Proof. exact (EQ_MP (@lem3648647 _93408 _93424 P f t) (@lem3648644 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648651 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3648653 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) : (term256 _93408 _93424 P f t) = (term293 _93408 _93424 P f t).
Proof. exact (@lem3648651 (term83 _93408 _93424 P f t)). Qed.
Lemma lem3648656 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term293 _93408 _93424 P f t.
Proof. exact (EQ_MP (@lem3648653 _93408 _93424 P f t) (@lem3648378 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648659 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : False.
Proof. exact (@lem3648656 _93408 _93424 s P f t h1 (@lem3648648 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648660 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : term294.
Proof. exact (fun h0 : ~ False => @lem3648659 _93408 _93424 s P f t h1). Qed.
Lemma lem3648662 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3648663 : term294 = False.
Proof. exact (@lem3648662 False). Qed.
Lemma lem3648664 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (t : _93408 -> Prop) (h1 : term118 _93408 _93424 s P f t) : False.
Proof. exact (EQ_MP (@lem3648663) (@lem3648660 _93408 _93424 s P f t h1)). Qed.
Lemma lem3648666 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : @SUBSET _93408 u s.
Proof. exact (proj1 (@lem3648270 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648667 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term262 _93408 u s.
Proof. exact (fun h0 : term254 _93408 u s => @lem3648666 _93408 _93424 u t' s P f h1). Qed.
Lemma lem3648669 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3648670 {_93408 : Type'} (u : _93408 -> Prop) (s : _93408 -> Prop) : (term262 _93408 u s) = (@SUBSET _93408 u s).
Proof. exact (@lem3648669 (@SUBSET _93408 u s)). Qed.
Lemma lem3648671 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : @SUBSET _93408 u s.
Proof. exact (EQ_MP (@lem3648670 _93408 u s) (@lem3648667 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648677 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3648678 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : (term84 _93408 _93424 s P f _40030) = (term295 _93408 _93424 P f _40030 s).
Proof. exact (@lem3648677 (term83 _93408 _93424 P f _40030) (term254 _93408 _40030 s)). Qed.
Lemma lem3648684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3648685 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : (term296 _93408 _93424 s P f _40030) = (term297 _93408 _93424 P f _40030 s).
Proof. exact (MK_COMB (@lem3648684) (@lem3648678 _93408 _93424 P f _40030 s)). Qed.
Lemma lem3648691 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : (term295 _93408 _93424 P f _40030 s) = (term295 _93408 _93424 P f _40030 s).
Proof. exact (eq_refl (term295 _93408 _93424 P f _40030 s)). Qed.
Lemma lem3648692 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : ((term84 _93408 _93424 s P f _40030) = (term295 _93408 _93424 P f _40030 s)) = ((term295 _93408 _93424 P f _40030 s) = (term295 _93408 _93424 P f _40030 s)).
Proof. exact (MK_COMB (@lem3648685 _93408 _93424 P f _40030 s) (@lem3648691 _93408 _93424 P f _40030 s)). Qed.
Lemma lem3648694 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3648695 (x : Prop) : (x = x) = True.
Proof. exact (@lem3648694 Prop x). Qed.
Lemma lem3648696 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : ((term295 _93408 _93424 P f _40030 s) = (term295 _93408 _93424 P f _40030 s)) = True.
Proof. exact (@lem3648695 (term295 _93408 _93424 P f _40030 s)). Qed.
Lemma lem3648697 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : ((term84 _93408 _93424 s P f _40030) = (term295 _93408 _93424 P f _40030 s)) = True.
Proof. exact (TRANS (@lem3648692 _93408 _93424 P f _40030 s) (@lem3648696 _93408 _93424 P f _40030 s)). Qed.
Lemma lem3648698 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : True = ((term84 _93408 _93424 s P f _40030) = (term295 _93408 _93424 P f _40030 s)).
Proof. exact (SYM (@lem3648697 _93408 _93424 P f _40030 s)). Qed.
Lemma lem3648699 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : (term84 _93408 _93424 s P f _40030) = (term295 _93408 _93424 P f _40030 s).
Proof. exact (EQ_MP (@lem3648698 _93408 _93424 P f _40030 s) (@lem0)). Qed.
Lemma lem3648700 {_93408 _93424 : Type'} (_40030 : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term295 _93408 _93424 P f _40030 s.
Proof. exact (EQ_MP (@lem3648699 _93408 _93424 P f _40030 s) (@lem3648418 _93408 _93424 _40030 u t' s P f h1)). Qed.
Lemma lem3648702 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3648703 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) : (term295 _93408 _93424 P f _40030 s) = (term298 _93408 _93424 s P f _40030).
Proof. exact (@lem3648702 (term254 _93408 _40030 s) (term83 _93408 _93424 P f _40030)). Qed.
Lemma lem3648705 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3648706 {_93408 : Type'} (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : (term283 _93408 _40030 s) = (@SUBSET _93408 _40030 s).
Proof. exact (@lem3648705 (@SUBSET _93408 _40030 s)). Qed.
Lemma lem3648707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3648708 {_93408 : Type'} (_40030 : _93408 -> Prop) (s : _93408 -> Prop) : (term299 _93408 _40030 s) = (term300 _93408 _40030 s).
Proof. exact (MK_COMB (@lem3648707) (@lem3648706 _93408 _40030 s)). Qed.
Lemma lem3648709 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) : (term83 _93408 _93424 P f _40030) = (term83 _93408 _93424 P f _40030).
Proof. exact (eq_refl (term83 _93408 _93424 P f _40030)). Qed.
Lemma lem3648710 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) : (term298 _93408 _93424 s P f _40030) = (term45 _93408 _93424 s P f _40030).
Proof. exact (MK_COMB (@lem3648708 _93408 _40030 s) (@lem3648709 _93408 _93424 P f _40030)). Qed.
Lemma lem3648711 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (_40030 : _93408 -> Prop) : (term295 _93408 _93424 P f _40030 s) = (term45 _93408 _93424 s P f _40030).
Proof. exact (TRANS (@lem3648703 _93408 _93424 s P f _40030) (@lem3648710 _93408 _93424 s P f _40030)). Qed.
Lemma lem3648714 {_93408 _93424 : Type'} (_40030 : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term45 _93408 _93424 s P f _40030.
Proof. exact (EQ_MP (@lem3648711 _93408 _93424 s P f _40030) (@lem3648700 _93408 _93424 _40030 u t' s P f h1)). Qed.
Lemma lem3648715 {_93408 _93424 : Type'} (_40030 : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term45 _93408 _93424 s P f _40030.
Proof. exact (@lem3648714 _93408 _93424 _40030 u t' s P f h1). Qed.
Lemma lem3648716 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term45 _93408 _93424 s P f u.
Proof. exact (@lem3648715 _93408 _93424 u u t' s P f h1). Qed.
Lemma lem3648719 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term83 _93408 _93424 P f u.
Proof. exact (@lem3648716 _93408 _93424 u t' s P f h1 (@lem3648671 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648720 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term292 _93408 _93424 P f u.
Proof. exact (fun h0 : term256 _93408 _93424 P f u => @lem3648719 _93408 _93424 u t' s P f h1). Qed.
Lemma lem3648722 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3648723 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term292 _93408 _93424 P f u) = (term83 _93408 _93424 P f u).
Proof. exact (@lem3648722 (term83 _93408 _93424 P f u)). Qed.
Lemma lem3648724 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term83 _93408 _93424 P f u.
Proof. exact (EQ_MP (@lem3648723 _93408 _93424 P f u) (@lem3648720 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648727 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3648729 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) (u : _93408 -> Prop) : (term256 _93408 _93424 P f u) = (term293 _93408 _93424 P f u).
Proof. exact (@lem3648727 (term83 _93408 _93424 P f u)). Qed.
Lemma lem3648732 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term293 _93408 _93424 P f u.
Proof. exact (EQ_MP (@lem3648729 _93408 _93424 P f u) (@lem3648431 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648735 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : False.
Proof. exact (@lem3648732 _93408 _93424 u t' s P f h1 (@lem3648724 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648736 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : term294.
Proof. exact (fun h0 : ~ False => @lem3648735 _93408 _93424 u t' s P f h1). Qed.
Lemma lem3648738 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3648739 : term294 = False.
Proof. exact (@lem3648738 False). Qed.
Lemma lem3648741 {_93408 _93424 : Type'} (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term171 _93408 _93424 u t' s P f) : False.
Proof. exact (EQ_MP (@lem3648739) (@lem3648736 _93408 _93424 u t' s P f h1)). Qed.
Lemma lem3648742 {_93408 _93424 : Type'} (t : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term221 _93408 _93424 t u t' s P f) : False.
Proof. exact (or_elim (@lem3648260 _93408 _93424 t u t' s P f h1) (fun h0 : term118 _93408 _93424 s P f t => @lem3648664 _93408 _93424 s P f t h0) (fun h0 : term171 _93408 _93424 u t' s P f => @lem3648741 _93408 _93424 u t' s P f h0)). Qed.
Lemma lem3648743 {_93408 _93424 : Type'} (t : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term221 _93408 _93424 t u t' s P f) : (term221 _93408 _93424 t u t' s P f) = False.
Proof. exact (prop_ext (fun h2 : term221 _93408 _93424 t u t' s P f => @lem3648742 _93408 _93424 t u t' s P f h1) (fun h2 : False => @lem3648260 _93408 _93424 t u t' s P f h1)). Qed.
Lemma lem3648744 {_93408 _93424 : Type'} (t : _93408 -> Prop) (u : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term221 _93408 _93424 t u t' s P f) : False.
Proof. exact (EQ_MP (@lem3648743 _93408 _93424 t u t' s P f h1) (@lem3648260 _93408 _93424 t u t' s P f h1)). Qed.
Lemma lem3648745 {_93408 _93424 : Type'} (t : _93408 -> Prop) (t' : _93424 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term224 _93408 _93424 t t' s P f) : False.
Proof. exact (ex_elim (@lem3648154 _93408 _93424 t t' s P f h1) (fun u : _93408 -> Prop => fun h0 : term223 _93408 _93424 t t' s P f u => @lem3648744 _93408 _93424 t u t' s P f h0)). Qed.
Lemma lem3648746 {_93408 _93424 : Type'} (t : _93408 -> Prop) (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term226 _93408 _93424 t s P f) : False.
Proof. exact (ex_elim (@lem3648153 _93408 _93424 t s P f h1) (fun t' : _93424 -> Prop => fun h0 : term225 _93408 _93424 t s P f t' => @lem3648745 _93408 _93424 t t' s P f h0)). Qed.
Lemma lem3648747 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term50 _93408 _93424 s P f) : False.
Proof. exact (ex_elim (@lem3648152 _93408 _93424 s P f h1) (fun t : _93408 -> Prop => fun h0 : term227 _93408 _93424 s P f t => @lem3648746 _93408 _93424 t s P f h0)). Qed.
Lemma lem3648748 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term50 _93408 _93424 s P f) : (term50 _93408 _93424 s P f) = False.
Proof. exact (prop_ext (fun h2 : term50 _93408 _93424 s P f => @lem3648747 _93408 _93424 s P f h1) (fun h2 : False => @lem3647606 _93408 _93424 s P f h1)). Qed.
Lemma lem3648749 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) (h1 : term50 _93408 _93424 s P f) : False.
Proof. exact (EQ_MP (@lem3648748 _93408 _93424 s P f h1) (@lem3647606 _93408 _93424 s P f h1)). Qed.
Lemma lem3648750 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : term49 _93408 _93424 s P f.
Proof. exact (fun h0 : term50 _93408 _93424 s P f => @lem3648749 _93408 _93424 s P f h0). Qed.
Lemma lem3648751 {_93408 _93424 : Type'} (s : _93408 -> Prop) (P : type686 _93424) (f : _93408 -> _93424) : (term21 _93408 _93424 s f P) = (term24 _93408 _93424 s P f).
Proof. exact (EQ_MP (@lem3647605 _93408 _93424 s P f) (@lem3648750 _93408 _93424 s P f)). Qed.
Lemma lem3648756 {_93408 _93424 : Type'} (P : type686 _93424) (f : _93408 -> _93424) : term28 _93408 _93424 P f.
Proof. exact (fun s : _93408 -> Prop => @lem3648751 _93408 _93424 s P f). Qed.
Lemma lem3648761 {_93408 _93424 : Type'} (P : type686 _93424) : term32 _93408 _93424 P.
Proof. exact (fun f : _93408 -> _93424 => @lem3648756 _93408 _93424 P f). Qed.
Lemma lem3648766 {_93408 _93424 : Type'} : term36 _93408 _93424.
Proof. exact (fun P : type686 _93424 => @lem3648761 _93408 _93424 P). Qed.
Lemma lem3648767 {_93408 _93424 : Type'} : term38 _93408 _93424.
Proof. exact (EQ_MP (@lem3647601 _93408 _93424) (@lem3648766 _93408 _93424)). Qed.
Lemma lem3648769 {_93408 _93424 : Type'} : term38 _93408 _93424.
Proof. exact (@lem3647435 _93408 _93424 (@lem3648767 _93408 _93424)). Qed.
Lemma lem3648770 {_93408 _93424 : Type'} (h1 : term39 _93408 _93424) : False.
Proof. exact (@lem3648769 _93408 _93424 (@lem3647419 _93408 _93424 h1)). Qed.
Lemma lem3648771 {_93408 _93424 : Type'} (h1 : term39 _93408 _93424) : (term39 _93408 _93424) = False.
Proof. exact (prop_ext (fun h2 : term39 _93408 _93424 => @lem3648770 _93408 _93424 h1) (fun h2 : False => @lem3647419 _93408 _93424 h1)). Qed.
Lemma lem3648772 {_93408 _93424 : Type'} (h1 : term39 _93408 _93424) : False.
Proof. exact (EQ_MP (@lem3648771 _93408 _93424 h1) (@lem3647419 _93408 _93424 h1)). Qed.
Lemma lem3648773 {_93408 _93424 : Type'} : term38 _93408 _93424.
Proof. exact (fun h0 : term39 _93408 _93424 => @lem3648772 _93408 _93424 h0). Qed.
Lemma lem3648774 {_93408 _93424 : Type'} : term36 _93408 _93424.
Proof. exact (EQ_MP (@lem3647418 _93408 _93424) (@lem3648773 _93408 _93424)). Qed.
Lemma lem3648775 {_93408 _93424 : Type'} : term35 _93408 _93424.
Proof. exact (EQ_MP (@lem3647414 _93408 _93424) (@lem3648774 _93408 _93424)). Qed.
