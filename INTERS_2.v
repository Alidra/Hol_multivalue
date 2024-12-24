Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_2_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19699_spec.
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
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3355418 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3355419 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (s = t) = (term0 _87260 s t).
Proof. exact (@lem3355418 _87260 s t). Qed.
Lemma lem3355420 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : ((term1 _87260 s t) = (@INTER _87260 s t)) = (term2 _87260 s t).
Proof. exact (@lem3355419 _87260 (term1 _87260 s t) (@INTER _87260 s t)). Qed.
Lemma lem3355429 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term2 _87260 s t) = ((term1 _87260 s t) = (@INTER _87260 s t)).
Proof. exact (SYM (@lem3355420 _87260 s t)). Qed.
Lemma lem3355437 {A : Type'} (s : type686 A) (x : A) : (term3 A x s) = (term4 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3355438 {_87260 : Type'} (s : type686 _87260) (x : _87260) : (term3 _87260 x s) = (term4 _87260 s x).
Proof. exact (@lem3355437 _87260 s x). Qed.
Lemma lem3355439 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term5 _87260 x s t) = (term6 _87260 s t x).
Proof. exact (@lem3355438 _87260 (term7 _87260 s t) x). Qed.
Lemma lem3355447 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3355448 {_87260 : Type'} (y : _87260 -> Prop) (x : _87260 -> Prop) (s : type686 _87260) : (term10 _87260 x y s) = (term11 _87260 y x s).
Proof. exact (@lem3355447 (_87260 -> Prop) y x s). Qed.
Lemma lem3355449 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term12 _87260 t' s t) = (term13 _87260 s t' t).
Proof. exact (@lem3355448 _87260 s t' (@INSERT (_87260 -> Prop) t (@EMPTY (_87260 -> Prop)))). Qed.
Lemma lem3355455 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3355456 {_87260 : Type'} (y : _87260 -> Prop) (x : _87260 -> Prop) (s : type686 _87260) : (term10 _87260 x y s) = (term11 _87260 y x s).
Proof. exact (@lem3355455 (_87260 -> Prop) y x s). Qed.
Lemma lem3355457 {_87260 : Type'} (t : _87260 -> Prop) (t' : _87260 -> Prop) : (term14 _87260 t' t) = (term15 _87260 t t').
Proof. exact (@lem3355456 _87260 t t' (@EMPTY (_87260 -> Prop))). Qed.
Lemma lem3355463 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3355464 {_87260 : Type'} (x : _87260 -> Prop) : (@IN (_87260 -> Prop) x (@EMPTY (_87260 -> Prop))) = False.
Proof. exact (@lem3355463 (_87260 -> Prop) x). Qed.
Lemma lem3355465 {_87260 : Type'} (t' : _87260 -> Prop) : (@IN (_87260 -> Prop) t' (@EMPTY (_87260 -> Prop))) = False.
Proof. exact (@lem3355464 _87260 t'). Qed.
Lemma lem3355466 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term16 _87260 t' t) = (term16 _87260 t' t).
Proof. exact (eq_refl (term16 _87260 t' t)). Qed.
Lemma lem3355467 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term15 _87260 t t') = (term17 _87260 t' t).
Proof. exact (MK_COMB (@lem3355466 _87260 t' t) (@lem3355465 _87260 t')). Qed.
Lemma lem3355469 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3355470 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term17 _87260 t' t) = (t' = t).
Proof. exact (@lem3355469 (t' = t)). Qed.
Lemma lem3355473 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term15 _87260 t t') = (t' = t).
Proof. exact (TRANS (@lem3355467 _87260 t' t) (@lem3355470 _87260 t' t)). Qed.
Lemma lem3355474 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term14 _87260 t' t) = (t' = t).
Proof. exact (TRANS (@lem3355457 _87260 t t') (@lem3355473 _87260 t' t)). Qed.
Lemma lem3355475 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) : (term16 _87260 t' s) = (term16 _87260 t' s).
Proof. exact (eq_refl (term16 _87260 t' s)). Qed.
Lemma lem3355476 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term13 _87260 s t' t) = (term18 _87260 s t' t).
Proof. exact (MK_COMB (@lem3355475 _87260 t' s) (@lem3355474 _87260 t' t)). Qed.
Lemma lem3355479 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term12 _87260 t' s t) = (term18 _87260 s t' t).
Proof. exact (TRANS (@lem3355449 _87260 s t' t) (@lem3355476 _87260 s t' t)). Qed.
Lemma lem3355480 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3355481 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term19 _87260 t' s t) = (term20 _87260 s t' t).
Proof. exact (MK_COMB (@lem3355480) (@lem3355479 _87260 s t' t)). Qed.
Lemma lem3355483 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3355484 {_87260 : Type'} (P : _87260 -> Prop) (x : _87260) : (@IN _87260 x P) = (P x).
Proof. exact (@lem3355483 _87260 P x). Qed.
Lemma lem3355485 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (@IN _87260 x t') = (t' x).
Proof. exact (@lem3355484 _87260 t' x). Qed.
Lemma lem3355486 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term21 _87260 s t x t') = (term22 _87260 s t t' x).
Proof. exact (MK_COMB (@lem3355481 _87260 s t' t) (@lem3355485 _87260 t' x)). Qed.
Lemma lem3355489 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term23 _87260 s t x) = (term24 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355486 _87260 s t t' x)). Qed.
Lemma lem3355490 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355491 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term6 _87260 s t x) = (term25 _87260 s t x).
Proof. exact (MK_COMB (@lem3355490 _87260) (@lem3355489 _87260 s t x)). Qed.
Lemma lem3355496 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term5 _87260 x s t) = (term25 _87260 s t x).
Proof. exact (TRANS (@lem3355439 _87260 s t x) (@lem3355491 _87260 s t x)). Qed.
Lemma lem3355497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355498 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term26 _87260 x s t) = (term27 _87260 s t x).
Proof. exact (MK_COMB (@lem3355497) (@lem3355496 _87260 s t x)). Qed.
Lemma lem3355500 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3355501 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t : _87260 -> Prop) : (term28 _87260 x s t) = (term29 _87260 s x t).
Proof. exact (@lem3355500 _87260 s x t). Qed.
Lemma lem3355505 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3355506 {_87260 : Type'} (P : _87260 -> Prop) (x : _87260) : (@IN _87260 x P) = (P x).
Proof. exact (@lem3355505 _87260 P x). Qed.
Lemma lem3355507 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (@IN _87260 x s) = (s x).
Proof. exact (@lem3355506 _87260 s x). Qed.
Lemma lem3355508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355509 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term30 _87260 x s) = (term31 _87260 s x).
Proof. exact (MK_COMB (@lem3355508) (@lem3355507 _87260 s x)). Qed.
Lemma lem3355511 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3355512 {_87260 : Type'} (P : _87260 -> Prop) (x : _87260) : (@IN _87260 x P) = (P x).
Proof. exact (@lem3355511 _87260 P x). Qed.
Lemma lem3355513 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (@IN _87260 x t) = (t x).
Proof. exact (@lem3355512 _87260 t x). Qed.
Lemma lem3355514 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term29 _87260 s x t) = (term32 _87260 s t x).
Proof. exact (MK_COMB (@lem3355509 _87260 s x) (@lem3355513 _87260 t x)). Qed.
Lemma lem3355517 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term28 _87260 x s t) = (term32 _87260 s t x).
Proof. exact (TRANS (@lem3355501 _87260 s x t) (@lem3355514 _87260 s t x)). Qed.
Lemma lem3355518 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term5 _87260 x s t) = (term28 _87260 x s t)) = ((term25 _87260 s t x) = (term32 _87260 s t x)).
Proof. exact (MK_COMB (@lem3355498 _87260 s t x) (@lem3355517 _87260 s t x)). Qed.
Lemma lem3355521 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term33 _87260 s t) = (term34 _87260 s t).
Proof. exact (fun_ext (fun x : _87260 => @lem3355518 _87260 s t x)). Qed.
Lemma lem3355522 {_87260 : Type'} : (@all _87260) = (@all _87260).
Proof. exact (eq_refl (@all _87260)). Qed.
Lemma lem3355523 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term2 _87260 s t) = (term35 _87260 s t).
Proof. exact (MK_COMB (@lem3355522 _87260) (@lem3355521 _87260 s t)). Qed.
Lemma lem3355528 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term35 _87260 s t) = (term2 _87260 s t).
Proof. exact (SYM (@lem3355523 _87260 s t)). Qed.
Lemma lem3355530 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3355531 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term35 _87260 s t) = (term37 _87260 s t).
Proof. exact (@lem3355530 (term35 _87260 s t)). Qed.
Lemma lem3355532 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term37 _87260 s t) = (term35 _87260 s t).
Proof. exact (SYM (@lem3355531 _87260 s t)). Qed.
Lemma lem3355533 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term38 _87260 s t) : term38 _87260 s t.
Proof. exact (h1). Qed.
Lemma lem3355536 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term37 _87260 s t) : term37 _87260 s t.
Proof. exact (h1). Qed.
Lemma lem3355537 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term39 _87260 s t.
Proof. exact (fun h0 : term37 _87260 s t => @lem3355536 _87260 s t h0). Qed.
Lemma lem3355538 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term39 _87260 s t) : term39 _87260 s t.
Proof. exact (h1). Qed.
Lemma lem3355539 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term37 _87260 s t) : term37 _87260 s t.
Proof. exact (h1). Qed.
Lemma lem3355540 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term37 _87260 s t) (h2 : term39 _87260 s t) : term37 _87260 s t.
Proof. exact (@lem3355538 _87260 s t h2 (@lem3355539 _87260 s t h1)). Qed.
Lemma lem3355541 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term37 _87260 s t) : term40 _87260 s t.
Proof. exact (fun h0 : term39 _87260 s t => @lem3355540 _87260 s t h1 h0). Qed.
Lemma lem3355542 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term39 _87260 s t) : term39 _87260 s t.
Proof. exact (h1). Qed.
Lemma lem3355543 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term37 _87260 s t) (h2 : term39 _87260 s t) : term37 _87260 s t.
Proof. exact (@lem3355541 _87260 s t h1 (@lem3355542 _87260 s t h2)). Qed.
Lemma lem3355544 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term39 _87260 s t) : term39 _87260 s t.
Proof. exact (fun h0 : term37 _87260 s t => @lem3355543 _87260 s t h0 h1). Qed.
Lemma lem3355545 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term41 _87260 s t.
Proof. exact (fun h0 : term39 _87260 s t => @lem3355544 _87260 s t h0). Qed.
Lemma lem3355548 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term39 _87260 s t.
Proof. exact (@lem3355545 _87260 s t (@lem3355537 _87260 s t)). Qed.
Lemma lem3355549 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term39 _87260 s t.
Proof. exact (@lem3355548 _87260 s t). Qed.
Lemma lem3355559 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3355560 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term37 _87260 s t) = (term42 _87260 s t).
Proof. exact (@lem3355559 (term38 _87260 s t)). Qed.
Lemma lem3355562 (t : Prop) : (term43 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3355563 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term42 _87260 s t) = (term35 _87260 s t).
Proof. exact (@lem3355562 (term35 _87260 s t)). Qed.
Lemma lem3355568 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term37 _87260 s t) = (term35 _87260 s t).
Proof. exact (TRANS (@lem3355560 _87260 s t) (@lem3355563 _87260 s t)). Qed.
Lemma lem3355579 {_87260 : Type'} (t : _87260 -> Prop) : (term44 _87260 t) = (term45 _87260 t).
Proof. exact (fun_ext (fun s : _87260 -> Prop => @lem3355568 _87260 s t)). Qed.
Lemma lem3355580 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355581 {_87260 : Type'} (t : _87260 -> Prop) : (term46 _87260 t) = (term47 _87260 t).
Proof. exact (MK_COMB (@lem3355580 _87260) (@lem3355579 _87260 t)). Qed.
Lemma lem3355586 {_87260 : Type'} : (term48 _87260) = (term49 _87260).
Proof. exact (fun_ext (fun t : _87260 -> Prop => @lem3355581 _87260 t)). Qed.
Lemma lem3355587 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355596 {_87260 : Type'} : (term50 _87260) = (term51 _87260).
Proof. exact (MK_COMB (@lem3355587 _87260) (@lem3355586 _87260)). Qed.
Lemma lem3355601 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term32 _87260 s t x) = (term32 _87260 s t x).
Proof. exact (eq_refl (term32 _87260 s t x)). Qed.
Lemma lem3355610 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term22 _87260 s t t' x) = (term22 _87260 s t t' x).
Proof. exact (eq_refl (term22 _87260 s t t' x)). Qed.
Lemma lem3355611 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term24 _87260 s t x) = (term24 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355610 _87260 s t t' x)). Qed.
Lemma lem3355612 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355613 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term25 _87260 s t x) = (term25 _87260 s t x).
Proof. exact (MK_COMB (@lem3355612 _87260) (@lem3355611 _87260 s t x)). Qed.
Lemma lem3355614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355615 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term27 _87260 s t x) = (term27 _87260 s t x).
Proof. exact (MK_COMB (@lem3355614) (@lem3355613 _87260 s t x)). Qed.
Lemma lem3355616 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term25 _87260 s t x) = (term32 _87260 s t x)) = ((term25 _87260 s t x) = (term32 _87260 s t x)).
Proof. exact (MK_COMB (@lem3355615 _87260 s t x) (@lem3355601 _87260 s t x)). Qed.
Lemma lem3355617 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term34 _87260 s t) = (term34 _87260 s t).
Proof. exact (fun_ext (fun x : _87260 => @lem3355616 _87260 s t x)). Qed.
Lemma lem3355618 {_87260 : Type'} : (@all _87260) = (@all _87260).
Proof. exact (eq_refl (@all _87260)). Qed.
Lemma lem3355619 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term35 _87260 s t) = (term35 _87260 s t).
Proof. exact (MK_COMB (@lem3355618 _87260) (@lem3355617 _87260 s t)). Qed.
Lemma lem3355620 {_87260 : Type'} (t : _87260 -> Prop) : (term45 _87260 t) = (term45 _87260 t).
Proof. exact (fun_ext (fun s : _87260 -> Prop => @lem3355619 _87260 s t)). Qed.
Lemma lem3355621 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355622 {_87260 : Type'} (t : _87260 -> Prop) : (term47 _87260 t) = (term47 _87260 t).
Proof. exact (MK_COMB (@lem3355621 _87260) (@lem3355620 _87260 t)). Qed.
Lemma lem3355623 {_87260 : Type'} : (term49 _87260) = (term49 _87260).
Proof. exact (fun_ext (fun t : _87260 -> Prop => @lem3355622 _87260 t)). Qed.
Lemma lem3355624 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355625 {_87260 : Type'} : (term51 _87260) = (term51 _87260).
Proof. exact (MK_COMB (@lem3355624 _87260) (@lem3355623 _87260)). Qed.
Lemma lem3355658 {_87260 : Type'} : (term50 _87260) = (term51 _87260).
Proof. exact (TRANS (@lem3355596 _87260) (@lem3355625 _87260)). Qed.
Lemma lem3355659 {_87260 : Type'} : (term51 _87260) = (term50 _87260).
Proof. exact (SYM (@lem3355658 _87260)). Qed.
Lemma lem3355661 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3355662 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term25 _87260 s t x) = (term32 _87260 s t x)) = (term52 _87260 s t x).
Proof. exact (@lem3355661 ((term25 _87260 s t x) = (term32 _87260 s t x))). Qed.
Lemma lem3355663 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term52 _87260 s t x) = ((term25 _87260 s t x) = (term32 _87260 s t x)).
Proof. exact (SYM (@lem3355662 _87260 s t x)). Qed.
Lemma lem3355664 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term53 _87260 s t x) : term53 _87260 s t x.
Proof. exact (h1). Qed.
Lemma lem3355673 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term54 _87260 s t' t) = (term55 _87260 s t' t).
Proof. exact (@lem17160 (t' = s) (t' = t)). Qed.
Lemma lem3355678 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (t' x) = (t' x).
Proof. exact (eq_refl (t' x)). Qed.
Lemma lem3355683 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term56 _87260 s t t' x) = (term57 _87260 s t t' x).
Proof. exact (@lem17362 (term18 _87260 s t' t) (t' x)). Qed.
Lemma lem3355684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3355685 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term58 _87260 s t' t) = (term59 _87260 s t' t).
Proof. exact (MK_COMB (@lem3355684) (@lem3355673 _87260 s t' t)). Qed.
Lemma lem3355686 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term60 _87260 s t t' x) = (term61 _87260 s t t' x).
Proof. exact (MK_COMB (@lem3355685 _87260 s t' t) (@lem3355678 _87260 t' x)). Qed.
Lemma lem3355687 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term22 _87260 s t t' x) = (term60 _87260 s t t' x).
Proof. exact (@lem17265 (term18 _87260 s t' t) (t' x)). Qed.
Lemma lem3355688 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term22 _87260 s t t' x) = (term61 _87260 s t t' x).
Proof. exact (TRANS (@lem3355687 _87260 s t t' x) (@lem3355686 _87260 s t t' x)). Qed.
Lemma lem3355689 {_87260 : Type'} (P : type686 _87260) : (term62 _87260 P) = (term63 _87260 P).
Proof. exact (@lem18392 (_87260 -> Prop) P). Qed.
Lemma lem3355690 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term64 _87260 s t x) = (term65 _87260 s t x).
Proof. exact (@lem3355689 _87260 (term24 _87260 s t x)). Qed.
Lemma lem3355691 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term66 _87260 s t x t') = (term22 _87260 s t t' x).
Proof. exact (eq_refl (term66 _87260 s t x t')). Qed.
Lemma lem3355692 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3355693 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term67 _87260 s t x t') = (term56 _87260 s t t' x).
Proof. exact (MK_COMB (@lem3355692) (@lem3355691 _87260 s t t' x)). Qed.
Lemma lem3355694 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term67 _87260 s t x t') = (term57 _87260 s t t' x).
Proof. exact (TRANS (@lem3355693 _87260 s t t' x) (@lem3355683 _87260 s t t' x)). Qed.
Lemma lem3355695 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term68 _87260 s t x) = (term69 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355694 _87260 s t t' x)). Qed.
Lemma lem3355696 {_87260 : Type'} : (@ex (_87260 -> Prop)) = (@ex (_87260 -> Prop)).
Proof. exact (eq_refl (@ex (_87260 -> Prop))). Qed.
Lemma lem3355697 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term65 _87260 s t x) = (term70 _87260 s t x).
Proof. exact (MK_COMB (@lem3355696 _87260) (@lem3355695 _87260 s t x)). Qed.
Lemma lem3355698 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term64 _87260 s t x) = (term70 _87260 s t x).
Proof. exact (TRANS (@lem3355690 _87260 s t x) (@lem3355697 _87260 s t x)). Qed.
Lemma lem3355699 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term24 _87260 s t x) = (term71 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355688 _87260 s t t' x)). Qed.
Lemma lem3355700 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355701 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term25 _87260 s t x) = (term72 _87260 s t x).
Proof. exact (MK_COMB (@lem3355700 _87260) (@lem3355699 _87260 s t x)). Qed.
Lemma lem3355710 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term73 _87260 s t x) = (term74 _87260 s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3355713 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term32 _87260 s t x) = (term32 _87260 s t x).
Proof. exact (eq_refl (term32 _87260 s t x)). Qed.
Lemma lem3355714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355715 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term75 _87260 s t x) = (term76 _87260 s t x).
Proof. exact (MK_COMB (@lem3355714) (@lem3355698 _87260 s t x)). Qed.
Lemma lem3355716 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term77 _87260 s t x) = (term78 _87260 s t x).
Proof. exact (MK_COMB (@lem3355715 _87260 s t x) (@lem3355713 _87260 s t x)). Qed.
Lemma lem3355717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355718 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term79 _87260 s t x) = (term80 _87260 s t x).
Proof. exact (MK_COMB (@lem3355717) (@lem3355701 _87260 s t x)). Qed.
Lemma lem3355719 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term81 _87260 s t x) = (term82 _87260 s t x).
Proof. exact (MK_COMB (@lem3355718 _87260 s t x) (@lem3355710 _87260 s t x)). Qed.
Lemma lem3355720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3355721 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term83 _87260 s t x) = (term84 _87260 s t x).
Proof. exact (MK_COMB (@lem3355720) (@lem3355719 _87260 s t x)). Qed.
Lemma lem3355722 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term85 _87260 s t x) = (term86 _87260 s t x).
Proof. exact (MK_COMB (@lem3355721 _87260 s t x) (@lem3355716 _87260 s t x)). Qed.
Lemma lem3355723 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term53 _87260 s t x) = (term85 _87260 s t x).
Proof. exact (@lem17646 (term25 _87260 s t x) (term32 _87260 s t x)). Qed.
Lemma lem3355724 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term53 _87260 s t x) = (term86 _87260 s t x).
Proof. exact (TRANS (@lem3355723 _87260 s t x) (@lem3355722 _87260 s t x)). Qed.
Lemma lem3355823 {A : Type'} (P : A -> Prop) (Q : Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3355824 {_87260 : Type'} (P : type686 _87260) (Q : Prop) : (term89 _87260 P Q) = (term90 _87260 P Q).
Proof. exact (@lem3355823 (_87260 -> Prop) P Q). Qed.
Lemma lem3355825 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term91 _87260 s t x) = (term92 _87260 s t x).
Proof. exact (@lem3355824 _87260 (term69 _87260 s t x) (term32 _87260 s t x)). Qed.
Lemma lem3355826 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term93 _87260 s t x t') = (term57 _87260 s t t' x).
Proof. exact (eq_refl (term93 _87260 s t x t')). Qed.
Lemma lem3355827 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term94 _87260 s t x) = (term69 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355826 _87260 s t t' x)). Qed.
Lemma lem3355828 {_87260 : Type'} : (@ex (_87260 -> Prop)) = (@ex (_87260 -> Prop)).
Proof. exact (eq_refl (@ex (_87260 -> Prop))). Qed.
Lemma lem3355829 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term95 _87260 s t x) = (term70 _87260 s t x).
Proof. exact (MK_COMB (@lem3355828 _87260) (@lem3355827 _87260 s t x)). Qed.
Lemma lem3355830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355831 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term96 _87260 s t x) = (term76 _87260 s t x).
Proof. exact (MK_COMB (@lem3355830) (@lem3355829 _87260 s t x)). Qed.
Lemma lem3355832 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term32 _87260 s t x) = (term32 _87260 s t x).
Proof. exact (eq_refl (term32 _87260 s t x)). Qed.
Lemma lem3355833 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term91 _87260 s t x) = (term78 _87260 s t x).
Proof. exact (MK_COMB (@lem3355831 _87260 s t x) (@lem3355832 _87260 s t x)). Qed.
Lemma lem3355834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355835 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term97 _87260 s t x) = (term98 _87260 s t x).
Proof. exact (MK_COMB (@lem3355834) (@lem3355833 _87260 s t x)). Qed.
Lemma lem3355836 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term93 _87260 s t x t') = (term57 _87260 s t t' x).
Proof. exact (eq_refl (term93 _87260 s t x t')). Qed.
Lemma lem3355837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355838 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term99 _87260 s t x t') = (term100 _87260 s t t' x).
Proof. exact (MK_COMB (@lem3355837) (@lem3355836 _87260 s t t' x)). Qed.
Lemma lem3355839 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term32 _87260 s t x) = (term32 _87260 s t x).
Proof. exact (eq_refl (term32 _87260 s t x)). Qed.
Lemma lem3355840 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term101 _87260 t' s t x) = (term102 _87260 t' s t x).
Proof. exact (MK_COMB (@lem3355838 _87260 s t t' x) (@lem3355839 _87260 s t x)). Qed.
Lemma lem3355841 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term103 _87260 s t x) = (term104 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355840 _87260 t' s t x)). Qed.
Lemma lem3355842 {_87260 : Type'} : (@ex (_87260 -> Prop)) = (@ex (_87260 -> Prop)).
Proof. exact (eq_refl (@ex (_87260 -> Prop))). Qed.
Lemma lem3355843 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term92 _87260 s t x) = (term105 _87260 s t x).
Proof. exact (MK_COMB (@lem3355842 _87260) (@lem3355841 _87260 s t x)). Qed.
Lemma lem3355844 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term91 _87260 s t x) = (term92 _87260 s t x)) = ((term78 _87260 s t x) = (term105 _87260 s t x)).
Proof. exact (MK_COMB (@lem3355835 _87260 s t x) (@lem3355843 _87260 s t x)). Qed.
Lemma lem3355845 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term78 _87260 s t x) = (term105 _87260 s t x).
Proof. exact (EQ_MP (@lem3355844 _87260 s t x) (@lem3355825 _87260 s t x)). Qed.
Lemma lem3355846 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term84 _87260 s t x) = (term84 _87260 s t x).
Proof. exact (eq_refl (term84 _87260 s t x)). Qed.
Lemma lem3355847 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term86 _87260 s t x) = (term106 _87260 s t x).
Proof. exact (MK_COMB (@lem3355846 _87260 s t x) (@lem3355845 _87260 s t x)). Qed.
Lemma lem3355849 {A : Type'} (P : Prop) (Q : A -> Prop) : (term107 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3355850 {_87260 : Type'} (P : Prop) (Q : type686 _87260) : (term109 _87260 P Q) = (term110 _87260 P Q).
Proof. exact (@lem3355849 (_87260 -> Prop) P Q). Qed.
Lemma lem3355851 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term111 _87260 s t x) = (term112 _87260 s t x).
Proof. exact (@lem3355850 _87260 (term82 _87260 s t x) (term104 _87260 s t x)). Qed.
Lemma lem3355852 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term113 _87260 s t x t') = (term102 _87260 t' s t x).
Proof. exact (eq_refl (term113 _87260 s t x t')). Qed.
Lemma lem3355853 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term114 _87260 s t x) = (term104 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355852 _87260 t' s t x)). Qed.
Lemma lem3355854 {_87260 : Type'} : (@ex (_87260 -> Prop)) = (@ex (_87260 -> Prop)).
Proof. exact (eq_refl (@ex (_87260 -> Prop))). Qed.
Lemma lem3355855 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term115 _87260 s t x) = (term105 _87260 s t x).
Proof. exact (MK_COMB (@lem3355854 _87260) (@lem3355853 _87260 s t x)). Qed.
Lemma lem3355856 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term84 _87260 s t x) = (term84 _87260 s t x).
Proof. exact (eq_refl (term84 _87260 s t x)). Qed.
Lemma lem3355857 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term111 _87260 s t x) = (term106 _87260 s t x).
Proof. exact (MK_COMB (@lem3355856 _87260 s t x) (@lem3355855 _87260 s t x)). Qed.
Lemma lem3355858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355859 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term116 _87260 s t x) = (term117 _87260 s t x).
Proof. exact (MK_COMB (@lem3355858) (@lem3355857 _87260 s t x)). Qed.
Lemma lem3355860 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term113 _87260 s t x t') = (term102 _87260 t' s t x).
Proof. exact (eq_refl (term113 _87260 s t x t')). Qed.
Lemma lem3355861 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term84 _87260 s t x) = (term84 _87260 s t x).
Proof. exact (eq_refl (term84 _87260 s t x)). Qed.
Lemma lem3355862 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term118 _87260 s t x t') = (term119 _87260 t' s t x).
Proof. exact (MK_COMB (@lem3355861 _87260 s t x) (@lem3355860 _87260 t' s t x)). Qed.
Lemma lem3355863 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term120 _87260 s t x) = (term121 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355862 _87260 t' s t x)). Qed.
Lemma lem3355864 {_87260 : Type'} : (@ex (_87260 -> Prop)) = (@ex (_87260 -> Prop)).
Proof. exact (eq_refl (@ex (_87260 -> Prop))). Qed.
Lemma lem3355865 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term112 _87260 s t x) = (term122 _87260 s t x).
Proof. exact (MK_COMB (@lem3355864 _87260) (@lem3355863 _87260 s t x)). Qed.
Lemma lem3355866 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term111 _87260 s t x) = (term112 _87260 s t x)) = ((term106 _87260 s t x) = (term122 _87260 s t x)).
Proof. exact (MK_COMB (@lem3355859 _87260 s t x) (@lem3355865 _87260 s t x)). Qed.
Lemma lem3355867 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term106 _87260 s t x) = (term122 _87260 s t x).
Proof. exact (EQ_MP (@lem3355866 _87260 s t x) (@lem3355851 _87260 s t x)). Qed.
Lemma lem3355869 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term86 _87260 s t x) = (term122 _87260 s t x).
Proof. exact (TRANS (@lem3355847 _87260 s t x) (@lem3355867 _87260 s t x)). Qed.
Lemma lem3355870 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term53 _87260 s t x) = (term122 _87260 s t x).
Proof. exact (TRANS (@lem3355724 _87260 s t x) (@lem3355869 _87260 s t x)). Qed.
Lemma lem3355871 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term53 _87260 s t x) : term122 _87260 s t x.
Proof. exact (EQ_MP (@lem3355870 _87260 s t x) (@lem3355664 _87260 s t x h1)). Qed.
Lemma lem3355872 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term119 _87260 t' s t x) : term119 _87260 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3355877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355878 {_87260 : Type'} (f : _87260 -> Prop) (x : _87260) : (f x) = (@I (_87260 -> Prop) f x).
Proof. exact (@lem3355877 _87260 Prop f x). Qed.
Lemma lem3355880 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (t x) = (@I (_87260 -> Prop) t x).
Proof. exact (@lem3355878 _87260 t x). Qed.
Lemma lem3355885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355886 {_87260 : Type'} (f : _87260 -> Prop) (x : _87260) : (f x) = (@I (_87260 -> Prop) f x).
Proof. exact (@lem3355885 _87260 Prop f x). Qed.
Lemma lem3355888 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (s x) = (@I (_87260 -> Prop) s x).
Proof. exact (@lem3355886 _87260 s x). Qed.
Lemma lem3355889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355890 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term31 _87260 s x) = (term123 _87260 s x).
Proof. exact (MK_COMB (@lem3355889) (@lem3355888 _87260 s x)). Qed.
Lemma lem3355891 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term32 _87260 s t x) = (term124 _87260 s t x).
Proof. exact (MK_COMB (@lem3355890 _87260 s x) (@lem3355880 _87260 t x)). Qed.
Lemma lem3355892 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3355897 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355898 {_87260 : Type'} (f : _87260 -> Prop) (x : _87260) : (f x) = (@I (_87260 -> Prop) f x).
Proof. exact (@lem3355897 _87260 Prop f x). Qed.
Lemma lem3355900 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (t' x) = (@I (_87260 -> Prop) t' x).
Proof. exact (@lem3355898 _87260 t' x). Qed.
Lemma lem3355901 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (term125 _87260 t' x) = (term126 _87260 t' x).
Proof. exact (MK_COMB (@lem3355892) (@lem3355900 _87260 t' x)). Qed.
Lemma lem3355916 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term127 _87260 s t' t) = (term127 _87260 s t' t).
Proof. exact (eq_refl (term127 _87260 s t' t)). Qed.
Lemma lem3355917 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term57 _87260 s t t' x) = (term128 _87260 s t t' x).
Proof. exact (MK_COMB (@lem3355916 _87260 s t' t) (@lem3355901 _87260 t' x)). Qed.
Lemma lem3355918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355919 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term100 _87260 s t t' x) = (term129 _87260 s t t' x).
Proof. exact (MK_COMB (@lem3355918) (@lem3355917 _87260 s t t' x)). Qed.
Lemma lem3355920 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term102 _87260 t' s t x) = (term130 _87260 t' s t x).
Proof. exact (MK_COMB (@lem3355919 _87260 s t t' x) (@lem3355891 _87260 s t x)). Qed.
Lemma lem3355921 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3355926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355927 {_87260 : Type'} (f : _87260 -> Prop) (x : _87260) : (f x) = (@I (_87260 -> Prop) f x).
Proof. exact (@lem3355926 _87260 Prop f x). Qed.
Lemma lem3355929 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (t x) = (@I (_87260 -> Prop) t x).
Proof. exact (@lem3355927 _87260 t x). Qed.
Lemma lem3355930 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (term125 _87260 t x) = (term126 _87260 t x).
Proof. exact (MK_COMB (@lem3355921) (@lem3355929 _87260 t x)). Qed.
Lemma lem3355931 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3355936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355937 {_87260 : Type'} (f : _87260 -> Prop) (x : _87260) : (f x) = (@I (_87260 -> Prop) f x).
Proof. exact (@lem3355936 _87260 Prop f x). Qed.
Lemma lem3355939 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (s x) = (@I (_87260 -> Prop) s x).
Proof. exact (@lem3355937 _87260 s x). Qed.
Lemma lem3355940 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term125 _87260 s x) = (term126 _87260 s x).
Proof. exact (MK_COMB (@lem3355931) (@lem3355939 _87260 s x)). Qed.
Lemma lem3355941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3355942 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term131 _87260 s x) = (term132 _87260 s x).
Proof. exact (MK_COMB (@lem3355941) (@lem3355940 _87260 s x)). Qed.
Lemma lem3355943 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term74 _87260 s t x) = (term133 _87260 s t x).
Proof. exact (MK_COMB (@lem3355942 _87260 s x) (@lem3355930 _87260 t x)). Qed.
Lemma lem3355948 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355949 {_87260 : Type'} (f : _87260 -> Prop) (x : _87260) : (f x) = (@I (_87260 -> Prop) f x).
Proof. exact (@lem3355948 _87260 Prop f x). Qed.
Lemma lem3355951 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (t' x) = (@I (_87260 -> Prop) t' x).
Proof. exact (@lem3355949 _87260 t' x). Qed.
Lemma lem3355970 {_87260 : Type'} (s : _87260 -> Prop) (t' : _87260 -> Prop) (t : _87260 -> Prop) : (term59 _87260 s t' t) = (term59 _87260 s t' t).
Proof. exact (eq_refl (term59 _87260 s t' t)). Qed.
Lemma lem3355971 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term61 _87260 s t t' x) = (term134 _87260 s t t' x).
Proof. exact (MK_COMB (@lem3355970 _87260 s t' t) (@lem3355951 _87260 t' x)). Qed.
Lemma lem3355972 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term71 _87260 s t x) = (term135 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3355971 _87260 s t t' x)). Qed.
Lemma lem3355973 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3355974 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term72 _87260 s t x) = (term136 _87260 s t x).
Proof. exact (MK_COMB (@lem3355973 _87260) (@lem3355972 _87260 s t x)). Qed.
Lemma lem3355975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355976 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term80 _87260 s t x) = (term137 _87260 s t x).
Proof. exact (MK_COMB (@lem3355975) (@lem3355974 _87260 s t x)). Qed.
Lemma lem3355977 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term82 _87260 s t x) = (term138 _87260 s t x).
Proof. exact (MK_COMB (@lem3355976 _87260 s t x) (@lem3355943 _87260 s t x)). Qed.
Lemma lem3355978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3355979 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term84 _87260 s t x) = (term139 _87260 s t x).
Proof. exact (MK_COMB (@lem3355978) (@lem3355977 _87260 s t x)). Qed.
Lemma lem3355980 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term119 _87260 t' s t x) = (term140 _87260 t' s t x).
Proof. exact (MK_COMB (@lem3355979 _87260 s t x) (@lem3355920 _87260 t' s t x)). Qed.
Lemma lem3355981 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term119 _87260 t' s t x) : term140 _87260 t' s t x.
Proof. exact (EQ_MP (@lem3355980 _87260 t' s t x) (@lem3355872 _87260 t' s t x h1)). Qed.
Lemma lem3355982 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term138 _87260 s t x.
Proof. exact (h1). Qed.
Lemma lem3355983 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term130 _87260 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3355984 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term133 _87260 s t x.
Proof. exact (proj2 (@lem3355982 _87260 s t x h1)). Qed.
Lemma lem3355985 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term136 _87260 s t x.
Proof. exact (proj1 (@lem3355982 _87260 s t x h1)). Qed.
Lemma lem3355988 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term124 _87260 s t x.
Proof. exact (proj2 (@lem3355983 _87260 t' s t x h1)). Qed.
Lemma lem3355989 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term128 _87260 s t t' x.
Proof. exact (proj1 (@lem3355983 _87260 t' s t x h1)). Qed.
Lemma lem3355993 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term18 _87260 s t' t.
Proof. exact (proj1 (@lem3355989 _87260 t' s t x h1)). Qed.
Lemma lem3356013 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term134 _87260 s t t' x) = (term141 _87260 s t t' x).
Proof. exact (@lem19699 (term142 _87260 t' s) (term142 _87260 t' t) (@I (_87260 -> Prop) t' x)). Qed.
Lemma lem3356014 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term135 _87260 s t x) = (term143 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3356013 _87260 s t t' x)). Qed.
Lemma lem3356015 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3356017 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term136 _87260 s t x) = (term144 _87260 s t x).
Proof. exact (MK_COMB (@lem3356015 _87260) (@lem3356014 _87260 s t x)). Qed.
Lemma lem3356018 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term144 _87260 s t x.
Proof. exact (EQ_MP (@lem3356017 _87260 s t x) (@lem3355985 _87260 s t x h1)). Qed.
Lemma lem3356022 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) : term126 _87260 s x.
Proof. exact (h1). Qed.
Lemma lem3356040 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (t' : _87260 -> Prop) (x : _87260) : (term134 _87260 s t t' x) = (term141 _87260 s t t' x).
Proof. exact (@lem19699 (term142 _87260 t' s) (term142 _87260 t' t) (@I (_87260 -> Prop) t' x)). Qed.
Lemma lem3356041 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term135 _87260 s t x) = (term143 _87260 s t x).
Proof. exact (fun_ext (fun t' : _87260 -> Prop => @lem3356040 _87260 s t t' x)). Qed.
Lemma lem3356042 {_87260 : Type'} : (@all (_87260 -> Prop)) = (@all (_87260 -> Prop)).
Proof. exact (eq_refl (@all (_87260 -> Prop))). Qed.
Lemma lem3356044 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term136 _87260 s t x) = (term144 _87260 s t x).
Proof. exact (MK_COMB (@lem3356042 _87260) (@lem3356041 _87260 s t x)). Qed.
Lemma lem3356045 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term144 _87260 s t x.
Proof. exact (EQ_MP (@lem3356044 _87260 s t x) (@lem3355985 _87260 s t x h1)). Qed.
Lemma lem3356049 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) : term126 _87260 t x.
Proof. exact (h1). Qed.
Lemma lem3356065 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : t' = s) : t' = s.
Proof. exact (h1). Qed.
Lemma lem3356081 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : t' = t) : t' = t.
Proof. exact (h1). Qed.
Lemma lem3356082 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term145 _87260 s t x _35007.
Proof. exact (@lem3356018 _87260 s t x h1 _35007). Qed.
Lemma lem3356083 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (_35007 : _87260 -> Prop) (x : _87260) : (term145 _87260 s t x _35007) = (term141 _87260 s t _35007 x).
Proof. exact (eq_refl (term145 _87260 s t x _35007)). Qed.
Lemma lem3356084 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term141 _87260 s t _35007 x.
Proof. exact (EQ_MP (@lem3356083 _87260 s t _35007 x) (@lem3356082 _87260 _35007 s t x h1)). Qed.
Lemma lem3356085 {_87260 : Type'} (_35008 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term145 _87260 s t x _35008.
Proof. exact (@lem3356045 _87260 s t x h1 _35008). Qed.
Lemma lem3356086 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (_35008 : _87260 -> Prop) (x : _87260) : (term145 _87260 s t x _35008) = (term141 _87260 s t _35008 x).
Proof. exact (eq_refl (term145 _87260 s t x _35008)). Qed.
Lemma lem3356087 {_87260 : Type'} (_35008 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term141 _87260 s t _35008 x.
Proof. exact (EQ_MP (@lem3356086 _87260 s t _35008 x) (@lem3356085 _87260 _35008 s t x h1)). Qed.
Lemma lem3356093 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) : term126 _87260 s x.
Proof. exact (h1). Qed.
Lemma lem3356099 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term146 _87260 s _35007 x.
Proof. exact (proj1 (@lem3356084 _87260 _35007 s t x h1)). Qed.
Lemma lem3356107 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) : term126 _87260 t x.
Proof. exact (h1). Qed.
Lemma lem3356119 {_87260 : Type'} (_35008 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term146 _87260 t _35008 x.
Proof. exact (proj2 (@lem3356087 _87260 _35008 s t x h1)). Qed.
Lemma lem3356125 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term126 _87260 t' x.
Proof. exact (proj2 (@lem3355989 _87260 t' s t x h1)). Qed.
Lemma lem3356127 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : t' = s) : t' = s.
Proof. exact (h1). Qed.
Lemma lem3356133 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term126 _87260 t' x.
Proof. exact (proj2 (@lem3355989 _87260 t' s t x h1)). Qed.
Lemma lem3356135 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : t' = t) : t' = t.
Proof. exact (h1). Qed.
Lemma lem3356178 {_87260 : Type'} (x : _87260) : (term147 _87260 x) = (term147 _87260 x).
Proof. exact (eq_refl (term147 _87260 x)). Qed.
Lemma lem3356179 {_87260 : Type'} (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : t' = s) : (term148 _87260 x t') = (term148 _87260 x s).
Proof. exact (MK_COMB (@lem3356178 _87260 x) (@lem3356127 _87260 t' s h1)). Qed.
Lemma lem3356180 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term148 _87260 x s) = (term126 _87260 s x).
Proof. exact (eq_refl (term148 _87260 x s)). Qed.
Lemma lem3356181 {_87260 : Type'} (x : _87260) (t' : _87260 -> Prop) : (term149 _87260 x t') = (term149 _87260 x t').
Proof. exact (eq_refl (term149 _87260 x t')). Qed.
Lemma lem3356182 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (x : _87260) : ((term148 _87260 x t') = (term148 _87260 x s)) = ((term148 _87260 x t') = (term126 _87260 s x)).
Proof. exact (MK_COMB (@lem3356181 _87260 x t') (@lem3356180 _87260 s x)). Qed.
Lemma lem3356183 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (term148 _87260 x t') = (term126 _87260 t' x).
Proof. exact (eq_refl (term148 _87260 x t')). Qed.
Lemma lem3356184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3356185 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (term149 _87260 x t') = (term150 _87260 t' x).
Proof. exact (MK_COMB (@lem3356184) (@lem3356183 _87260 t' x)). Qed.
Lemma lem3356186 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term126 _87260 s x) = (term126 _87260 s x).
Proof. exact (eq_refl (term126 _87260 s x)). Qed.
Lemma lem3356187 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (x : _87260) : ((term148 _87260 x t') = (term126 _87260 s x)) = ((term126 _87260 t' x) = (term126 _87260 s x)).
Proof. exact (MK_COMB (@lem3356185 _87260 t' x) (@lem3356186 _87260 s x)). Qed.
Lemma lem3356188 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (x : _87260) : ((term148 _87260 x t') = (term148 _87260 x s)) = ((term126 _87260 t' x) = (term126 _87260 s x)).
Proof. exact (TRANS (@lem3356182 _87260 t' s x) (@lem3356187 _87260 t' s x)). Qed.
Lemma lem3356189 {_87260 : Type'} (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : t' = s) : (term126 _87260 t' x) = (term126 _87260 s x).
Proof. exact (EQ_MP (@lem3356188 _87260 t' s x) (@lem3356179 _87260 x t' s h1)). Qed.
Lemma lem3356190 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : term126 _87260 s x.
Proof. exact (EQ_MP (@lem3356189 _87260 x t' s h2) (@lem3356125 _87260 t' s t x h1)). Qed.
Lemma lem3356233 {_87260 : Type'} (x : _87260) : (term147 _87260 x) = (term147 _87260 x).
Proof. exact (eq_refl (term147 _87260 x)). Qed.
Lemma lem3356234 {_87260 : Type'} (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : t' = t) : (term148 _87260 x t') = (term148 _87260 x t).
Proof. exact (MK_COMB (@lem3356233 _87260 x) (@lem3356135 _87260 t' t h1)). Qed.
Lemma lem3356235 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (term148 _87260 x t) = (term126 _87260 t x).
Proof. exact (eq_refl (term148 _87260 x t)). Qed.
Lemma lem3356236 {_87260 : Type'} (x : _87260) (t' : _87260 -> Prop) : (term149 _87260 x t') = (term149 _87260 x t').
Proof. exact (eq_refl (term149 _87260 x t')). Qed.
Lemma lem3356237 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term148 _87260 x t') = (term148 _87260 x t)) = ((term148 _87260 x t') = (term126 _87260 t x)).
Proof. exact (MK_COMB (@lem3356236 _87260 x t') (@lem3356235 _87260 t x)). Qed.
Lemma lem3356238 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (term148 _87260 x t') = (term126 _87260 t' x).
Proof. exact (eq_refl (term148 _87260 x t')). Qed.
Lemma lem3356239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3356240 {_87260 : Type'} (t' : _87260 -> Prop) (x : _87260) : (term149 _87260 x t') = (term150 _87260 t' x).
Proof. exact (MK_COMB (@lem3356239) (@lem3356238 _87260 t' x)). Qed.
Lemma lem3356241 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (term126 _87260 t x) = (term126 _87260 t x).
Proof. exact (eq_refl (term126 _87260 t x)). Qed.
Lemma lem3356242 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term148 _87260 x t') = (term126 _87260 t x)) = ((term126 _87260 t' x) = (term126 _87260 t x)).
Proof. exact (MK_COMB (@lem3356240 _87260 t' x) (@lem3356241 _87260 t x)). Qed.
Lemma lem3356243 {_87260 : Type'} (t' : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : ((term148 _87260 x t') = (term148 _87260 x t)) = ((term126 _87260 t' x) = (term126 _87260 t x)).
Proof. exact (TRANS (@lem3356237 _87260 t' t x) (@lem3356242 _87260 t' t x)). Qed.
Lemma lem3356244 {_87260 : Type'} (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : t' = t) : (term126 _87260 t' x) = (term126 _87260 t x).
Proof. exact (EQ_MP (@lem3356243 _87260 t' t x) (@lem3356234 _87260 x t' t h1)). Qed.
Lemma lem3356245 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : term126 _87260 t x.
Proof. exact (EQ_MP (@lem3356244 _87260 x t' t h2) (@lem3356133 _87260 t' s t x h1)). Qed.
Lemma lem3356270 {_87260 : Type'} (x : _87260 -> Prop) : x = x.
Proof. exact (@lem21386 (_87260 -> Prop) x). Qed.
Lemma lem3356271 {_87260 : Type'} (x : _87260 -> Prop) : x = x.
Proof. exact (@lem3356270 _87260 x). Qed.
Lemma lem3356272 {_87260 : Type'} (s : _87260 -> Prop) : s = s.
Proof. exact (@lem3356271 _87260 s). Qed.
Lemma lem3356273 {_87260 : Type'} (s : _87260 -> Prop) : term151 _87260 s.
Proof. exact (fun h0 : term152 _87260 s => @lem3356272 _87260 s). Qed.
Lemma lem3356275 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356276 {_87260 : Type'} (s : _87260 -> Prop) : (term151 _87260 s) = (s = s).
Proof. exact (@lem3356275 (s = s)). Qed.
Lemma lem3356277 {_87260 : Type'} (s : _87260 -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3356276 _87260 s) (@lem3356273 _87260 s)). Qed.
Lemma lem3356283 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3356284 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : (term146 _87260 s _35007 x) = (term154 _87260 x _35007 s).
Proof. exact (@lem3356283 (@I (_87260 -> Prop) _35007 x) (term142 _87260 _35007 s)). Qed.
Lemma lem3356292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3356293 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : (term155 _87260 s _35007 x) = (term156 _87260 x _35007 s).
Proof. exact (MK_COMB (@lem3356292) (@lem3356284 _87260 x _35007 s)). Qed.
Lemma lem3356301 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : (term154 _87260 x _35007 s) = (term154 _87260 x _35007 s).
Proof. exact (eq_refl (term154 _87260 x _35007 s)). Qed.
Lemma lem3356302 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : ((term146 _87260 s _35007 x) = (term154 _87260 x _35007 s)) = ((term154 _87260 x _35007 s) = (term154 _87260 x _35007 s)).
Proof. exact (MK_COMB (@lem3356293 _87260 x _35007 s) (@lem3356301 _87260 x _35007 s)). Qed.
Lemma lem3356304 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3356305 (x : Prop) : (x = x) = True.
Proof. exact (@lem3356304 Prop x). Qed.
Lemma lem3356306 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : ((term154 _87260 x _35007 s) = (term154 _87260 x _35007 s)) = True.
Proof. exact (@lem3356305 (term154 _87260 x _35007 s)). Qed.
Lemma lem3356307 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : ((term146 _87260 s _35007 x) = (term154 _87260 x _35007 s)) = True.
Proof. exact (TRANS (@lem3356302 _87260 x _35007 s) (@lem3356306 _87260 x _35007 s)). Qed.
Lemma lem3356308 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : True = ((term146 _87260 s _35007 x) = (term154 _87260 x _35007 s)).
Proof. exact (SYM (@lem3356307 _87260 x _35007 s)). Qed.
Lemma lem3356309 {_87260 : Type'} (x : _87260) (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : (term146 _87260 s _35007 x) = (term154 _87260 x _35007 s).
Proof. exact (EQ_MP (@lem3356308 _87260 x _35007 s) (@lem0)). Qed.
Lemma lem3356310 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term154 _87260 x _35007 s.
Proof. exact (EQ_MP (@lem3356309 _87260 x _35007 s) (@lem3356099 _87260 _35007 s t x h1)). Qed.
Lemma lem3356312 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3356313 {_87260 : Type'} (s : _87260 -> Prop) (_35007 : _87260 -> Prop) (x : _87260) : (term154 _87260 x _35007 s) = (term158 _87260 s _35007 x).
Proof. exact (@lem3356312 (term142 _87260 _35007 s) (@I (_87260 -> Prop) _35007 x)). Qed.
Lemma lem3356315 (a : Prop) : (term43 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3356316 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : (term159 _87260 _35007 s) = (_35007 = s).
Proof. exact (@lem3356315 (_35007 = s)). Qed.
Lemma lem3356317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3356318 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) : (term160 _87260 _35007 s) = (term161 _87260 _35007 s).
Proof. exact (MK_COMB (@lem3356317) (@lem3356316 _87260 _35007 s)). Qed.
Lemma lem3356319 {_87260 : Type'} (_35007 : _87260 -> Prop) (x : _87260) : (@I (_87260 -> Prop) _35007 x) = (@I (_87260 -> Prop) _35007 x).
Proof. exact (eq_refl (@I (_87260 -> Prop) _35007 x)). Qed.
Lemma lem3356320 {_87260 : Type'} (s : _87260 -> Prop) (_35007 : _87260 -> Prop) (x : _87260) : (term158 _87260 s _35007 x) = (term162 _87260 s _35007 x).
Proof. exact (MK_COMB (@lem3356318 _87260 _35007 s) (@lem3356319 _87260 _35007 x)). Qed.
Lemma lem3356321 {_87260 : Type'} (s : _87260 -> Prop) (_35007 : _87260 -> Prop) (x : _87260) : (term154 _87260 x _35007 s) = (term162 _87260 s _35007 x).
Proof. exact (TRANS (@lem3356313 _87260 s _35007 x) (@lem3356320 _87260 s _35007 x)). Qed.
Lemma lem3356324 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term162 _87260 s _35007 x.
Proof. exact (EQ_MP (@lem3356321 _87260 s _35007 x) (@lem3356310 _87260 _35007 s t x h1)). Qed.
Lemma lem3356325 {_87260 : Type'} (_35007 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term162 _87260 s _35007 x.
Proof. exact (@lem3356324 _87260 _35007 s t x h1). Qed.
Lemma lem3356326 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term163 _87260 s x.
Proof. exact (@lem3356325 _87260 s s t x h1). Qed.
Lemma lem3356329 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : @I (_87260 -> Prop) s x.
Proof. exact (@lem3356326 _87260 s t x h1 (@lem3356277 _87260 s)). Qed.
Lemma lem3356330 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term164 _87260 s x.
Proof. exact (fun h0 : term126 _87260 s x => @lem3356329 _87260 s t x h1). Qed.
Lemma lem3356332 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356333 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term164 _87260 s x) = (@I (_87260 -> Prop) s x).
Proof. exact (@lem3356332 (@I (_87260 -> Prop) s x)). Qed.
Lemma lem3356334 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : @I (_87260 -> Prop) s x.
Proof. exact (EQ_MP (@lem3356333 _87260 s x) (@lem3356330 _87260 s t x h1)). Qed.
Lemma lem3356337 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3356339 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term126 _87260 s x) = (term165 _87260 s x).
Proof. exact (@lem3356337 (@I (_87260 -> Prop) s x)). Qed.
Lemma lem3356342 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) : term165 _87260 s x.
Proof. exact (EQ_MP (@lem3356339 _87260 s x) (@lem3356093 _87260 s x h1)). Qed.
Lemma lem3356345 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : False.
Proof. exact (@lem3356342 _87260 s x h1 (@lem3356334 _87260 s t x h2)). Qed.
Lemma lem3356346 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : term166.
Proof. exact (fun h0 : ~ False => @lem3356345 _87260 s t x h1 h2). Qed.
Lemma lem3356348 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356349 : term166 = False.
Proof. exact (@lem3356348 False). Qed.
Lemma lem3356350 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356349) (@lem3356346 _87260 s t x h1 h2)). Qed.
Lemma lem3356375 {_87260 : Type'} (x : _87260 -> Prop) : x = x.
Proof. exact (@lem21386 (_87260 -> Prop) x). Qed.
Lemma lem3356376 {_87260 : Type'} (x : _87260 -> Prop) : x = x.
Proof. exact (@lem3356375 _87260 x). Qed.
Lemma lem3356377 {_87260 : Type'} (t : _87260 -> Prop) : t = t.
Proof. exact (@lem3356376 _87260 t). Qed.
Lemma lem3356378 {_87260 : Type'} (t : _87260 -> Prop) : term151 _87260 t.
Proof. exact (fun h0 : term152 _87260 t => @lem3356377 _87260 t). Qed.
Lemma lem3356380 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356381 {_87260 : Type'} (t : _87260 -> Prop) : (term151 _87260 t) = (t = t).
Proof. exact (@lem3356380 (t = t)). Qed.
Lemma lem3356382 {_87260 : Type'} (t : _87260 -> Prop) : t = t.
Proof. exact (EQ_MP (@lem3356381 _87260 t) (@lem3356378 _87260 t)). Qed.
Lemma lem3356388 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3356389 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : (term146 _87260 t _35008 x) = (term154 _87260 x _35008 t).
Proof. exact (@lem3356388 (@I (_87260 -> Prop) _35008 x) (term142 _87260 _35008 t)). Qed.
Lemma lem3356397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3356398 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : (term155 _87260 t _35008 x) = (term156 _87260 x _35008 t).
Proof. exact (MK_COMB (@lem3356397) (@lem3356389 _87260 x _35008 t)). Qed.
Lemma lem3356406 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : (term154 _87260 x _35008 t) = (term154 _87260 x _35008 t).
Proof. exact (eq_refl (term154 _87260 x _35008 t)). Qed.
Lemma lem3356407 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : ((term146 _87260 t _35008 x) = (term154 _87260 x _35008 t)) = ((term154 _87260 x _35008 t) = (term154 _87260 x _35008 t)).
Proof. exact (MK_COMB (@lem3356398 _87260 x _35008 t) (@lem3356406 _87260 x _35008 t)). Qed.
Lemma lem3356409 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3356410 (x : Prop) : (x = x) = True.
Proof. exact (@lem3356409 Prop x). Qed.
Lemma lem3356411 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : ((term154 _87260 x _35008 t) = (term154 _87260 x _35008 t)) = True.
Proof. exact (@lem3356410 (term154 _87260 x _35008 t)). Qed.
Lemma lem3356412 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : ((term146 _87260 t _35008 x) = (term154 _87260 x _35008 t)) = True.
Proof. exact (TRANS (@lem3356407 _87260 x _35008 t) (@lem3356411 _87260 x _35008 t)). Qed.
Lemma lem3356413 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : True = ((term146 _87260 t _35008 x) = (term154 _87260 x _35008 t)).
Proof. exact (SYM (@lem3356412 _87260 x _35008 t)). Qed.
Lemma lem3356414 {_87260 : Type'} (x : _87260) (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : (term146 _87260 t _35008 x) = (term154 _87260 x _35008 t).
Proof. exact (EQ_MP (@lem3356413 _87260 x _35008 t) (@lem0)). Qed.
Lemma lem3356415 {_87260 : Type'} (_35008 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term154 _87260 x _35008 t.
Proof. exact (EQ_MP (@lem3356414 _87260 x _35008 t) (@lem3356119 _87260 _35008 s t x h1)). Qed.
Lemma lem3356417 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3356418 {_87260 : Type'} (t : _87260 -> Prop) (_35008 : _87260 -> Prop) (x : _87260) : (term154 _87260 x _35008 t) = (term158 _87260 t _35008 x).
Proof. exact (@lem3356417 (term142 _87260 _35008 t) (@I (_87260 -> Prop) _35008 x)). Qed.
Lemma lem3356420 (a : Prop) : (term43 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3356421 {_87260 : Type'} (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : (term159 _87260 _35008 t) = (_35008 = t).
Proof. exact (@lem3356420 (_35008 = t)). Qed.
Lemma lem3356422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3356423 {_87260 : Type'} (_35008 : _87260 -> Prop) (t : _87260 -> Prop) : (term160 _87260 _35008 t) = (term161 _87260 _35008 t).
Proof. exact (MK_COMB (@lem3356422) (@lem3356421 _87260 _35008 t)). Qed.
Lemma lem3356424 {_87260 : Type'} (_35008 : _87260 -> Prop) (x : _87260) : (@I (_87260 -> Prop) _35008 x) = (@I (_87260 -> Prop) _35008 x).
Proof. exact (eq_refl (@I (_87260 -> Prop) _35008 x)). Qed.
Lemma lem3356425 {_87260 : Type'} (t : _87260 -> Prop) (_35008 : _87260 -> Prop) (x : _87260) : (term158 _87260 t _35008 x) = (term162 _87260 t _35008 x).
Proof. exact (MK_COMB (@lem3356423 _87260 _35008 t) (@lem3356424 _87260 _35008 x)). Qed.
Lemma lem3356426 {_87260 : Type'} (t : _87260 -> Prop) (_35008 : _87260 -> Prop) (x : _87260) : (term154 _87260 x _35008 t) = (term162 _87260 t _35008 x).
Proof. exact (TRANS (@lem3356418 _87260 t _35008 x) (@lem3356425 _87260 t _35008 x)). Qed.
Lemma lem3356429 {_87260 : Type'} (_35008 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term162 _87260 t _35008 x.
Proof. exact (EQ_MP (@lem3356426 _87260 t _35008 x) (@lem3356415 _87260 _35008 s t x h1)). Qed.
Lemma lem3356430 {_87260 : Type'} (_35008 : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term162 _87260 t _35008 x.
Proof. exact (@lem3356429 _87260 _35008 s t x h1). Qed.
Lemma lem3356431 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term163 _87260 t x.
Proof. exact (@lem3356430 _87260 t s t x h1). Qed.
Lemma lem3356434 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : @I (_87260 -> Prop) t x.
Proof. exact (@lem3356431 _87260 s t x h1 (@lem3356382 _87260 t)). Qed.
Lemma lem3356435 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : term164 _87260 t x.
Proof. exact (fun h0 : term126 _87260 t x => @lem3356434 _87260 s t x h1). Qed.
Lemma lem3356437 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356438 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (term164 _87260 t x) = (@I (_87260 -> Prop) t x).
Proof. exact (@lem3356437 (@I (_87260 -> Prop) t x)). Qed.
Lemma lem3356439 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : @I (_87260 -> Prop) t x.
Proof. exact (EQ_MP (@lem3356438 _87260 t x) (@lem3356435 _87260 s t x h1)). Qed.
Lemma lem3356442 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3356444 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (term126 _87260 t x) = (term165 _87260 t x).
Proof. exact (@lem3356442 (@I (_87260 -> Prop) t x)). Qed.
Lemma lem3356447 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) : term165 _87260 t x.
Proof. exact (EQ_MP (@lem3356444 _87260 t x) (@lem3356107 _87260 t x h1)). Qed.
Lemma lem3356450 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : False.
Proof. exact (@lem3356447 _87260 t x h1 (@lem3356439 _87260 s t x h2)). Qed.
Lemma lem3356451 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : term166.
Proof. exact (fun h0 : ~ False => @lem3356450 _87260 s t x h1 h2). Qed.
Lemma lem3356453 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356454 : term166 = False.
Proof. exact (@lem3356453 False). Qed.
Lemma lem3356455 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356454) (@lem3356451 _87260 s t x h1 h2)). Qed.
Lemma lem3356457 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : @I (_87260 -> Prop) s x.
Proof. exact (proj1 (@lem3355988 _87260 t' s t x h1)). Qed.
Lemma lem3356458 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term164 _87260 s x.
Proof. exact (fun h0 : term126 _87260 s x => @lem3356457 _87260 t' s t x h1). Qed.
Lemma lem3356460 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356461 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term164 _87260 s x) = (@I (_87260 -> Prop) s x).
Proof. exact (@lem3356460 (@I (_87260 -> Prop) s x)). Qed.
Lemma lem3356462 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : @I (_87260 -> Prop) s x.
Proof. exact (EQ_MP (@lem3356461 _87260 s x) (@lem3356458 _87260 t' s t x h1)). Qed.
Lemma lem3356465 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3356467 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) : (term126 _87260 s x) = (term165 _87260 s x).
Proof. exact (@lem3356465 (@I (_87260 -> Prop) s x)). Qed.
Lemma lem3356470 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : term165 _87260 s x.
Proof. exact (EQ_MP (@lem3356467 _87260 s x) (@lem3356190 _87260 t x t' s h1 h2)). Qed.
Lemma lem3356473 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : False.
Proof. exact (@lem3356470 _87260 t x t' s h1 h2 (@lem3356462 _87260 t' s t x h1)). Qed.
Lemma lem3356474 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : term166.
Proof. exact (fun h0 : ~ False => @lem3356473 _87260 t x t' s h1 h2). Qed.
Lemma lem3356476 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356477 : term166 = False.
Proof. exact (@lem3356476 False). Qed.
Lemma lem3356480 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : @I (_87260 -> Prop) t x.
Proof. exact (proj2 (@lem3355988 _87260 t' s t x h1)). Qed.
Lemma lem3356481 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : term164 _87260 t x.
Proof. exact (fun h0 : term126 _87260 t x => @lem3356480 _87260 t' s t x h1). Qed.
Lemma lem3356483 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356484 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (term164 _87260 t x) = (@I (_87260 -> Prop) t x).
Proof. exact (@lem3356483 (@I (_87260 -> Prop) t x)). Qed.
Lemma lem3356485 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : @I (_87260 -> Prop) t x.
Proof. exact (EQ_MP (@lem3356484 _87260 t x) (@lem3356481 _87260 t' s t x h1)). Qed.
Lemma lem3356488 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3356490 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) : (term126 _87260 t x) = (term165 _87260 t x).
Proof. exact (@lem3356488 (@I (_87260 -> Prop) t x)). Qed.
Lemma lem3356493 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : term165 _87260 t x.
Proof. exact (EQ_MP (@lem3356490 _87260 t x) (@lem3356245 _87260 s x t' t h1 h2)). Qed.
Lemma lem3356496 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : False.
Proof. exact (@lem3356493 _87260 s x t' t h1 h2 (@lem3356485 _87260 t' s t x h1)). Qed.
Lemma lem3356497 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : term166.
Proof. exact (fun h0 : ~ False => @lem3356496 _87260 s x t' t h1 h2). Qed.
Lemma lem3356499 (p : Prop) : (term153 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3356500 : term166 = False.
Proof. exact (@lem3356499 False). Qed.
Lemma lem3356502 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3356500) (@lem3356497 _87260 s x t' t h1 h2)). Qed.
Lemma lem3356503 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3356477) (@lem3356474 _87260 t x t' s h1 h2)). Qed.
Lemma lem3356504 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : (t' = t) = False.
Proof. exact (prop_ext (fun h3 : t' = t => @lem3356502 _87260 s x t' t h1 h2) (fun h3 : False => @lem3356135 _87260 t' t h2)). Qed.
Lemma lem3356505 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3356504 _87260 s x t' t h1 h2) (@lem3356135 _87260 t' t h2)). Qed.
Lemma lem3356506 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : (t' = s) = False.
Proof. exact (prop_ext (fun h3 : t' = s => @lem3356503 _87260 t x t' s h1 h2) (fun h3 : False => @lem3356127 _87260 t' s h2)). Qed.
Lemma lem3356507 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3356506 _87260 t x t' s h1 h2) (@lem3356127 _87260 t' s h2)). Qed.
Lemma lem3356508 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : (term126 _87260 t x) = False.
Proof. exact (prop_ext (fun h3 : term126 _87260 t x => @lem3356455 _87260 s t x h1 h2) (fun h3 : False => @lem3356107 _87260 t x h1)). Qed.
Lemma lem3356509 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356508 _87260 s t x h1 h2) (@lem3356107 _87260 t x h1)). Qed.
Lemma lem3356510 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : (term126 _87260 s x) = False.
Proof. exact (prop_ext (fun h3 : term126 _87260 s x => @lem3356350 _87260 s t x h1 h2) (fun h3 : False => @lem3356093 _87260 s x h1)). Qed.
Lemma lem3356511 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356510 _87260 s t x h1 h2) (@lem3356093 _87260 s x h1)). Qed.
Lemma lem3356512 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : (t' = t) = False.
Proof. exact (prop_ext (fun h3 : t' = t => @lem3356505 _87260 s x t' t h1 h2) (fun h3 : False => @lem3356081 _87260 t' t h2)). Qed.
Lemma lem3356513 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3356512 _87260 s x t' t h1 h2) (@lem3356081 _87260 t' t h2)). Qed.
Lemma lem3356514 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : (t' = s) = False.
Proof. exact (prop_ext (fun h3 : t' = s => @lem3356507 _87260 t x t' s h1 h2) (fun h3 : False => @lem3356065 _87260 t' s h2)). Qed.
Lemma lem3356515 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3356514 _87260 t x t' s h1 h2) (@lem3356065 _87260 t' s h2)). Qed.
Lemma lem3356516 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : (term126 _87260 t x) = False.
Proof. exact (prop_ext (fun h3 : term126 _87260 t x => @lem3356509 _87260 s t x h1 h2) (fun h3 : False => @lem3356049 _87260 t x h1)). Qed.
Lemma lem3356517 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356516 _87260 s t x h1 h2) (@lem3356049 _87260 t x h1)). Qed.
Lemma lem3356518 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : (term126 _87260 s x) = False.
Proof. exact (prop_ext (fun h3 : term126 _87260 s x => @lem3356511 _87260 s t x h1 h2) (fun h3 : False => @lem3356022 _87260 s x h1)). Qed.
Lemma lem3356519 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356518 _87260 s t x h1 h2) (@lem3356022 _87260 s x h1)). Qed.
Lemma lem3356520 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : (t' = t) = False.
Proof. exact (prop_ext (fun h3 : t' = t => @lem3356513 _87260 s x t' t h1 h2) (fun h3 : False => @lem3356081 _87260 t' t h2)). Qed.
Lemma lem3356521 {_87260 : Type'} (s : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3356520 _87260 s x t' t h1 h2) (@lem3356081 _87260 t' t h2)). Qed.
Lemma lem3356522 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : (t' = s) = False.
Proof. exact (prop_ext (fun h3 : t' = s => @lem3356515 _87260 t x t' s h1 h2) (fun h3 : False => @lem3356065 _87260 t' s h2)). Qed.
Lemma lem3356523 {_87260 : Type'} (t : _87260 -> Prop) (x : _87260) (t' : _87260 -> Prop) (s : _87260 -> Prop) (h1 : term130 _87260 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3356522 _87260 t x t' s h1 h2) (@lem3356065 _87260 t' s h2)). Qed.
Lemma lem3356524 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : (term126 _87260 t x) = False.
Proof. exact (prop_ext (fun h3 : term126 _87260 t x => @lem3356517 _87260 s t x h1 h2) (fun h3 : False => @lem3356049 _87260 t x h1)). Qed.
Lemma lem3356525 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 t x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356524 _87260 s t x h1 h2) (@lem3356049 _87260 t x h1)). Qed.
Lemma lem3356526 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : (term126 _87260 s x) = False.
Proof. exact (prop_ext (fun h3 : term126 _87260 s x => @lem3356519 _87260 s t x h1 h2) (fun h3 : False => @lem3356022 _87260 s x h1)). Qed.
Lemma lem3356527 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term126 _87260 s x) (h2 : term138 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356526 _87260 s t x h1 h2) (@lem3356022 _87260 s x h1)). Qed.
Lemma lem3356528 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term130 _87260 t' s t x) : False.
Proof. exact (or_elim (@lem3355993 _87260 t' s t x h1) (fun h0 : t' = s => @lem3356523 _87260 t x t' s h1 h0) (fun h0 : t' = t => @lem3356521 _87260 s x t' t h1 h0)). Qed.
Lemma lem3356529 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term138 _87260 s t x) : False.
Proof. exact (or_elim (@lem3355984 _87260 s t x h1) (fun h0 : term126 _87260 s x => @lem3356527 _87260 s t x h0 h1) (fun h0 : term126 _87260 t x => @lem3356525 _87260 s t x h0 h1)). Qed.
Lemma lem3356530 {_87260 : Type'} (t' : _87260 -> Prop) (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term119 _87260 t' s t x) : False.
Proof. exact (or_elim (@lem3355981 _87260 t' s t x h1) (fun h0 : term138 _87260 s t x => @lem3356529 _87260 s t x h0) (fun h0 : term130 _87260 t' s t x => @lem3356528 _87260 t' s t x h0)). Qed.
Lemma lem3356531 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term53 _87260 s t x) : False.
Proof. exact (ex_elim (@lem3355871 _87260 s t x h1) (fun t' : _87260 -> Prop => fun h0 : term121 _87260 s t x t' => @lem3356530 _87260 t' s t x h0)). Qed.
Lemma lem3356532 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term53 _87260 s t x) : (term53 _87260 s t x) = False.
Proof. exact (prop_ext (fun h2 : term53 _87260 s t x => @lem3356531 _87260 s t x h1) (fun h2 : False => @lem3355664 _87260 s t x h1)). Qed.
Lemma lem3356533 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) (h1 : term53 _87260 s t x) : False.
Proof. exact (EQ_MP (@lem3356532 _87260 s t x h1) (@lem3355664 _87260 s t x h1)). Qed.
Lemma lem3356534 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : term52 _87260 s t x.
Proof. exact (fun h0 : term53 _87260 s t x => @lem3356533 _87260 s t x h0). Qed.
Lemma lem3356535 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (x : _87260) : (term25 _87260 s t x) = (term32 _87260 s t x).
Proof. exact (EQ_MP (@lem3355663 _87260 s t x) (@lem3356534 _87260 s t x)). Qed.
Lemma lem3356540 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term35 _87260 s t.
Proof. exact (fun x : _87260 => @lem3356535 _87260 s t x). Qed.
Lemma lem3356545 {_87260 : Type'} (t : _87260 -> Prop) : term47 _87260 t.
Proof. exact (fun s : _87260 -> Prop => @lem3356540 _87260 s t). Qed.
Lemma lem3356550 {_87260 : Type'} : term51 _87260.
Proof. exact (fun t : _87260 -> Prop => @lem3356545 _87260 t). Qed.
Lemma lem3356551 {_87260 : Type'} : term50 _87260.
Proof. exact (EQ_MP (@lem3355659 _87260) (@lem3356550 _87260)). Qed.
Lemma lem3356552 {_87260 : Type'} (t : _87260 -> Prop) : term167 _87260 t.
Proof. exact (@lem3356551 _87260 t). Qed.
Lemma lem3356553 {_87260 : Type'} (t : _87260 -> Prop) : (term167 _87260 t) = (term46 _87260 t).
Proof. exact (eq_refl (term167 _87260 t)). Qed.
Lemma lem3356554 {_87260 : Type'} (t : _87260 -> Prop) : term46 _87260 t.
Proof. exact (EQ_MP (@lem3356553 _87260 t) (@lem3356552 _87260 t)). Qed.
Lemma lem3356555 {_87260 : Type'} (t : _87260 -> Prop) (s : _87260 -> Prop) : term168 _87260 t s.
Proof. exact (@lem3356554 _87260 t s). Qed.
Lemma lem3356556 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term168 _87260 t s) = (term37 _87260 s t).
Proof. exact (eq_refl (term168 _87260 t s)). Qed.
Lemma lem3356557 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term37 _87260 s t.
Proof. exact (EQ_MP (@lem3356556 _87260 s t) (@lem3356555 _87260 t s)). Qed.
Lemma lem3356559 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term37 _87260 s t.
Proof. exact (@lem3355549 _87260 s t (@lem3356557 _87260 s t)). Qed.
Lemma lem3356560 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term38 _87260 s t) : False.
Proof. exact (@lem3356559 _87260 s t (@lem3355533 _87260 s t h1)). Qed.
Lemma lem3356561 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term38 _87260 s t) : (term38 _87260 s t) = False.
Proof. exact (prop_ext (fun h2 : term38 _87260 s t => @lem3356560 _87260 s t h1) (fun h2 : False => @lem3355533 _87260 s t h1)). Qed.
Lemma lem3356562 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : term38 _87260 s t) : False.
Proof. exact (EQ_MP (@lem3356561 _87260 s t h1) (@lem3355533 _87260 s t h1)). Qed.
Lemma lem3356563 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term37 _87260 s t.
Proof. exact (fun h0 : term38 _87260 s t => @lem3356562 _87260 s t h0). Qed.
Lemma lem3356564 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term35 _87260 s t.
Proof. exact (EQ_MP (@lem3355532 _87260 s t) (@lem3356563 _87260 s t)). Qed.
Lemma lem3356565 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : term2 _87260 s t.
Proof. exact (EQ_MP (@lem3355528 _87260 s t) (@lem3356564 _87260 s t)). Qed.
Lemma lem3356566 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (term1 _87260 s t) = (@INTER _87260 s t).
Proof. exact (EQ_MP (@lem3355429 _87260 s t) (@lem3356565 _87260 s t)). Qed.
