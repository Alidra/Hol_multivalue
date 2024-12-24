Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_UNION_term_abbrevs.
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
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3345355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3345356 {_87123 : Type'} (s : _87123 -> Prop) (t : _87123 -> Prop) : (s = t) = (term0 _87123 s t).
Proof. exact (@lem3345355 _87123 s t). Qed.
Lemma lem3345357 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) : ((term1 _87123 s t) = (term2 _87123 s t)) = (term3 _87123 s t).
Proof. exact (@lem3345356 _87123 (term1 _87123 s t) (term2 _87123 s t)). Qed.
Lemma lem3345366 {_87123 : Type'} (s : type686 _87123) : (term4 _87123 s) = (term5 _87123 s).
Proof. exact (fun_ext (fun t : type686 _87123 => @lem3345357 _87123 s t)). Qed.
Lemma lem3345367 {_87123 : Type'} : (@all ((_87123 -> Prop) -> Prop)) = (@all ((_87123 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87123 -> Prop) -> Prop))). Qed.
Lemma lem3345368 {_87123 : Type'} (s : type686 _87123) : (term6 _87123 s) = (term7 _87123 s).
Proof. exact (MK_COMB (@lem3345367 _87123) (@lem3345366 _87123 s)). Qed.
Lemma lem3345373 {_87123 : Type'} : (term8 _87123) = (term9 _87123).
Proof. exact (fun_ext (fun s : type686 _87123 => @lem3345368 _87123 s)). Qed.
Lemma lem3345374 {_87123 : Type'} : (@all ((_87123 -> Prop) -> Prop)) = (@all ((_87123 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87123 -> Prop) -> Prop))). Qed.
Lemma lem3345375 {_87123 : Type'} : (term10 _87123) = (term11 _87123).
Proof. exact (MK_COMB (@lem3345374 _87123) (@lem3345373 _87123)). Qed.
Lemma lem3345380 {_87123 : Type'} : (term11 _87123) = (term10 _87123).
Proof. exact (SYM (@lem3345375 _87123)). Qed.
Lemma lem3345396 {A : Type'} (s : type686 A) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3345397 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term12 _87123 x s) = (term13 _87123 s x).
Proof. exact (@lem3345396 _87123 s x). Qed.
Lemma lem3345398 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term14 _87123 x s t) = (term15 _87123 s t x).
Proof. exact (@lem3345397 _87123 (@UNION (_87123 -> Prop) s t) x). Qed.
Lemma lem3345406 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3345407 {_87123 : Type'} (s : type686 _87123) (x : _87123 -> Prop) (t : type686 _87123) : (term18 _87123 x s t) = (term19 _87123 s x t).
Proof. exact (@lem3345406 (_87123 -> Prop) s x t). Qed.
Lemma lem3345408 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (t' : type686 _87123) : (term18 _87123 t s t') = (term19 _87123 s t t').
Proof. exact (@lem3345407 _87123 s t t'). Qed.
Lemma lem3345412 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3345413 {_87123 : Type'} (P : type686 _87123) (x : _87123 -> Prop) : (@IN (_87123 -> Prop) x P) = (P x).
Proof. exact (@lem3345412 (_87123 -> Prop) P x). Qed.
Lemma lem3345414 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (@IN (_87123 -> Prop) t s) = (s t).
Proof. exact (@lem3345413 _87123 s t). Qed.
Lemma lem3345415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3345416 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (term20 _87123 t s) = (term21 _87123 s t).
Proof. exact (MK_COMB (@lem3345415) (@lem3345414 _87123 s t)). Qed.
Lemma lem3345418 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3345419 {_87123 : Type'} (P : type686 _87123) (x : _87123 -> Prop) : (@IN (_87123 -> Prop) x P) = (P x).
Proof. exact (@lem3345418 (_87123 -> Prop) P x). Qed.
Lemma lem3345420 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (@IN (_87123 -> Prop) t' t) = (t t').
Proof. exact (@lem3345419 _87123 t t'). Qed.
Lemma lem3345421 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term19 _87123 s t' t) = (term22 _87123 s t t').
Proof. exact (MK_COMB (@lem3345416 _87123 s t') (@lem3345420 _87123 t t')). Qed.
Lemma lem3345424 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term18 _87123 t' s t) = (term22 _87123 s t t').
Proof. exact (TRANS (@lem3345408 _87123 s t' t) (@lem3345421 _87123 s t t')). Qed.
Lemma lem3345425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3345426 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term23 _87123 t' s t) = (term24 _87123 s t t').
Proof. exact (MK_COMB (@lem3345425) (@lem3345424 _87123 s t t')). Qed.
Lemma lem3345428 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3345429 {_87123 : Type'} (P : _87123 -> Prop) (x : _87123) : (@IN _87123 x P) = (P x).
Proof. exact (@lem3345428 _87123 P x). Qed.
Lemma lem3345430 {_87123 : Type'} (t : _87123 -> Prop) (x : _87123) : (@IN _87123 x t) = (t x).
Proof. exact (@lem3345429 _87123 t x). Qed.
Lemma lem3345431 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term25 _87123 s t x t') = (term26 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3345426 _87123 s t t') (@lem3345430 _87123 t' x)). Qed.
Lemma lem3345434 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term27 _87123 s t x) = (term28 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345431 _87123 s t t' x)). Qed.
Lemma lem3345435 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345436 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term15 _87123 s t x) = (term29 _87123 s t x).
Proof. exact (MK_COMB (@lem3345435 _87123) (@lem3345434 _87123 s t x)). Qed.
Lemma lem3345441 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term14 _87123 x s t) = (term29 _87123 s t x).
Proof. exact (TRANS (@lem3345398 _87123 s t x) (@lem3345436 _87123 s t x)). Qed.
Lemma lem3345442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3345443 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term30 _87123 x s t) = (term31 _87123 s t x).
Proof. exact (MK_COMB (@lem3345442) (@lem3345441 _87123 s t x)). Qed.
Lemma lem3345445 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term33 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3345446 {_87123 : Type'} (s : _87123 -> Prop) (x : _87123) (t : _87123 -> Prop) : (term32 _87123 x s t) = (term33 _87123 s x t).
Proof. exact (@lem3345445 _87123 s x t). Qed.
Lemma lem3345447 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) : (term34 _87123 x s t) = (term35 _87123 s x t).
Proof. exact (@lem3345446 _87123 (@INTERS _87123 s) x (@INTERS _87123 t)). Qed.
Lemma lem3345451 {A : Type'} (s : type686 A) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3345452 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term12 _87123 x s) = (term13 _87123 s x).
Proof. exact (@lem3345451 _87123 s x). Qed.
Lemma lem3345460 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3345461 {_87123 : Type'} (P : type686 _87123) (x : _87123 -> Prop) : (@IN (_87123 -> Prop) x P) = (P x).
Proof. exact (@lem3345460 (_87123 -> Prop) P x). Qed.
Lemma lem3345462 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (@IN (_87123 -> Prop) t s) = (s t).
Proof. exact (@lem3345461 _87123 s t). Qed.
Lemma lem3345463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3345464 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (term36 _87123 t s) = (term37 _87123 s t).
Proof. exact (MK_COMB (@lem3345463) (@lem3345462 _87123 s t)). Qed.
Lemma lem3345466 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3345467 {_87123 : Type'} (P : _87123 -> Prop) (x : _87123) : (@IN _87123 x P) = (P x).
Proof. exact (@lem3345466 _87123 P x). Qed.
Lemma lem3345468 {_87123 : Type'} (t : _87123 -> Prop) (x : _87123) : (@IN _87123 x t) = (t x).
Proof. exact (@lem3345467 _87123 t x). Qed.
Lemma lem3345469 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term38 _87123 s x t) = (term39 _87123 s t x).
Proof. exact (MK_COMB (@lem3345464 _87123 s t) (@lem3345468 _87123 t x)). Qed.
Lemma lem3345472 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term40 _87123 s x) = (term41 _87123 s x).
Proof. exact (fun_ext (fun t : _87123 -> Prop => @lem3345469 _87123 s t x)). Qed.
Lemma lem3345473 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345474 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term13 _87123 s x) = (term42 _87123 s x).
Proof. exact (MK_COMB (@lem3345473 _87123) (@lem3345472 _87123 s x)). Qed.
Lemma lem3345479 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term12 _87123 x s) = (term42 _87123 s x).
Proof. exact (TRANS (@lem3345452 _87123 s x) (@lem3345474 _87123 s x)). Qed.
Lemma lem3345480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3345481 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term43 _87123 x s) = (term44 _87123 s x).
Proof. exact (MK_COMB (@lem3345480) (@lem3345479 _87123 s x)). Qed.
Lemma lem3345483 {A : Type'} (s : type686 A) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3345484 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term12 _87123 x s) = (term13 _87123 s x).
Proof. exact (@lem3345483 _87123 s x). Qed.
Lemma lem3345485 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term12 _87123 x t) = (term13 _87123 t x).
Proof. exact (@lem3345484 _87123 t x). Qed.
Lemma lem3345493 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3345494 {_87123 : Type'} (P : type686 _87123) (x : _87123 -> Prop) : (@IN (_87123 -> Prop) x P) = (P x).
Proof. exact (@lem3345493 (_87123 -> Prop) P x). Qed.
Lemma lem3345495 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (@IN (_87123 -> Prop) t' t) = (t t').
Proof. exact (@lem3345494 _87123 t t'). Qed.
Lemma lem3345496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3345497 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (term36 _87123 t' t) = (term37 _87123 t t').
Proof. exact (MK_COMB (@lem3345496) (@lem3345495 _87123 t t')). Qed.
Lemma lem3345499 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3345500 {_87123 : Type'} (P : _87123 -> Prop) (x : _87123) : (@IN _87123 x P) = (P x).
Proof. exact (@lem3345499 _87123 P x). Qed.
Lemma lem3345501 {_87123 : Type'} (t : _87123 -> Prop) (x : _87123) : (@IN _87123 x t) = (t x).
Proof. exact (@lem3345500 _87123 t x). Qed.
Lemma lem3345502 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term38 _87123 t x t') = (term39 _87123 t t' x).
Proof. exact (MK_COMB (@lem3345497 _87123 t t') (@lem3345501 _87123 t' x)). Qed.
Lemma lem3345505 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term40 _87123 t x) = (term41 _87123 t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345502 _87123 t t' x)). Qed.
Lemma lem3345506 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345507 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term13 _87123 t x) = (term42 _87123 t x).
Proof. exact (MK_COMB (@lem3345506 _87123) (@lem3345505 _87123 t x)). Qed.
Lemma lem3345512 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term12 _87123 x t) = (term42 _87123 t x).
Proof. exact (TRANS (@lem3345485 _87123 t x) (@lem3345507 _87123 t x)). Qed.
Lemma lem3345513 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term35 _87123 s x t) = (term45 _87123 s t x).
Proof. exact (MK_COMB (@lem3345481 _87123 s x) (@lem3345512 _87123 t x)). Qed.
Lemma lem3345516 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term34 _87123 x s t) = (term45 _87123 s t x).
Proof. exact (TRANS (@lem3345447 _87123 s x t) (@lem3345513 _87123 s t x)). Qed.
Lemma lem3345517 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : ((term14 _87123 x s t) = (term34 _87123 x s t)) = ((term29 _87123 s t x) = (term45 _87123 s t x)).
Proof. exact (MK_COMB (@lem3345443 _87123 s t x) (@lem3345516 _87123 s t x)). Qed.
Lemma lem3345520 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) : (term46 _87123 s t) = (term47 _87123 s t).
Proof. exact (fun_ext (fun x : _87123 => @lem3345517 _87123 s t x)). Qed.
Lemma lem3345521 {_87123 : Type'} : (@all _87123) = (@all _87123).
Proof. exact (eq_refl (@all _87123)). Qed.
Lemma lem3345522 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) : (term3 _87123 s t) = (term48 _87123 s t).
Proof. exact (MK_COMB (@lem3345521 _87123) (@lem3345520 _87123 s t)). Qed.
Lemma lem3345527 {_87123 : Type'} (s : type686 _87123) : (term5 _87123 s) = (term49 _87123 s).
Proof. exact (fun_ext (fun t : type686 _87123 => @lem3345522 _87123 s t)). Qed.
Lemma lem3345528 {_87123 : Type'} : (@all ((_87123 -> Prop) -> Prop)) = (@all ((_87123 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87123 -> Prop) -> Prop))). Qed.
Lemma lem3345529 {_87123 : Type'} (s : type686 _87123) : (term7 _87123 s) = (term50 _87123 s).
Proof. exact (MK_COMB (@lem3345528 _87123) (@lem3345527 _87123 s)). Qed.
Lemma lem3345534 {_87123 : Type'} : (term9 _87123) = (term51 _87123).
Proof. exact (fun_ext (fun s : type686 _87123 => @lem3345529 _87123 s)). Qed.
Lemma lem3345535 {_87123 : Type'} : (@all ((_87123 -> Prop) -> Prop)) = (@all ((_87123 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87123 -> Prop) -> Prop))). Qed.
Lemma lem3345536 {_87123 : Type'} : (term11 _87123) = (term52 _87123).
Proof. exact (MK_COMB (@lem3345535 _87123) (@lem3345534 _87123)). Qed.
Lemma lem3345541 {_87123 : Type'} : (term52 _87123) = (term11 _87123).
Proof. exact (SYM (@lem3345536 _87123)). Qed.
Lemma lem3345543 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3345544 {_87123 : Type'} : (term52 _87123) = (term54 _87123).
Proof. exact (@lem3345543 (term52 _87123)). Qed.
Lemma lem3345545 {_87123 : Type'} : (term54 _87123) = (term52 _87123).
Proof. exact (SYM (@lem3345544 _87123)). Qed.
Lemma lem3345546 {_87123 : Type'} (h1 : term55 _87123) : term55 _87123.
Proof. exact (h1). Qed.
Lemma lem3345549 {_87123 : Type'} (h1 : term54 _87123) : term54 _87123.
Proof. exact (h1). Qed.
Lemma lem3345550 {_87123 : Type'} : term56 _87123.
Proof. exact (fun h0 : term54 _87123 => @lem3345549 _87123 h0). Qed.
Lemma lem3345551 {_87123 : Type'} (h1 : term56 _87123) : term56 _87123.
Proof. exact (h1). Qed.
Lemma lem3345552 {_87123 : Type'} (h1 : term54 _87123) : term54 _87123.
Proof. exact (h1). Qed.
Lemma lem3345553 {_87123 : Type'} (h1 : term54 _87123) (h2 : term56 _87123) : term54 _87123.
Proof. exact (@lem3345551 _87123 h2 (@lem3345552 _87123 h1)). Qed.
Lemma lem3345554 {_87123 : Type'} (h1 : term54 _87123) : term57 _87123.
Proof. exact (fun h0 : term56 _87123 => @lem3345553 _87123 h1 h0). Qed.
Lemma lem3345555 {_87123 : Type'} (h1 : term56 _87123) : term56 _87123.
Proof. exact (h1). Qed.
Lemma lem3345556 {_87123 : Type'} (h1 : term54 _87123) (h2 : term56 _87123) : term54 _87123.
Proof. exact (@lem3345554 _87123 h1 (@lem3345555 _87123 h2)). Qed.
Lemma lem3345557 {_87123 : Type'} (h1 : term56 _87123) : term56 _87123.
Proof. exact (fun h0 : term54 _87123 => @lem3345556 _87123 h0 h1). Qed.
Lemma lem3345558 {_87123 : Type'} : term58 _87123.
Proof. exact (fun h0 : term56 _87123 => @lem3345557 _87123 h0). Qed.
Lemma lem3345561 {_87123 : Type'} : term56 _87123.
Proof. exact (@lem3345558 _87123 (@lem3345550 _87123)). Qed.
Lemma lem3345562 {_87123 : Type'} : term56 _87123.
Proof. exact (@lem3345561 _87123). Qed.
Lemma lem3345564 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3345565 {_87123 : Type'} : (term54 _87123) = (term59 _87123).
Proof. exact (@lem3345564 (term55 _87123)). Qed.
Lemma lem3345567 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3345568 {_87123 : Type'} : (term59 _87123) = (term52 _87123).
Proof. exact (@lem3345567 (term52 _87123)). Qed.
Lemma lem3345607 {_87123 : Type'} : (term54 _87123) = (term52 _87123).
Proof. exact (TRANS (@lem3345565 _87123) (@lem3345568 _87123)). Qed.
Lemma lem3345612 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term39 _87123 t t' x) = (term39 _87123 t t' x).
Proof. exact (eq_refl (term39 _87123 t t' x)). Qed.
Lemma lem3345613 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term41 _87123 t x) = (term41 _87123 t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345612 _87123 t t' x)). Qed.
Lemma lem3345614 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345615 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term42 _87123 t x) = (term42 _87123 t x).
Proof. exact (MK_COMB (@lem3345614 _87123) (@lem3345613 _87123 t x)). Qed.
Lemma lem3345620 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term39 _87123 s t x) = (term39 _87123 s t x).
Proof. exact (eq_refl (term39 _87123 s t x)). Qed.
Lemma lem3345621 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term41 _87123 s x) = (term41 _87123 s x).
Proof. exact (fun_ext (fun t : _87123 -> Prop => @lem3345620 _87123 s t x)). Qed.
Lemma lem3345622 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345623 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term42 _87123 s x) = (term42 _87123 s x).
Proof. exact (MK_COMB (@lem3345622 _87123) (@lem3345621 _87123 s x)). Qed.
Lemma lem3345624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3345625 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term44 _87123 s x) = (term44 _87123 s x).
Proof. exact (MK_COMB (@lem3345624) (@lem3345623 _87123 s x)). Qed.
Lemma lem3345626 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term45 _87123 s t x) = (term45 _87123 s t x).
Proof. exact (MK_COMB (@lem3345625 _87123 s x) (@lem3345615 _87123 t x)). Qed.
Lemma lem3345635 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term26 _87123 s t t' x) = (term26 _87123 s t t' x).
Proof. exact (eq_refl (term26 _87123 s t t' x)). Qed.
Lemma lem3345636 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term28 _87123 s t x) = (term28 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345635 _87123 s t t' x)). Qed.
Lemma lem3345637 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345638 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term29 _87123 s t x) = (term29 _87123 s t x).
Proof. exact (MK_COMB (@lem3345637 _87123) (@lem3345636 _87123 s t x)). Qed.
Lemma lem3345639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3345640 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term31 _87123 s t x) = (term31 _87123 s t x).
Proof. exact (MK_COMB (@lem3345639) (@lem3345638 _87123 s t x)). Qed.
Lemma lem3345641 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : ((term29 _87123 s t x) = (term45 _87123 s t x)) = ((term29 _87123 s t x) = (term45 _87123 s t x)).
Proof. exact (MK_COMB (@lem3345640 _87123 s t x) (@lem3345626 _87123 s t x)). Qed.
Lemma lem3345642 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) : (term47 _87123 s t) = (term47 _87123 s t).
Proof. exact (fun_ext (fun x : _87123 => @lem3345641 _87123 s t x)). Qed.
Lemma lem3345643 {_87123 : Type'} : (@all _87123) = (@all _87123).
Proof. exact (eq_refl (@all _87123)). Qed.
Lemma lem3345644 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) : (term48 _87123 s t) = (term48 _87123 s t).
Proof. exact (MK_COMB (@lem3345643 _87123) (@lem3345642 _87123 s t)). Qed.
Lemma lem3345645 {_87123 : Type'} (s : type686 _87123) : (term49 _87123 s) = (term49 _87123 s).
Proof. exact (fun_ext (fun t : type686 _87123 => @lem3345644 _87123 s t)). Qed.
Lemma lem3345646 {_87123 : Type'} : (@all ((_87123 -> Prop) -> Prop)) = (@all ((_87123 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87123 -> Prop) -> Prop))). Qed.
Lemma lem3345647 {_87123 : Type'} (s : type686 _87123) : (term50 _87123 s) = (term50 _87123 s).
Proof. exact (MK_COMB (@lem3345646 _87123) (@lem3345645 _87123 s)). Qed.
Lemma lem3345648 {_87123 : Type'} : (term51 _87123) = (term51 _87123).
Proof. exact (fun_ext (fun s : type686 _87123 => @lem3345647 _87123 s)). Qed.
Lemma lem3345649 {_87123 : Type'} : (@all ((_87123 -> Prop) -> Prop)) = (@all ((_87123 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87123 -> Prop) -> Prop))). Qed.
Lemma lem3345650 {_87123 : Type'} : (term52 _87123) = (term52 _87123).
Proof. exact (MK_COMB (@lem3345649 _87123) (@lem3345648 _87123)). Qed.
Lemma lem3345699 {_87123 : Type'} : (term54 _87123) = (term52 _87123).
Proof. exact (TRANS (@lem3345607 _87123) (@lem3345650 _87123)). Qed.
Lemma lem3345700 {_87123 : Type'} : (term52 _87123) = (term54 _87123).
Proof. exact (SYM (@lem3345699 _87123)). Qed.
Lemma lem3345702 (p : Prop) : p = (term53 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3345703 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : ((term29 _87123 s t x) = (term45 _87123 s t x)) = (term61 _87123 s t x).
Proof. exact (@lem3345702 ((term29 _87123 s t x) = (term45 _87123 s t x))). Qed.
Lemma lem3345704 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term61 _87123 s t x) = ((term29 _87123 s t x) = (term45 _87123 s t x)).
Proof. exact (SYM (@lem3345703 _87123 s t x)). Qed.
Lemma lem3345705 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term62 _87123 s t x) : term62 _87123 s t x.
Proof. exact (h1). Qed.
Lemma lem3345714 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term63 _87123 s t t') = (term64 _87123 s t t').
Proof. exact (@lem17160 (s t') (t t')). Qed.
Lemma lem3345719 {_87123 : Type'} (t : _87123 -> Prop) (x : _87123) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3345724 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term65 _87123 s t t' x) = (term66 _87123 s t t' x).
Proof. exact (@lem17362 (term22 _87123 s t t') (t' x)). Qed.
Lemma lem3345725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3345726 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term67 _87123 s t t') = (term68 _87123 s t t').
Proof. exact (MK_COMB (@lem3345725) (@lem3345714 _87123 s t t')). Qed.
Lemma lem3345727 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term69 _87123 s t t' x) = (term70 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3345726 _87123 s t t') (@lem3345719 _87123 t' x)). Qed.
Lemma lem3345728 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term26 _87123 s t t' x) = (term69 _87123 s t t' x).
Proof. exact (@lem17265 (term22 _87123 s t t') (t' x)). Qed.
Lemma lem3345729 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term26 _87123 s t t' x) = (term70 _87123 s t t' x).
Proof. exact (TRANS (@lem3345728 _87123 s t t' x) (@lem3345727 _87123 s t t' x)). Qed.
Lemma lem3345730 {_87123 : Type'} (P : type686 _87123) : (term71 _87123 P) = (term72 _87123 P).
Proof. exact (@lem18392 (_87123 -> Prop) P). Qed.
Lemma lem3345731 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term73 _87123 s t x) = (term74 _87123 s t x).
Proof. exact (@lem3345730 _87123 (term28 _87123 s t x)). Qed.
Lemma lem3345732 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term75 _87123 s t x t') = (term26 _87123 s t t' x).
Proof. exact (eq_refl (term75 _87123 s t x t')). Qed.
Lemma lem3345733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3345734 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term76 _87123 s t x t') = (term65 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3345733) (@lem3345732 _87123 s t t' x)). Qed.
Lemma lem3345735 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term76 _87123 s t x t') = (term66 _87123 s t t' x).
Proof. exact (TRANS (@lem3345734 _87123 s t t' x) (@lem3345724 _87123 s t t' x)). Qed.
Lemma lem3345736 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term77 _87123 s t x) = (term78 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345735 _87123 s t t' x)). Qed.
Lemma lem3345737 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3345738 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term74 _87123 s t x) = (term79 _87123 s t x).
Proof. exact (MK_COMB (@lem3345737 _87123) (@lem3345736 _87123 s t x)). Qed.
Lemma lem3345739 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term73 _87123 s t x) = (term79 _87123 s t x).
Proof. exact (TRANS (@lem3345731 _87123 s t x) (@lem3345738 _87123 s t x)). Qed.
Lemma lem3345740 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term28 _87123 s t x) = (term80 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345729 _87123 s t t' x)). Qed.
Lemma lem3345741 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345742 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term29 _87123 s t x) = (term81 _87123 s t x).
Proof. exact (MK_COMB (@lem3345741 _87123) (@lem3345740 _87123 s t x)). Qed.
Lemma lem3345751 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term82 _87123 s t x) = (term83 _87123 s t x).
Proof. exact (@lem17362 (s t) (t x)). Qed.
Lemma lem3345756 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term39 _87123 s t x) = (term84 _87123 s t x).
Proof. exact (@lem17265 (s t) (t x)). Qed.
Lemma lem3345757 {_87123 : Type'} (P : type686 _87123) : (term71 _87123 P) = (term72 _87123 P).
Proof. exact (@lem18392 (_87123 -> Prop) P). Qed.
Lemma lem3345758 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term85 _87123 s x) = (term86 _87123 s x).
Proof. exact (@lem3345757 _87123 (term41 _87123 s x)). Qed.
Lemma lem3345759 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term87 _87123 s x t) = (term39 _87123 s t x).
Proof. exact (eq_refl (term87 _87123 s x t)). Qed.
Lemma lem3345760 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3345761 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term88 _87123 s x t) = (term82 _87123 s t x).
Proof. exact (MK_COMB (@lem3345760) (@lem3345759 _87123 s t x)). Qed.
Lemma lem3345762 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term88 _87123 s x t) = (term83 _87123 s t x).
Proof. exact (TRANS (@lem3345761 _87123 s t x) (@lem3345751 _87123 s t x)). Qed.
Lemma lem3345763 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term89 _87123 s x) = (term90 _87123 s x).
Proof. exact (fun_ext (fun t : _87123 -> Prop => @lem3345762 _87123 s t x)). Qed.
Lemma lem3345764 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3345765 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term86 _87123 s x) = (term91 _87123 s x).
Proof. exact (MK_COMB (@lem3345764 _87123) (@lem3345763 _87123 s x)). Qed.
Lemma lem3345766 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term85 _87123 s x) = (term91 _87123 s x).
Proof. exact (TRANS (@lem3345758 _87123 s x) (@lem3345765 _87123 s x)). Qed.
Lemma lem3345767 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term41 _87123 s x) = (term92 _87123 s x).
Proof. exact (fun_ext (fun t : _87123 -> Prop => @lem3345756 _87123 s t x)). Qed.
Lemma lem3345768 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345769 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term42 _87123 s x) = (term93 _87123 s x).
Proof. exact (MK_COMB (@lem3345768 _87123) (@lem3345767 _87123 s x)). Qed.
Lemma lem3345778 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term82 _87123 t t' x) = (term83 _87123 t t' x).
Proof. exact (@lem17362 (t t') (t' x)). Qed.
Lemma lem3345783 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term39 _87123 t t' x) = (term84 _87123 t t' x).
Proof. exact (@lem17265 (t t') (t' x)). Qed.
Lemma lem3345784 {_87123 : Type'} (P : type686 _87123) : (term71 _87123 P) = (term72 _87123 P).
Proof. exact (@lem18392 (_87123 -> Prop) P). Qed.
Lemma lem3345785 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term85 _87123 t x) = (term86 _87123 t x).
Proof. exact (@lem3345784 _87123 (term41 _87123 t x)). Qed.
Lemma lem3345786 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term87 _87123 t x t') = (term39 _87123 t t' x).
Proof. exact (eq_refl (term87 _87123 t x t')). Qed.
Lemma lem3345787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3345788 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term88 _87123 t x t') = (term82 _87123 t t' x).
Proof. exact (MK_COMB (@lem3345787) (@lem3345786 _87123 t t' x)). Qed.
Lemma lem3345789 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term88 _87123 t x t') = (term83 _87123 t t' x).
Proof. exact (TRANS (@lem3345788 _87123 t t' x) (@lem3345778 _87123 t t' x)). Qed.
Lemma lem3345790 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term89 _87123 t x) = (term90 _87123 t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345789 _87123 t t' x)). Qed.
Lemma lem3345791 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3345792 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term86 _87123 t x) = (term91 _87123 t x).
Proof. exact (MK_COMB (@lem3345791 _87123) (@lem3345790 _87123 t x)). Qed.
Lemma lem3345793 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term85 _87123 t x) = (term91 _87123 t x).
Proof. exact (TRANS (@lem3345785 _87123 t x) (@lem3345792 _87123 t x)). Qed.
Lemma lem3345794 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term41 _87123 t x) = (term92 _87123 t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3345783 _87123 t t' x)). Qed.
Lemma lem3345795 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3345796 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term42 _87123 t x) = (term93 _87123 t x).
Proof. exact (MK_COMB (@lem3345795 _87123) (@lem3345794 _87123 t x)). Qed.
Lemma lem3345797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3345798 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term94 _87123 s x) = (term95 _87123 s x).
Proof. exact (MK_COMB (@lem3345797) (@lem3345766 _87123 s x)). Qed.
Lemma lem3345799 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term96 _87123 s t x) = (term97 _87123 s t x).
Proof. exact (MK_COMB (@lem3345798 _87123 s x) (@lem3345793 _87123 t x)). Qed.
Lemma lem3345800 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term98 _87123 s t x) = (term96 _87123 s t x).
Proof. exact (@lem17045 (term42 _87123 s x) (term42 _87123 t x)). Qed.
Lemma lem3345801 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term98 _87123 s t x) = (term97 _87123 s t x).
Proof. exact (TRANS (@lem3345800 _87123 s t x) (@lem3345799 _87123 s t x)). Qed.
Lemma lem3345802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3345803 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term44 _87123 s x) = (term99 _87123 s x).
Proof. exact (MK_COMB (@lem3345802) (@lem3345769 _87123 s x)). Qed.
Lemma lem3345804 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term45 _87123 s t x) = (term100 _87123 s t x).
Proof. exact (MK_COMB (@lem3345803 _87123 s x) (@lem3345796 _87123 t x)). Qed.
Lemma lem3345805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3345806 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term101 _87123 s t x) = (term102 _87123 s t x).
Proof. exact (MK_COMB (@lem3345805) (@lem3345739 _87123 s t x)). Qed.
Lemma lem3345807 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term103 _87123 s t x) = (term104 _87123 s t x).
Proof. exact (MK_COMB (@lem3345806 _87123 s t x) (@lem3345804 _87123 s t x)). Qed.
Lemma lem3345808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3345809 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term105 _87123 s t x) = (term106 _87123 s t x).
Proof. exact (MK_COMB (@lem3345808) (@lem3345742 _87123 s t x)). Qed.
Lemma lem3345810 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term107 _87123 s t x) = (term108 _87123 s t x).
Proof. exact (MK_COMB (@lem3345809 _87123 s t x) (@lem3345801 _87123 s t x)). Qed.
Lemma lem3345811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3345812 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term109 _87123 s t x) = (term110 _87123 s t x).
Proof. exact (MK_COMB (@lem3345811) (@lem3345810 _87123 s t x)). Qed.
Lemma lem3345813 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term111 _87123 s t x) = (term112 _87123 s t x).
Proof. exact (MK_COMB (@lem3345812 _87123 s t x) (@lem3345807 _87123 s t x)). Qed.
Lemma lem3345814 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term62 _87123 s t x) = (term111 _87123 s t x).
Proof. exact (@lem17646 (term29 _87123 s t x) (term45 _87123 s t x)). Qed.
Lemma lem3345815 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term62 _87123 s t x) = (term112 _87123 s t x).
Proof. exact (TRANS (@lem3345814 _87123 s t x) (@lem3345813 _87123 s t x)). Qed.
Lemma lem3346066 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3346067 {_87123 : Type'} (P : type686 _87123) (Q : type686 _87123) : (term115 _87123 P Q) = (term116 _87123 P Q).
Proof. exact (@lem3346066 (_87123 -> Prop) P Q). Qed.
Lemma lem3346068 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term117 _87123 s t x) = (term118 _87123 s t x).
Proof. exact (@lem3346067 _87123 (term90 _87123 s x) (term90 _87123 t x)). Qed.
Lemma lem3346069 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term119 _87123 s x t) = (term83 _87123 s t x).
Proof. exact (eq_refl (term119 _87123 s x t)). Qed.
Lemma lem3346070 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term120 _87123 s x) = (term90 _87123 s x).
Proof. exact (fun_ext (fun t : _87123 -> Prop => @lem3346069 _87123 s t x)). Qed.
Lemma lem3346071 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346072 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term121 _87123 s x) = (term91 _87123 s x).
Proof. exact (MK_COMB (@lem3346071 _87123) (@lem3346070 _87123 s x)). Qed.
Lemma lem3346073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346074 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term122 _87123 s x) = (term95 _87123 s x).
Proof. exact (MK_COMB (@lem3346073) (@lem3346072 _87123 s x)). Qed.
Lemma lem3346075 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term119 _87123 t x t') = (term83 _87123 t t' x).
Proof. exact (eq_refl (term119 _87123 t x t')). Qed.
Lemma lem3346076 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term120 _87123 t x) = (term90 _87123 t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346075 _87123 t t' x)). Qed.
Lemma lem3346077 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346078 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term121 _87123 t x) = (term91 _87123 t x).
Proof. exact (MK_COMB (@lem3346077 _87123) (@lem3346076 _87123 t x)). Qed.
Lemma lem3346079 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term117 _87123 s t x) = (term97 _87123 s t x).
Proof. exact (MK_COMB (@lem3346074 _87123 s x) (@lem3346078 _87123 t x)). Qed.
Lemma lem3346080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346081 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term123 _87123 s t x) = (term124 _87123 s t x).
Proof. exact (MK_COMB (@lem3346080) (@lem3346079 _87123 s t x)). Qed.
Lemma lem3346082 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term119 _87123 s x t) = (term83 _87123 s t x).
Proof. exact (eq_refl (term119 _87123 s x t)). Qed.
Lemma lem3346083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346084 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term125 _87123 s x t) = (term126 _87123 s t x).
Proof. exact (MK_COMB (@lem3346083) (@lem3346082 _87123 s t x)). Qed.
Lemma lem3346085 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term119 _87123 t x t') = (term83 _87123 t t' x).
Proof. exact (eq_refl (term119 _87123 t x t')). Qed.
Lemma lem3346086 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term127 _87123 s t x t') = (term128 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346084 _87123 s t' x) (@lem3346085 _87123 t t' x)). Qed.
Lemma lem3346087 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term129 _87123 s t x) = (term130 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346086 _87123 s t t' x)). Qed.
Lemma lem3346088 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346089 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term118 _87123 s t x) = (term131 _87123 s t x).
Proof. exact (MK_COMB (@lem3346088 _87123) (@lem3346087 _87123 s t x)). Qed.
Lemma lem3346090 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : ((term117 _87123 s t x) = (term118 _87123 s t x)) = ((term97 _87123 s t x) = (term131 _87123 s t x)).
Proof. exact (MK_COMB (@lem3346081 _87123 s t x) (@lem3346089 _87123 s t x)). Qed.
Lemma lem3346091 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term97 _87123 s t x) = (term131 _87123 s t x).
Proof. exact (EQ_MP (@lem3346090 _87123 s t x) (@lem3346068 _87123 s t x)). Qed.
Lemma lem3346092 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term106 _87123 s t x) = (term106 _87123 s t x).
Proof. exact (eq_refl (term106 _87123 s t x)). Qed.
Lemma lem3346093 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term108 _87123 s t x) = (term132 _87123 s t x).
Proof. exact (MK_COMB (@lem3346092 _87123 s t x) (@lem3346091 _87123 s t x)). Qed.
Lemma lem3346095 {A : Type'} (P : Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3346096 {_87123 : Type'} (P : Prop) (Q : type686 _87123) : (term135 _87123 P Q) = (term136 _87123 P Q).
Proof. exact (@lem3346095 (_87123 -> Prop) P Q). Qed.
Lemma lem3346097 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term137 _87123 s t x) = (term138 _87123 s t x).
Proof. exact (@lem3346096 _87123 (term81 _87123 s t x) (term130 _87123 s t x)). Qed.
Lemma lem3346098 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term139 _87123 s t x t') = (term128 _87123 s t t' x).
Proof. exact (eq_refl (term139 _87123 s t x t')). Qed.
Lemma lem3346099 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term140 _87123 s t x) = (term130 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346098 _87123 s t t' x)). Qed.
Lemma lem3346100 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346101 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term141 _87123 s t x) = (term131 _87123 s t x).
Proof. exact (MK_COMB (@lem3346100 _87123) (@lem3346099 _87123 s t x)). Qed.
Lemma lem3346102 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term106 _87123 s t x) = (term106 _87123 s t x).
Proof. exact (eq_refl (term106 _87123 s t x)). Qed.
Lemma lem3346103 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term137 _87123 s t x) = (term132 _87123 s t x).
Proof. exact (MK_COMB (@lem3346102 _87123 s t x) (@lem3346101 _87123 s t x)). Qed.
Lemma lem3346104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346105 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term142 _87123 s t x) = (term143 _87123 s t x).
Proof. exact (MK_COMB (@lem3346104) (@lem3346103 _87123 s t x)). Qed.
Lemma lem3346106 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term139 _87123 s t x t') = (term128 _87123 s t t' x).
Proof. exact (eq_refl (term139 _87123 s t x t')). Qed.
Lemma lem3346107 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term106 _87123 s t x) = (term106 _87123 s t x).
Proof. exact (eq_refl (term106 _87123 s t x)). Qed.
Lemma lem3346108 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term144 _87123 s t x t') = (term145 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346107 _87123 s t x) (@lem3346106 _87123 s t t' x)). Qed.
Lemma lem3346109 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term146 _87123 s t x) = (term147 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346108 _87123 s t t' x)). Qed.
Lemma lem3346110 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346111 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term138 _87123 s t x) = (term148 _87123 s t x).
Proof. exact (MK_COMB (@lem3346110 _87123) (@lem3346109 _87123 s t x)). Qed.
Lemma lem3346112 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : ((term137 _87123 s t x) = (term138 _87123 s t x)) = ((term132 _87123 s t x) = (term148 _87123 s t x)).
Proof. exact (MK_COMB (@lem3346105 _87123 s t x) (@lem3346111 _87123 s t x)). Qed.
Lemma lem3346113 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term132 _87123 s t x) = (term148 _87123 s t x).
Proof. exact (EQ_MP (@lem3346112 _87123 s t x) (@lem3346097 _87123 s t x)). Qed.
Lemma lem3346114 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term108 _87123 s t x) = (term148 _87123 s t x).
Proof. exact (TRANS (@lem3346093 _87123 s t x) (@lem3346113 _87123 s t x)). Qed.
Lemma lem3346115 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346116 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term110 _87123 s t x) = (term149 _87123 s t x).
Proof. exact (MK_COMB (@lem3346115) (@lem3346114 _87123 s t x)). Qed.
Lemma lem3346118 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3346119 {_87123 : Type'} (P : type686 _87123) (Q : Prop) : (term152 _87123 P Q) = (term153 _87123 P Q).
Proof. exact (@lem3346118 (_87123 -> Prop) P Q). Qed.
Lemma lem3346120 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term154 _87123 s t x) = (term155 _87123 s t x).
Proof. exact (@lem3346119 _87123 (term78 _87123 s t x) (term100 _87123 s t x)). Qed.
Lemma lem3346121 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term156 _87123 s t x t') = (term66 _87123 s t t' x).
Proof. exact (eq_refl (term156 _87123 s t x t')). Qed.
Lemma lem3346122 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term157 _87123 s t x) = (term78 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346121 _87123 s t t' x)). Qed.
Lemma lem3346123 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346124 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term158 _87123 s t x) = (term79 _87123 s t x).
Proof. exact (MK_COMB (@lem3346123 _87123) (@lem3346122 _87123 s t x)). Qed.
Lemma lem3346125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346126 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term159 _87123 s t x) = (term102 _87123 s t x).
Proof. exact (MK_COMB (@lem3346125) (@lem3346124 _87123 s t x)). Qed.
Lemma lem3346127 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term100 _87123 s t x) = (term100 _87123 s t x).
Proof. exact (eq_refl (term100 _87123 s t x)). Qed.
Lemma lem3346128 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term154 _87123 s t x) = (term104 _87123 s t x).
Proof. exact (MK_COMB (@lem3346126 _87123 s t x) (@lem3346127 _87123 s t x)). Qed.
Lemma lem3346129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346130 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term160 _87123 s t x) = (term161 _87123 s t x).
Proof. exact (MK_COMB (@lem3346129) (@lem3346128 _87123 s t x)). Qed.
Lemma lem3346131 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term156 _87123 s t x t') = (term66 _87123 s t t' x).
Proof. exact (eq_refl (term156 _87123 s t x t')). Qed.
Lemma lem3346132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346133 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term162 _87123 s t x t') = (term163 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346132) (@lem3346131 _87123 s t t' x)). Qed.
Lemma lem3346134 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term100 _87123 s t x) = (term100 _87123 s t x).
Proof. exact (eq_refl (term100 _87123 s t x)). Qed.
Lemma lem3346135 {_87123 : Type'} (t : _87123 -> Prop) (s : type686 _87123) (t' : type686 _87123) (x : _87123) : (term164 _87123 t s t' x) = (term165 _87123 t s t' x).
Proof. exact (MK_COMB (@lem3346133 _87123 s t' t x) (@lem3346134 _87123 s t' x)). Qed.
Lemma lem3346136 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term166 _87123 s t x) = (term167 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346135 _87123 t' s t x)). Qed.
Lemma lem3346137 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346138 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term155 _87123 s t x) = (term168 _87123 s t x).
Proof. exact (MK_COMB (@lem3346137 _87123) (@lem3346136 _87123 s t x)). Qed.
Lemma lem3346139 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : ((term154 _87123 s t x) = (term155 _87123 s t x)) = ((term104 _87123 s t x) = (term168 _87123 s t x)).
Proof. exact (MK_COMB (@lem3346130 _87123 s t x) (@lem3346138 _87123 s t x)). Qed.
Lemma lem3346140 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term104 _87123 s t x) = (term168 _87123 s t x).
Proof. exact (EQ_MP (@lem3346139 _87123 s t x) (@lem3346120 _87123 s t x)). Qed.
Lemma lem3346141 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term112 _87123 s t x) = (term169 _87123 s t x).
Proof. exact (MK_COMB (@lem3346116 _87123 s t x) (@lem3346140 _87123 s t x)). Qed.
Lemma lem3346143 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3346144 {_87123 : Type'} (P : type686 _87123) (Q : type686 _87123) : (term115 _87123 P Q) = (term116 _87123 P Q).
Proof. exact (@lem3346143 (_87123 -> Prop) P Q). Qed.
Lemma lem3346145 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term170 _87123 s t x) = (term171 _87123 s t x).
Proof. exact (@lem3346144 _87123 (term147 _87123 s t x) (term167 _87123 s t x)). Qed.
Lemma lem3346146 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term172 _87123 s t x t') = (term145 _87123 s t t' x).
Proof. exact (eq_refl (term172 _87123 s t x t')). Qed.
Lemma lem3346147 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term173 _87123 s t x) = (term147 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346146 _87123 s t t' x)). Qed.
Lemma lem3346148 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346149 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term174 _87123 s t x) = (term148 _87123 s t x).
Proof. exact (MK_COMB (@lem3346148 _87123) (@lem3346147 _87123 s t x)). Qed.
Lemma lem3346150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346151 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term175 _87123 s t x) = (term149 _87123 s t x).
Proof. exact (MK_COMB (@lem3346150) (@lem3346149 _87123 s t x)). Qed.
Lemma lem3346152 {_87123 : Type'} (t : _87123 -> Prop) (s : type686 _87123) (t' : type686 _87123) (x : _87123) : (term176 _87123 s t' x t) = (term165 _87123 t s t' x).
Proof. exact (eq_refl (term176 _87123 s t' x t)). Qed.
Lemma lem3346153 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term177 _87123 s t x) = (term167 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346152 _87123 t' s t x)). Qed.
Lemma lem3346154 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346155 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term178 _87123 s t x) = (term168 _87123 s t x).
Proof. exact (MK_COMB (@lem3346154 _87123) (@lem3346153 _87123 s t x)). Qed.
Lemma lem3346156 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term170 _87123 s t x) = (term169 _87123 s t x).
Proof. exact (MK_COMB (@lem3346151 _87123 s t x) (@lem3346155 _87123 s t x)). Qed.
Lemma lem3346157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346158 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term179 _87123 s t x) = (term180 _87123 s t x).
Proof. exact (MK_COMB (@lem3346157) (@lem3346156 _87123 s t x)). Qed.
Lemma lem3346159 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term172 _87123 s t x t') = (term145 _87123 s t t' x).
Proof. exact (eq_refl (term172 _87123 s t x t')). Qed.
Lemma lem3346160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346161 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term181 _87123 s t x t') = (term182 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346160) (@lem3346159 _87123 s t t' x)). Qed.
Lemma lem3346162 {_87123 : Type'} (t : _87123 -> Prop) (s : type686 _87123) (t' : type686 _87123) (x : _87123) : (term176 _87123 s t' x t) = (term165 _87123 t s t' x).
Proof. exact (eq_refl (term176 _87123 s t' x t)). Qed.
Lemma lem3346163 {_87123 : Type'} (t : _87123 -> Prop) (s : type686 _87123) (t' : type686 _87123) (x : _87123) : (term183 _87123 s t' x t) = (term184 _87123 t s t' x).
Proof. exact (MK_COMB (@lem3346161 _87123 s t' t x) (@lem3346162 _87123 t s t' x)). Qed.
Lemma lem3346164 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term185 _87123 s t x) = (term186 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346163 _87123 t' s t x)). Qed.
Lemma lem3346165 {_87123 : Type'} : (@ex (_87123 -> Prop)) = (@ex (_87123 -> Prop)).
Proof. exact (eq_refl (@ex (_87123 -> Prop))). Qed.
Lemma lem3346166 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term171 _87123 s t x) = (term187 _87123 s t x).
Proof. exact (MK_COMB (@lem3346165 _87123) (@lem3346164 _87123 s t x)). Qed.
Lemma lem3346167 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : ((term170 _87123 s t x) = (term171 _87123 s t x)) = ((term169 _87123 s t x) = (term187 _87123 s t x)).
Proof. exact (MK_COMB (@lem3346158 _87123 s t x) (@lem3346166 _87123 s t x)). Qed.
Lemma lem3346168 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term169 _87123 s t x) = (term187 _87123 s t x).
Proof. exact (EQ_MP (@lem3346167 _87123 s t x) (@lem3346145 _87123 s t x)). Qed.
Lemma lem3346170 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term112 _87123 s t x) = (term187 _87123 s t x).
Proof. exact (TRANS (@lem3346141 _87123 s t x) (@lem3346168 _87123 s t x)). Qed.
Lemma lem3346171 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term62 _87123 s t x) = (term187 _87123 s t x).
Proof. exact (TRANS (@lem3345815 _87123 s t x) (@lem3346170 _87123 s t x)). Qed.
Lemma lem3346172 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term62 _87123 s t x) : term187 _87123 s t x.
Proof. exact (EQ_MP (@lem3346171 _87123 s t x) (@lem3345705 _87123 s t x h1)). Qed.
Lemma lem3346173 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term184 _87123 t' s t x) : term184 _87123 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3346178 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346179 {_87123 : Type'} (f : _87123 -> Prop) (x : _87123) : (f x) = (@I (_87123 -> Prop) f x).
Proof. exact (@lem3346178 _87123 Prop f x). Qed.
Lemma lem3346181 {_87123 : Type'} (t : _87123 -> Prop) (x : _87123) : (t x) = (@I (_87123 -> Prop) t x).
Proof. exact (@lem3346179 _87123 t x). Qed.
Lemma lem3346182 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3346187 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346188 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346187 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346190 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (t t') = (@I ((_87123 -> Prop) -> Prop) t t').
Proof. exact (@lem3346188 _87123 t t'). Qed.
Lemma lem3346191 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (term188 _87123 t t') = (term189 _87123 t t').
Proof. exact (MK_COMB (@lem3346182) (@lem3346190 _87123 t t')). Qed.
Lemma lem3346192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346193 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (term190 _87123 t t') = (term191 _87123 t t').
Proof. exact (MK_COMB (@lem3346192) (@lem3346191 _87123 t t')). Qed.
Lemma lem3346194 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term84 _87123 t t' x) = (term192 _87123 t t' x).
Proof. exact (MK_COMB (@lem3346193 _87123 t t') (@lem3346181 _87123 t' x)). Qed.
Lemma lem3346195 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term92 _87123 t x) = (term193 _87123 t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346194 _87123 t t' x)). Qed.
Lemma lem3346196 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3346197 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term93 _87123 t x) = (term194 _87123 t x).
Proof. exact (MK_COMB (@lem3346196 _87123) (@lem3346195 _87123 t x)). Qed.
Lemma lem3346202 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346203 {_87123 : Type'} (f : _87123 -> Prop) (x : _87123) : (f x) = (@I (_87123 -> Prop) f x).
Proof. exact (@lem3346202 _87123 Prop f x). Qed.
Lemma lem3346205 {_87123 : Type'} (t : _87123 -> Prop) (x : _87123) : (t x) = (@I (_87123 -> Prop) t x).
Proof. exact (@lem3346203 _87123 t x). Qed.
Lemma lem3346206 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3346211 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346212 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346211 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346214 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (s t) = (@I ((_87123 -> Prop) -> Prop) s t).
Proof. exact (@lem3346212 _87123 s t). Qed.
Lemma lem3346215 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (term188 _87123 s t) = (term189 _87123 s t).
Proof. exact (MK_COMB (@lem3346206) (@lem3346214 _87123 s t)). Qed.
Lemma lem3346216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346217 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (term190 _87123 s t) = (term191 _87123 s t).
Proof. exact (MK_COMB (@lem3346216) (@lem3346215 _87123 s t)). Qed.
Lemma lem3346218 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term84 _87123 s t x) = (term192 _87123 s t x).
Proof. exact (MK_COMB (@lem3346217 _87123 s t) (@lem3346205 _87123 t x)). Qed.
Lemma lem3346219 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term92 _87123 s x) = (term193 _87123 s x).
Proof. exact (fun_ext (fun t : _87123 -> Prop => @lem3346218 _87123 s t x)). Qed.
Lemma lem3346220 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3346221 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term93 _87123 s x) = (term194 _87123 s x).
Proof. exact (MK_COMB (@lem3346220 _87123) (@lem3346219 _87123 s x)). Qed.
Lemma lem3346222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346223 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term99 _87123 s x) = (term195 _87123 s x).
Proof. exact (MK_COMB (@lem3346222) (@lem3346221 _87123 s x)). Qed.
Lemma lem3346224 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term100 _87123 s t x) = (term196 _87123 s t x).
Proof. exact (MK_COMB (@lem3346223 _87123 s x) (@lem3346197 _87123 t x)). Qed.
Lemma lem3346225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3346230 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346231 {_87123 : Type'} (f : _87123 -> Prop) (x : _87123) : (f x) = (@I (_87123 -> Prop) f x).
Proof. exact (@lem3346230 _87123 Prop f x). Qed.
Lemma lem3346233 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (t' x) = (@I (_87123 -> Prop) t' x).
Proof. exact (@lem3346231 _87123 t' x). Qed.
Lemma lem3346234 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term197 _87123 t' x) = (term198 _87123 t' x).
Proof. exact (MK_COMB (@lem3346225) (@lem3346233 _87123 t' x)). Qed.
Lemma lem3346239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346240 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346239 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346242 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (t t') = (@I ((_87123 -> Prop) -> Prop) t t').
Proof. exact (@lem3346240 _87123 t t'). Qed.
Lemma lem3346247 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346248 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346247 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346250 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) : (s t') = (@I ((_87123 -> Prop) -> Prop) s t').
Proof. exact (@lem3346248 _87123 s t'). Qed.
Lemma lem3346251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346252 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) : (term21 _87123 s t') = (term199 _87123 s t').
Proof. exact (MK_COMB (@lem3346251) (@lem3346250 _87123 s t')). Qed.
Lemma lem3346253 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term22 _87123 s t t') = (term200 _87123 s t t').
Proof. exact (MK_COMB (@lem3346252 _87123 s t') (@lem3346242 _87123 t t')). Qed.
Lemma lem3346254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346255 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term201 _87123 s t t') = (term202 _87123 s t t').
Proof. exact (MK_COMB (@lem3346254) (@lem3346253 _87123 s t t')). Qed.
Lemma lem3346256 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term66 _87123 s t t' x) = (term203 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346255 _87123 s t t') (@lem3346234 _87123 t' x)). Qed.
Lemma lem3346257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346258 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term163 _87123 s t t' x) = (term204 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346257) (@lem3346256 _87123 s t t' x)). Qed.
Lemma lem3346259 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term165 _87123 t' s t x) = (term205 _87123 t' s t x).
Proof. exact (MK_COMB (@lem3346258 _87123 s t t' x) (@lem3346224 _87123 s t x)). Qed.
Lemma lem3346260 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3346265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346266 {_87123 : Type'} (f : _87123 -> Prop) (x : _87123) : (f x) = (@I (_87123 -> Prop) f x).
Proof. exact (@lem3346265 _87123 Prop f x). Qed.
Lemma lem3346268 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (t' x) = (@I (_87123 -> Prop) t' x).
Proof. exact (@lem3346266 _87123 t' x). Qed.
Lemma lem3346269 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term197 _87123 t' x) = (term198 _87123 t' x).
Proof. exact (MK_COMB (@lem3346260) (@lem3346268 _87123 t' x)). Qed.
Lemma lem3346274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346275 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346274 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346277 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (t t') = (@I ((_87123 -> Prop) -> Prop) t t').
Proof. exact (@lem3346275 _87123 t t'). Qed.
Lemma lem3346278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346279 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (term206 _87123 t t') = (term207 _87123 t t').
Proof. exact (MK_COMB (@lem3346278) (@lem3346277 _87123 t t')). Qed.
Lemma lem3346280 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term83 _87123 t t' x) = (term208 _87123 t t' x).
Proof. exact (MK_COMB (@lem3346279 _87123 t t') (@lem3346269 _87123 t' x)). Qed.
Lemma lem3346281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3346286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346287 {_87123 : Type'} (f : _87123 -> Prop) (x : _87123) : (f x) = (@I (_87123 -> Prop) f x).
Proof. exact (@lem3346286 _87123 Prop f x). Qed.
Lemma lem3346289 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (t' x) = (@I (_87123 -> Prop) t' x).
Proof. exact (@lem3346287 _87123 t' x). Qed.
Lemma lem3346290 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term197 _87123 t' x) = (term198 _87123 t' x).
Proof. exact (MK_COMB (@lem3346281) (@lem3346289 _87123 t' x)). Qed.
Lemma lem3346295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346296 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346295 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346298 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) : (s t') = (@I ((_87123 -> Prop) -> Prop) s t').
Proof. exact (@lem3346296 _87123 s t'). Qed.
Lemma lem3346299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346300 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) : (term206 _87123 s t') = (term207 _87123 s t').
Proof. exact (MK_COMB (@lem3346299) (@lem3346298 _87123 s t')). Qed.
Lemma lem3346301 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term83 _87123 s t' x) = (term208 _87123 s t' x).
Proof. exact (MK_COMB (@lem3346300 _87123 s t') (@lem3346290 _87123 t' x)). Qed.
Lemma lem3346302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346303 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term126 _87123 s t' x) = (term209 _87123 s t' x).
Proof. exact (MK_COMB (@lem3346302) (@lem3346301 _87123 s t' x)). Qed.
Lemma lem3346304 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term128 _87123 s t t' x) = (term210 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346303 _87123 s t' x) (@lem3346280 _87123 t t' x)). Qed.
Lemma lem3346309 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346310 {_87123 : Type'} (f : _87123 -> Prop) (x : _87123) : (f x) = (@I (_87123 -> Prop) f x).
Proof. exact (@lem3346309 _87123 Prop f x). Qed.
Lemma lem3346312 {_87123 : Type'} (t : _87123 -> Prop) (x : _87123) : (t x) = (@I (_87123 -> Prop) t x).
Proof. exact (@lem3346310 _87123 t x). Qed.
Lemma lem3346313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3346318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346319 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346318 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346321 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (t t') = (@I ((_87123 -> Prop) -> Prop) t t').
Proof. exact (@lem3346319 _87123 t t'). Qed.
Lemma lem3346322 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (term188 _87123 t t') = (term189 _87123 t t').
Proof. exact (MK_COMB (@lem3346313) (@lem3346321 _87123 t t')). Qed.
Lemma lem3346323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3346328 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3346329 {_87123 : Type'} (f : type686 _87123) (x : _87123 -> Prop) : (f x) = (@I ((_87123 -> Prop) -> Prop) f x).
Proof. exact (@lem3346328 (_87123 -> Prop) Prop f x). Qed.
Lemma lem3346331 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (s t) = (@I ((_87123 -> Prop) -> Prop) s t).
Proof. exact (@lem3346329 _87123 s t). Qed.
Lemma lem3346332 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (term188 _87123 s t) = (term189 _87123 s t).
Proof. exact (MK_COMB (@lem3346323) (@lem3346331 _87123 s t)). Qed.
Lemma lem3346333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346334 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) : (term211 _87123 s t) = (term212 _87123 s t).
Proof. exact (MK_COMB (@lem3346333) (@lem3346332 _87123 s t)). Qed.
Lemma lem3346335 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term64 _87123 s t t') = (term213 _87123 s t t').
Proof. exact (MK_COMB (@lem3346334 _87123 s t') (@lem3346322 _87123 t t')). Qed.
Lemma lem3346336 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346337 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) : (term68 _87123 s t t') = (term214 _87123 s t t').
Proof. exact (MK_COMB (@lem3346336) (@lem3346335 _87123 s t t')). Qed.
Lemma lem3346338 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term70 _87123 s t t' x) = (term215 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346337 _87123 s t t') (@lem3346312 _87123 t' x)). Qed.
Lemma lem3346339 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term80 _87123 s t x) = (term216 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346338 _87123 s t t' x)). Qed.
Lemma lem3346340 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3346341 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term81 _87123 s t x) = (term217 _87123 s t x).
Proof. exact (MK_COMB (@lem3346340 _87123) (@lem3346339 _87123 s t x)). Qed.
Lemma lem3346342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3346343 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term106 _87123 s t x) = (term218 _87123 s t x).
Proof. exact (MK_COMB (@lem3346342) (@lem3346341 _87123 s t x)). Qed.
Lemma lem3346344 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term145 _87123 s t t' x) = (term219 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346343 _87123 s t x) (@lem3346304 _87123 s t t' x)). Qed.
Lemma lem3346345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3346346 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term182 _87123 s t t' x) = (term220 _87123 s t t' x).
Proof. exact (MK_COMB (@lem3346345) (@lem3346344 _87123 s t t' x)). Qed.
Lemma lem3346347 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term184 _87123 t' s t x) = (term221 _87123 t' s t x).
Proof. exact (MK_COMB (@lem3346346 _87123 s t t' x) (@lem3346259 _87123 t' s t x)). Qed.
Lemma lem3346348 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term184 _87123 t' s t x) : term221 _87123 t' s t x.
Proof. exact (EQ_MP (@lem3346347 _87123 t' s t x) (@lem3346173 _87123 t' s t x h1)). Qed.
Lemma lem3346349 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term219 _87123 s t t' x.
Proof. exact (h1). Qed.
Lemma lem3346350 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term205 _87123 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3346351 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term210 _87123 s t t' x.
Proof. exact (proj2 (@lem3346349 _87123 s t t' x h1)). Qed.
Lemma lem3346352 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term217 _87123 s t x.
Proof. exact (proj1 (@lem3346349 _87123 s t t' x h1)). Qed.
Lemma lem3346353 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 s t' x) : term208 _87123 s t' x.
Proof. exact (h1). Qed.
Lemma lem3346354 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 t t' x) : term208 _87123 t t' x.
Proof. exact (h1). Qed.
Lemma lem3346359 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term196 _87123 s t x.
Proof. exact (proj2 (@lem3346350 _87123 t' s t x h1)). Qed.
Lemma lem3346360 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term203 _87123 s t t' x.
Proof. exact (proj1 (@lem3346350 _87123 t' s t x h1)). Qed.
Lemma lem3346361 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term194 _87123 t x.
Proof. exact (proj2 (@lem3346359 _87123 t' s t x h1)). Qed.
Lemma lem3346362 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term194 _87123 s x.
Proof. exact (proj1 (@lem3346359 _87123 t' s t x h1)). Qed.
Lemma lem3346364 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term200 _87123 s t t'.
Proof. exact (proj1 (@lem3346360 _87123 t' s t x h1)). Qed.
Lemma lem3346384 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term215 _87123 s t t' x) = (term222 _87123 s t t' x).
Proof. exact (@lem19699 (term189 _87123 s t') (term189 _87123 t t') (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346385 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term216 _87123 s t x) = (term223 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346384 _87123 s t t' x)). Qed.
Lemma lem3346386 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3346388 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term217 _87123 s t x) = (term224 _87123 s t x).
Proof. exact (MK_COMB (@lem3346386 _87123) (@lem3346385 _87123 s t x)). Qed.
Lemma lem3346389 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term224 _87123 s t x.
Proof. exact (EQ_MP (@lem3346388 _87123 s t x) (@lem3346352 _87123 s t t' x h1)). Qed.
Lemma lem3346415 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term215 _87123 s t t' x) = (term222 _87123 s t t' x).
Proof. exact (@lem19699 (term189 _87123 s t') (term189 _87123 t t') (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346416 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term216 _87123 s t x) = (term223 _87123 s t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346415 _87123 s t t' x)). Qed.
Lemma lem3346417 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3346419 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term217 _87123 s t x) = (term224 _87123 s t x).
Proof. exact (MK_COMB (@lem3346417 _87123) (@lem3346416 _87123 s t x)). Qed.
Lemma lem3346420 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term224 _87123 s t x.
Proof. exact (EQ_MP (@lem3346419 _87123 s t x) (@lem3346352 _87123 s t t' x h1)). Qed.
Lemma lem3346436 {_87123 : Type'} (s : type686 _87123) (t : _87123 -> Prop) (x : _87123) : (term192 _87123 s t x) = (term192 _87123 s t x).
Proof. exact (eq_refl (term192 _87123 s t x)). Qed.
Lemma lem3346437 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term193 _87123 s x) = (term193 _87123 s x).
Proof. exact (fun_ext (fun t : _87123 -> Prop => @lem3346436 _87123 s t x)). Qed.
Lemma lem3346438 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3346440 {_87123 : Type'} (s : type686 _87123) (x : _87123) : (term194 _87123 s x) = (term194 _87123 s x).
Proof. exact (MK_COMB (@lem3346438 _87123) (@lem3346437 _87123 s x)). Qed.
Lemma lem3346441 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term194 _87123 s x.
Proof. exact (EQ_MP (@lem3346440 _87123 s x) (@lem3346362 _87123 t' s t x h1)). Qed.
Lemma lem3346462 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) s t') : @I ((_87123 -> Prop) -> Prop) s t'.
Proof. exact (h1). Qed.
Lemma lem3346483 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) : (term192 _87123 t t' x) = (term192 _87123 t t' x).
Proof. exact (eq_refl (term192 _87123 t t' x)). Qed.
Lemma lem3346484 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term193 _87123 t x) = (term193 _87123 t x).
Proof. exact (fun_ext (fun t' : _87123 -> Prop => @lem3346483 _87123 t t' x)). Qed.
Lemma lem3346485 {_87123 : Type'} : (@all (_87123 -> Prop)) = (@all (_87123 -> Prop)).
Proof. exact (eq_refl (@all (_87123 -> Prop))). Qed.
Lemma lem3346487 {_87123 : Type'} (t : type686 _87123) (x : _87123) : (term194 _87123 t x) = (term194 _87123 t x).
Proof. exact (MK_COMB (@lem3346485 _87123) (@lem3346484 _87123 t x)). Qed.
Lemma lem3346488 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term194 _87123 t x.
Proof. exact (EQ_MP (@lem3346487 _87123 t x) (@lem3346361 _87123 t' s t x h1)). Qed.
Lemma lem3346496 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) t t') : @I ((_87123 -> Prop) -> Prop) t t'.
Proof. exact (h1). Qed.
Lemma lem3346497 {_87123 : Type'} (_34899 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term225 _87123 s t x _34899.
Proof. exact (@lem3346389 _87123 s t t' x h1 _34899). Qed.
Lemma lem3346498 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (_34899 : _87123 -> Prop) (x : _87123) : (term225 _87123 s t x _34899) = (term222 _87123 s t _34899 x).
Proof. exact (eq_refl (term225 _87123 s t x _34899)). Qed.
Lemma lem3346499 {_87123 : Type'} (_34899 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term222 _87123 s t _34899 x.
Proof. exact (EQ_MP (@lem3346498 _87123 s t _34899 x) (@lem3346497 _87123 _34899 s t t' x h1)). Qed.
Lemma lem3346500 {_87123 : Type'} (_34900 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term225 _87123 s t x _34900.
Proof. exact (@lem3346420 _87123 s t t' x h1 _34900). Qed.
Lemma lem3346501 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) (x : _87123) : (term225 _87123 s t x _34900) = (term222 _87123 s t _34900 x).
Proof. exact (eq_refl (term225 _87123 s t x _34900)). Qed.
Lemma lem3346502 {_87123 : Type'} (_34900 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term222 _87123 s t _34900 x.
Proof. exact (EQ_MP (@lem3346501 _87123 s t _34900 x) (@lem3346500 _87123 _34900 s t t' x h1)). Qed.
Lemma lem3346503 {_87123 : Type'} (_34901 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term226 _87123 s x _34901.
Proof. exact (@lem3346441 _87123 t' s t x h1 _34901). Qed.
Lemma lem3346504 {_87123 : Type'} (s : type686 _87123) (_34901 : _87123 -> Prop) (x : _87123) : (term226 _87123 s x _34901) = (term192 _87123 s _34901 x).
Proof. exact (eq_refl (term226 _87123 s x _34901)). Qed.
Lemma lem3346512 {_87123 : Type'} (_34904 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term226 _87123 t x _34904.
Proof. exact (@lem3346488 _87123 t' s t x h1 _34904). Qed.
Lemma lem3346513 {_87123 : Type'} (t : type686 _87123) (_34904 : _87123 -> Prop) (x : _87123) : (term226 _87123 t x _34904) = (term192 _87123 t _34904 x).
Proof. exact (eq_refl (term226 _87123 t x _34904)). Qed.
Lemma lem3346522 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 s t' x) : term198 _87123 t' x.
Proof. exact (proj2 (@lem3346353 _87123 s t' x h1)). Qed.
Lemma lem3346528 {_87123 : Type'} (_34899 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term192 _87123 s _34899 x.
Proof. exact (proj1 (@lem3346499 _87123 _34899 s t t' x h1)). Qed.
Lemma lem3346538 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 t t' x) : term198 _87123 t' x.
Proof. exact (proj2 (@lem3346354 _87123 t t' x h1)). Qed.
Lemma lem3346550 {_87123 : Type'} (_34900 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term192 _87123 t _34900 x.
Proof. exact (proj2 (@lem3346502 _87123 _34900 s t t' x h1)). Qed.
Lemma lem3346556 {_87123 : Type'} (_34901 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term192 _87123 s _34901 x.
Proof. exact (EQ_MP (@lem3346504 _87123 s _34901 x) (@lem3346503 _87123 _34901 t' s t x h1)). Qed.
Lemma lem3346564 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term198 _87123 t' x.
Proof. exact (proj2 (@lem3346360 _87123 t' s t x h1)). Qed.
Lemma lem3346566 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) s t') : @I ((_87123 -> Prop) -> Prop) s t'.
Proof. exact (h1). Qed.
Lemma lem3346578 {_87123 : Type'} (_34904 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term192 _87123 t _34904 x.
Proof. exact (EQ_MP (@lem3346513 _87123 t _34904 x) (@lem3346512 _87123 _34904 t' s t x h1)). Qed.
Lemma lem3346580 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term198 _87123 t' x.
Proof. exact (proj2 (@lem3346360 _87123 t' s t x h1)). Qed.
Lemma lem3346582 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) t t') : @I ((_87123 -> Prop) -> Prop) t t'.
Proof. exact (h1). Qed.
Lemma lem3346584 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 s t' x) : @I ((_87123 -> Prop) -> Prop) s t'.
Proof. exact (proj1 (@lem3346353 _87123 s t' x h1)). Qed.
Lemma lem3346585 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 s t' x) : term227 _87123 s t'.
Proof. exact (fun h0 : term189 _87123 s t' => @lem3346584 _87123 s t' x h1). Qed.
Lemma lem3346587 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346588 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) : (term227 _87123 s t') = (@I ((_87123 -> Prop) -> Prop) s t').
Proof. exact (@lem3346587 (@I ((_87123 -> Prop) -> Prop) s t')). Qed.
Lemma lem3346589 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 s t' x) : @I ((_87123 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3346588 _87123 s t') (@lem3346585 _87123 s t' x h1)). Qed.
Lemma lem3346595 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3346596 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : (term192 _87123 s _34899 x) = (term229 _87123 x s _34899).
Proof. exact (@lem3346595 (@I (_87123 -> Prop) _34899 x) (term189 _87123 s _34899)). Qed.
Lemma lem3346602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346603 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : (term230 _87123 s _34899 x) = (term231 _87123 x s _34899).
Proof. exact (MK_COMB (@lem3346602) (@lem3346596 _87123 x s _34899)). Qed.
Lemma lem3346609 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : (term229 _87123 x s _34899) = (term229 _87123 x s _34899).
Proof. exact (eq_refl (term229 _87123 x s _34899)). Qed.
Lemma lem3346610 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : ((term192 _87123 s _34899 x) = (term229 _87123 x s _34899)) = ((term229 _87123 x s _34899) = (term229 _87123 x s _34899)).
Proof. exact (MK_COMB (@lem3346603 _87123 x s _34899) (@lem3346609 _87123 x s _34899)). Qed.
Lemma lem3346612 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3346613 (x : Prop) : (x = x) = True.
Proof. exact (@lem3346612 Prop x). Qed.
Lemma lem3346614 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : ((term229 _87123 x s _34899) = (term229 _87123 x s _34899)) = True.
Proof. exact (@lem3346613 (term229 _87123 x s _34899)). Qed.
Lemma lem3346615 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : ((term192 _87123 s _34899 x) = (term229 _87123 x s _34899)) = True.
Proof. exact (TRANS (@lem3346610 _87123 x s _34899) (@lem3346614 _87123 x s _34899)). Qed.
Lemma lem3346616 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : True = ((term192 _87123 s _34899 x) = (term229 _87123 x s _34899)).
Proof. exact (SYM (@lem3346615 _87123 x s _34899)). Qed.
Lemma lem3346617 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34899 : _87123 -> Prop) : (term192 _87123 s _34899 x) = (term229 _87123 x s _34899).
Proof. exact (EQ_MP (@lem3346616 _87123 x s _34899) (@lem0)). Qed.
Lemma lem3346618 {_87123 : Type'} (_34899 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term229 _87123 x s _34899.
Proof. exact (EQ_MP (@lem3346617 _87123 x s _34899) (@lem3346528 _87123 _34899 s t t' x h1)). Qed.
Lemma lem3346620 (b : Prop) (a : Prop) : (a \/ b) = (term232 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3346621 {_87123 : Type'} (s : type686 _87123) (_34899 : _87123 -> Prop) (x : _87123) : (term229 _87123 x s _34899) = (term233 _87123 s _34899 x).
Proof. exact (@lem3346620 (term189 _87123 s _34899) (@I (_87123 -> Prop) _34899 x)). Qed.
Lemma lem3346623 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3346624 {_87123 : Type'} (s : type686 _87123) (_34899 : _87123 -> Prop) : (term234 _87123 s _34899) = (@I ((_87123 -> Prop) -> Prop) s _34899).
Proof. exact (@lem3346623 (@I ((_87123 -> Prop) -> Prop) s _34899)). Qed.
Lemma lem3346625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3346626 {_87123 : Type'} (s : type686 _87123) (_34899 : _87123 -> Prop) : (term235 _87123 s _34899) = (term236 _87123 s _34899).
Proof. exact (MK_COMB (@lem3346625) (@lem3346624 _87123 s _34899)). Qed.
Lemma lem3346627 {_87123 : Type'} (_34899 : _87123 -> Prop) (x : _87123) : (@I (_87123 -> Prop) _34899 x) = (@I (_87123 -> Prop) _34899 x).
Proof. exact (eq_refl (@I (_87123 -> Prop) _34899 x)). Qed.
Lemma lem3346628 {_87123 : Type'} (s : type686 _87123) (_34899 : _87123 -> Prop) (x : _87123) : (term233 _87123 s _34899 x) = (term237 _87123 s _34899 x).
Proof. exact (MK_COMB (@lem3346626 _87123 s _34899) (@lem3346627 _87123 _34899 x)). Qed.
Lemma lem3346629 {_87123 : Type'} (s : type686 _87123) (_34899 : _87123 -> Prop) (x : _87123) : (term229 _87123 x s _34899) = (term237 _87123 s _34899 x).
Proof. exact (TRANS (@lem3346621 _87123 s _34899 x) (@lem3346628 _87123 s _34899 x)). Qed.
Lemma lem3346632 {_87123 : Type'} (_34899 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term237 _87123 s _34899 x.
Proof. exact (EQ_MP (@lem3346629 _87123 s _34899 x) (@lem3346618 _87123 _34899 s t t' x h1)). Qed.
Lemma lem3346633 {_87123 : Type'} (_34899 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term237 _87123 s _34899 x.
Proof. exact (@lem3346632 _87123 _34899 s t t' x h1). Qed.
Lemma lem3346634 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term237 _87123 s t' x.
Proof. exact (@lem3346633 _87123 t' s t t' x h1). Qed.
Lemma lem3346637 {_87123 : Type'} (t : type686 _87123) (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 s t' x) : @I (_87123 -> Prop) t' x.
Proof. exact (@lem3346634 _87123 s t t' x h1 (@lem3346589 _87123 s t' x h2)). Qed.
Lemma lem3346638 {_87123 : Type'} (t : type686 _87123) (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 s t' x) : term238 _87123 t' x.
Proof. exact (fun h0 : term198 _87123 t' x => @lem3346637 _87123 t s t' x h1 h2). Qed.
Lemma lem3346640 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346641 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term238 _87123 t' x) = (@I (_87123 -> Prop) t' x).
Proof. exact (@lem3346640 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346642 {_87123 : Type'} (t : type686 _87123) (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 s t' x) : @I (_87123 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3346641 _87123 t' x) (@lem3346638 _87123 t s t' x h1 h2)). Qed.
Lemma lem3346645 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3346647 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term198 _87123 t' x) = (term239 _87123 t' x).
Proof. exact (@lem3346645 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346650 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 s t' x) : term239 _87123 t' x.
Proof. exact (EQ_MP (@lem3346647 _87123 t' x) (@lem3346522 _87123 s t' x h1)). Qed.
Lemma lem3346653 {_87123 : Type'} (t : type686 _87123) (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 s t' x) : False.
Proof. exact (@lem3346650 _87123 s t' x h2 (@lem3346642 _87123 t s t' x h1 h2)). Qed.
Lemma lem3346654 {_87123 : Type'} (t : type686 _87123) (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 s t' x) : term240.
Proof. exact (fun h0 : ~ False => @lem3346653 _87123 t s t' x h1 h2). Qed.
Lemma lem3346656 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346657 : term240 = False.
Proof. exact (@lem3346656 False). Qed.
Lemma lem3346658 {_87123 : Type'} (t : type686 _87123) (s : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 s t' x) : False.
Proof. exact (EQ_MP (@lem3346657) (@lem3346654 _87123 t s t' x h1 h2)). Qed.
Lemma lem3346660 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 t t' x) : @I ((_87123 -> Prop) -> Prop) t t'.
Proof. exact (proj1 (@lem3346354 _87123 t t' x h1)). Qed.
Lemma lem3346661 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 t t' x) : term227 _87123 t t'.
Proof. exact (fun h0 : term189 _87123 t t' => @lem3346660 _87123 t t' x h1). Qed.
Lemma lem3346663 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346664 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (term227 _87123 t t') = (@I ((_87123 -> Prop) -> Prop) t t').
Proof. exact (@lem3346663 (@I ((_87123 -> Prop) -> Prop) t t')). Qed.
Lemma lem3346665 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 t t' x) : @I ((_87123 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3346664 _87123 t t') (@lem3346661 _87123 t t' x h1)). Qed.
Lemma lem3346671 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3346672 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : (term192 _87123 t _34900 x) = (term229 _87123 x t _34900).
Proof. exact (@lem3346671 (@I (_87123 -> Prop) _34900 x) (term189 _87123 t _34900)). Qed.
Lemma lem3346678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346679 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : (term230 _87123 t _34900 x) = (term231 _87123 x t _34900).
Proof. exact (MK_COMB (@lem3346678) (@lem3346672 _87123 x t _34900)). Qed.
Lemma lem3346685 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : (term229 _87123 x t _34900) = (term229 _87123 x t _34900).
Proof. exact (eq_refl (term229 _87123 x t _34900)). Qed.
Lemma lem3346686 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : ((term192 _87123 t _34900 x) = (term229 _87123 x t _34900)) = ((term229 _87123 x t _34900) = (term229 _87123 x t _34900)).
Proof. exact (MK_COMB (@lem3346679 _87123 x t _34900) (@lem3346685 _87123 x t _34900)). Qed.
Lemma lem3346688 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3346689 (x : Prop) : (x = x) = True.
Proof. exact (@lem3346688 Prop x). Qed.
Lemma lem3346690 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : ((term229 _87123 x t _34900) = (term229 _87123 x t _34900)) = True.
Proof. exact (@lem3346689 (term229 _87123 x t _34900)). Qed.
Lemma lem3346691 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : ((term192 _87123 t _34900 x) = (term229 _87123 x t _34900)) = True.
Proof. exact (TRANS (@lem3346686 _87123 x t _34900) (@lem3346690 _87123 x t _34900)). Qed.
Lemma lem3346692 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : True = ((term192 _87123 t _34900 x) = (term229 _87123 x t _34900)).
Proof. exact (SYM (@lem3346691 _87123 x t _34900)). Qed.
Lemma lem3346693 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34900 : _87123 -> Prop) : (term192 _87123 t _34900 x) = (term229 _87123 x t _34900).
Proof. exact (EQ_MP (@lem3346692 _87123 x t _34900) (@lem0)). Qed.
Lemma lem3346694 {_87123 : Type'} (_34900 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term229 _87123 x t _34900.
Proof. exact (EQ_MP (@lem3346693 _87123 x t _34900) (@lem3346550 _87123 _34900 s t t' x h1)). Qed.
Lemma lem3346696 (b : Prop) (a : Prop) : (a \/ b) = (term232 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3346697 {_87123 : Type'} (t : type686 _87123) (_34900 : _87123 -> Prop) (x : _87123) : (term229 _87123 x t _34900) = (term233 _87123 t _34900 x).
Proof. exact (@lem3346696 (term189 _87123 t _34900) (@I (_87123 -> Prop) _34900 x)). Qed.
Lemma lem3346699 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3346700 {_87123 : Type'} (t : type686 _87123) (_34900 : _87123 -> Prop) : (term234 _87123 t _34900) = (@I ((_87123 -> Prop) -> Prop) t _34900).
Proof. exact (@lem3346699 (@I ((_87123 -> Prop) -> Prop) t _34900)). Qed.
Lemma lem3346701 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3346702 {_87123 : Type'} (t : type686 _87123) (_34900 : _87123 -> Prop) : (term235 _87123 t _34900) = (term236 _87123 t _34900).
Proof. exact (MK_COMB (@lem3346701) (@lem3346700 _87123 t _34900)). Qed.
Lemma lem3346703 {_87123 : Type'} (_34900 : _87123 -> Prop) (x : _87123) : (@I (_87123 -> Prop) _34900 x) = (@I (_87123 -> Prop) _34900 x).
Proof. exact (eq_refl (@I (_87123 -> Prop) _34900 x)). Qed.
Lemma lem3346704 {_87123 : Type'} (t : type686 _87123) (_34900 : _87123 -> Prop) (x : _87123) : (term233 _87123 t _34900 x) = (term237 _87123 t _34900 x).
Proof. exact (MK_COMB (@lem3346702 _87123 t _34900) (@lem3346703 _87123 _34900 x)). Qed.
Lemma lem3346705 {_87123 : Type'} (t : type686 _87123) (_34900 : _87123 -> Prop) (x : _87123) : (term229 _87123 x t _34900) = (term237 _87123 t _34900 x).
Proof. exact (TRANS (@lem3346697 _87123 t _34900 x) (@lem3346704 _87123 t _34900 x)). Qed.
Lemma lem3346708 {_87123 : Type'} (_34900 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term237 _87123 t _34900 x.
Proof. exact (EQ_MP (@lem3346705 _87123 t _34900 x) (@lem3346694 _87123 _34900 s t t' x h1)). Qed.
Lemma lem3346709 {_87123 : Type'} (_34900 : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term237 _87123 t _34900 x.
Proof. exact (@lem3346708 _87123 _34900 s t t' x h1). Qed.
Lemma lem3346710 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : term237 _87123 t t' x.
Proof. exact (@lem3346709 _87123 t' s t t' x h1). Qed.
Lemma lem3346713 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 t t' x) : @I (_87123 -> Prop) t' x.
Proof. exact (@lem3346710 _87123 s t t' x h1 (@lem3346665 _87123 t t' x h2)). Qed.
Lemma lem3346714 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 t t' x) : term238 _87123 t' x.
Proof. exact (fun h0 : term198 _87123 t' x => @lem3346713 _87123 s t t' x h1 h2). Qed.
Lemma lem3346716 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346717 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term238 _87123 t' x) = (@I (_87123 -> Prop) t' x).
Proof. exact (@lem3346716 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346718 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 t t' x) : @I (_87123 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3346717 _87123 t' x) (@lem3346714 _87123 s t t' x h1 h2)). Qed.
Lemma lem3346721 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3346723 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term198 _87123 t' x) = (term239 _87123 t' x).
Proof. exact (@lem3346721 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346726 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term208 _87123 t t' x) : term239 _87123 t' x.
Proof. exact (EQ_MP (@lem3346723 _87123 t' x) (@lem3346538 _87123 t t' x h1)). Qed.
Lemma lem3346729 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 t t' x) : False.
Proof. exact (@lem3346726 _87123 t t' x h2 (@lem3346718 _87123 s t t' x h1 h2)). Qed.
Lemma lem3346730 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 t t' x) : term240.
Proof. exact (fun h0 : ~ False => @lem3346729 _87123 s t t' x h1 h2). Qed.
Lemma lem3346732 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346733 : term240 = False.
Proof. exact (@lem3346732 False). Qed.
Lemma lem3346734 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) (h2 : term208 _87123 t t' x) : False.
Proof. exact (EQ_MP (@lem3346733) (@lem3346730 _87123 s t t' x h1 h2)). Qed.
Lemma lem3346736 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) s t') : @I ((_87123 -> Prop) -> Prop) s t'.
Proof. exact (h1). Qed.
Lemma lem3346737 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) s t') : term227 _87123 s t'.
Proof. exact (fun h0 : term189 _87123 s t' => @lem3346736 _87123 s t' h1). Qed.
Lemma lem3346739 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346740 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) : (term227 _87123 s t') = (@I ((_87123 -> Prop) -> Prop) s t').
Proof. exact (@lem3346739 (@I ((_87123 -> Prop) -> Prop) s t')). Qed.
Lemma lem3346741 {_87123 : Type'} (s : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) s t') : @I ((_87123 -> Prop) -> Prop) s t'.
Proof. exact (EQ_MP (@lem3346740 _87123 s t') (@lem3346737 _87123 s t' h1)). Qed.
Lemma lem3346747 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3346748 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : (term192 _87123 s _34901 x) = (term229 _87123 x s _34901).
Proof. exact (@lem3346747 (@I (_87123 -> Prop) _34901 x) (term189 _87123 s _34901)). Qed.
Lemma lem3346754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346755 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : (term230 _87123 s _34901 x) = (term231 _87123 x s _34901).
Proof. exact (MK_COMB (@lem3346754) (@lem3346748 _87123 x s _34901)). Qed.
Lemma lem3346761 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : (term229 _87123 x s _34901) = (term229 _87123 x s _34901).
Proof. exact (eq_refl (term229 _87123 x s _34901)). Qed.
Lemma lem3346762 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : ((term192 _87123 s _34901 x) = (term229 _87123 x s _34901)) = ((term229 _87123 x s _34901) = (term229 _87123 x s _34901)).
Proof. exact (MK_COMB (@lem3346755 _87123 x s _34901) (@lem3346761 _87123 x s _34901)). Qed.
Lemma lem3346764 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3346765 (x : Prop) : (x = x) = True.
Proof. exact (@lem3346764 Prop x). Qed.
Lemma lem3346766 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : ((term229 _87123 x s _34901) = (term229 _87123 x s _34901)) = True.
Proof. exact (@lem3346765 (term229 _87123 x s _34901)). Qed.
Lemma lem3346767 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : ((term192 _87123 s _34901 x) = (term229 _87123 x s _34901)) = True.
Proof. exact (TRANS (@lem3346762 _87123 x s _34901) (@lem3346766 _87123 x s _34901)). Qed.
Lemma lem3346768 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : True = ((term192 _87123 s _34901 x) = (term229 _87123 x s _34901)).
Proof. exact (SYM (@lem3346767 _87123 x s _34901)). Qed.
Lemma lem3346769 {_87123 : Type'} (x : _87123) (s : type686 _87123) (_34901 : _87123 -> Prop) : (term192 _87123 s _34901 x) = (term229 _87123 x s _34901).
Proof. exact (EQ_MP (@lem3346768 _87123 x s _34901) (@lem0)). Qed.
Lemma lem3346770 {_87123 : Type'} (_34901 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term229 _87123 x s _34901.
Proof. exact (EQ_MP (@lem3346769 _87123 x s _34901) (@lem3346556 _87123 _34901 t' s t x h1)). Qed.
Lemma lem3346772 (b : Prop) (a : Prop) : (a \/ b) = (term232 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3346773 {_87123 : Type'} (s : type686 _87123) (_34901 : _87123 -> Prop) (x : _87123) : (term229 _87123 x s _34901) = (term233 _87123 s _34901 x).
Proof. exact (@lem3346772 (term189 _87123 s _34901) (@I (_87123 -> Prop) _34901 x)). Qed.
Lemma lem3346775 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3346776 {_87123 : Type'} (s : type686 _87123) (_34901 : _87123 -> Prop) : (term234 _87123 s _34901) = (@I ((_87123 -> Prop) -> Prop) s _34901).
Proof. exact (@lem3346775 (@I ((_87123 -> Prop) -> Prop) s _34901)). Qed.
Lemma lem3346777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3346778 {_87123 : Type'} (s : type686 _87123) (_34901 : _87123 -> Prop) : (term235 _87123 s _34901) = (term236 _87123 s _34901).
Proof. exact (MK_COMB (@lem3346777) (@lem3346776 _87123 s _34901)). Qed.
Lemma lem3346779 {_87123 : Type'} (_34901 : _87123 -> Prop) (x : _87123) : (@I (_87123 -> Prop) _34901 x) = (@I (_87123 -> Prop) _34901 x).
Proof. exact (eq_refl (@I (_87123 -> Prop) _34901 x)). Qed.
Lemma lem3346780 {_87123 : Type'} (s : type686 _87123) (_34901 : _87123 -> Prop) (x : _87123) : (term233 _87123 s _34901 x) = (term237 _87123 s _34901 x).
Proof. exact (MK_COMB (@lem3346778 _87123 s _34901) (@lem3346779 _87123 _34901 x)). Qed.
Lemma lem3346781 {_87123 : Type'} (s : type686 _87123) (_34901 : _87123 -> Prop) (x : _87123) : (term229 _87123 x s _34901) = (term237 _87123 s _34901 x).
Proof. exact (TRANS (@lem3346773 _87123 s _34901 x) (@lem3346780 _87123 s _34901 x)). Qed.
Lemma lem3346784 {_87123 : Type'} (_34901 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term237 _87123 s _34901 x.
Proof. exact (EQ_MP (@lem3346781 _87123 s _34901 x) (@lem3346770 _87123 _34901 t' s t x h1)). Qed.
Lemma lem3346785 {_87123 : Type'} (_34901 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term237 _87123 s _34901 x.
Proof. exact (@lem3346784 _87123 _34901 t' s t x h1). Qed.
Lemma lem3346786 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term237 _87123 s t' x.
Proof. exact (@lem3346785 _87123 t' t' s t x h1). Qed.
Lemma lem3346789 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : @I (_87123 -> Prop) t' x.
Proof. exact (@lem3346786 _87123 t' s t x h1 (@lem3346741 _87123 s t' h2)). Qed.
Lemma lem3346790 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : term238 _87123 t' x.
Proof. exact (fun h0 : term198 _87123 t' x => @lem3346789 _87123 t x s t' h1 h2). Qed.
Lemma lem3346792 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346793 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term238 _87123 t' x) = (@I (_87123 -> Prop) t' x).
Proof. exact (@lem3346792 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346794 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : @I (_87123 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3346793 _87123 t' x) (@lem3346790 _87123 t x s t' h1 h2)). Qed.
Lemma lem3346797 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3346799 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term198 _87123 t' x) = (term239 _87123 t' x).
Proof. exact (@lem3346797 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346802 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term239 _87123 t' x.
Proof. exact (EQ_MP (@lem3346799 _87123 t' x) (@lem3346564 _87123 t' s t x h1)). Qed.
Lemma lem3346805 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : False.
Proof. exact (@lem3346802 _87123 t' s t x h1 (@lem3346794 _87123 t x s t' h1 h2)). Qed.
Lemma lem3346806 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : term240.
Proof. exact (fun h0 : ~ False => @lem3346805 _87123 t x s t' h1 h2). Qed.
Lemma lem3346808 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346809 : term240 = False.
Proof. exact (@lem3346808 False). Qed.
Lemma lem3346810 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3346809) (@lem3346806 _87123 t x s t' h1 h2)). Qed.
Lemma lem3346812 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) t t') : @I ((_87123 -> Prop) -> Prop) t t'.
Proof. exact (h1). Qed.
Lemma lem3346813 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) t t') : term227 _87123 t t'.
Proof. exact (fun h0 : term189 _87123 t t' => @lem3346812 _87123 t t' h1). Qed.
Lemma lem3346815 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346816 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) : (term227 _87123 t t') = (@I ((_87123 -> Prop) -> Prop) t t').
Proof. exact (@lem3346815 (@I ((_87123 -> Prop) -> Prop) t t')). Qed.
Lemma lem3346817 {_87123 : Type'} (t : type686 _87123) (t' : _87123 -> Prop) (h1 : @I ((_87123 -> Prop) -> Prop) t t') : @I ((_87123 -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem3346816 _87123 t t') (@lem3346813 _87123 t t' h1)). Qed.
Lemma lem3346823 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3346824 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : (term192 _87123 t _34904 x) = (term229 _87123 x t _34904).
Proof. exact (@lem3346823 (@I (_87123 -> Prop) _34904 x) (term189 _87123 t _34904)). Qed.
Lemma lem3346830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3346831 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : (term230 _87123 t _34904 x) = (term231 _87123 x t _34904).
Proof. exact (MK_COMB (@lem3346830) (@lem3346824 _87123 x t _34904)). Qed.
Lemma lem3346837 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : (term229 _87123 x t _34904) = (term229 _87123 x t _34904).
Proof. exact (eq_refl (term229 _87123 x t _34904)). Qed.
Lemma lem3346838 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : ((term192 _87123 t _34904 x) = (term229 _87123 x t _34904)) = ((term229 _87123 x t _34904) = (term229 _87123 x t _34904)).
Proof. exact (MK_COMB (@lem3346831 _87123 x t _34904) (@lem3346837 _87123 x t _34904)). Qed.
Lemma lem3346840 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3346841 (x : Prop) : (x = x) = True.
Proof. exact (@lem3346840 Prop x). Qed.
Lemma lem3346842 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : ((term229 _87123 x t _34904) = (term229 _87123 x t _34904)) = True.
Proof. exact (@lem3346841 (term229 _87123 x t _34904)). Qed.
Lemma lem3346843 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : ((term192 _87123 t _34904 x) = (term229 _87123 x t _34904)) = True.
Proof. exact (TRANS (@lem3346838 _87123 x t _34904) (@lem3346842 _87123 x t _34904)). Qed.
Lemma lem3346844 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : True = ((term192 _87123 t _34904 x) = (term229 _87123 x t _34904)).
Proof. exact (SYM (@lem3346843 _87123 x t _34904)). Qed.
Lemma lem3346845 {_87123 : Type'} (x : _87123) (t : type686 _87123) (_34904 : _87123 -> Prop) : (term192 _87123 t _34904 x) = (term229 _87123 x t _34904).
Proof. exact (EQ_MP (@lem3346844 _87123 x t _34904) (@lem0)). Qed.
Lemma lem3346846 {_87123 : Type'} (_34904 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term229 _87123 x t _34904.
Proof. exact (EQ_MP (@lem3346845 _87123 x t _34904) (@lem3346578 _87123 _34904 t' s t x h1)). Qed.
Lemma lem3346848 (b : Prop) (a : Prop) : (a \/ b) = (term232 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3346849 {_87123 : Type'} (t : type686 _87123) (_34904 : _87123 -> Prop) (x : _87123) : (term229 _87123 x t _34904) = (term233 _87123 t _34904 x).
Proof. exact (@lem3346848 (term189 _87123 t _34904) (@I (_87123 -> Prop) _34904 x)). Qed.
Lemma lem3346851 (a : Prop) : (term60 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3346852 {_87123 : Type'} (t : type686 _87123) (_34904 : _87123 -> Prop) : (term234 _87123 t _34904) = (@I ((_87123 -> Prop) -> Prop) t _34904).
Proof. exact (@lem3346851 (@I ((_87123 -> Prop) -> Prop) t _34904)). Qed.
Lemma lem3346853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3346854 {_87123 : Type'} (t : type686 _87123) (_34904 : _87123 -> Prop) : (term235 _87123 t _34904) = (term236 _87123 t _34904).
Proof. exact (MK_COMB (@lem3346853) (@lem3346852 _87123 t _34904)). Qed.
Lemma lem3346855 {_87123 : Type'} (_34904 : _87123 -> Prop) (x : _87123) : (@I (_87123 -> Prop) _34904 x) = (@I (_87123 -> Prop) _34904 x).
Proof. exact (eq_refl (@I (_87123 -> Prop) _34904 x)). Qed.
Lemma lem3346856 {_87123 : Type'} (t : type686 _87123) (_34904 : _87123 -> Prop) (x : _87123) : (term233 _87123 t _34904 x) = (term237 _87123 t _34904 x).
Proof. exact (MK_COMB (@lem3346854 _87123 t _34904) (@lem3346855 _87123 _34904 x)). Qed.
Lemma lem3346857 {_87123 : Type'} (t : type686 _87123) (_34904 : _87123 -> Prop) (x : _87123) : (term229 _87123 x t _34904) = (term237 _87123 t _34904 x).
Proof. exact (TRANS (@lem3346849 _87123 t _34904 x) (@lem3346856 _87123 t _34904 x)). Qed.
Lemma lem3346860 {_87123 : Type'} (_34904 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term237 _87123 t _34904 x.
Proof. exact (EQ_MP (@lem3346857 _87123 t _34904 x) (@lem3346846 _87123 _34904 t' s t x h1)). Qed.
Lemma lem3346861 {_87123 : Type'} (_34904 : _87123 -> Prop) (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term237 _87123 t _34904 x.
Proof. exact (@lem3346860 _87123 _34904 t' s t x h1). Qed.
Lemma lem3346862 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term237 _87123 t t' x.
Proof. exact (@lem3346861 _87123 t' t' s t x h1). Qed.
Lemma lem3346865 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : @I (_87123 -> Prop) t' x.
Proof. exact (@lem3346862 _87123 t' s t x h1 (@lem3346817 _87123 t t' h2)). Qed.
Lemma lem3346866 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : term238 _87123 t' x.
Proof. exact (fun h0 : term198 _87123 t' x => @lem3346865 _87123 s x t t' h1 h2). Qed.
Lemma lem3346868 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346869 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term238 _87123 t' x) = (@I (_87123 -> Prop) t' x).
Proof. exact (@lem3346868 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346870 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : @I (_87123 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3346869 _87123 t' x) (@lem3346866 _87123 s x t t' h1 h2)). Qed.
Lemma lem3346873 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3346875 {_87123 : Type'} (t' : _87123 -> Prop) (x : _87123) : (term198 _87123 t' x) = (term239 _87123 t' x).
Proof. exact (@lem3346873 (@I (_87123 -> Prop) t' x)). Qed.
Lemma lem3346878 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : term239 _87123 t' x.
Proof. exact (EQ_MP (@lem3346875 _87123 t' x) (@lem3346580 _87123 t' s t x h1)). Qed.
Lemma lem3346881 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : False.
Proof. exact (@lem3346878 _87123 t' s t x h1 (@lem3346870 _87123 s x t t' h1 h2)). Qed.
Lemma lem3346882 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : term240.
Proof. exact (fun h0 : ~ False => @lem3346881 _87123 s x t t' h1 h2). Qed.
Lemma lem3346884 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3346885 : term240 = False.
Proof. exact (@lem3346884 False). Qed.
Lemma lem3346886 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3346885) (@lem3346882 _87123 s x t t' h1 h2)). Qed.
Lemma lem3346887 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : (@I ((_87123 -> Prop) -> Prop) t t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87123 -> Prop) -> Prop) t t' => @lem3346886 _87123 s x t t' h1 h2) (fun h3 : False => @lem3346582 _87123 t t' h2)). Qed.
Lemma lem3346888 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3346887 _87123 s x t t' h1 h2) (@lem3346582 _87123 t t' h2)). Qed.
Lemma lem3346889 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : (@I ((_87123 -> Prop) -> Prop) s t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87123 -> Prop) -> Prop) s t' => @lem3346810 _87123 t x s t' h1 h2) (fun h3 : False => @lem3346566 _87123 s t' h2)). Qed.
Lemma lem3346890 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3346889 _87123 t x s t' h1 h2) (@lem3346566 _87123 s t' h2)). Qed.
Lemma lem3346891 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : (@I ((_87123 -> Prop) -> Prop) t t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87123 -> Prop) -> Prop) t t' => @lem3346888 _87123 s x t t' h1 h2) (fun h3 : False => @lem3346496 _87123 t t' h2)). Qed.
Lemma lem3346892 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3346891 _87123 s x t t' h1 h2) (@lem3346496 _87123 t t' h2)). Qed.
Lemma lem3346893 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : (@I ((_87123 -> Prop) -> Prop) s t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87123 -> Prop) -> Prop) s t' => @lem3346890 _87123 t x s t' h1 h2) (fun h3 : False => @lem3346462 _87123 s t' h2)). Qed.
Lemma lem3346894 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3346893 _87123 t x s t' h1 h2) (@lem3346462 _87123 s t' h2)). Qed.
Lemma lem3346895 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : (@I ((_87123 -> Prop) -> Prop) t t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87123 -> Prop) -> Prop) t t' => @lem3346892 _87123 s x t t' h1 h2) (fun h3 : False => @lem3346496 _87123 t t' h2)). Qed.
Lemma lem3346896 {_87123 : Type'} (s : type686 _87123) (x : _87123) (t : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) t t') : False.
Proof. exact (EQ_MP (@lem3346895 _87123 s x t t' h1 h2) (@lem3346496 _87123 t t' h2)). Qed.
Lemma lem3346897 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : (@I ((_87123 -> Prop) -> Prop) s t') = False.
Proof. exact (prop_ext (fun h3 : @I ((_87123 -> Prop) -> Prop) s t' => @lem3346894 _87123 t x s t' h1 h2) (fun h3 : False => @lem3346462 _87123 s t' h2)). Qed.
Lemma lem3346898 {_87123 : Type'} (t : type686 _87123) (x : _87123) (s : type686 _87123) (t' : _87123 -> Prop) (h1 : term205 _87123 t' s t x) (h2 : @I ((_87123 -> Prop) -> Prop) s t') : False.
Proof. exact (EQ_MP (@lem3346897 _87123 t x s t' h1 h2) (@lem3346462 _87123 s t' h2)). Qed.
Lemma lem3346899 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term205 _87123 t' s t x) : False.
Proof. exact (or_elim (@lem3346364 _87123 t' s t x h1) (fun h0 : @I ((_87123 -> Prop) -> Prop) s t' => @lem3346898 _87123 t x s t' h1 h0) (fun h0 : @I ((_87123 -> Prop) -> Prop) t t' => @lem3346896 _87123 s x t t' h1 h0)). Qed.
Lemma lem3346900 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (t' : _87123 -> Prop) (x : _87123) (h1 : term219 _87123 s t t' x) : False.
Proof. exact (or_elim (@lem3346351 _87123 s t t' x h1) (fun h0 : term208 _87123 s t' x => @lem3346658 _87123 t s t' x h1 h0) (fun h0 : term208 _87123 t t' x => @lem3346734 _87123 s t t' x h1 h0)). Qed.
Lemma lem3346901 {_87123 : Type'} (t' : _87123 -> Prop) (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term184 _87123 t' s t x) : False.
Proof. exact (or_elim (@lem3346348 _87123 t' s t x h1) (fun h0 : term219 _87123 s t t' x => @lem3346900 _87123 s t t' x h0) (fun h0 : term205 _87123 t' s t x => @lem3346899 _87123 t' s t x h0)). Qed.
Lemma lem3346902 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term62 _87123 s t x) : False.
Proof. exact (ex_elim (@lem3346172 _87123 s t x h1) (fun t' : _87123 -> Prop => fun h0 : term186 _87123 s t x t' => @lem3346901 _87123 t' s t x h0)). Qed.
Lemma lem3346903 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term62 _87123 s t x) : (term62 _87123 s t x) = False.
Proof. exact (prop_ext (fun h2 : term62 _87123 s t x => @lem3346902 _87123 s t x h1) (fun h2 : False => @lem3345705 _87123 s t x h1)). Qed.
Lemma lem3346904 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) (h1 : term62 _87123 s t x) : False.
Proof. exact (EQ_MP (@lem3346903 _87123 s t x h1) (@lem3345705 _87123 s t x h1)). Qed.
Lemma lem3346905 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : term61 _87123 s t x.
Proof. exact (fun h0 : term62 _87123 s t x => @lem3346904 _87123 s t x h0). Qed.
Lemma lem3346906 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) (x : _87123) : (term29 _87123 s t x) = (term45 _87123 s t x).
Proof. exact (EQ_MP (@lem3345704 _87123 s t x) (@lem3346905 _87123 s t x)). Qed.
Lemma lem3346911 {_87123 : Type'} (s : type686 _87123) (t : type686 _87123) : term48 _87123 s t.
Proof. exact (fun x : _87123 => @lem3346906 _87123 s t x). Qed.
Lemma lem3346916 {_87123 : Type'} (s : type686 _87123) : term50 _87123 s.
Proof. exact (fun t : type686 _87123 => @lem3346911 _87123 s t). Qed.
Lemma lem3346921 {_87123 : Type'} : term52 _87123.
Proof. exact (fun s : type686 _87123 => @lem3346916 _87123 s). Qed.
Lemma lem3346922 {_87123 : Type'} : term54 _87123.
Proof. exact (EQ_MP (@lem3345700 _87123) (@lem3346921 _87123)). Qed.
Lemma lem3346924 {_87123 : Type'} : term54 _87123.
Proof. exact (@lem3345562 _87123 (@lem3346922 _87123)). Qed.
Lemma lem3346925 {_87123 : Type'} (h1 : term55 _87123) : False.
Proof. exact (@lem3346924 _87123 (@lem3345546 _87123 h1)). Qed.
Lemma lem3346926 {_87123 : Type'} (h1 : term55 _87123) : (term55 _87123) = False.
Proof. exact (prop_ext (fun h2 : term55 _87123 => @lem3346925 _87123 h1) (fun h2 : False => @lem3345546 _87123 h1)). Qed.
Lemma lem3346927 {_87123 : Type'} (h1 : term55 _87123) : False.
Proof. exact (EQ_MP (@lem3346926 _87123 h1) (@lem3345546 _87123 h1)). Qed.
Lemma lem3346928 {_87123 : Type'} : term54 _87123.
Proof. exact (fun h0 : term55 _87123 => @lem3346927 _87123 h0). Qed.
Lemma lem3346929 {_87123 : Type'} : term52 _87123.
Proof. exact (EQ_MP (@lem3345545 _87123) (@lem3346928 _87123)). Qed.
Lemma lem3346930 {_87123 : Type'} : term11 _87123.
Proof. exact (EQ_MP (@lem3345541 _87123) (@lem3346929 _87123)). Qed.
Lemma lem3346931 {_87123 : Type'} : term10 _87123.
Proof. exact (EQ_MP (@lem3345380 _87123) (@lem3346930 _87123)). Qed.
