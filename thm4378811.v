Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4378811_term_abbrevs.
Require Import DISJ_ACI_spec.
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
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
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
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4372346_spec.
Lemma lem4377374 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4377375 {_104961 : Type'} (s : type686 _104961) (t : type686 _104961) : (s = t) = (term1 _104961 s t).
Proof. exact (@lem4377374 (_104961 -> Prop) s t). Qed.
Lemma lem4377376 {_104961 : Type'} (f : type686 _104961) : (f = (@EMPTY (_104961 -> Prop))) = (term2 _104961 f).
Proof. exact (@lem4377375 _104961 f (@EMPTY (_104961 -> Prop))). Qed.
Lemma lem4377385 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4377386 {_104961 : Type'} (f : type686 _104961) : (term3 _104961 f) = (term4 _104961 f).
Proof. exact (MK_COMB (@lem4377385) (@lem4377376 _104961 f)). Qed.
Lemma lem4377387 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377388 {_104961 : Type'} (f : type686 _104961) : (term5 _104961 f) = (term6 _104961 f).
Proof. exact (MK_COMB (@lem4377387) (@lem4377386 _104961 f)). Qed.
Lemma lem4377411 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term7 _104960 _104961 f s) = (term7 _104960 _104961 f s).
Proof. exact (eq_refl (term7 _104960 _104961 f s)). Qed.
Lemma lem4377412 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term8 _104960 _104961 f s) = (term9 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4377388 _104961 f) (@lem4377411 _104960 _104961 f s)). Qed.
Lemma lem4377415 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term9 _104960 _104961 f s) = (term8 _104960 _104961 f s).
Proof. exact (SYM (@lem4377412 _104960 _104961 f s)). Qed.
Lemma lem4377425 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377426 {_104961 : Type'} (P : type686 _104961) (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x P) = (P x).
Proof. exact (@lem4377425 (_104961 -> Prop) P x). Qed.
Lemma lem4377427 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x f) = (f x).
Proof. exact (@lem4377426 _104961 f x). Qed.
Lemma lem4377428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4377429 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term10 _104961 x f) = (term11 _104961 f x).
Proof. exact (MK_COMB (@lem4377428) (@lem4377427 _104961 f x)). Qed.
Lemma lem4377431 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4377432 {_104961 : Type'} (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x (@EMPTY (_104961 -> Prop))) = False.
Proof. exact (@lem4377431 (_104961 -> Prop) x). Qed.
Lemma lem4377433 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : ((@IN (_104961 -> Prop) x f) = (@IN (_104961 -> Prop) x (@EMPTY (_104961 -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem4377429 _104961 f x) (@lem4377432 _104961 x)). Qed.
Lemma lem4377435 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4377436 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : ((f x) = False) = (term12 _104961 f x).
Proof. exact (@lem4377435 (f x)). Qed.
Lemma lem4377437 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : ((@IN (_104961 -> Prop) x f) = (@IN (_104961 -> Prop) x (@EMPTY (_104961 -> Prop)))) = (term12 _104961 f x).
Proof. exact (TRANS (@lem4377433 _104961 f x) (@lem4377436 _104961 f x)). Qed.
Lemma lem4377438 {_104961 : Type'} (f : type686 _104961) : (term13 _104961 f) = (term14 _104961 f).
Proof. exact (fun_ext (fun x : _104961 -> Prop => @lem4377437 _104961 f x)). Qed.
Lemma lem4377439 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377440 {_104961 : Type'} (f : type686 _104961) : (term2 _104961 f) = (term15 _104961 f).
Proof. exact (MK_COMB (@lem4377439 _104961) (@lem4377438 _104961 f)). Qed.
Lemma lem4377445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4377446 {_104961 : Type'} (f : type686 _104961) : (term4 _104961 f) = (term16 _104961 f).
Proof. exact (MK_COMB (@lem4377445) (@lem4377440 _104961 f)). Qed.
Lemma lem4377447 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377448 {_104961 : Type'} (f : type686 _104961) : (term6 _104961 f) = (term17 _104961 f).
Proof. exact (MK_COMB (@lem4377447) (@lem4377446 _104961 f)). Qed.
Lemma lem4377462 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377463 {_104960 : Type'} (P : _104960 -> Prop) (x : _104960) : (@IN _104960 x P) = (P x).
Proof. exact (@lem4377462 _104960 P x). Qed.
Lemma lem4377464 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (@IN _104960 p1 s) = (s p1).
Proof. exact (@lem4377463 _104960 s p1). Qed.
Lemma lem4377465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4377466 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term18 _104960 p1 s) = (term19 _104960 s p1).
Proof. exact (MK_COMB (@lem4377465) (@lem4377464 _104960 s p1)). Qed.
Lemma lem4377468 {A : Type'} (s : type686 A) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4377469 {_104961 : Type'} (s : type686 _104961) (x : _104961) : (term20 _104961 x s) = (term21 _104961 s x).
Proof. exact (@lem4377468 _104961 s x). Qed.
Lemma lem4377470 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term20 _104961 p2 f) = (term21 _104961 f p2).
Proof. exact (@lem4377469 _104961 f p2). Qed.
Lemma lem4377478 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377479 {_104961 : Type'} (P : type686 _104961) (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x P) = (P x).
Proof. exact (@lem4377478 (_104961 -> Prop) P x). Qed.
Lemma lem4377480 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (@IN (_104961 -> Prop) t f) = (f t).
Proof. exact (@lem4377479 _104961 f t). Qed.
Lemma lem4377481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377482 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term22 _104961 t f) = (term23 _104961 f t).
Proof. exact (MK_COMB (@lem4377481) (@lem4377480 _104961 f t)). Qed.
Lemma lem4377484 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377485 {_104961 : Type'} (P : _104961 -> Prop) (x : _104961) : (@IN _104961 x P) = (P x).
Proof. exact (@lem4377484 _104961 P x). Qed.
Lemma lem4377486 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (@IN _104961 p2 t) = (t p2).
Proof. exact (@lem4377485 _104961 t p2). Qed.
Lemma lem4377487 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term24 _104961 f p2 t) = (term25 _104961 f t p2).
Proof. exact (MK_COMB (@lem4377482 _104961 f t) (@lem4377486 _104961 t p2)). Qed.
Lemma lem4377490 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term26 _104961 f p2) = (term27 _104961 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377487 _104961 f t p2)). Qed.
Lemma lem4377491 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377492 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term21 _104961 f p2) = (term28 _104961 f p2).
Proof. exact (MK_COMB (@lem4377491 _104961) (@lem4377490 _104961 f p2)). Qed.
Lemma lem4377497 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term20 _104961 p2 f) = (term28 _104961 f p2).
Proof. exact (TRANS (@lem4377470 _104961 f p2) (@lem4377492 _104961 f p2)). Qed.
Lemma lem4377498 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term29 _104960 _104961 p1 s p2 f) = (term30 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377466 _104960 s p1) (@lem4377497 _104961 f p2)). Qed.
Lemma lem4377501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4377502 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term31 _104960 _104961 p1 s p2 f) = (term32 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377501) (@lem4377498 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4377510 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377511 {_104961 : Type'} (P : type686 _104961) (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x P) = (P x).
Proof. exact (@lem4377510 (_104961 -> Prop) P x). Qed.
Lemma lem4377512 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (@IN (_104961 -> Prop) t f) = (f t).
Proof. exact (@lem4377511 _104961 f t). Qed.
Lemma lem4377513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377514 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term22 _104961 t f) = (term23 _104961 f t).
Proof. exact (MK_COMB (@lem4377513) (@lem4377512 _104961 f t)). Qed.
Lemma lem4377518 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377519 {_104960 : Type'} (P : _104960 -> Prop) (x : _104960) : (@IN _104960 x P) = (P x).
Proof. exact (@lem4377518 _104960 P x). Qed.
Lemma lem4377520 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (@IN _104960 p1 s) = (s p1).
Proof. exact (@lem4377519 _104960 s p1). Qed.
Lemma lem4377521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4377522 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term18 _104960 p1 s) = (term19 _104960 s p1).
Proof. exact (MK_COMB (@lem4377521) (@lem4377520 _104960 s p1)). Qed.
Lemma lem4377524 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377525 {_104961 : Type'} (P : _104961 -> Prop) (x : _104961) : (@IN _104961 x P) = (P x).
Proof. exact (@lem4377524 _104961 P x). Qed.
Lemma lem4377526 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (@IN _104961 p2 t) = (t p2).
Proof. exact (@lem4377525 _104961 t p2). Qed.
Lemma lem4377527 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term33 _104960 _104961 p1 s p2 t) = (term34 _104960 _104961 s p1 t p2).
Proof. exact (MK_COMB (@lem4377522 _104960 s p1) (@lem4377526 _104961 t p2)). Qed.
Lemma lem4377530 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term35 _104960 _104961 f p1 s p2 t) = (term36 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4377514 _104961 f t) (@lem4377527 _104960 _104961 s p1 t p2)). Qed.
Lemma lem4377533 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term37 _104960 _104961 f p1 s p2) = (term38 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377530 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377534 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377535 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term39 _104960 _104961 f p1 s p2) = (term40 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377534 _104961) (@lem4377533 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377540 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : ((term29 _104960 _104961 p1 s p2 f) = (term39 _104960 _104961 f p1 s p2)) = ((term30 _104960 _104961 s p1 f p2) = (term40 _104960 _104961 f s p1 p2)).
Proof. exact (MK_COMB (@lem4377502 _104960 _104961 s p1 f p2) (@lem4377535 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377543 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) : (term41 _104960 _104961 f p1 s) = (term42 _104960 _104961 f s p1).
Proof. exact (fun_ext (fun p2 : _104961 => @lem4377540 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377544 {_104961 : Type'} : (@all _104961) = (@all _104961).
Proof. exact (eq_refl (@all _104961)). Qed.
Lemma lem4377545 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) : (term43 _104960 _104961 f p1 s) = (term44 _104960 _104961 f s p1).
Proof. exact (MK_COMB (@lem4377544 _104961) (@lem4377543 _104960 _104961 f s p1)). Qed.
Lemma lem4377550 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term45 _104960 _104961 f s) = (term46 _104960 _104961 f s).
Proof. exact (fun_ext (fun p1 : _104960 => @lem4377545 _104960 _104961 f s p1)). Qed.
Lemma lem4377551 {_104960 : Type'} : (@all _104960) = (@all _104960).
Proof. exact (eq_refl (@all _104960)). Qed.
Lemma lem4377552 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term7 _104960 _104961 f s) = (term47 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4377551 _104960) (@lem4377550 _104960 _104961 f s)). Qed.
Lemma lem4377557 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term9 _104960 _104961 f s) = (term48 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4377448 _104961 f) (@lem4377552 _104960 _104961 f s)). Qed.
Lemma lem4377560 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term48 _104960 _104961 f s) = (term9 _104960 _104961 f s).
Proof. exact (SYM (@lem4377557 _104960 _104961 f s)). Qed.
Lemma lem4377562 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4377563 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term48 _104960 _104961 f s) = (term50 _104960 _104961 f s).
Proof. exact (@lem4377562 (term48 _104960 _104961 f s)). Qed.
Lemma lem4377564 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term50 _104960 _104961 f s) = (term48 _104960 _104961 f s).
Proof. exact (SYM (@lem4377563 _104960 _104961 f s)). Qed.
Lemma lem4377565 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term51 _104960 _104961 f s) : term51 _104960 _104961 f s.
Proof. exact (h1). Qed.
Lemma lem4377568 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term50 _104960 _104961 f s) : term50 _104960 _104961 f s.
Proof. exact (h1). Qed.
Lemma lem4377569 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term52 _104960 _104961 f s.
Proof. exact (fun h0 : term50 _104960 _104961 f s => @lem4377568 _104960 _104961 f s h0). Qed.
Lemma lem4377570 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term52 _104960 _104961 f s) : term52 _104960 _104961 f s.
Proof. exact (h1). Qed.
Lemma lem4377571 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term50 _104960 _104961 f s) : term50 _104960 _104961 f s.
Proof. exact (h1). Qed.
Lemma lem4377572 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term50 _104960 _104961 f s) (h2 : term52 _104960 _104961 f s) : term50 _104960 _104961 f s.
Proof. exact (@lem4377570 _104960 _104961 f s h2 (@lem4377571 _104960 _104961 f s h1)). Qed.
Lemma lem4377573 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term50 _104960 _104961 f s) : term53 _104960 _104961 f s.
Proof. exact (fun h0 : term52 _104960 _104961 f s => @lem4377572 _104960 _104961 f s h1 h0). Qed.
Lemma lem4377574 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term52 _104960 _104961 f s) : term52 _104960 _104961 f s.
Proof. exact (h1). Qed.
Lemma lem4377575 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term50 _104960 _104961 f s) (h2 : term52 _104960 _104961 f s) : term50 _104960 _104961 f s.
Proof. exact (@lem4377573 _104960 _104961 f s h1 (@lem4377574 _104960 _104961 f s h2)). Qed.
Lemma lem4377576 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term52 _104960 _104961 f s) : term52 _104960 _104961 f s.
Proof. exact (fun h0 : term50 _104960 _104961 f s => @lem4377575 _104960 _104961 f s h0 h1). Qed.
Lemma lem4377577 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term54 _104960 _104961 f s.
Proof. exact (fun h0 : term52 _104960 _104961 f s => @lem4377576 _104960 _104961 f s h0). Qed.
Lemma lem4377580 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term52 _104960 _104961 f s.
Proof. exact (@lem4377577 _104960 _104961 f s (@lem4377569 _104960 _104961 f s)). Qed.
Lemma lem4377581 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term52 _104960 _104961 f s.
Proof. exact (@lem4377580 _104960 _104961 f s). Qed.
Lemma lem4377591 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4377592 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term50 _104960 _104961 f s) = (term55 _104960 _104961 f s).
Proof. exact (@lem4377591 (term51 _104960 _104961 f s)). Qed.
Lemma lem4377594 (t : Prop) : (term56 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4377595 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term55 _104960 _104961 f s) = (term48 _104960 _104961 f s).
Proof. exact (@lem4377594 (term48 _104960 _104961 f s)). Qed.
Lemma lem4377598 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term50 _104960 _104961 f s) = (term48 _104960 _104961 f s).
Proof. exact (TRANS (@lem4377592 _104960 _104961 f s) (@lem4377595 _104960 _104961 f s)). Qed.
Lemma lem4377627 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term57 _104960 _104961 s) = (term58 _104960 _104961 s).
Proof. exact (fun_ext (fun f : type686 _104961 => @lem4377598 _104960 _104961 f s)). Qed.
Lemma lem4377628 {_104961 : Type'} : (@all ((_104961 -> Prop) -> Prop)) = (@all ((_104961 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104961 -> Prop) -> Prop))). Qed.
Lemma lem4377629 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term59 _104960 _104961 s) = (term60 _104960 _104961 s).
Proof. exact (MK_COMB (@lem4377628 _104961) (@lem4377627 _104960 _104961 s)). Qed.
Lemma lem4377634 {_104960 _104961 : Type'} : (term61 _104960 _104961) = (term62 _104960 _104961).
Proof. exact (fun_ext (fun s : _104960 -> Prop => @lem4377629 _104960 _104961 s)). Qed.
Lemma lem4377635 {_104960 : Type'} : (@all (_104960 -> Prop)) = (@all (_104960 -> Prop)).
Proof. exact (eq_refl (@all (_104960 -> Prop))). Qed.
Lemma lem4377644 {_104960 _104961 : Type'} : (term63 _104960 _104961) = (term64 _104960 _104961).
Proof. exact (MK_COMB (@lem4377635 _104960) (@lem4377634 _104960 _104961)). Qed.
Lemma lem4377653 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term36 _104960 _104961 f s p1 t p2) = (term36 _104960 _104961 f s p1 t p2).
Proof. exact (eq_refl (term36 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377654 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term38 _104960 _104961 f s p1 p2) = (term38 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377653 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377655 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377656 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term40 _104960 _104961 f s p1 p2) = (term40 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377655 _104961) (@lem4377654 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377661 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term25 _104961 f t p2) = (term25 _104961 f t p2).
Proof. exact (eq_refl (term25 _104961 f t p2)). Qed.
Lemma lem4377662 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term27 _104961 f p2) = (term27 _104961 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377661 _104961 f t p2)). Qed.
Lemma lem4377663 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377664 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term28 _104961 f p2) = (term28 _104961 f p2).
Proof. exact (MK_COMB (@lem4377663 _104961) (@lem4377662 _104961 f p2)). Qed.
Lemma lem4377667 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term19 _104960 s p1) = (term19 _104960 s p1).
Proof. exact (eq_refl (term19 _104960 s p1)). Qed.
Lemma lem4377668 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term30 _104960 _104961 s p1 f p2) = (term30 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377667 _104960 s p1) (@lem4377664 _104961 f p2)). Qed.
Lemma lem4377669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4377670 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term32 _104960 _104961 s p1 f p2) = (term32 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377669) (@lem4377668 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4377671 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : ((term30 _104960 _104961 s p1 f p2) = (term40 _104960 _104961 f s p1 p2)) = ((term30 _104960 _104961 s p1 f p2) = (term40 _104960 _104961 f s p1 p2)).
Proof. exact (MK_COMB (@lem4377670 _104960 _104961 s p1 f p2) (@lem4377656 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377672 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) : (term42 _104960 _104961 f s p1) = (term42 _104960 _104961 f s p1).
Proof. exact (fun_ext (fun p2 : _104961 => @lem4377671 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377673 {_104961 : Type'} : (@all _104961) = (@all _104961).
Proof. exact (eq_refl (@all _104961)). Qed.
Lemma lem4377674 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) : (term44 _104960 _104961 f s p1) = (term44 _104960 _104961 f s p1).
Proof. exact (MK_COMB (@lem4377673 _104961) (@lem4377672 _104960 _104961 f s p1)). Qed.
Lemma lem4377675 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term46 _104960 _104961 f s) = (term46 _104960 _104961 f s).
Proof. exact (fun_ext (fun p1 : _104960 => @lem4377674 _104960 _104961 f s p1)). Qed.
Lemma lem4377676 {_104960 : Type'} : (@all _104960) = (@all _104960).
Proof. exact (eq_refl (@all _104960)). Qed.
Lemma lem4377677 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term47 _104960 _104961 f s) = (term47 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4377676 _104960) (@lem4377675 _104960 _104961 f s)). Qed.
Lemma lem4377680 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term12 _104961 f x) = (term12 _104961 f x).
Proof. exact (eq_refl (term12 _104961 f x)). Qed.
Lemma lem4377681 {_104961 : Type'} (f : type686 _104961) : (term14 _104961 f) = (term14 _104961 f).
Proof. exact (fun_ext (fun x : _104961 -> Prop => @lem4377680 _104961 f x)). Qed.
Lemma lem4377682 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377683 {_104961 : Type'} (f : type686 _104961) : (term15 _104961 f) = (term15 _104961 f).
Proof. exact (MK_COMB (@lem4377682 _104961) (@lem4377681 _104961 f)). Qed.
Lemma lem4377684 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4377685 {_104961 : Type'} (f : type686 _104961) : (term16 _104961 f) = (term16 _104961 f).
Proof. exact (MK_COMB (@lem4377684) (@lem4377683 _104961 f)). Qed.
Lemma lem4377686 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377687 {_104961 : Type'} (f : type686 _104961) : (term17 _104961 f) = (term17 _104961 f).
Proof. exact (MK_COMB (@lem4377686) (@lem4377685 _104961 f)). Qed.
Lemma lem4377688 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term48 _104960 _104961 f s) = (term48 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4377687 _104961 f) (@lem4377677 _104960 _104961 f s)). Qed.
Lemma lem4377689 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term58 _104960 _104961 s) = (term58 _104960 _104961 s).
Proof. exact (fun_ext (fun f : type686 _104961 => @lem4377688 _104960 _104961 f s)). Qed.
Lemma lem4377690 {_104961 : Type'} : (@all ((_104961 -> Prop) -> Prop)) = (@all ((_104961 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104961 -> Prop) -> Prop))). Qed.
Lemma lem4377691 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term60 _104960 _104961 s) = (term60 _104960 _104961 s).
Proof. exact (MK_COMB (@lem4377690 _104961) (@lem4377689 _104960 _104961 s)). Qed.
Lemma lem4377692 {_104960 _104961 : Type'} : (term62 _104960 _104961) = (term62 _104960 _104961).
Proof. exact (fun_ext (fun s : _104960 -> Prop => @lem4377691 _104960 _104961 s)). Qed.
Lemma lem4377693 {_104960 : Type'} : (@all (_104960 -> Prop)) = (@all (_104960 -> Prop)).
Proof. exact (eq_refl (@all (_104960 -> Prop))). Qed.
Lemma lem4377694 {_104960 _104961 : Type'} : (term64 _104960 _104961) = (term64 _104960 _104961).
Proof. exact (MK_COMB (@lem4377693 _104960) (@lem4377692 _104960 _104961)). Qed.
Lemma lem4377749 {_104960 _104961 : Type'} : (term63 _104960 _104961) = (term64 _104960 _104961).
Proof. exact (TRANS (@lem4377644 _104960 _104961) (@lem4377694 _104960 _104961)). Qed.
Lemma lem4377750 {_104960 _104961 : Type'} : (term64 _104960 _104961) = (term63 _104960 _104961).
Proof. exact (SYM (@lem4377749 _104960 _104961)). Qed.
Lemma lem4377751 {_104961 : Type'} (f : type686 _104961) (h1 : term16 _104961 f) : term16 _104961 f.
Proof. exact (h1). Qed.
Lemma lem4377753 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4377754 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : ((term30 _104960 _104961 s p1 f p2) = (term40 _104960 _104961 f s p1 p2)) = (term65 _104960 _104961 f s p1 p2).
Proof. exact (@lem4377753 ((term30 _104960 _104961 s p1 f p2) = (term40 _104960 _104961 f s p1 p2))). Qed.
Lemma lem4377755 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term65 _104960 _104961 f s p1 p2) = ((term30 _104960 _104961 s p1 f p2) = (term40 _104960 _104961 f s p1 p2)).
Proof. exact (SYM (@lem4377754 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377756 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term66 _104960 _104961 f s p1 p2) : term66 _104960 _104961 f s p1 p2.
Proof. exact (h1). Qed.
Lemma lem4377759 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term67 _104961 f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem4377760 {_104961 : Type'} (P : type686 _104961) : (term68 _104961 P) = (term69 _104961 P).
Proof. exact (@lem18392 (_104961 -> Prop) P). Qed.
Lemma lem4377761 {_104961 : Type'} (f : type686 _104961) : (term16 _104961 f) = (term70 _104961 f).
Proof. exact (@lem4377760 _104961 (term14 _104961 f)). Qed.
Lemma lem4377762 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term71 _104961 f x) = (term12 _104961 f x).
Proof. exact (eq_refl (term71 _104961 f x)). Qed.
Lemma lem4377763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4377764 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term72 _104961 f x) = (term67 _104961 f x).
Proof. exact (MK_COMB (@lem4377763) (@lem4377762 _104961 f x)). Qed.
Lemma lem4377765 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term72 _104961 f x) = (f x).
Proof. exact (TRANS (@lem4377764 _104961 f x) (@lem4377759 _104961 f x)). Qed.
Lemma lem4377766 {_104961 : Type'} (f : type686 _104961) : (term73 _104961 f) = (term74 _104961 f).
Proof. exact (fun_ext (fun x : _104961 -> Prop => @lem4377765 _104961 f x)). Qed.
Lemma lem4377767 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4377768 {_104961 : Type'} (f : type686 _104961) : (term70 _104961 f) = (term75 _104961 f).
Proof. exact (MK_COMB (@lem4377767 _104961) (@lem4377766 _104961 f)). Qed.
Lemma lem4377777 {_104961 : Type'} (f : type686 _104961) : (term16 _104961 f) = (term75 _104961 f).
Proof. exact (TRANS (@lem4377761 _104961 f) (@lem4377768 _104961 f)). Qed.
Lemma lem4377778 {_104961 : Type'} (f : type686 _104961) (h1 : term16 _104961 f) : term75 _104961 f.
Proof. exact (EQ_MP (@lem4377777 _104961 f) (@lem4377751 _104961 f h1)). Qed.
Lemma lem4377789 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term76 _104961 f t p2) = (term77 _104961 f t p2).
Proof. exact (@lem17362 (f t) (t p2)). Qed.
Lemma lem4377794 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term25 _104961 f t p2) = (term78 _104961 f t p2).
Proof. exact (@lem17265 (f t) (t p2)). Qed.
Lemma lem4377795 {_104961 : Type'} (P : type686 _104961) : (term68 _104961 P) = (term69 _104961 P).
Proof. exact (@lem18392 (_104961 -> Prop) P). Qed.
Lemma lem4377796 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term79 _104961 f p2) = (term80 _104961 f p2).
Proof. exact (@lem4377795 _104961 (term27 _104961 f p2)). Qed.
Lemma lem4377797 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term81 _104961 f p2 t) = (term25 _104961 f t p2).
Proof. exact (eq_refl (term81 _104961 f p2 t)). Qed.
Lemma lem4377798 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4377799 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term82 _104961 f p2 t) = (term76 _104961 f t p2).
Proof. exact (MK_COMB (@lem4377798) (@lem4377797 _104961 f t p2)). Qed.
Lemma lem4377800 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term82 _104961 f p2 t) = (term77 _104961 f t p2).
Proof. exact (TRANS (@lem4377799 _104961 f t p2) (@lem4377789 _104961 f t p2)). Qed.
Lemma lem4377801 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term83 _104961 f p2) = (term84 _104961 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377800 _104961 f t p2)). Qed.
Lemma lem4377802 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4377803 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term80 _104961 f p2) = (term85 _104961 f p2).
Proof. exact (MK_COMB (@lem4377802 _104961) (@lem4377801 _104961 f p2)). Qed.
Lemma lem4377804 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term79 _104961 f p2) = (term85 _104961 f p2).
Proof. exact (TRANS (@lem4377796 _104961 f p2) (@lem4377803 _104961 f p2)). Qed.
Lemma lem4377805 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term27 _104961 f p2) = (term86 _104961 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377794 _104961 f t p2)). Qed.
Lemma lem4377806 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377807 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term28 _104961 f p2) = (term87 _104961 f p2).
Proof. exact (MK_COMB (@lem4377806 _104961) (@lem4377805 _104961 f p2)). Qed.
Lemma lem4377809 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term88 _104960 s p1) = (term88 _104960 s p1).
Proof. exact (eq_refl (term88 _104960 s p1)). Qed.
Lemma lem4377810 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term89 _104960 _104961 s p1 f p2) = (term90 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377809 _104960 s p1) (@lem4377804 _104961 f p2)). Qed.
Lemma lem4377811 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term91 _104960 _104961 s p1 f p2) = (term89 _104960 _104961 s p1 f p2).
Proof. exact (@lem17045 (s p1) (term28 _104961 f p2)). Qed.
Lemma lem4377812 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term91 _104960 _104961 s p1 f p2) = (term90 _104960 _104961 s p1 f p2).
Proof. exact (TRANS (@lem4377811 _104960 _104961 s p1 f p2) (@lem4377810 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4377814 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term19 _104960 s p1) = (term19 _104960 s p1).
Proof. exact (eq_refl (term19 _104960 s p1)). Qed.
Lemma lem4377815 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term30 _104960 _104961 s p1 f p2) = (term92 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377814 _104960 s p1) (@lem4377807 _104961 f p2)). Qed.
Lemma lem4377826 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term93 _104960 _104961 s p1 t p2) = (term94 _104960 _104961 s p1 t p2).
Proof. exact (@lem17045 (s p1) (t p2)). Qed.
Lemma lem4377831 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term95 _104961 f t) = (term95 _104961 f t).
Proof. exact (eq_refl (term95 _104961 f t)). Qed.
Lemma lem4377832 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term96 _104960 _104961 f s p1 t p2) = (term97 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4377831 _104961 f t) (@lem4377826 _104960 _104961 s p1 t p2)). Qed.
Lemma lem4377833 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term98 _104960 _104961 f s p1 t p2) = (term96 _104960 _104961 f s p1 t p2).
Proof. exact (@lem17362 (f t) (term34 _104960 _104961 s p1 t p2)). Qed.
Lemma lem4377834 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term98 _104960 _104961 f s p1 t p2) = (term97 _104960 _104961 f s p1 t p2).
Proof. exact (TRANS (@lem4377833 _104960 _104961 f s p1 t p2) (@lem4377832 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377839 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term36 _104960 _104961 f s p1 t p2) = (term99 _104960 _104961 f s p1 t p2).
Proof. exact (@lem17265 (f t) (term34 _104960 _104961 s p1 t p2)). Qed.
Lemma lem4377840 {_104961 : Type'} (P : type686 _104961) : (term68 _104961 P) = (term69 _104961 P).
Proof. exact (@lem18392 (_104961 -> Prop) P). Qed.
Lemma lem4377841 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term100 _104960 _104961 f s p1 p2) = (term101 _104960 _104961 f s p1 p2).
Proof. exact (@lem4377840 _104961 (term38 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377842 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term102 _104960 _104961 f s p1 p2 t) = (term36 _104960 _104961 f s p1 t p2).
Proof. exact (eq_refl (term102 _104960 _104961 f s p1 p2 t)). Qed.
Lemma lem4377843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4377844 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term103 _104960 _104961 f s p1 p2 t) = (term98 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4377843) (@lem4377842 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377845 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term103 _104960 _104961 f s p1 p2 t) = (term97 _104960 _104961 f s p1 t p2).
Proof. exact (TRANS (@lem4377844 _104960 _104961 f s p1 t p2) (@lem4377834 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377846 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term104 _104960 _104961 f s p1 p2) = (term105 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377845 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377847 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4377848 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term101 _104960 _104961 f s p1 p2) = (term106 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377847 _104961) (@lem4377846 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377849 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term100 _104960 _104961 f s p1 p2) = (term106 _104960 _104961 f s p1 p2).
Proof. exact (TRANS (@lem4377841 _104960 _104961 f s p1 p2) (@lem4377848 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377850 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term38 _104960 _104961 f s p1 p2) = (term107 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377839 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4377851 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377852 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term40 _104960 _104961 f s p1 p2) = (term108 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377851 _104961) (@lem4377850 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4377854 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term109 _104960 _104961 s p1 f p2) = (term110 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377853) (@lem4377812 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4377855 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term111 _104960 _104961 f s p1 p2) = (term112 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377854 _104960 _104961 s p1 f p2) (@lem4377852 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4377857 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term113 _104960 _104961 s p1 f p2) = (term114 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4377856) (@lem4377815 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4377858 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term115 _104960 _104961 f s p1 p2) = (term116 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377857 _104960 _104961 s p1 f p2) (@lem4377849 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4377860 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term117 _104960 _104961 f s p1 p2) = (term118 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377859) (@lem4377858 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377861 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term119 _104960 _104961 f s p1 p2) = (term120 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4377860 _104960 _104961 f s p1 p2) (@lem4377855 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377862 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term66 _104960 _104961 f s p1 p2) = (term119 _104960 _104961 f s p1 p2).
Proof. exact (@lem17646 (term30 _104960 _104961 s p1 f p2) (term40 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4377863 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term66 _104960 _104961 f s p1 p2) = (term120 _104960 _104961 f s p1 p2).
Proof. exact (TRANS (@lem4377862 _104960 _104961 f s p1 p2) (@lem4377861 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4378019 {_104961 : Type'} (P : Prop) (Q : type686 _104961) : (term123 _104961 P Q) = (term124 _104961 P Q).
Proof. exact (@lem4378018 (_104961 -> Prop) P Q). Qed.
Lemma lem4378020 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term125 _104960 _104961 f s p1 p2) = (term126 _104960 _104961 f s p1 p2).
Proof. exact (@lem4378019 _104961 (term92 _104960 _104961 s p1 f p2) (term105 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378021 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term127 _104960 _104961 f s p1 p2 t) = (term97 _104960 _104961 f s p1 t p2).
Proof. exact (eq_refl (term127 _104960 _104961 f s p1 p2 t)). Qed.
Lemma lem4378022 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term128 _104960 _104961 f s p1 p2) = (term105 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378021 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378023 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378024 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term129 _104960 _104961 f s p1 p2) = (term106 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378023 _104961) (@lem4378022 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378025 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term114 _104960 _104961 s p1 f p2) = (term114 _104960 _104961 s p1 f p2).
Proof. exact (eq_refl (term114 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378026 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term125 _104960 _104961 f s p1 p2) = (term116 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378025 _104960 _104961 s p1 f p2) (@lem4378024 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378028 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term130 _104960 _104961 f s p1 p2) = (term131 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378027) (@lem4378026 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378029 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term127 _104960 _104961 f s p1 p2 t) = (term97 _104960 _104961 f s p1 t p2).
Proof. exact (eq_refl (term127 _104960 _104961 f s p1 p2 t)). Qed.
Lemma lem4378030 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term114 _104960 _104961 s p1 f p2) = (term114 _104960 _104961 s p1 f p2).
Proof. exact (eq_refl (term114 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378031 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term132 _104960 _104961 f s p1 p2 t) = (term133 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4378030 _104960 _104961 s p1 f p2) (@lem4378029 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378032 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term134 _104960 _104961 f s p1 p2) = (term135 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378031 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378033 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378034 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term126 _104960 _104961 f s p1 p2) = (term136 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378033 _104961) (@lem4378032 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378035 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : ((term125 _104960 _104961 f s p1 p2) = (term126 _104960 _104961 f s p1 p2)) = ((term116 _104960 _104961 f s p1 p2) = (term136 _104960 _104961 f s p1 p2)).
Proof. exact (MK_COMB (@lem4378028 _104960 _104961 f s p1 p2) (@lem4378034 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378036 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term116 _104960 _104961 f s p1 p2) = (term136 _104960 _104961 f s p1 p2).
Proof. exact (EQ_MP (@lem4378035 _104960 _104961 f s p1 p2) (@lem4378020 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378038 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term118 _104960 _104961 f s p1 p2) = (term137 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378037) (@lem4378036 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378040 {A : Type'} (P : Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4378041 {_104961 : Type'} (P : Prop) (Q : type686 _104961) : (term140 _104961 P Q) = (term141 _104961 P Q).
Proof. exact (@lem4378040 (_104961 -> Prop) P Q). Qed.
Lemma lem4378042 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term142 _104960 _104961 s p1 f p2) = (term143 _104960 _104961 s p1 f p2).
Proof. exact (@lem4378041 _104961 (term144 _104960 s p1) (term84 _104961 f p2)). Qed.
Lemma lem4378043 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term145 _104961 f p2 t) = (term77 _104961 f t p2).
Proof. exact (eq_refl (term145 _104961 f p2 t)). Qed.
Lemma lem4378044 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term146 _104961 f p2) = (term84 _104961 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378043 _104961 f t p2)). Qed.
Lemma lem4378045 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378046 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term147 _104961 f p2) = (term85 _104961 f p2).
Proof. exact (MK_COMB (@lem4378045 _104961) (@lem4378044 _104961 f p2)). Qed.
Lemma lem4378047 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term88 _104960 s p1) = (term88 _104960 s p1).
Proof. exact (eq_refl (term88 _104960 s p1)). Qed.
Lemma lem4378048 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term142 _104960 _104961 s p1 f p2) = (term90 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378047 _104960 s p1) (@lem4378046 _104961 f p2)). Qed.
Lemma lem4378049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378050 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term148 _104960 _104961 s p1 f p2) = (term149 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378049) (@lem4378048 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378051 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term145 _104961 f p2 t) = (term77 _104961 f t p2).
Proof. exact (eq_refl (term145 _104961 f p2 t)). Qed.
Lemma lem4378052 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term88 _104960 s p1) = (term88 _104960 s p1).
Proof. exact (eq_refl (term88 _104960 s p1)). Qed.
Lemma lem4378053 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term150 _104960 _104961 s p1 f p2 t) = (term151 _104960 _104961 s p1 f t p2).
Proof. exact (MK_COMB (@lem4378052 _104960 s p1) (@lem4378051 _104961 f t p2)). Qed.
Lemma lem4378054 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term152 _104960 _104961 s p1 f p2) = (term153 _104960 _104961 s p1 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378053 _104960 _104961 s p1 f t p2)). Qed.
Lemma lem4378055 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378056 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term143 _104960 _104961 s p1 f p2) = (term154 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378055 _104961) (@lem4378054 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378057 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : ((term142 _104960 _104961 s p1 f p2) = (term143 _104960 _104961 s p1 f p2)) = ((term90 _104960 _104961 s p1 f p2) = (term154 _104960 _104961 s p1 f p2)).
Proof. exact (MK_COMB (@lem4378050 _104960 _104961 s p1 f p2) (@lem4378056 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378058 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term90 _104960 _104961 s p1 f p2) = (term154 _104960 _104961 s p1 f p2).
Proof. exact (EQ_MP (@lem4378057 _104960 _104961 s p1 f p2) (@lem4378042 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378060 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term110 _104960 _104961 s p1 f p2) = (term155 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378059) (@lem4378058 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378061 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term108 _104960 _104961 f s p1 p2) = (term108 _104960 _104961 f s p1 p2).
Proof. exact (eq_refl (term108 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378062 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term112 _104960 _104961 f s p1 p2) = (term156 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378060 _104960 _104961 s p1 f p2) (@lem4378061 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378064 {A : Type'} (P : A -> Prop) (Q : Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4378065 {_104961 : Type'} (P : type686 _104961) (Q : Prop) : (term159 _104961 P Q) = (term160 _104961 P Q).
Proof. exact (@lem4378064 (_104961 -> Prop) P Q). Qed.
Lemma lem4378066 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term161 _104960 _104961 f s p1 p2) = (term162 _104960 _104961 f s p1 p2).
Proof. exact (@lem4378065 _104961 (term153 _104960 _104961 s p1 f p2) (term108 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378067 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term163 _104960 _104961 s p1 f p2 t) = (term151 _104960 _104961 s p1 f t p2).
Proof. exact (eq_refl (term163 _104960 _104961 s p1 f p2 t)). Qed.
Lemma lem4378068 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term164 _104960 _104961 s p1 f p2) = (term153 _104960 _104961 s p1 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378067 _104960 _104961 s p1 f t p2)). Qed.
Lemma lem4378069 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378070 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term165 _104960 _104961 s p1 f p2) = (term154 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378069 _104961) (@lem4378068 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378072 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term166 _104960 _104961 s p1 f p2) = (term155 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378071) (@lem4378070 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378073 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term108 _104960 _104961 f s p1 p2) = (term108 _104960 _104961 f s p1 p2).
Proof. exact (eq_refl (term108 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378074 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term161 _104960 _104961 f s p1 p2) = (term156 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378072 _104960 _104961 s p1 f p2) (@lem4378073 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378076 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term167 _104960 _104961 f s p1 p2) = (term168 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378075) (@lem4378074 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378077 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term163 _104960 _104961 s p1 f p2 t) = (term151 _104960 _104961 s p1 f t p2).
Proof. exact (eq_refl (term163 _104960 _104961 s p1 f p2 t)). Qed.
Lemma lem4378078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378079 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term169 _104960 _104961 s p1 f p2 t) = (term170 _104960 _104961 s p1 f t p2).
Proof. exact (MK_COMB (@lem4378078) (@lem4378077 _104960 _104961 s p1 f t p2)). Qed.
Lemma lem4378080 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term108 _104960 _104961 f s p1 p2) = (term108 _104960 _104961 f s p1 p2).
Proof. exact (eq_refl (term108 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378081 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term171 _104960 _104961 t f s p1 p2) = (term172 _104960 _104961 t f s p1 p2).
Proof. exact (MK_COMB (@lem4378079 _104960 _104961 s p1 f t p2) (@lem4378080 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378082 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term173 _104960 _104961 f s p1 p2) = (term174 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378081 _104960 _104961 t f s p1 p2)). Qed.
Lemma lem4378083 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378084 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term162 _104960 _104961 f s p1 p2) = (term175 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378083 _104961) (@lem4378082 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378085 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : ((term161 _104960 _104961 f s p1 p2) = (term162 _104960 _104961 f s p1 p2)) = ((term156 _104960 _104961 f s p1 p2) = (term175 _104960 _104961 f s p1 p2)).
Proof. exact (MK_COMB (@lem4378076 _104960 _104961 f s p1 p2) (@lem4378084 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378086 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term156 _104960 _104961 f s p1 p2) = (term175 _104960 _104961 f s p1 p2).
Proof. exact (EQ_MP (@lem4378085 _104960 _104961 f s p1 p2) (@lem4378066 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378087 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term112 _104960 _104961 f s p1 p2) = (term175 _104960 _104961 f s p1 p2).
Proof. exact (TRANS (@lem4378062 _104960 _104961 f s p1 p2) (@lem4378086 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378088 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term120 _104960 _104961 f s p1 p2) = (term176 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378038 _104960 _104961 f s p1 p2) (@lem4378087 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378090 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4378091 {_104961 : Type'} (P : type686 _104961) (Q : type686 _104961) : (term179 _104961 P Q) = (term180 _104961 P Q).
Proof. exact (@lem4378090 (_104961 -> Prop) P Q). Qed.
Lemma lem4378092 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term181 _104960 _104961 f s p1 p2) = (term182 _104960 _104961 f s p1 p2).
Proof. exact (@lem4378091 _104961 (term135 _104960 _104961 f s p1 p2) (term174 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378093 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term183 _104960 _104961 f s p1 p2 t) = (term133 _104960 _104961 f s p1 t p2).
Proof. exact (eq_refl (term183 _104960 _104961 f s p1 p2 t)). Qed.
Lemma lem4378094 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term184 _104960 _104961 f s p1 p2) = (term135 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378093 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378095 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378096 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term185 _104960 _104961 f s p1 p2) = (term136 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378095 _104961) (@lem4378094 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378098 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term186 _104960 _104961 f s p1 p2) = (term137 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378097) (@lem4378096 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378099 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term187 _104960 _104961 f s p1 p2 t) = (term172 _104960 _104961 t f s p1 p2).
Proof. exact (eq_refl (term187 _104960 _104961 f s p1 p2 t)). Qed.
Lemma lem4378100 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term188 _104960 _104961 f s p1 p2) = (term174 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378099 _104960 _104961 t f s p1 p2)). Qed.
Lemma lem4378101 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378102 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term189 _104960 _104961 f s p1 p2) = (term175 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378101 _104961) (@lem4378100 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378103 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term181 _104960 _104961 f s p1 p2) = (term176 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378098 _104960 _104961 f s p1 p2) (@lem4378102 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378105 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term190 _104960 _104961 f s p1 p2) = (term191 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378104) (@lem4378103 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378106 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term183 _104960 _104961 f s p1 p2 t) = (term133 _104960 _104961 f s p1 t p2).
Proof. exact (eq_refl (term183 _104960 _104961 f s p1 p2 t)). Qed.
Lemma lem4378107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378108 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term192 _104960 _104961 f s p1 p2 t) = (term193 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4378107) (@lem4378106 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378109 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term187 _104960 _104961 f s p1 p2 t) = (term172 _104960 _104961 t f s p1 p2).
Proof. exact (eq_refl (term187 _104960 _104961 f s p1 p2 t)). Qed.
Lemma lem4378110 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term194 _104960 _104961 f s p1 p2 t) = (term195 _104960 _104961 t f s p1 p2).
Proof. exact (MK_COMB (@lem4378108 _104960 _104961 f s p1 t p2) (@lem4378109 _104960 _104961 t f s p1 p2)). Qed.
Lemma lem4378111 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term196 _104960 _104961 f s p1 p2) = (term197 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378110 _104960 _104961 t f s p1 p2)). Qed.
Lemma lem4378112 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4378113 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term182 _104960 _104961 f s p1 p2) = (term198 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378112 _104961) (@lem4378111 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378114 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : ((term181 _104960 _104961 f s p1 p2) = (term182 _104960 _104961 f s p1 p2)) = ((term176 _104960 _104961 f s p1 p2) = (term198 _104960 _104961 f s p1 p2)).
Proof. exact (MK_COMB (@lem4378105 _104960 _104961 f s p1 p2) (@lem4378113 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378115 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term176 _104960 _104961 f s p1 p2) = (term198 _104960 _104961 f s p1 p2).
Proof. exact (EQ_MP (@lem4378114 _104960 _104961 f s p1 p2) (@lem4378092 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378117 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term120 _104960 _104961 f s p1 p2) = (term198 _104960 _104961 f s p1 p2).
Proof. exact (TRANS (@lem4378088 _104960 _104961 f s p1 p2) (@lem4378115 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378118 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term66 _104960 _104961 f s p1 p2) = (term198 _104960 _104961 f s p1 p2).
Proof. exact (TRANS (@lem4377863 _104960 _104961 f s p1 p2) (@lem4378117 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378119 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term66 _104960 _104961 f s p1 p2) : term198 _104960 _104961 f s p1 p2.
Proof. exact (EQ_MP (@lem4378118 _104960 _104961 f s p1 p2) (@lem4377756 _104960 _104961 f s p1 p2 h1)). Qed.
Lemma lem4378120 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term195 _104960 _104961 t f s p1 p2) : term195 _104960 _104961 t f s p1 p2.
Proof. exact (h1). Qed.
Lemma lem4378121 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) (h1 : f x) : f x.
Proof. exact (h1). Qed.
Lemma lem4378126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378127 {_104961 : Type'} (f : _104961 -> Prop) (x : _104961) : (f x) = (@I (_104961 -> Prop) f x).
Proof. exact (@lem4378126 _104961 Prop f x). Qed.
Lemma lem4378129 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (t p2) = (@I (_104961 -> Prop) t p2).
Proof. exact (@lem4378127 _104961 t p2). Qed.
Lemma lem4378134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378135 {_104960 : Type'} (f : _104960 -> Prop) (x : _104960) : (f x) = (@I (_104960 -> Prop) f x).
Proof. exact (@lem4378134 _104960 Prop f x). Qed.
Lemma lem4378137 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (s p1) = (@I (_104960 -> Prop) s p1).
Proof. exact (@lem4378135 _104960 s p1). Qed.
Lemma lem4378138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378139 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term19 _104960 s p1) = (term199 _104960 s p1).
Proof. exact (MK_COMB (@lem4378138) (@lem4378137 _104960 s p1)). Qed.
Lemma lem4378140 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term34 _104960 _104961 s p1 t p2) = (term200 _104960 _104961 s p1 t p2).
Proof. exact (MK_COMB (@lem4378139 _104960 s p1) (@lem4378129 _104961 t p2)). Qed.
Lemma lem4378141 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4378146 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378147 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (f x) = (@I ((_104961 -> Prop) -> Prop) f x).
Proof. exact (@lem4378146 (_104961 -> Prop) Prop f x). Qed.
Lemma lem4378149 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (f t) = (@I ((_104961 -> Prop) -> Prop) f t).
Proof. exact (@lem4378147 _104961 f t). Qed.
Lemma lem4378150 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term12 _104961 f t) = (term201 _104961 f t).
Proof. exact (MK_COMB (@lem4378141) (@lem4378149 _104961 f t)). Qed.
Lemma lem4378151 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378152 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term202 _104961 f t) = (term203 _104961 f t).
Proof. exact (MK_COMB (@lem4378151) (@lem4378150 _104961 f t)). Qed.
Lemma lem4378153 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term99 _104960 _104961 f s p1 t p2) = (term204 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4378152 _104961 f t) (@lem4378140 _104960 _104961 s p1 t p2)). Qed.
Lemma lem4378154 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term107 _104960 _104961 f s p1 p2) = (term205 _104960 _104961 f s p1 p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378153 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378155 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4378156 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term108 _104960 _104961 f s p1 p2) = (term206 _104960 _104961 f s p1 p2).
Proof. exact (MK_COMB (@lem4378155 _104961) (@lem4378154 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4378162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378163 {_104961 : Type'} (f : _104961 -> Prop) (x : _104961) : (f x) = (@I (_104961 -> Prop) f x).
Proof. exact (@lem4378162 _104961 Prop f x). Qed.
Lemma lem4378165 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (t p2) = (@I (_104961 -> Prop) t p2).
Proof. exact (@lem4378163 _104961 t p2). Qed.
Lemma lem4378166 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term144 _104961 t p2) = (term207 _104961 t p2).
Proof. exact (MK_COMB (@lem4378157) (@lem4378165 _104961 t p2)). Qed.
Lemma lem4378171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378172 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (f x) = (@I ((_104961 -> Prop) -> Prop) f x).
Proof. exact (@lem4378171 (_104961 -> Prop) Prop f x). Qed.
Lemma lem4378174 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (f t) = (@I ((_104961 -> Prop) -> Prop) f t).
Proof. exact (@lem4378172 _104961 f t). Qed.
Lemma lem4378175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378176 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term95 _104961 f t) = (term208 _104961 f t).
Proof. exact (MK_COMB (@lem4378175) (@lem4378174 _104961 f t)). Qed.
Lemma lem4378177 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term77 _104961 f t p2) = (term209 _104961 f t p2).
Proof. exact (MK_COMB (@lem4378176 _104961 f t) (@lem4378166 _104961 t p2)). Qed.
Lemma lem4378178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4378183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378184 {_104960 : Type'} (f : _104960 -> Prop) (x : _104960) : (f x) = (@I (_104960 -> Prop) f x).
Proof. exact (@lem4378183 _104960 Prop f x). Qed.
Lemma lem4378186 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (s p1) = (@I (_104960 -> Prop) s p1).
Proof. exact (@lem4378184 _104960 s p1). Qed.
Lemma lem4378187 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term144 _104960 s p1) = (term207 _104960 s p1).
Proof. exact (MK_COMB (@lem4378178) (@lem4378186 _104960 s p1)). Qed.
Lemma lem4378188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378189 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term88 _104960 s p1) = (term210 _104960 s p1).
Proof. exact (MK_COMB (@lem4378188) (@lem4378187 _104960 s p1)). Qed.
Lemma lem4378190 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term151 _104960 _104961 s p1 f t p2) = (term211 _104960 _104961 s p1 f t p2).
Proof. exact (MK_COMB (@lem4378189 _104960 s p1) (@lem4378177 _104961 f t p2)). Qed.
Lemma lem4378191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378192 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term170 _104960 _104961 s p1 f t p2) = (term212 _104960 _104961 s p1 f t p2).
Proof. exact (MK_COMB (@lem4378191) (@lem4378190 _104960 _104961 s p1 f t p2)). Qed.
Lemma lem4378193 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term172 _104960 _104961 t f s p1 p2) = (term213 _104960 _104961 t f s p1 p2).
Proof. exact (MK_COMB (@lem4378192 _104960 _104961 s p1 f t p2) (@lem4378156 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4378194 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4378199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378200 {_104961 : Type'} (f : _104961 -> Prop) (x : _104961) : (f x) = (@I (_104961 -> Prop) f x).
Proof. exact (@lem4378199 _104961 Prop f x). Qed.
Lemma lem4378202 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (t p2) = (@I (_104961 -> Prop) t p2).
Proof. exact (@lem4378200 _104961 t p2). Qed.
Lemma lem4378203 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term144 _104961 t p2) = (term207 _104961 t p2).
Proof. exact (MK_COMB (@lem4378194) (@lem4378202 _104961 t p2)). Qed.
Lemma lem4378204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4378209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378210 {_104960 : Type'} (f : _104960 -> Prop) (x : _104960) : (f x) = (@I (_104960 -> Prop) f x).
Proof. exact (@lem4378209 _104960 Prop f x). Qed.
Lemma lem4378212 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (s p1) = (@I (_104960 -> Prop) s p1).
Proof. exact (@lem4378210 _104960 s p1). Qed.
Lemma lem4378213 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term144 _104960 s p1) = (term207 _104960 s p1).
Proof. exact (MK_COMB (@lem4378204) (@lem4378212 _104960 s p1)). Qed.
Lemma lem4378214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378215 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term88 _104960 s p1) = (term210 _104960 s p1).
Proof. exact (MK_COMB (@lem4378214) (@lem4378213 _104960 s p1)). Qed.
Lemma lem4378216 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term94 _104960 _104961 s p1 t p2) = (term214 _104960 _104961 s p1 t p2).
Proof. exact (MK_COMB (@lem4378215 _104960 s p1) (@lem4378203 _104961 t p2)). Qed.
Lemma lem4378221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378222 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (f x) = (@I ((_104961 -> Prop) -> Prop) f x).
Proof. exact (@lem4378221 (_104961 -> Prop) Prop f x). Qed.
Lemma lem4378224 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (f t) = (@I ((_104961 -> Prop) -> Prop) f t).
Proof. exact (@lem4378222 _104961 f t). Qed.
Lemma lem4378225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378226 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term95 _104961 f t) = (term208 _104961 f t).
Proof. exact (MK_COMB (@lem4378225) (@lem4378224 _104961 f t)). Qed.
Lemma lem4378227 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term97 _104960 _104961 f s p1 t p2) = (term215 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4378226 _104961 f t) (@lem4378216 _104960 _104961 s p1 t p2)). Qed.
Lemma lem4378232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378233 {_104961 : Type'} (f : _104961 -> Prop) (x : _104961) : (f x) = (@I (_104961 -> Prop) f x).
Proof. exact (@lem4378232 _104961 Prop f x). Qed.
Lemma lem4378235 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (t p2) = (@I (_104961 -> Prop) t p2).
Proof. exact (@lem4378233 _104961 t p2). Qed.
Lemma lem4378236 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4378241 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378242 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (f x) = (@I ((_104961 -> Prop) -> Prop) f x).
Proof. exact (@lem4378241 (_104961 -> Prop) Prop f x). Qed.
Lemma lem4378244 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (f t) = (@I ((_104961 -> Prop) -> Prop) f t).
Proof. exact (@lem4378242 _104961 f t). Qed.
Lemma lem4378245 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term12 _104961 f t) = (term201 _104961 f t).
Proof. exact (MK_COMB (@lem4378236) (@lem4378244 _104961 f t)). Qed.
Lemma lem4378246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378247 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term202 _104961 f t) = (term203 _104961 f t).
Proof. exact (MK_COMB (@lem4378246) (@lem4378245 _104961 f t)). Qed.
Lemma lem4378248 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term78 _104961 f t p2) = (term216 _104961 f t p2).
Proof. exact (MK_COMB (@lem4378247 _104961 f t) (@lem4378235 _104961 t p2)). Qed.
Lemma lem4378249 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term86 _104961 f p2) = (term217 _104961 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378248 _104961 f t p2)). Qed.
Lemma lem4378250 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4378251 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term87 _104961 f p2) = (term218 _104961 f p2).
Proof. exact (MK_COMB (@lem4378250 _104961) (@lem4378249 _104961 f p2)). Qed.
Lemma lem4378256 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378257 {_104960 : Type'} (f : _104960 -> Prop) (x : _104960) : (f x) = (@I (_104960 -> Prop) f x).
Proof. exact (@lem4378256 _104960 Prop f x). Qed.
Lemma lem4378259 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (s p1) = (@I (_104960 -> Prop) s p1).
Proof. exact (@lem4378257 _104960 s p1). Qed.
Lemma lem4378260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378261 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term19 _104960 s p1) = (term199 _104960 s p1).
Proof. exact (MK_COMB (@lem4378260) (@lem4378259 _104960 s p1)). Qed.
Lemma lem4378262 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term92 _104960 _104961 s p1 f p2) = (term219 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378261 _104960 s p1) (@lem4378251 _104961 f p2)). Qed.
Lemma lem4378263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378264 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term114 _104960 _104961 s p1 f p2) = (term220 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378263) (@lem4378262 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378265 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term133 _104960 _104961 f s p1 t p2) = (term221 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4378264 _104960 _104961 s p1 f p2) (@lem4378227 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4378267 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) : (term193 _104960 _104961 f s p1 t p2) = (term222 _104960 _104961 f s p1 t p2).
Proof. exact (MK_COMB (@lem4378266) (@lem4378265 _104960 _104961 f s p1 t p2)). Qed.
Lemma lem4378268 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term195 _104960 _104961 t f s p1 p2) = (term223 _104960 _104961 t f s p1 p2).
Proof. exact (MK_COMB (@lem4378267 _104960 _104961 f s p1 t p2) (@lem4378193 _104960 _104961 t f s p1 p2)). Qed.
Lemma lem4378269 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term195 _104960 _104961 t f s p1 p2) : term223 _104960 _104961 t f s p1 p2.
Proof. exact (EQ_MP (@lem4378268 _104960 _104961 t f s p1 p2) (@lem4378120 _104960 _104961 t f s p1 p2 h1)). Qed.
Lemma lem4378274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4378276 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (f x) = (@I ((_104961 -> Prop) -> Prop) f x).
Proof. exact (@lem4378274 (_104961 -> Prop) Prop f x). Qed.
Lemma lem4378278 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term221 _104960 _104961 f s p1 t p2.
Proof. exact (h1). Qed.
Lemma lem4378279 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term213 _104960 _104961 t f s p1 p2.
Proof. exact (h1). Qed.
Lemma lem4378280 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term215 _104960 _104961 f s p1 t p2.
Proof. exact (proj2 (@lem4378278 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378281 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term219 _104960 _104961 s p1 f p2.
Proof. exact (proj1 (@lem4378278 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378282 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term214 _104960 _104961 s p1 t p2.
Proof. exact (proj2 (@lem4378280 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378284 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term218 _104961 f p2.
Proof. exact (proj2 (@lem4378281 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378288 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term206 _104960 _104961 f s p1 p2.
Proof. exact (proj2 (@lem4378279 _104960 _104961 t f s p1 p2 h1)). Qed.
Lemma lem4378289 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term211 _104960 _104961 s p1 f t p2.
Proof. exact (proj1 (@lem4378279 _104960 _104961 t f s p1 p2 h1)). Qed.
Lemma lem4378291 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) (h1 : term209 _104961 f t p2) : term209 _104961 f t p2.
Proof. exact (h1). Qed.
Lemma lem4378322 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) (h1 : term207 _104960 s p1) : term207 _104960 s p1.
Proof. exact (h1). Qed.
Lemma lem4378342 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term216 _104961 f t p2) = (term216 _104961 f t p2).
Proof. exact (eq_refl (term216 _104961 f t p2)). Qed.
Lemma lem4378343 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term217 _104961 f p2) = (term217 _104961 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378342 _104961 f t p2)). Qed.
Lemma lem4378344 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4378346 {_104961 : Type'} (f : type686 _104961) (p2 : _104961) : (term218 _104961 f p2) = (term218 _104961 f p2).
Proof. exact (MK_COMB (@lem4378344 _104961) (@lem4378343 _104961 f p2)). Qed.
Lemma lem4378347 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term218 _104961 f p2.
Proof. exact (EQ_MP (@lem4378346 _104961 f p2) (@lem4378284 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378351 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) : term207 _104961 t p2.
Proof. exact (h1). Qed.
Lemma lem4378373 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term204 _104960 _104961 f s p1 t p2) = (term224 _104960 _104961 s p1 f t p2).
Proof. exact (@lem19490 (@I (_104960 -> Prop) s p1) (term201 _104961 f t) (@I (_104961 -> Prop) t p2)). Qed.
Lemma lem4378374 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term205 _104960 _104961 f s p1 p2) = (term225 _104960 _104961 s p1 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378373 _104960 _104961 s p1 f t p2)). Qed.
Lemma lem4378375 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4378377 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term206 _104960 _104961 f s p1 p2) = (term226 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378375 _104961) (@lem4378374 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378378 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term226 _104960 _104961 s p1 f p2.
Proof. exact (EQ_MP (@lem4378377 _104960 _104961 s p1 f p2) (@lem4378288 _104960 _104961 t f s p1 p2 h1)). Qed.
Lemma lem4378382 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) (h1 : term207 _104960 s p1) : term207 _104960 s p1.
Proof. exact (h1). Qed.
Lemma lem4378404 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) : (term204 _104960 _104961 f s p1 t p2) = (term224 _104960 _104961 s p1 f t p2).
Proof. exact (@lem19490 (@I (_104960 -> Prop) s p1) (term201 _104961 f t) (@I (_104961 -> Prop) t p2)). Qed.
Lemma lem4378405 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term205 _104960 _104961 f s p1 p2) = (term225 _104960 _104961 s p1 f p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4378404 _104960 _104961 s p1 f t p2)). Qed.
Lemma lem4378406 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4378408 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (p2 : _104961) : (term206 _104960 _104961 f s p1 p2) = (term226 _104960 _104961 s p1 f p2).
Proof. exact (MK_COMB (@lem4378406 _104961) (@lem4378405 _104960 _104961 s p1 f p2)). Qed.
Lemma lem4378409 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term226 _104960 _104961 s p1 f p2.
Proof. exact (EQ_MP (@lem4378408 _104960 _104961 s p1 f p2) (@lem4378288 _104960 _104961 t f s p1 p2 h1)). Qed.
Lemma lem4378421 {_104960 _104961 : Type'} (_50037 : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term227 _104961 f p2 _50037.
Proof. exact (@lem4378347 _104960 _104961 f s p1 t p2 h1 _50037). Qed.
Lemma lem4378422 {_104961 : Type'} (f : type686 _104961) (_50037 : _104961 -> Prop) (p2 : _104961) : (term227 _104961 f p2 _50037) = (term216 _104961 f _50037 p2).
Proof. exact (eq_refl (term227 _104961 f p2 _50037)). Qed.
Lemma lem4378424 {_104960 _104961 : Type'} (_50038 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term228 _104960 _104961 s p1 f p2 _50038.
Proof. exact (@lem4378378 _104960 _104961 t f s p1 p2 h1 _50038). Qed.
Lemma lem4378425 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) (p2 : _104961) : (term228 _104960 _104961 s p1 f p2 _50038) = (term224 _104960 _104961 s p1 f _50038 p2).
Proof. exact (eq_refl (term228 _104960 _104961 s p1 f p2 _50038)). Qed.
Lemma lem4378426 {_104960 _104961 : Type'} (_50038 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term224 _104960 _104961 s p1 f _50038 p2.
Proof. exact (EQ_MP (@lem4378425 _104960 _104961 s p1 f _50038 p2) (@lem4378424 _104960 _104961 _50038 t f s p1 p2 h1)). Qed.
Lemma lem4378427 {_104960 _104961 : Type'} (_50039 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term228 _104960 _104961 s p1 f p2 _50039.
Proof. exact (@lem4378409 _104960 _104961 t f s p1 p2 h1 _50039). Qed.
Lemma lem4378428 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50039 : _104961 -> Prop) (p2 : _104961) : (term228 _104960 _104961 s p1 f p2 _50039) = (term224 _104960 _104961 s p1 f _50039 p2).
Proof. exact (eq_refl (term228 _104960 _104961 s p1 f p2 _50039)). Qed.
Lemma lem4378429 {_104960 _104961 : Type'} (_50039 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term224 _104960 _104961 s p1 f _50039 p2.
Proof. exact (EQ_MP (@lem4378428 _104960 _104961 s p1 f _50039 p2) (@lem4378427 _104960 _104961 _50039 t f s p1 p2 h1)). Qed.
Lemma lem4378447 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) (h1 : term207 _104960 s p1) : term207 _104960 s p1.
Proof. exact (h1). Qed.
Lemma lem4378459 {_104960 _104961 : Type'} (_50037 : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term216 _104961 f _50037 p2.
Proof. exact (EQ_MP (@lem4378422 _104961 f _50037 p2) (@lem4378421 _104960 _104961 _50037 f s p1 t p2 h1)). Qed.
Lemma lem4378461 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) : term207 _104961 t p2.
Proof. exact (h1). Qed.
Lemma lem4378465 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) (h1 : term207 _104960 s p1) : term207 _104960 s p1.
Proof. exact (h1). Qed.
Lemma lem4378471 {_104960 _104961 : Type'} (_50038 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term229 _104960 _104961 f _50038 s p1.
Proof. exact (proj1 (@lem4378426 _104960 _104961 _50038 t f s p1 p2 h1)). Qed.
Lemma lem4378483 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) (h1 : term209 _104961 f t p2) : term207 _104961 t p2.
Proof. exact (proj2 (@lem4378291 _104961 f t p2 h1)). Qed.
Lemma lem4378495 {_104960 _104961 : Type'} (_50039 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term216 _104961 f _50039 p2.
Proof. exact (proj2 (@lem4378429 _104960 _104961 _50039 t f s p1 p2 h1)). Qed.
Lemma lem4378497 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : @I (_104960 -> Prop) s p1.
Proof. exact (proj1 (@lem4378281 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378498 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term230 _104960 s p1.
Proof. exact (fun h0 : term207 _104960 s p1 => @lem4378497 _104960 _104961 f s p1 t p2 h1). Qed.
Lemma lem4378500 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378501 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term230 _104960 s p1) = (@I (_104960 -> Prop) s p1).
Proof. exact (@lem4378500 (@I (_104960 -> Prop) s p1)). Qed.
Lemma lem4378502 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : @I (_104960 -> Prop) s p1.
Proof. exact (EQ_MP (@lem4378501 _104960 s p1) (@lem4378498 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378505 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4378507 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term207 _104960 s p1) = (term232 _104960 s p1).
Proof. exact (@lem4378505 (@I (_104960 -> Prop) s p1)). Qed.
Lemma lem4378510 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) (h1 : term207 _104960 s p1) : term232 _104960 s p1.
Proof. exact (EQ_MP (@lem4378507 _104960 s p1) (@lem4378447 _104960 s p1 h1)). Qed.
Lemma lem4378513 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (@lem4378510 _104960 s p1 h1 (@lem4378502 _104960 _104961 f s p1 t p2 h2)). Qed.
Lemma lem4378514 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : term233.
Proof. exact (fun h0 : ~ False => @lem4378513 _104960 _104961 f s p1 t p2 h1 h2). Qed.
Lemma lem4378516 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378517 : term233 = False.
Proof. exact (@lem4378516 False). Qed.
Lemma lem4378518 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378517) (@lem4378514 _104960 _104961 f s p1 t p2 h1 h2)). Qed.
Lemma lem4378520 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : @I ((_104961 -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem4378280 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378521 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term234 _104961 f t.
Proof. exact (fun h0 : term201 _104961 f t => @lem4378520 _104960 _104961 f s p1 t p2 h1). Qed.
Lemma lem4378523 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378524 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term234 _104961 f t) = (@I ((_104961 -> Prop) -> Prop) f t).
Proof. exact (@lem4378523 (@I ((_104961 -> Prop) -> Prop) f t)). Qed.
Lemma lem4378525 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : @I ((_104961 -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem4378524 _104961 f t) (@lem4378521 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378531 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4378532 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : (term216 _104961 f _50037 p2) = (term235 _104961 p2 f _50037).
Proof. exact (@lem4378531 (@I (_104961 -> Prop) _50037 p2) (term201 _104961 f _50037)). Qed.
Lemma lem4378538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378539 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : (term236 _104961 f _50037 p2) = (term237 _104961 p2 f _50037).
Proof. exact (MK_COMB (@lem4378538) (@lem4378532 _104961 p2 f _50037)). Qed.
Lemma lem4378545 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : (term235 _104961 p2 f _50037) = (term235 _104961 p2 f _50037).
Proof. exact (eq_refl (term235 _104961 p2 f _50037)). Qed.
Lemma lem4378546 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : ((term216 _104961 f _50037 p2) = (term235 _104961 p2 f _50037)) = ((term235 _104961 p2 f _50037) = (term235 _104961 p2 f _50037)).
Proof. exact (MK_COMB (@lem4378539 _104961 p2 f _50037) (@lem4378545 _104961 p2 f _50037)). Qed.
Lemma lem4378548 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4378549 (x : Prop) : (x = x) = True.
Proof. exact (@lem4378548 Prop x). Qed.
Lemma lem4378550 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : ((term235 _104961 p2 f _50037) = (term235 _104961 p2 f _50037)) = True.
Proof. exact (@lem4378549 (term235 _104961 p2 f _50037)). Qed.
Lemma lem4378551 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : ((term216 _104961 f _50037 p2) = (term235 _104961 p2 f _50037)) = True.
Proof. exact (TRANS (@lem4378546 _104961 p2 f _50037) (@lem4378550 _104961 p2 f _50037)). Qed.
Lemma lem4378552 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : True = ((term216 _104961 f _50037 p2) = (term235 _104961 p2 f _50037)).
Proof. exact (SYM (@lem4378551 _104961 p2 f _50037)). Qed.
Lemma lem4378553 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50037 : _104961 -> Prop) : (term216 _104961 f _50037 p2) = (term235 _104961 p2 f _50037).
Proof. exact (EQ_MP (@lem4378552 _104961 p2 f _50037) (@lem0)). Qed.
Lemma lem4378554 {_104960 _104961 : Type'} (_50037 : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term235 _104961 p2 f _50037.
Proof. exact (EQ_MP (@lem4378553 _104961 p2 f _50037) (@lem4378459 _104960 _104961 _50037 f s p1 t p2 h1)). Qed.
Lemma lem4378556 (b : Prop) (a : Prop) : (a \/ b) = (term238 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4378557 {_104961 : Type'} (f : type686 _104961) (_50037 : _104961 -> Prop) (p2 : _104961) : (term235 _104961 p2 f _50037) = (term239 _104961 f _50037 p2).
Proof. exact (@lem4378556 (term201 _104961 f _50037) (@I (_104961 -> Prop) _50037 p2)). Qed.
Lemma lem4378559 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4378560 {_104961 : Type'} (f : type686 _104961) (_50037 : _104961 -> Prop) : (term240 _104961 f _50037) = (@I ((_104961 -> Prop) -> Prop) f _50037).
Proof. exact (@lem4378559 (@I ((_104961 -> Prop) -> Prop) f _50037)). Qed.
Lemma lem4378561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4378562 {_104961 : Type'} (f : type686 _104961) (_50037 : _104961 -> Prop) : (term241 _104961 f _50037) = (term242 _104961 f _50037).
Proof. exact (MK_COMB (@lem4378561) (@lem4378560 _104961 f _50037)). Qed.
Lemma lem4378563 {_104961 : Type'} (_50037 : _104961 -> Prop) (p2 : _104961) : (@I (_104961 -> Prop) _50037 p2) = (@I (_104961 -> Prop) _50037 p2).
Proof. exact (eq_refl (@I (_104961 -> Prop) _50037 p2)). Qed.
Lemma lem4378564 {_104961 : Type'} (f : type686 _104961) (_50037 : _104961 -> Prop) (p2 : _104961) : (term239 _104961 f _50037 p2) = (term243 _104961 f _50037 p2).
Proof. exact (MK_COMB (@lem4378562 _104961 f _50037) (@lem4378563 _104961 _50037 p2)). Qed.
Lemma lem4378565 {_104961 : Type'} (f : type686 _104961) (_50037 : _104961 -> Prop) (p2 : _104961) : (term235 _104961 p2 f _50037) = (term243 _104961 f _50037 p2).
Proof. exact (TRANS (@lem4378557 _104961 f _50037 p2) (@lem4378564 _104961 f _50037 p2)). Qed.
Lemma lem4378568 {_104960 _104961 : Type'} (_50037 : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term243 _104961 f _50037 p2.
Proof. exact (EQ_MP (@lem4378565 _104961 f _50037 p2) (@lem4378554 _104960 _104961 _50037 f s p1 t p2 h1)). Qed.
Lemma lem4378569 {_104960 _104961 : Type'} (_50037 : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term243 _104961 f _50037 p2.
Proof. exact (@lem4378568 _104960 _104961 _50037 f s p1 t p2 h1). Qed.
Lemma lem4378570 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term243 _104961 f t p2.
Proof. exact (@lem4378569 _104960 _104961 t f s p1 t p2 h1). Qed.
Lemma lem4378573 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : @I (_104961 -> Prop) t p2.
Proof. exact (@lem4378570 _104960 _104961 f s p1 t p2 h1 (@lem4378525 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378574 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : term230 _104961 t p2.
Proof. exact (fun h0 : term207 _104961 t p2 => @lem4378573 _104960 _104961 f s p1 t p2 h1). Qed.
Lemma lem4378576 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378577 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term230 _104961 t p2) = (@I (_104961 -> Prop) t p2).
Proof. exact (@lem4378576 (@I (_104961 -> Prop) t p2)). Qed.
Lemma lem4378578 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : @I (_104961 -> Prop) t p2.
Proof. exact (EQ_MP (@lem4378577 _104961 t p2) (@lem4378574 _104960 _104961 f s p1 t p2 h1)). Qed.
Lemma lem4378581 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4378583 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term207 _104961 t p2) = (term232 _104961 t p2).
Proof. exact (@lem4378581 (@I (_104961 -> Prop) t p2)). Qed.
Lemma lem4378586 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) : term232 _104961 t p2.
Proof. exact (EQ_MP (@lem4378583 _104961 t p2) (@lem4378461 _104961 t p2 h1)). Qed.
Lemma lem4378589 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (@lem4378586 _104961 t p2 h1 (@lem4378578 _104960 _104961 f s p1 t p2 h2)). Qed.
Lemma lem4378590 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : term233.
Proof. exact (fun h0 : ~ False => @lem4378589 _104960 _104961 f s p1 t p2 h1 h2). Qed.
Lemma lem4378592 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378593 : term233 = False.
Proof. exact (@lem4378592 False). Qed.
Lemma lem4378594 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378593) (@lem4378590 _104960 _104961 f s p1 t p2 h1 h2)). Qed.
Lemma lem4378596 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) (h1 : f x) : @I ((_104961 -> Prop) -> Prop) f x.
Proof. exact (EQ_MP (@lem4378276 _104961 f x) (@lem4378121 _104961 f x h1)). Qed.
Lemma lem4378597 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) (h1 : f x) : term234 _104961 f x.
Proof. exact (fun h0 : term201 _104961 f x => @lem4378596 _104961 f x h1). Qed.
Lemma lem4378599 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378600 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term234 _104961 f x) = (@I ((_104961 -> Prop) -> Prop) f x).
Proof. exact (@lem4378599 (@I ((_104961 -> Prop) -> Prop) f x)). Qed.
Lemma lem4378601 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) (h1 : f x) : @I ((_104961 -> Prop) -> Prop) f x.
Proof. exact (EQ_MP (@lem4378600 _104961 f x) (@lem4378597 _104961 f x h1)). Qed.
Lemma lem4378607 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4378608 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : (term229 _104960 _104961 f _50038 s p1) = (term244 _104960 _104961 s p1 f _50038).
Proof. exact (@lem4378607 (@I (_104960 -> Prop) s p1) (term201 _104961 f _50038)). Qed.
Lemma lem4378614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378615 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : (term245 _104960 _104961 f _50038 s p1) = (term246 _104960 _104961 s p1 f _50038).
Proof. exact (MK_COMB (@lem4378614) (@lem4378608 _104960 _104961 s p1 f _50038)). Qed.
Lemma lem4378621 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : (term244 _104960 _104961 s p1 f _50038) = (term244 _104960 _104961 s p1 f _50038).
Proof. exact (eq_refl (term244 _104960 _104961 s p1 f _50038)). Qed.
Lemma lem4378622 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : ((term229 _104960 _104961 f _50038 s p1) = (term244 _104960 _104961 s p1 f _50038)) = ((term244 _104960 _104961 s p1 f _50038) = (term244 _104960 _104961 s p1 f _50038)).
Proof. exact (MK_COMB (@lem4378615 _104960 _104961 s p1 f _50038) (@lem4378621 _104960 _104961 s p1 f _50038)). Qed.
Lemma lem4378624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4378625 (x : Prop) : (x = x) = True.
Proof. exact (@lem4378624 Prop x). Qed.
Lemma lem4378626 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : ((term244 _104960 _104961 s p1 f _50038) = (term244 _104960 _104961 s p1 f _50038)) = True.
Proof. exact (@lem4378625 (term244 _104960 _104961 s p1 f _50038)). Qed.
Lemma lem4378627 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : ((term229 _104960 _104961 f _50038 s p1) = (term244 _104960 _104961 s p1 f _50038)) = True.
Proof. exact (TRANS (@lem4378622 _104960 _104961 s p1 f _50038) (@lem4378626 _104960 _104961 s p1 f _50038)). Qed.
Lemma lem4378628 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : True = ((term229 _104960 _104961 f _50038 s p1) = (term244 _104960 _104961 s p1 f _50038)).
Proof. exact (SYM (@lem4378627 _104960 _104961 s p1 f _50038)). Qed.
Lemma lem4378629 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (_50038 : _104961 -> Prop) : (term229 _104960 _104961 f _50038 s p1) = (term244 _104960 _104961 s p1 f _50038).
Proof. exact (EQ_MP (@lem4378628 _104960 _104961 s p1 f _50038) (@lem0)). Qed.
Lemma lem4378630 {_104960 _104961 : Type'} (_50038 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term244 _104960 _104961 s p1 f _50038.
Proof. exact (EQ_MP (@lem4378629 _104960 _104961 s p1 f _50038) (@lem4378471 _104960 _104961 _50038 t f s p1 p2 h1)). Qed.
Lemma lem4378632 (b : Prop) (a : Prop) : (a \/ b) = (term238 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4378633 {_104960 _104961 : Type'} (f : type686 _104961) (_50038 : _104961 -> Prop) (s : _104960 -> Prop) (p1 : _104960) : (term244 _104960 _104961 s p1 f _50038) = (term247 _104960 _104961 f _50038 s p1).
Proof. exact (@lem4378632 (term201 _104961 f _50038) (@I (_104960 -> Prop) s p1)). Qed.
Lemma lem4378635 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4378636 {_104961 : Type'} (f : type686 _104961) (_50038 : _104961 -> Prop) : (term240 _104961 f _50038) = (@I ((_104961 -> Prop) -> Prop) f _50038).
Proof. exact (@lem4378635 (@I ((_104961 -> Prop) -> Prop) f _50038)). Qed.
Lemma lem4378637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4378638 {_104961 : Type'} (f : type686 _104961) (_50038 : _104961 -> Prop) : (term241 _104961 f _50038) = (term242 _104961 f _50038).
Proof. exact (MK_COMB (@lem4378637) (@lem4378636 _104961 f _50038)). Qed.
Lemma lem4378639 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (@I (_104960 -> Prop) s p1) = (@I (_104960 -> Prop) s p1).
Proof. exact (eq_refl (@I (_104960 -> Prop) s p1)). Qed.
Lemma lem4378640 {_104960 _104961 : Type'} (f : type686 _104961) (_50038 : _104961 -> Prop) (s : _104960 -> Prop) (p1 : _104960) : (term247 _104960 _104961 f _50038 s p1) = (term248 _104960 _104961 f _50038 s p1).
Proof. exact (MK_COMB (@lem4378638 _104961 f _50038) (@lem4378639 _104960 s p1)). Qed.
Lemma lem4378641 {_104960 _104961 : Type'} (f : type686 _104961) (_50038 : _104961 -> Prop) (s : _104960 -> Prop) (p1 : _104960) : (term244 _104960 _104961 s p1 f _50038) = (term248 _104960 _104961 f _50038 s p1).
Proof. exact (TRANS (@lem4378633 _104960 _104961 f _50038 s p1) (@lem4378640 _104960 _104961 f _50038 s p1)). Qed.
Lemma lem4378644 {_104960 _104961 : Type'} (_50038 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term248 _104960 _104961 f _50038 s p1.
Proof. exact (EQ_MP (@lem4378641 _104960 _104961 f _50038 s p1) (@lem4378630 _104960 _104961 _50038 t f s p1 p2 h1)). Qed.
Lemma lem4378645 {_104960 _104961 : Type'} (_50038 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term248 _104960 _104961 f _50038 s p1.
Proof. exact (@lem4378644 _104960 _104961 _50038 t f s p1 p2 h1). Qed.
Lemma lem4378646 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term248 _104960 _104961 f x s p1.
Proof. exact (@lem4378645 _104960 _104961 x t f s p1 p2 h1). Qed.
Lemma lem4378649 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : f x) (h2 : term213 _104960 _104961 t f s p1 p2) : @I (_104960 -> Prop) s p1.
Proof. exact (@lem4378646 _104960 _104961 x t f s p1 p2 h2 (@lem4378601 _104961 f x h1)). Qed.
Lemma lem4378650 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : f x) (h2 : term213 _104960 _104961 t f s p1 p2) : term230 _104960 s p1.
Proof. exact (fun h0 : term207 _104960 s p1 => @lem4378649 _104960 _104961 x t f s p1 p2 h1 h2). Qed.
Lemma lem4378652 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378653 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term230 _104960 s p1) = (@I (_104960 -> Prop) s p1).
Proof. exact (@lem4378652 (@I (_104960 -> Prop) s p1)). Qed.
Lemma lem4378654 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : f x) (h2 : term213 _104960 _104961 t f s p1 p2) : @I (_104960 -> Prop) s p1.
Proof. exact (EQ_MP (@lem4378653 _104960 s p1) (@lem4378650 _104960 _104961 x t f s p1 p2 h1 h2)). Qed.
Lemma lem4378657 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4378659 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term207 _104960 s p1) = (term232 _104960 s p1).
Proof. exact (@lem4378657 (@I (_104960 -> Prop) s p1)). Qed.
Lemma lem4378662 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) (h1 : term207 _104960 s p1) : term232 _104960 s p1.
Proof. exact (EQ_MP (@lem4378659 _104960 s p1) (@lem4378465 _104960 s p1 h1)). Qed.
Lemma lem4378665 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (@lem4378662 _104960 s p1 h1 (@lem4378654 _104960 _104961 x t f s p1 p2 h2 h3)). Qed.
Lemma lem4378666 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : term233.
Proof. exact (fun h0 : ~ False => @lem4378665 _104960 _104961 x t f s p1 p2 h1 h2 h3). Qed.
Lemma lem4378668 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378669 : term233 = False.
Proof. exact (@lem4378668 False). Qed.
Lemma lem4378670 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (EQ_MP (@lem4378669) (@lem4378666 _104960 _104961 x t f s p1 p2 h1 h2 h3)). Qed.
Lemma lem4378672 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) (h1 : term209 _104961 f t p2) : @I ((_104961 -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem4378291 _104961 f t p2 h1)). Qed.
Lemma lem4378673 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) (h1 : term209 _104961 f t p2) : term234 _104961 f t.
Proof. exact (fun h0 : term201 _104961 f t => @lem4378672 _104961 f t p2 h1). Qed.
Lemma lem4378675 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378676 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) : (term234 _104961 f t) = (@I ((_104961 -> Prop) -> Prop) f t).
Proof. exact (@lem4378675 (@I ((_104961 -> Prop) -> Prop) f t)). Qed.
Lemma lem4378677 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) (h1 : term209 _104961 f t p2) : @I ((_104961 -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem4378676 _104961 f t) (@lem4378673 _104961 f t p2 h1)). Qed.
Lemma lem4378683 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4378684 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : (term216 _104961 f _50039 p2) = (term235 _104961 p2 f _50039).
Proof. exact (@lem4378683 (@I (_104961 -> Prop) _50039 p2) (term201 _104961 f _50039)). Qed.
Lemma lem4378690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378691 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : (term236 _104961 f _50039 p2) = (term237 _104961 p2 f _50039).
Proof. exact (MK_COMB (@lem4378690) (@lem4378684 _104961 p2 f _50039)). Qed.
Lemma lem4378697 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : (term235 _104961 p2 f _50039) = (term235 _104961 p2 f _50039).
Proof. exact (eq_refl (term235 _104961 p2 f _50039)). Qed.
Lemma lem4378698 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : ((term216 _104961 f _50039 p2) = (term235 _104961 p2 f _50039)) = ((term235 _104961 p2 f _50039) = (term235 _104961 p2 f _50039)).
Proof. exact (MK_COMB (@lem4378691 _104961 p2 f _50039) (@lem4378697 _104961 p2 f _50039)). Qed.
Lemma lem4378700 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4378701 (x : Prop) : (x = x) = True.
Proof. exact (@lem4378700 Prop x). Qed.
Lemma lem4378702 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : ((term235 _104961 p2 f _50039) = (term235 _104961 p2 f _50039)) = True.
Proof. exact (@lem4378701 (term235 _104961 p2 f _50039)). Qed.
Lemma lem4378703 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : ((term216 _104961 f _50039 p2) = (term235 _104961 p2 f _50039)) = True.
Proof. exact (TRANS (@lem4378698 _104961 p2 f _50039) (@lem4378702 _104961 p2 f _50039)). Qed.
Lemma lem4378704 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : True = ((term216 _104961 f _50039 p2) = (term235 _104961 p2 f _50039)).
Proof. exact (SYM (@lem4378703 _104961 p2 f _50039)). Qed.
Lemma lem4378705 {_104961 : Type'} (p2 : _104961) (f : type686 _104961) (_50039 : _104961 -> Prop) : (term216 _104961 f _50039 p2) = (term235 _104961 p2 f _50039).
Proof. exact (EQ_MP (@lem4378704 _104961 p2 f _50039) (@lem0)). Qed.
Lemma lem4378706 {_104960 _104961 : Type'} (_50039 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term235 _104961 p2 f _50039.
Proof. exact (EQ_MP (@lem4378705 _104961 p2 f _50039) (@lem4378495 _104960 _104961 _50039 t f s p1 p2 h1)). Qed.
Lemma lem4378708 (b : Prop) (a : Prop) : (a \/ b) = (term238 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4378709 {_104961 : Type'} (f : type686 _104961) (_50039 : _104961 -> Prop) (p2 : _104961) : (term235 _104961 p2 f _50039) = (term239 _104961 f _50039 p2).
Proof. exact (@lem4378708 (term201 _104961 f _50039) (@I (_104961 -> Prop) _50039 p2)). Qed.
Lemma lem4378711 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4378712 {_104961 : Type'} (f : type686 _104961) (_50039 : _104961 -> Prop) : (term240 _104961 f _50039) = (@I ((_104961 -> Prop) -> Prop) f _50039).
Proof. exact (@lem4378711 (@I ((_104961 -> Prop) -> Prop) f _50039)). Qed.
Lemma lem4378713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4378714 {_104961 : Type'} (f : type686 _104961) (_50039 : _104961 -> Prop) : (term241 _104961 f _50039) = (term242 _104961 f _50039).
Proof. exact (MK_COMB (@lem4378713) (@lem4378712 _104961 f _50039)). Qed.
Lemma lem4378715 {_104961 : Type'} (_50039 : _104961 -> Prop) (p2 : _104961) : (@I (_104961 -> Prop) _50039 p2) = (@I (_104961 -> Prop) _50039 p2).
Proof. exact (eq_refl (@I (_104961 -> Prop) _50039 p2)). Qed.
Lemma lem4378716 {_104961 : Type'} (f : type686 _104961) (_50039 : _104961 -> Prop) (p2 : _104961) : (term239 _104961 f _50039 p2) = (term243 _104961 f _50039 p2).
Proof. exact (MK_COMB (@lem4378714 _104961 f _50039) (@lem4378715 _104961 _50039 p2)). Qed.
Lemma lem4378717 {_104961 : Type'} (f : type686 _104961) (_50039 : _104961 -> Prop) (p2 : _104961) : (term235 _104961 p2 f _50039) = (term243 _104961 f _50039 p2).
Proof. exact (TRANS (@lem4378709 _104961 f _50039 p2) (@lem4378716 _104961 f _50039 p2)). Qed.
Lemma lem4378720 {_104960 _104961 : Type'} (_50039 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term243 _104961 f _50039 p2.
Proof. exact (EQ_MP (@lem4378717 _104961 f _50039 p2) (@lem4378706 _104960 _104961 _50039 t f s p1 p2 h1)). Qed.
Lemma lem4378721 {_104960 _104961 : Type'} (_50039 : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term243 _104961 f _50039 p2.
Proof. exact (@lem4378720 _104960 _104961 _50039 t f s p1 p2 h1). Qed.
Lemma lem4378722 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term213 _104960 _104961 t f s p1 p2) : term243 _104961 f t p2.
Proof. exact (@lem4378721 _104960 _104961 t t f s p1 p2 h1). Qed.
Lemma lem4378725 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term209 _104961 f t p2) (h2 : term213 _104960 _104961 t f s p1 p2) : @I (_104961 -> Prop) t p2.
Proof. exact (@lem4378722 _104960 _104961 t f s p1 p2 h2 (@lem4378677 _104961 f t p2 h1)). Qed.
Lemma lem4378726 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term209 _104961 f t p2) (h2 : term213 _104960 _104961 t f s p1 p2) : term230 _104961 t p2.
Proof. exact (fun h0 : term207 _104961 t p2 => @lem4378725 _104960 _104961 t f s p1 p2 h1 h2). Qed.
Lemma lem4378728 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378729 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term230 _104961 t p2) = (@I (_104961 -> Prop) t p2).
Proof. exact (@lem4378728 (@I (_104961 -> Prop) t p2)). Qed.
Lemma lem4378730 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term209 _104961 f t p2) (h2 : term213 _104960 _104961 t f s p1 p2) : @I (_104961 -> Prop) t p2.
Proof. exact (EQ_MP (@lem4378729 _104961 t p2) (@lem4378726 _104960 _104961 t f s p1 p2 h1 h2)). Qed.
Lemma lem4378733 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4378735 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term207 _104961 t p2) = (term232 _104961 t p2).
Proof. exact (@lem4378733 (@I (_104961 -> Prop) t p2)). Qed.
Lemma lem4378738 {_104961 : Type'} (f : type686 _104961) (t : _104961 -> Prop) (p2 : _104961) (h1 : term209 _104961 f t p2) : term232 _104961 t p2.
Proof. exact (EQ_MP (@lem4378735 _104961 t p2) (@lem4378483 _104961 f t p2 h1)). Qed.
Lemma lem4378741 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term209 _104961 f t p2) (h2 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (@lem4378738 _104961 f t p2 h1 (@lem4378730 _104960 _104961 t f s p1 p2 h1 h2)). Qed.
Lemma lem4378742 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term209 _104961 f t p2) (h2 : term213 _104960 _104961 t f s p1 p2) : term233.
Proof. exact (fun h0 : ~ False => @lem4378741 _104960 _104961 t f s p1 p2 h1 h2). Qed.
Lemma lem4378744 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4378745 : term233 = False.
Proof. exact (@lem4378744 False). Qed.
Lemma lem4378746 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term209 _104961 f t p2) (h2 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (EQ_MP (@lem4378745) (@lem4378742 _104960 _104961 t f s p1 p2 h1 h2)). Qed.
Lemma lem4378747 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : (term207 _104960 s p1) = False.
Proof. exact (prop_ext (fun h4 : term207 _104960 s p1 => @lem4378670 _104960 _104961 x t f s p1 p2 h1 h2 h3) (fun h4 : False => @lem4378465 _104960 s p1 h1)). Qed.
Lemma lem4378748 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (EQ_MP (@lem4378747 _104960 _104961 x t f s p1 p2 h1 h2 h3) (@lem4378465 _104960 s p1 h1)). Qed.
Lemma lem4378749 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : (term207 _104961 t p2) = False.
Proof. exact (prop_ext (fun h3 : term207 _104961 t p2 => @lem4378594 _104960 _104961 f s p1 t p2 h1 h2) (fun h3 : False => @lem4378461 _104961 t p2 h1)). Qed.
Lemma lem4378750 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378749 _104960 _104961 f s p1 t p2 h1 h2) (@lem4378461 _104961 t p2 h1)). Qed.
Lemma lem4378751 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : (term207 _104960 s p1) = False.
Proof. exact (prop_ext (fun h3 : term207 _104960 s p1 => @lem4378518 _104960 _104961 f s p1 t p2 h1 h2) (fun h3 : False => @lem4378447 _104960 s p1 h1)). Qed.
Lemma lem4378752 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378751 _104960 _104961 f s p1 t p2 h1 h2) (@lem4378447 _104960 s p1 h1)). Qed.
Lemma lem4378753 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : (term207 _104960 s p1) = False.
Proof. exact (prop_ext (fun h4 : term207 _104960 s p1 => @lem4378748 _104960 _104961 x t f s p1 p2 h1 h2 h3) (fun h4 : False => @lem4378382 _104960 s p1 h1)). Qed.
Lemma lem4378754 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (EQ_MP (@lem4378753 _104960 _104961 x t f s p1 p2 h1 h2 h3) (@lem4378382 _104960 s p1 h1)). Qed.
Lemma lem4378755 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : (term207 _104961 t p2) = False.
Proof. exact (prop_ext (fun h3 : term207 _104961 t p2 => @lem4378750 _104960 _104961 f s p1 t p2 h1 h2) (fun h3 : False => @lem4378351 _104961 t p2 h1)). Qed.
Lemma lem4378756 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378755 _104960 _104961 f s p1 t p2 h1 h2) (@lem4378351 _104961 t p2 h1)). Qed.
Lemma lem4378757 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : (term207 _104960 s p1) = False.
Proof. exact (prop_ext (fun h3 : term207 _104960 s p1 => @lem4378752 _104960 _104961 f s p1 t p2 h1 h2) (fun h3 : False => @lem4378322 _104960 s p1 h1)). Qed.
Lemma lem4378758 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378757 _104960 _104961 f s p1 t p2 h1 h2) (@lem4378322 _104960 s p1 h1)). Qed.
Lemma lem4378759 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : (term207 _104960 s p1) = False.
Proof. exact (prop_ext (fun h4 : term207 _104960 s p1 => @lem4378754 _104960 _104961 x t f s p1 p2 h1 h2 h3) (fun h4 : False => @lem4378382 _104960 s p1 h1)). Qed.
Lemma lem4378760 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : f x) (h3 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (EQ_MP (@lem4378759 _104960 _104961 x t f s p1 p2 h1 h2 h3) (@lem4378382 _104960 s p1 h1)). Qed.
Lemma lem4378761 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : (term207 _104961 t p2) = False.
Proof. exact (prop_ext (fun h3 : term207 _104961 t p2 => @lem4378756 _104960 _104961 f s p1 t p2 h1 h2) (fun h3 : False => @lem4378351 _104961 t p2 h1)). Qed.
Lemma lem4378762 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104961 t p2) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378761 _104960 _104961 f s p1 t p2 h1 h2) (@lem4378351 _104961 t p2 h1)). Qed.
Lemma lem4378763 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : (term207 _104960 s p1) = False.
Proof. exact (prop_ext (fun h3 : term207 _104960 s p1 => @lem4378758 _104960 _104961 f s p1 t p2 h1 h2) (fun h3 : False => @lem4378322 _104960 s p1 h1)). Qed.
Lemma lem4378764 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term207 _104960 s p1) (h2 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4378763 _104960 _104961 f s p1 t p2 h1 h2) (@lem4378322 _104960 s p1 h1)). Qed.
Lemma lem4378765 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : f x) (h2 : term213 _104960 _104961 t f s p1 p2) : False.
Proof. exact (or_elim (@lem4378289 _104960 _104961 t f s p1 p2 h2) (fun h0 : term207 _104960 s p1 => @lem4378760 _104960 _104961 x t f s p1 p2 h0 h1 h2) (fun h0 : term209 _104961 f t p2 => @lem4378746 _104960 _104961 t f s p1 p2 h0 h2)). Qed.
Lemma lem4378766 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (t : _104961 -> Prop) (p2 : _104961) (h1 : term221 _104960 _104961 f s p1 t p2) : False.
Proof. exact (or_elim (@lem4378282 _104960 _104961 f s p1 t p2 h1) (fun h0 : term207 _104960 s p1 => @lem4378764 _104960 _104961 f s p1 t p2 h0 h1) (fun h0 : term207 _104961 t p2 => @lem4378762 _104960 _104961 f s p1 t p2 h0 h1)). Qed.
Lemma lem4378767 {_104960 _104961 : Type'} (x : _104961 -> Prop) (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : f x) (h2 : term195 _104960 _104961 t f s p1 p2) : False.
Proof. exact (or_elim (@lem4378269 _104960 _104961 t f s p1 p2 h2) (fun h0 : term221 _104960 _104961 f s p1 t p2 => @lem4378766 _104960 _104961 f s p1 t p2 h0) (fun h0 : term213 _104960 _104961 t f s p1 p2 => @lem4378765 _104960 _104961 x t f s p1 p2 h1 h0)). Qed.
Lemma lem4378768 {_104960 _104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term16 _104961 f) (h2 : term195 _104960 _104961 t f s p1 p2) : False.
Proof. exact (ex_elim (@lem4377778 _104961 f h1) (fun x : _104961 -> Prop => fun h0 : term74 _104961 f x => @lem4378767 _104960 _104961 x t f s p1 p2 h0 h2)). Qed.
Lemma lem4378769 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term16 _104961 f) (h2 : term66 _104960 _104961 f s p1 p2) : False.
Proof. exact (ex_elim (@lem4378119 _104960 _104961 f s p1 p2 h2) (fun t : _104961 -> Prop => fun h0 : term197 _104960 _104961 f s p1 p2 t => @lem4378768 _104960 _104961 t f s p1 p2 h1 h0)). Qed.
Lemma lem4378770 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term16 _104961 f) (h2 : term66 _104960 _104961 f s p1 p2) : (term66 _104960 _104961 f s p1 p2) = False.
Proof. exact (prop_ext (fun h3 : term66 _104960 _104961 f s p1 p2 => @lem4378769 _104960 _104961 f s p1 p2 h1 h2) (fun h3 : False => @lem4377756 _104960 _104961 f s p1 p2 h2)). Qed.
Lemma lem4378771 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (h1 : term16 _104961 f) (h2 : term66 _104960 _104961 f s p1 p2) : False.
Proof. exact (EQ_MP (@lem4378770 _104960 _104961 f s p1 p2 h1 h2) (@lem4377756 _104960 _104961 f s p1 p2 h2)). Qed.
Lemma lem4378772 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (f : type686 _104961) (h1 : term16 _104961 f) : term65 _104960 _104961 f s p1 p2.
Proof. exact (fun h0 : term66 _104960 _104961 f s p1 p2 => @lem4378771 _104960 _104961 f s p1 p2 h1 h0). Qed.
Lemma lem4378773 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) (f : type686 _104961) (h1 : term16 _104961 f) : (term30 _104960 _104961 s p1 f p2) = (term40 _104960 _104961 f s p1 p2).
Proof. exact (EQ_MP (@lem4377755 _104960 _104961 f s p1 p2) (@lem4378772 _104960 _104961 s p1 p2 f h1)). Qed.
Lemma lem4378778 {_104960 _104961 : Type'} (s : _104960 -> Prop) (p1 : _104960) (f : type686 _104961) (h1 : term16 _104961 f) : term44 _104960 _104961 f s p1.
Proof. exact (fun p2 : _104961 => @lem4378773 _104960 _104961 s p1 p2 f h1). Qed.
Lemma lem4378783 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : term16 _104961 f) : term47 _104960 _104961 f s.
Proof. exact (fun p1 : _104960 => @lem4378778 _104960 _104961 s p1 f h1). Qed.
Lemma lem4378784 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term48 _104960 _104961 f s.
Proof. exact (fun h0 : term16 _104961 f => @lem4378783 _104960 _104961 s f h0). Qed.
Lemma lem4378789 {_104960 _104961 : Type'} (s : _104960 -> Prop) : term60 _104960 _104961 s.
Proof. exact (fun f : type686 _104961 => @lem4378784 _104960 _104961 f s). Qed.
Lemma lem4378794 {_104960 _104961 : Type'} : term64 _104960 _104961.
Proof. exact (fun s : _104960 -> Prop => @lem4378789 _104960 _104961 s). Qed.
Lemma lem4378795 {_104960 _104961 : Type'} : term63 _104960 _104961.
Proof. exact (EQ_MP (@lem4377750 _104960 _104961) (@lem4378794 _104960 _104961)). Qed.
Lemma lem4378796 {_104960 _104961 : Type'} (s : _104960 -> Prop) : term249 _104960 _104961 s.
Proof. exact (@lem4378795 _104960 _104961 s). Qed.
Lemma lem4378797 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term249 _104960 _104961 s) = (term59 _104960 _104961 s).
Proof. exact (eq_refl (term249 _104960 _104961 s)). Qed.
Lemma lem4378798 {_104960 _104961 : Type'} (s : _104960 -> Prop) : term59 _104960 _104961 s.
Proof. exact (EQ_MP (@lem4378797 _104960 _104961 s) (@lem4378796 _104960 _104961 s)). Qed.
Lemma lem4378799 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) : term250 _104960 _104961 s f.
Proof. exact (@lem4378798 _104960 _104961 s f). Qed.
Lemma lem4378800 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term250 _104960 _104961 s f) = (term50 _104960 _104961 f s).
Proof. exact (eq_refl (term250 _104960 _104961 s f)). Qed.
Lemma lem4378801 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term50 _104960 _104961 f s.
Proof. exact (EQ_MP (@lem4378800 _104960 _104961 f s) (@lem4378799 _104960 _104961 s f)). Qed.
Lemma lem4378803 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term50 _104960 _104961 f s.
Proof. exact (@lem4377581 _104960 _104961 f s (@lem4378801 _104960 _104961 f s)). Qed.
Lemma lem4378804 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term51 _104960 _104961 f s) : False.
Proof. exact (@lem4378803 _104960 _104961 f s (@lem4377565 _104960 _104961 f s h1)). Qed.
Lemma lem4378805 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term51 _104960 _104961 f s) : (term51 _104960 _104961 f s) = False.
Proof. exact (prop_ext (fun h2 : term51 _104960 _104961 f s => @lem4378804 _104960 _104961 f s h1) (fun h2 : False => @lem4377565 _104960 _104961 f s h1)). Qed.
Lemma lem4378806 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (h1 : term51 _104960 _104961 f s) : False.
Proof. exact (EQ_MP (@lem4378805 _104960 _104961 f s h1) (@lem4377565 _104960 _104961 f s h1)). Qed.
Lemma lem4378807 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term50 _104960 _104961 f s.
Proof. exact (fun h0 : term51 _104960 _104961 f s => @lem4378806 _104960 _104961 f s h0). Qed.
Lemma lem4378808 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term48 _104960 _104961 f s.
Proof. exact (EQ_MP (@lem4377564 _104960 _104961 f s) (@lem4378807 _104960 _104961 f s)). Qed.
Lemma lem4378809 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term9 _104960 _104961 f s.
Proof. exact (EQ_MP (@lem4377560 _104960 _104961 f s) (@lem4378808 _104960 _104961 f s)). Qed.
Lemma lem4378810 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term8 _104960 _104961 f s.
Proof. exact (EQ_MP (@lem4377415 _104960 _104961 f s) (@lem4378809 _104960 _104961 f s)). Qed.
Lemma lem4378811 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : term3 _104961 f) : term7 _104960 _104961 f s.
Proof. exact (@lem4378810 _104960 _104961 f s (@lem4372346 _104961 f h1)). Qed.
