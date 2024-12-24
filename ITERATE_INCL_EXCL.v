Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_INCL_EXCL_term_abbrevs.
Require Import FINITE_DIFF_spec.
Require Import FINITE_INTER_spec.
Require Import FINITE_UNION_spec.
Require Import ITERATE_UNION_spec.
Require Import MONOIDAL_AC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem5773319 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem5773320 {_120849 : Type'} (s : _120849 -> Prop) (t : _120849 -> Prop) : (@DISJOINT _120849 s t) = ((@INTER _120849 s t) = (@EMPTY _120849)).
Proof. exact (@lem5773319 _120849 s t). Qed.
Lemma lem5773321 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term0 _120849 s s') = ((term1 _120849 s s') = (@EMPTY _120849)).
Proof. exact (@lem5773320 _120849 (@DIFF _120849 s s') (@INTER _120849 s s')). Qed.
Lemma lem5773325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5773326 {_120849 : Type'} (s : _120849 -> Prop) (t : _120849 -> Prop) : (s = t) = (term2 _120849 s t).
Proof. exact (@lem5773325 _120849 s t). Qed.
Lemma lem5773327 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : ((term1 _120849 s s') = (@EMPTY _120849)) = (term3 _120849 s s').
Proof. exact (@lem5773326 _120849 (term1 _120849 s s') (@EMPTY _120849)). Qed.
Lemma lem5773332 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term0 _120849 s s') = (term3 _120849 s s').
Proof. exact (TRANS (@lem5773321 _120849 s s') (@lem5773327 _120849 s s')). Qed.
Lemma lem5773337 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term3 _120849 s s') = (term0 _120849 s s').
Proof. exact (SYM (@lem5773332 _120849 s s')). Qed.
Lemma lem5773345 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5773346 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) (t : _120849 -> Prop) : (term4 _120849 x s t) = (term5 _120849 s x t).
Proof. exact (@lem5773345 _120849 s x t). Qed.
Lemma lem5773347 {_120849 : Type'} (x : _120849) (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term6 _120849 x s s') = (term7 _120849 x s s').
Proof. exact (@lem5773346 _120849 (@DIFF _120849 s s') x (@INTER _120849 s s')). Qed.
Lemma lem5773351 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5773352 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) (t : _120849 -> Prop) : (term8 _120849 x s t) = (term9 _120849 s x t).
Proof. exact (@lem5773351 _120849 s x t). Qed.
Lemma lem5773353 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) (s' : _120849 -> Prop) : (term8 _120849 x s s') = (term9 _120849 s x s').
Proof. exact (@lem5773352 _120849 s x s'). Qed.
Lemma lem5773357 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773358 {_120849 : Type'} (P : _120849 -> Prop) (x : _120849) : (@IN _120849 x P) = (P x).
Proof. exact (@lem5773357 _120849 P x). Qed.
Lemma lem5773359 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) : (@IN _120849 x s) = (s x).
Proof. exact (@lem5773358 _120849 s x). Qed.
Lemma lem5773360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773361 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) : (term10 _120849 x s) = (term11 _120849 s x).
Proof. exact (MK_COMB (@lem5773360) (@lem5773359 _120849 s x)). Qed.
Lemma lem5773363 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773364 {_120849 : Type'} (P : _120849 -> Prop) (x : _120849) : (@IN _120849 x P) = (P x).
Proof. exact (@lem5773363 _120849 P x). Qed.
Lemma lem5773365 {_120849 : Type'} (s' : _120849 -> Prop) (x : _120849) : (@IN _120849 x s') = (s' x).
Proof. exact (@lem5773364 _120849 s' x). Qed.
Lemma lem5773366 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5773367 {_120849 : Type'} (s' : _120849 -> Prop) (x : _120849) : (term12 _120849 x s') = (term13 _120849 s' x).
Proof. exact (MK_COMB (@lem5773366) (@lem5773365 _120849 s' x)). Qed.
Lemma lem5773368 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term9 _120849 s x s') = (term14 _120849 s s' x).
Proof. exact (MK_COMB (@lem5773361 _120849 s x) (@lem5773367 _120849 s' x)). Qed.
Lemma lem5773371 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term8 _120849 x s s') = (term14 _120849 s s' x).
Proof. exact (TRANS (@lem5773353 _120849 s x s') (@lem5773368 _120849 s s' x)). Qed.
Lemma lem5773372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773373 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term15 _120849 x s s') = (term16 _120849 s s' x).
Proof. exact (MK_COMB (@lem5773372) (@lem5773371 _120849 s s' x)). Qed.
Lemma lem5773375 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5773376 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) (t : _120849 -> Prop) : (term4 _120849 x s t) = (term5 _120849 s x t).
Proof. exact (@lem5773375 _120849 s x t). Qed.
Lemma lem5773377 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) (s' : _120849 -> Prop) : (term4 _120849 x s s') = (term5 _120849 s x s').
Proof. exact (@lem5773376 _120849 s x s'). Qed.
Lemma lem5773381 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773382 {_120849 : Type'} (P : _120849 -> Prop) (x : _120849) : (@IN _120849 x P) = (P x).
Proof. exact (@lem5773381 _120849 P x). Qed.
Lemma lem5773383 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) : (@IN _120849 x s) = (s x).
Proof. exact (@lem5773382 _120849 s x). Qed.
Lemma lem5773384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773385 {_120849 : Type'} (s : _120849 -> Prop) (x : _120849) : (term10 _120849 x s) = (term11 _120849 s x).
Proof. exact (MK_COMB (@lem5773384) (@lem5773383 _120849 s x)). Qed.
Lemma lem5773387 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773388 {_120849 : Type'} (P : _120849 -> Prop) (x : _120849) : (@IN _120849 x P) = (P x).
Proof. exact (@lem5773387 _120849 P x). Qed.
Lemma lem5773389 {_120849 : Type'} (s' : _120849 -> Prop) (x : _120849) : (@IN _120849 x s') = (s' x).
Proof. exact (@lem5773388 _120849 s' x). Qed.
Lemma lem5773390 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term5 _120849 s x s') = (term17 _120849 s s' x).
Proof. exact (MK_COMB (@lem5773385 _120849 s x) (@lem5773389 _120849 s' x)). Qed.
Lemma lem5773393 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term4 _120849 x s s') = (term17 _120849 s s' x).
Proof. exact (TRANS (@lem5773377 _120849 s x s') (@lem5773390 _120849 s s' x)). Qed.
Lemma lem5773394 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term7 _120849 x s s') = (term18 _120849 s s' x).
Proof. exact (MK_COMB (@lem5773373 _120849 s s' x) (@lem5773393 _120849 s s' x)). Qed.
Lemma lem5773397 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term6 _120849 x s s') = (term18 _120849 s s' x).
Proof. exact (TRANS (@lem5773347 _120849 x s s') (@lem5773394 _120849 s s' x)). Qed.
Lemma lem5773398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5773399 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term19 _120849 x s s') = (term20 _120849 s s' x).
Proof. exact (MK_COMB (@lem5773398) (@lem5773397 _120849 s s' x)). Qed.
Lemma lem5773401 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5773402 {_120849 : Type'} (x : _120849) : (@IN _120849 x (@EMPTY _120849)) = False.
Proof. exact (@lem5773401 _120849 x). Qed.
Lemma lem5773403 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : ((term6 _120849 x s s') = (@IN _120849 x (@EMPTY _120849))) = ((term18 _120849 s s' x) = False).
Proof. exact (MK_COMB (@lem5773399 _120849 s s' x) (@lem5773402 _120849 x)). Qed.
Lemma lem5773405 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5773406 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : ((term18 _120849 s s' x) = False) = (term21 _120849 s s' x).
Proof. exact (@lem5773405 (term18 _120849 s s' x)). Qed.
Lemma lem5773413 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : ((term6 _120849 x s s') = (@IN _120849 x (@EMPTY _120849))) = (term21 _120849 s s' x).
Proof. exact (TRANS (@lem5773403 _120849 s s' x) (@lem5773406 _120849 s s' x)). Qed.
Lemma lem5773414 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term22 _120849 s s') = (term23 _120849 s s').
Proof. exact (fun_ext (fun x : _120849 => @lem5773413 _120849 s s' x)). Qed.
Lemma lem5773415 {_120849 : Type'} : (@all _120849) = (@all _120849).
Proof. exact (eq_refl (@all _120849)). Qed.
Lemma lem5773416 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term3 _120849 s s') = (term24 _120849 s s').
Proof. exact (MK_COMB (@lem5773415 _120849) (@lem5773414 _120849 s s')). Qed.
Lemma lem5773421 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term24 _120849 s s') = (term3 _120849 s s').
Proof. exact (SYM (@lem5773416 _120849 s s')). Qed.
Lemma lem5773423 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5773424 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term24 _120849 s s') = (term26 _120849 s s').
Proof. exact (@lem5773423 (term24 _120849 s s')). Qed.
Lemma lem5773425 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term26 _120849 s s') = (term24 _120849 s s').
Proof. exact (SYM (@lem5773424 _120849 s s')). Qed.
Lemma lem5773426 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term27 _120849 s s') : term27 _120849 s s'.
Proof. exact (h1). Qed.
Lemma lem5773429 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term26 _120849 s s') : term26 _120849 s s'.
Proof. exact (h1). Qed.
Lemma lem5773430 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term28 _120849 s s'.
Proof. exact (fun h0 : term26 _120849 s s' => @lem5773429 _120849 s s' h0). Qed.
Lemma lem5773431 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term28 _120849 s s') : term28 _120849 s s'.
Proof. exact (h1). Qed.
Lemma lem5773432 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term26 _120849 s s') : term26 _120849 s s'.
Proof. exact (h1). Qed.
Lemma lem5773433 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term26 _120849 s s') (h2 : term28 _120849 s s') : term26 _120849 s s'.
Proof. exact (@lem5773431 _120849 s s' h2 (@lem5773432 _120849 s s' h1)). Qed.
Lemma lem5773434 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term26 _120849 s s') : term29 _120849 s s'.
Proof. exact (fun h0 : term28 _120849 s s' => @lem5773433 _120849 s s' h1 h0). Qed.
Lemma lem5773435 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term28 _120849 s s') : term28 _120849 s s'.
Proof. exact (h1). Qed.
Lemma lem5773436 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term26 _120849 s s') (h2 : term28 _120849 s s') : term26 _120849 s s'.
Proof. exact (@lem5773434 _120849 s s' h1 (@lem5773435 _120849 s s' h2)). Qed.
Lemma lem5773437 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term28 _120849 s s') : term28 _120849 s s'.
Proof. exact (fun h0 : term26 _120849 s s' => @lem5773436 _120849 s s' h0 h1). Qed.
Lemma lem5773438 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term30 _120849 s s'.
Proof. exact (fun h0 : term28 _120849 s s' => @lem5773437 _120849 s s' h0). Qed.
Lemma lem5773441 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term28 _120849 s s'.
Proof. exact (@lem5773438 _120849 s s' (@lem5773430 _120849 s s')). Qed.
Lemma lem5773442 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term28 _120849 s s'.
Proof. exact (@lem5773441 _120849 s s'). Qed.
Lemma lem5773452 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5773453 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term26 _120849 s s') = (term31 _120849 s s').
Proof. exact (@lem5773452 (term27 _120849 s s')). Qed.
Lemma lem5773455 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5773456 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term31 _120849 s s') = (term24 _120849 s s').
Proof. exact (@lem5773455 (term24 _120849 s s')). Qed.
Lemma lem5773461 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term26 _120849 s s') = (term24 _120849 s s').
Proof. exact (TRANS (@lem5773453 _120849 s s') (@lem5773456 _120849 s s')). Qed.
Lemma lem5773468 {_120849 : Type'} (s' : _120849 -> Prop) : (term33 _120849 s') = (term34 _120849 s').
Proof. exact (fun_ext (fun s : _120849 -> Prop => @lem5773461 _120849 s s')). Qed.
Lemma lem5773469 {_120849 : Type'} : (@all (_120849 -> Prop)) = (@all (_120849 -> Prop)).
Proof. exact (eq_refl (@all (_120849 -> Prop))). Qed.
Lemma lem5773470 {_120849 : Type'} (s' : _120849 -> Prop) : (term35 _120849 s') = (term36 _120849 s').
Proof. exact (MK_COMB (@lem5773469 _120849) (@lem5773468 _120849 s')). Qed.
Lemma lem5773475 {_120849 : Type'} : (term37 _120849) = (term38 _120849).
Proof. exact (fun_ext (fun s' : _120849 -> Prop => @lem5773470 _120849 s')). Qed.
Lemma lem5773476 {_120849 : Type'} : (@all (_120849 -> Prop)) = (@all (_120849 -> Prop)).
Proof. exact (eq_refl (@all (_120849 -> Prop))). Qed.
Lemma lem5773485 {_120849 : Type'} : (term39 _120849) = (term40 _120849).
Proof. exact (MK_COMB (@lem5773476 _120849) (@lem5773475 _120849)). Qed.
Lemma lem5773502 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term21 _120849 s s' x) = (term21 _120849 s s' x).
Proof. exact (eq_refl (term21 _120849 s s' x)). Qed.
Lemma lem5773503 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term23 _120849 s s') = (term23 _120849 s s').
Proof. exact (fun_ext (fun x : _120849 => @lem5773502 _120849 s s' x)). Qed.
Lemma lem5773504 {_120849 : Type'} : (@all _120849) = (@all _120849).
Proof. exact (eq_refl (@all _120849)). Qed.
Lemma lem5773505 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term24 _120849 s s') = (term24 _120849 s s').
Proof. exact (MK_COMB (@lem5773504 _120849) (@lem5773503 _120849 s s')). Qed.
Lemma lem5773506 {_120849 : Type'} (s' : _120849 -> Prop) : (term34 _120849 s') = (term34 _120849 s').
Proof. exact (fun_ext (fun s : _120849 -> Prop => @lem5773505 _120849 s s')). Qed.
Lemma lem5773507 {_120849 : Type'} : (@all (_120849 -> Prop)) = (@all (_120849 -> Prop)).
Proof. exact (eq_refl (@all (_120849 -> Prop))). Qed.
Lemma lem5773508 {_120849 : Type'} (s' : _120849 -> Prop) : (term36 _120849 s') = (term36 _120849 s').
Proof. exact (MK_COMB (@lem5773507 _120849) (@lem5773506 _120849 s')). Qed.
Lemma lem5773509 {_120849 : Type'} : (term38 _120849) = (term38 _120849).
Proof. exact (fun_ext (fun s' : _120849 -> Prop => @lem5773508 _120849 s')). Qed.
Lemma lem5773510 {_120849 : Type'} : (@all (_120849 -> Prop)) = (@all (_120849 -> Prop)).
Proof. exact (eq_refl (@all (_120849 -> Prop))). Qed.
Lemma lem5773511 {_120849 : Type'} : (term40 _120849) = (term40 _120849).
Proof. exact (MK_COMB (@lem5773510 _120849) (@lem5773509 _120849)). Qed.
Lemma lem5773538 {_120849 : Type'} : (term39 _120849) = (term40 _120849).
Proof. exact (TRANS (@lem5773485 _120849) (@lem5773511 _120849)). Qed.
Lemma lem5773539 {_120849 : Type'} : (term40 _120849) = (term39 _120849).
Proof. exact (SYM (@lem5773538 _120849)). Qed.
Lemma lem5773558 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term18 _120849 s s' x.
Proof. exact (h1). Qed.
Lemma lem5773582 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term18 _120849 s s' x.
Proof. exact (h1). Qed.
Lemma lem5773583 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term17 _120849 s s' x.
Proof. exact (proj2 (@lem5773582 _120849 s s' x h1)). Qed.
Lemma lem5773584 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term14 _120849 s s' x.
Proof. exact (proj1 (@lem5773582 _120849 s s' x h1)). Qed.
Lemma lem5773612 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term13 _120849 s' x.
Proof. exact (proj2 (@lem5773584 _120849 s s' x h1)). Qed.
Lemma lem5773614 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : s' x.
Proof. exact (proj2 (@lem5773583 _120849 s s' x h1)). Qed.
Lemma lem5773615 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term41 _120849 s' x.
Proof. exact (fun h0 : term13 _120849 s' x => @lem5773614 _120849 s s' x h1). Qed.
Lemma lem5773617 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5773618 {_120849 : Type'} (s' : _120849 -> Prop) (x : _120849) : (term41 _120849 s' x) = (s' x).
Proof. exact (@lem5773617 (s' x)). Qed.
Lemma lem5773619 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : s' x.
Proof. exact (EQ_MP (@lem5773618 _120849 s' x) (@lem5773615 _120849 s s' x h1)). Qed.
Lemma lem5773622 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5773624 {_120849 : Type'} (s' : _120849 -> Prop) (x : _120849) : (term13 _120849 s' x) = (term43 _120849 s' x).
Proof. exact (@lem5773622 (s' x)). Qed.
Lemma lem5773627 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term43 _120849 s' x.
Proof. exact (EQ_MP (@lem5773624 _120849 s' x) (@lem5773612 _120849 s s' x h1)). Qed.
Lemma lem5773630 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : False.
Proof. exact (@lem5773627 _120849 s s' x h1 (@lem5773619 _120849 s s' x h1)). Qed.
Lemma lem5773631 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : term44.
Proof. exact (fun h0 : ~ False => @lem5773630 _120849 s s' x h1). Qed.
Lemma lem5773633 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5773634 : term44 = False.
Proof. exact (@lem5773633 False). Qed.
Lemma lem5773635 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : False.
Proof. exact (EQ_MP (@lem5773634) (@lem5773631 _120849 s s' x h1)). Qed.
Lemma lem5773636 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : (term18 _120849 s s' x) = False.
Proof. exact (prop_ext (fun h2 : term18 _120849 s s' x => @lem5773635 _120849 s s' x h1) (fun h2 : False => @lem5773582 _120849 s s' x h1)). Qed.
Lemma lem5773637 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : False.
Proof. exact (EQ_MP (@lem5773636 _120849 s s' x h1) (@lem5773582 _120849 s s' x h1)). Qed.
Lemma lem5773638 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : (term18 _120849 s s' x) = False.
Proof. exact (prop_ext (fun h2 : term18 _120849 s s' x => @lem5773637 _120849 s s' x h1) (fun h2 : False => @lem5773558 _120849 s s' x h1)). Qed.
Lemma lem5773639 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) (h1 : term18 _120849 s s' x) : False.
Proof. exact (EQ_MP (@lem5773638 _120849 s s' x h1) (@lem5773558 _120849 s s' x h1)). Qed.
Lemma lem5773640 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : term45 _120849 s s' x.
Proof. exact (fun h0 : term18 _120849 s s' x => @lem5773639 _120849 s s' x h0). Qed.
Lemma lem5773641 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : (term45 _120849 s s' x) = (term21 _120849 s s' x).
Proof. exact (@lem69 (term18 _120849 s s' x)). Qed.
Lemma lem5773642 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (x : _120849) : term21 _120849 s s' x.
Proof. exact (EQ_MP (@lem5773641 _120849 s s' x) (@lem5773640 _120849 s s' x)). Qed.
Lemma lem5773647 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term24 _120849 s s'.
Proof. exact (fun x : _120849 => @lem5773642 _120849 s s' x). Qed.
Lemma lem5773652 {_120849 : Type'} (s' : _120849 -> Prop) : term36 _120849 s'.
Proof. exact (fun s : _120849 -> Prop => @lem5773647 _120849 s s'). Qed.
Lemma lem5773657 {_120849 : Type'} : term40 _120849.
Proof. exact (fun s' : _120849 -> Prop => @lem5773652 _120849 s'). Qed.
Lemma lem5773658 {_120849 : Type'} : term39 _120849.
Proof. exact (EQ_MP (@lem5773539 _120849) (@lem5773657 _120849)). Qed.
Lemma lem5773659 {_120849 : Type'} (s' : _120849 -> Prop) : term46 _120849 s'.
Proof. exact (@lem5773658 _120849 s'). Qed.
Lemma lem5773660 {_120849 : Type'} (s' : _120849 -> Prop) : (term46 _120849 s') = (term35 _120849 s').
Proof. exact (eq_refl (term46 _120849 s')). Qed.
Lemma lem5773661 {_120849 : Type'} (s' : _120849 -> Prop) : term35 _120849 s'.
Proof. exact (EQ_MP (@lem5773660 _120849 s') (@lem5773659 _120849 s')). Qed.
Lemma lem5773662 {_120849 : Type'} (s' : _120849 -> Prop) (s : _120849 -> Prop) : term47 _120849 s' s.
Proof. exact (@lem5773661 _120849 s' s). Qed.
Lemma lem5773663 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term47 _120849 s' s) = (term26 _120849 s s').
Proof. exact (eq_refl (term47 _120849 s' s)). Qed.
Lemma lem5773664 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term26 _120849 s s'.
Proof. exact (EQ_MP (@lem5773663 _120849 s s') (@lem5773662 _120849 s' s)). Qed.
Lemma lem5773666 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term26 _120849 s s'.
Proof. exact (@lem5773442 _120849 s s' (@lem5773664 _120849 s s')). Qed.
Lemma lem5773667 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term27 _120849 s s') : False.
Proof. exact (@lem5773666 _120849 s s' (@lem5773426 _120849 s s' h1)). Qed.
Lemma lem5773668 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term27 _120849 s s') : (term27 _120849 s s') = False.
Proof. exact (prop_ext (fun h2 : term27 _120849 s s' => @lem5773667 _120849 s s' h1) (fun h2 : False => @lem5773426 _120849 s s' h1)). Qed.
Lemma lem5773669 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) (h1 : term27 _120849 s s') : False.
Proof. exact (EQ_MP (@lem5773668 _120849 s s' h1) (@lem5773426 _120849 s s' h1)). Qed.
Lemma lem5773670 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term26 _120849 s s'.
Proof. exact (fun h0 : term27 _120849 s s' => @lem5773669 _120849 s s' h0). Qed.
Lemma lem5773671 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term24 _120849 s s'.
Proof. exact (EQ_MP (@lem5773425 _120849 s s') (@lem5773670 _120849 s s')). Qed.
Lemma lem5773672 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term3 _120849 s s'.
Proof. exact (EQ_MP (@lem5773421 _120849 s s') (@lem5773671 _120849 s s')). Qed.
Lemma lem5773673 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : term0 _120849 s s'.
Proof. exact (EQ_MP (@lem5773337 _120849 s s') (@lem5773672 _120849 s s')). Qed.
Lemma lem5773685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem5773686 {_120859 : Type'} (s : _120859 -> Prop) (t : _120859 -> Prop) : (@DISJOINT _120859 s t) = ((@INTER _120859 s t) = (@EMPTY _120859)).
Proof. exact (@lem5773685 _120859 s t). Qed.
Lemma lem5773687 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term48 _120859 s' s) = ((term49 _120859 s' s) = (@EMPTY _120859)).
Proof. exact (@lem5773686 _120859 (@DIFF _120859 s s') (@INTER _120859 s' s)). Qed.
Lemma lem5773691 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5773692 {_120859 : Type'} (s : _120859 -> Prop) (t : _120859 -> Prop) : (s = t) = (term2 _120859 s t).
Proof. exact (@lem5773691 _120859 s t). Qed.
Lemma lem5773693 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : ((term49 _120859 s' s) = (@EMPTY _120859)) = (term50 _120859 s' s).
Proof. exact (@lem5773692 _120859 (term49 _120859 s' s) (@EMPTY _120859)). Qed.
Lemma lem5773698 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term48 _120859 s' s) = (term50 _120859 s' s).
Proof. exact (TRANS (@lem5773687 _120859 s' s) (@lem5773693 _120859 s' s)). Qed.
Lemma lem5773703 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term50 _120859 s' s) = (term48 _120859 s' s).
Proof. exact (SYM (@lem5773698 _120859 s' s)). Qed.
Lemma lem5773711 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5773712 {_120859 : Type'} (s : _120859 -> Prop) (x : _120859) (t : _120859 -> Prop) : (term4 _120859 x s t) = (term5 _120859 s x t).
Proof. exact (@lem5773711 _120859 s x t). Qed.
Lemma lem5773713 {_120859 : Type'} (x : _120859) (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term51 _120859 x s' s) = (term52 _120859 x s' s).
Proof. exact (@lem5773712 _120859 (@DIFF _120859 s s') x (@INTER _120859 s' s)). Qed.
Lemma lem5773717 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5773718 {_120859 : Type'} (s : _120859 -> Prop) (x : _120859) (t : _120859 -> Prop) : (term8 _120859 x s t) = (term9 _120859 s x t).
Proof. exact (@lem5773717 _120859 s x t). Qed.
Lemma lem5773719 {_120859 : Type'} (s : _120859 -> Prop) (x : _120859) (s' : _120859 -> Prop) : (term8 _120859 x s s') = (term9 _120859 s x s').
Proof. exact (@lem5773718 _120859 s x s'). Qed.
Lemma lem5773723 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773724 {_120859 : Type'} (P : _120859 -> Prop) (x : _120859) : (@IN _120859 x P) = (P x).
Proof. exact (@lem5773723 _120859 P x). Qed.
Lemma lem5773725 {_120859 : Type'} (s : _120859 -> Prop) (x : _120859) : (@IN _120859 x s) = (s x).
Proof. exact (@lem5773724 _120859 s x). Qed.
Lemma lem5773726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773727 {_120859 : Type'} (s : _120859 -> Prop) (x : _120859) : (term10 _120859 x s) = (term11 _120859 s x).
Proof. exact (MK_COMB (@lem5773726) (@lem5773725 _120859 s x)). Qed.
Lemma lem5773729 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773730 {_120859 : Type'} (P : _120859 -> Prop) (x : _120859) : (@IN _120859 x P) = (P x).
Proof. exact (@lem5773729 _120859 P x). Qed.
Lemma lem5773731 {_120859 : Type'} (s' : _120859 -> Prop) (x : _120859) : (@IN _120859 x s') = (s' x).
Proof. exact (@lem5773730 _120859 s' x). Qed.
Lemma lem5773732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5773733 {_120859 : Type'} (s' : _120859 -> Prop) (x : _120859) : (term12 _120859 x s') = (term13 _120859 s' x).
Proof. exact (MK_COMB (@lem5773732) (@lem5773731 _120859 s' x)). Qed.
Lemma lem5773734 {_120859 : Type'} (s : _120859 -> Prop) (s' : _120859 -> Prop) (x : _120859) : (term9 _120859 s x s') = (term14 _120859 s s' x).
Proof. exact (MK_COMB (@lem5773727 _120859 s x) (@lem5773733 _120859 s' x)). Qed.
Lemma lem5773737 {_120859 : Type'} (s : _120859 -> Prop) (s' : _120859 -> Prop) (x : _120859) : (term8 _120859 x s s') = (term14 _120859 s s' x).
Proof. exact (TRANS (@lem5773719 _120859 s x s') (@lem5773734 _120859 s s' x)). Qed.
Lemma lem5773738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773739 {_120859 : Type'} (s : _120859 -> Prop) (s' : _120859 -> Prop) (x : _120859) : (term15 _120859 x s s') = (term16 _120859 s s' x).
Proof. exact (MK_COMB (@lem5773738) (@lem5773737 _120859 s s' x)). Qed.
Lemma lem5773741 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5773742 {_120859 : Type'} (s : _120859 -> Prop) (x : _120859) (t : _120859 -> Prop) : (term4 _120859 x s t) = (term5 _120859 s x t).
Proof. exact (@lem5773741 _120859 s x t). Qed.
Lemma lem5773743 {_120859 : Type'} (s' : _120859 -> Prop) (x : _120859) (s : _120859 -> Prop) : (term4 _120859 x s' s) = (term5 _120859 s' x s).
Proof. exact (@lem5773742 _120859 s' x s). Qed.
Lemma lem5773747 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773748 {_120859 : Type'} (P : _120859 -> Prop) (x : _120859) : (@IN _120859 x P) = (P x).
Proof. exact (@lem5773747 _120859 P x). Qed.
Lemma lem5773749 {_120859 : Type'} (s' : _120859 -> Prop) (x : _120859) : (@IN _120859 x s') = (s' x).
Proof. exact (@lem5773748 _120859 s' x). Qed.
Lemma lem5773750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773751 {_120859 : Type'} (s' : _120859 -> Prop) (x : _120859) : (term10 _120859 x s') = (term11 _120859 s' x).
Proof. exact (MK_COMB (@lem5773750) (@lem5773749 _120859 s' x)). Qed.
Lemma lem5773753 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5773754 {_120859 : Type'} (P : _120859 -> Prop) (x : _120859) : (@IN _120859 x P) = (P x).
Proof. exact (@lem5773753 _120859 P x). Qed.
Lemma lem5773755 {_120859 : Type'} (s : _120859 -> Prop) (x : _120859) : (@IN _120859 x s) = (s x).
Proof. exact (@lem5773754 _120859 s x). Qed.
Lemma lem5773756 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : (term5 _120859 s' x s) = (term17 _120859 s' s x).
Proof. exact (MK_COMB (@lem5773751 _120859 s' x) (@lem5773755 _120859 s x)). Qed.
Lemma lem5773759 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : (term4 _120859 x s' s) = (term17 _120859 s' s x).
Proof. exact (TRANS (@lem5773743 _120859 s' x s) (@lem5773756 _120859 s' s x)). Qed.
Lemma lem5773760 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : (term52 _120859 x s' s) = (term53 _120859 s' s x).
Proof. exact (MK_COMB (@lem5773739 _120859 s s' x) (@lem5773759 _120859 s' s x)). Qed.
Lemma lem5773763 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : (term51 _120859 x s' s) = (term53 _120859 s' s x).
Proof. exact (TRANS (@lem5773713 _120859 x s' s) (@lem5773760 _120859 s' s x)). Qed.
Lemma lem5773764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5773765 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : (term54 _120859 x s' s) = (term55 _120859 s' s x).
Proof. exact (MK_COMB (@lem5773764) (@lem5773763 _120859 s' s x)). Qed.
Lemma lem5773767 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5773768 {_120859 : Type'} (x : _120859) : (@IN _120859 x (@EMPTY _120859)) = False.
Proof. exact (@lem5773767 _120859 x). Qed.
Lemma lem5773769 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : ((term51 _120859 x s' s) = (@IN _120859 x (@EMPTY _120859))) = ((term53 _120859 s' s x) = False).
Proof. exact (MK_COMB (@lem5773765 _120859 s' s x) (@lem5773768 _120859 x)). Qed.
Lemma lem5773771 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5773772 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : ((term53 _120859 s' s x) = False) = (term56 _120859 s' s x).
Proof. exact (@lem5773771 (term53 _120859 s' s x)). Qed.
Lemma lem5773779 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : ((term51 _120859 x s' s) = (@IN _120859 x (@EMPTY _120859))) = (term56 _120859 s' s x).
Proof. exact (TRANS (@lem5773769 _120859 s' s x) (@lem5773772 _120859 s' s x)). Qed.
Lemma lem5773780 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term57 _120859 s' s) = (term58 _120859 s' s).
Proof. exact (fun_ext (fun x : _120859 => @lem5773779 _120859 s' s x)). Qed.
Lemma lem5773781 {_120859 : Type'} : (@all _120859) = (@all _120859).
Proof. exact (eq_refl (@all _120859)). Qed.
Lemma lem5773782 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term50 _120859 s' s) = (term59 _120859 s' s).
Proof. exact (MK_COMB (@lem5773781 _120859) (@lem5773780 _120859 s' s)). Qed.
Lemma lem5773787 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term59 _120859 s' s) = (term50 _120859 s' s).
Proof. exact (SYM (@lem5773782 _120859 s' s)). Qed.
Lemma lem5773789 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5773790 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term59 _120859 s' s) = (term60 _120859 s' s).
Proof. exact (@lem5773789 (term59 _120859 s' s)). Qed.
Lemma lem5773791 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term60 _120859 s' s) = (term59 _120859 s' s).
Proof. exact (SYM (@lem5773790 _120859 s' s)). Qed.
Lemma lem5773792 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term61 _120859 s' s) : term61 _120859 s' s.
Proof. exact (h1). Qed.
Lemma lem5773795 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term60 _120859 s' s) : term60 _120859 s' s.
Proof. exact (h1). Qed.
Lemma lem5773796 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term62 _120859 s' s.
Proof. exact (fun h0 : term60 _120859 s' s => @lem5773795 _120859 s' s h0). Qed.
Lemma lem5773797 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term62 _120859 s' s) : term62 _120859 s' s.
Proof. exact (h1). Qed.
Lemma lem5773798 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term60 _120859 s' s) : term60 _120859 s' s.
Proof. exact (h1). Qed.
Lemma lem5773799 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term60 _120859 s' s) (h2 : term62 _120859 s' s) : term60 _120859 s' s.
Proof. exact (@lem5773797 _120859 s' s h2 (@lem5773798 _120859 s' s h1)). Qed.
Lemma lem5773800 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term60 _120859 s' s) : term63 _120859 s' s.
Proof. exact (fun h0 : term62 _120859 s' s => @lem5773799 _120859 s' s h1 h0). Qed.
Lemma lem5773801 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term62 _120859 s' s) : term62 _120859 s' s.
Proof. exact (h1). Qed.
Lemma lem5773802 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term60 _120859 s' s) (h2 : term62 _120859 s' s) : term60 _120859 s' s.
Proof. exact (@lem5773800 _120859 s' s h1 (@lem5773801 _120859 s' s h2)). Qed.
Lemma lem5773803 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term62 _120859 s' s) : term62 _120859 s' s.
Proof. exact (fun h0 : term60 _120859 s' s => @lem5773802 _120859 s' s h0 h1). Qed.
Lemma lem5773804 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term64 _120859 s' s.
Proof. exact (fun h0 : term62 _120859 s' s => @lem5773803 _120859 s' s h0). Qed.
Lemma lem5773807 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term62 _120859 s' s.
Proof. exact (@lem5773804 _120859 s' s (@lem5773796 _120859 s' s)). Qed.
Lemma lem5773808 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term62 _120859 s' s.
Proof. exact (@lem5773807 _120859 s' s). Qed.
Lemma lem5773818 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5773819 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term60 _120859 s' s) = (term65 _120859 s' s).
Proof. exact (@lem5773818 (term61 _120859 s' s)). Qed.
Lemma lem5773821 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5773822 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term65 _120859 s' s) = (term59 _120859 s' s).
Proof. exact (@lem5773821 (term59 _120859 s' s)). Qed.
Lemma lem5773827 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term60 _120859 s' s) = (term59 _120859 s' s).
Proof. exact (TRANS (@lem5773819 _120859 s' s) (@lem5773822 _120859 s' s)). Qed.
Lemma lem5773834 {_120859 : Type'} (s : _120859 -> Prop) : (term66 _120859 s) = (term67 _120859 s).
Proof. exact (fun_ext (fun s' : _120859 -> Prop => @lem5773827 _120859 s' s)). Qed.
Lemma lem5773835 {_120859 : Type'} : (@all (_120859 -> Prop)) = (@all (_120859 -> Prop)).
Proof. exact (eq_refl (@all (_120859 -> Prop))). Qed.
Lemma lem5773836 {_120859 : Type'} (s : _120859 -> Prop) : (term68 _120859 s) = (term69 _120859 s).
Proof. exact (MK_COMB (@lem5773835 _120859) (@lem5773834 _120859 s)). Qed.
Lemma lem5773841 {_120859 : Type'} : (term70 _120859) = (term71 _120859).
Proof. exact (fun_ext (fun s : _120859 -> Prop => @lem5773836 _120859 s)). Qed.
Lemma lem5773842 {_120859 : Type'} : (@all (_120859 -> Prop)) = (@all (_120859 -> Prop)).
Proof. exact (eq_refl (@all (_120859 -> Prop))). Qed.
Lemma lem5773851 {_120859 : Type'} : (term72 _120859) = (term73 _120859).
Proof. exact (MK_COMB (@lem5773842 _120859) (@lem5773841 _120859)). Qed.
Lemma lem5773868 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : (term56 _120859 s' s x) = (term56 _120859 s' s x).
Proof. exact (eq_refl (term56 _120859 s' s x)). Qed.
Lemma lem5773869 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term58 _120859 s' s) = (term58 _120859 s' s).
Proof. exact (fun_ext (fun x : _120859 => @lem5773868 _120859 s' s x)). Qed.
Lemma lem5773870 {_120859 : Type'} : (@all _120859) = (@all _120859).
Proof. exact (eq_refl (@all _120859)). Qed.
Lemma lem5773871 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term59 _120859 s' s) = (term59 _120859 s' s).
Proof. exact (MK_COMB (@lem5773870 _120859) (@lem5773869 _120859 s' s)). Qed.
Lemma lem5773872 {_120859 : Type'} (s : _120859 -> Prop) : (term67 _120859 s) = (term67 _120859 s).
Proof. exact (fun_ext (fun s' : _120859 -> Prop => @lem5773871 _120859 s' s)). Qed.
Lemma lem5773873 {_120859 : Type'} : (@all (_120859 -> Prop)) = (@all (_120859 -> Prop)).
Proof. exact (eq_refl (@all (_120859 -> Prop))). Qed.
Lemma lem5773874 {_120859 : Type'} (s : _120859 -> Prop) : (term69 _120859 s) = (term69 _120859 s).
Proof. exact (MK_COMB (@lem5773873 _120859) (@lem5773872 _120859 s)). Qed.
Lemma lem5773875 {_120859 : Type'} : (term71 _120859) = (term71 _120859).
Proof. exact (fun_ext (fun s : _120859 -> Prop => @lem5773874 _120859 s)). Qed.
Lemma lem5773876 {_120859 : Type'} : (@all (_120859 -> Prop)) = (@all (_120859 -> Prop)).
Proof. exact (eq_refl (@all (_120859 -> Prop))). Qed.
Lemma lem5773877 {_120859 : Type'} : (term73 _120859) = (term73 _120859).
Proof. exact (MK_COMB (@lem5773876 _120859) (@lem5773875 _120859)). Qed.
Lemma lem5773904 {_120859 : Type'} : (term72 _120859) = (term73 _120859).
Proof. exact (TRANS (@lem5773851 _120859) (@lem5773877 _120859)). Qed.
Lemma lem5773905 {_120859 : Type'} : (term73 _120859) = (term72 _120859).
Proof. exact (SYM (@lem5773904 _120859)). Qed.
Lemma lem5773924 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term53 _120859 s' s x.
Proof. exact (h1). Qed.
Lemma lem5773948 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term53 _120859 s' s x.
Proof. exact (h1). Qed.
Lemma lem5773949 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term17 _120859 s' s x.
Proof. exact (proj2 (@lem5773948 _120859 s' s x h1)). Qed.
Lemma lem5773950 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term14 _120859 s s' x.
Proof. exact (proj1 (@lem5773948 _120859 s' s x h1)). Qed.
Lemma lem5773978 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term13 _120859 s' x.
Proof. exact (proj2 (@lem5773950 _120859 s' s x h1)). Qed.
Lemma lem5773980 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : s' x.
Proof. exact (proj1 (@lem5773949 _120859 s' s x h1)). Qed.
Lemma lem5773981 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term41 _120859 s' x.
Proof. exact (fun h0 : term13 _120859 s' x => @lem5773980 _120859 s' s x h1). Qed.
Lemma lem5773983 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5773984 {_120859 : Type'} (s' : _120859 -> Prop) (x : _120859) : (term41 _120859 s' x) = (s' x).
Proof. exact (@lem5773983 (s' x)). Qed.
Lemma lem5773985 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : s' x.
Proof. exact (EQ_MP (@lem5773984 _120859 s' x) (@lem5773981 _120859 s' s x h1)). Qed.
Lemma lem5773988 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5773990 {_120859 : Type'} (s' : _120859 -> Prop) (x : _120859) : (term13 _120859 s' x) = (term43 _120859 s' x).
Proof. exact (@lem5773988 (s' x)). Qed.
Lemma lem5773993 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term43 _120859 s' x.
Proof. exact (EQ_MP (@lem5773990 _120859 s' x) (@lem5773978 _120859 s' s x h1)). Qed.
Lemma lem5773996 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : False.
Proof. exact (@lem5773993 _120859 s' s x h1 (@lem5773985 _120859 s' s x h1)). Qed.
Lemma lem5773997 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : term44.
Proof. exact (fun h0 : ~ False => @lem5773996 _120859 s' s x h1). Qed.
Lemma lem5773999 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5774000 : term44 = False.
Proof. exact (@lem5773999 False). Qed.
Lemma lem5774001 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : False.
Proof. exact (EQ_MP (@lem5774000) (@lem5773997 _120859 s' s x h1)). Qed.
Lemma lem5774002 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : (term53 _120859 s' s x) = False.
Proof. exact (prop_ext (fun h2 : term53 _120859 s' s x => @lem5774001 _120859 s' s x h1) (fun h2 : False => @lem5773948 _120859 s' s x h1)). Qed.
Lemma lem5774003 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : False.
Proof. exact (EQ_MP (@lem5774002 _120859 s' s x h1) (@lem5773948 _120859 s' s x h1)). Qed.
Lemma lem5774004 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : (term53 _120859 s' s x) = False.
Proof. exact (prop_ext (fun h2 : term53 _120859 s' s x => @lem5774003 _120859 s' s x h1) (fun h2 : False => @lem5773924 _120859 s' s x h1)). Qed.
Lemma lem5774005 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) (h1 : term53 _120859 s' s x) : False.
Proof. exact (EQ_MP (@lem5774004 _120859 s' s x h1) (@lem5773924 _120859 s' s x h1)). Qed.
Lemma lem5774006 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : term74 _120859 s' s x.
Proof. exact (fun h0 : term53 _120859 s' s x => @lem5774005 _120859 s' s x h0). Qed.
Lemma lem5774007 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : (term74 _120859 s' s x) = (term56 _120859 s' s x).
Proof. exact (@lem69 (term53 _120859 s' s x)). Qed.
Lemma lem5774008 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (x : _120859) : term56 _120859 s' s x.
Proof. exact (EQ_MP (@lem5774007 _120859 s' s x) (@lem5774006 _120859 s' s x)). Qed.
Lemma lem5774013 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term59 _120859 s' s.
Proof. exact (fun x : _120859 => @lem5774008 _120859 s' s x). Qed.
Lemma lem5774018 {_120859 : Type'} (s : _120859 -> Prop) : term69 _120859 s.
Proof. exact (fun s' : _120859 -> Prop => @lem5774013 _120859 s' s). Qed.
Lemma lem5774023 {_120859 : Type'} : term73 _120859.
Proof. exact (fun s : _120859 -> Prop => @lem5774018 _120859 s). Qed.
Lemma lem5774024 {_120859 : Type'} : term72 _120859.
Proof. exact (EQ_MP (@lem5773905 _120859) (@lem5774023 _120859)). Qed.
Lemma lem5774025 {_120859 : Type'} (s : _120859 -> Prop) : term75 _120859 s.
Proof. exact (@lem5774024 _120859 s). Qed.
Lemma lem5774026 {_120859 : Type'} (s : _120859 -> Prop) : (term75 _120859 s) = (term68 _120859 s).
Proof. exact (eq_refl (term75 _120859 s)). Qed.
Lemma lem5774027 {_120859 : Type'} (s : _120859 -> Prop) : term68 _120859 s.
Proof. exact (EQ_MP (@lem5774026 _120859 s) (@lem5774025 _120859 s)). Qed.
Lemma lem5774028 {_120859 : Type'} (s : _120859 -> Prop) (s' : _120859 -> Prop) : term76 _120859 s s'.
Proof. exact (@lem5774027 _120859 s s'). Qed.
Lemma lem5774029 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term76 _120859 s s') = (term60 _120859 s' s).
Proof. exact (eq_refl (term76 _120859 s s')). Qed.
Lemma lem5774030 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term60 _120859 s' s.
Proof. exact (EQ_MP (@lem5774029 _120859 s' s) (@lem5774028 _120859 s s')). Qed.
Lemma lem5774032 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term60 _120859 s' s.
Proof. exact (@lem5773808 _120859 s' s (@lem5774030 _120859 s' s)). Qed.
Lemma lem5774033 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term61 _120859 s' s) : False.
Proof. exact (@lem5774032 _120859 s' s (@lem5773792 _120859 s' s h1)). Qed.
Lemma lem5774034 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term61 _120859 s' s) : (term61 _120859 s' s) = False.
Proof. exact (prop_ext (fun h2 : term61 _120859 s' s => @lem5774033 _120859 s' s h1) (fun h2 : False => @lem5773792 _120859 s' s h1)). Qed.
Lemma lem5774035 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) (h1 : term61 _120859 s' s) : False.
Proof. exact (EQ_MP (@lem5774034 _120859 s' s h1) (@lem5773792 _120859 s' s h1)). Qed.
Lemma lem5774036 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term60 _120859 s' s.
Proof. exact (fun h0 : term61 _120859 s' s => @lem5774035 _120859 s' s h0). Qed.
Lemma lem5774037 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term59 _120859 s' s.
Proof. exact (EQ_MP (@lem5773791 _120859 s' s) (@lem5774036 _120859 s' s)). Qed.
Lemma lem5774038 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term50 _120859 s' s.
Proof. exact (EQ_MP (@lem5773787 _120859 s' s) (@lem5774037 _120859 s' s)). Qed.
Lemma lem5774039 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : term48 _120859 s' s.
Proof. exact (EQ_MP (@lem5773703 _120859 s' s) (@lem5774038 _120859 s' s)). Qed.
Lemma lem5774051 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem5774052 {_120869 : Type'} (s : _120869 -> Prop) (t : _120869 -> Prop) : (@DISJOINT _120869 s t) = ((@INTER _120869 s t) = (@EMPTY _120869)).
Proof. exact (@lem5774051 _120869 s t). Qed.
Lemma lem5774053 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term77 _120869 s' s) = ((term78 _120869 s' s) = (@EMPTY _120869)).
Proof. exact (@lem5774052 _120869 (@DIFF _120869 s s') (@DIFF _120869 s' s)). Qed.
Lemma lem5774057 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5774058 {_120869 : Type'} (s : _120869 -> Prop) (t : _120869 -> Prop) : (s = t) = (term2 _120869 s t).
Proof. exact (@lem5774057 _120869 s t). Qed.
Lemma lem5774059 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : ((term78 _120869 s' s) = (@EMPTY _120869)) = (term79 _120869 s' s).
Proof. exact (@lem5774058 _120869 (term78 _120869 s' s) (@EMPTY _120869)). Qed.
Lemma lem5774064 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term77 _120869 s' s) = (term79 _120869 s' s).
Proof. exact (TRANS (@lem5774053 _120869 s' s) (@lem5774059 _120869 s' s)). Qed.
Lemma lem5774069 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term79 _120869 s' s) = (term77 _120869 s' s).
Proof. exact (SYM (@lem5774064 _120869 s' s)). Qed.
Lemma lem5774077 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5774078 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) (t : _120869 -> Prop) : (term4 _120869 x s t) = (term5 _120869 s x t).
Proof. exact (@lem5774077 _120869 s x t). Qed.
Lemma lem5774079 {_120869 : Type'} (x : _120869) (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term80 _120869 x s' s) = (term81 _120869 x s' s).
Proof. exact (@lem5774078 _120869 (@DIFF _120869 s s') x (@DIFF _120869 s' s)). Qed.
Lemma lem5774083 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5774084 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) (t : _120869 -> Prop) : (term8 _120869 x s t) = (term9 _120869 s x t).
Proof. exact (@lem5774083 _120869 s x t). Qed.
Lemma lem5774085 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) (s' : _120869 -> Prop) : (term8 _120869 x s s') = (term9 _120869 s x s').
Proof. exact (@lem5774084 _120869 s x s'). Qed.
Lemma lem5774089 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774090 {_120869 : Type'} (P : _120869 -> Prop) (x : _120869) : (@IN _120869 x P) = (P x).
Proof. exact (@lem5774089 _120869 P x). Qed.
Lemma lem5774091 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) : (@IN _120869 x s) = (s x).
Proof. exact (@lem5774090 _120869 s x). Qed.
Lemma lem5774092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774093 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) : (term10 _120869 x s) = (term11 _120869 s x).
Proof. exact (MK_COMB (@lem5774092) (@lem5774091 _120869 s x)). Qed.
Lemma lem5774095 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774096 {_120869 : Type'} (P : _120869 -> Prop) (x : _120869) : (@IN _120869 x P) = (P x).
Proof. exact (@lem5774095 _120869 P x). Qed.
Lemma lem5774097 {_120869 : Type'} (s' : _120869 -> Prop) (x : _120869) : (@IN _120869 x s') = (s' x).
Proof. exact (@lem5774096 _120869 s' x). Qed.
Lemma lem5774098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5774099 {_120869 : Type'} (s' : _120869 -> Prop) (x : _120869) : (term12 _120869 x s') = (term13 _120869 s' x).
Proof. exact (MK_COMB (@lem5774098) (@lem5774097 _120869 s' x)). Qed.
Lemma lem5774100 {_120869 : Type'} (s : _120869 -> Prop) (s' : _120869 -> Prop) (x : _120869) : (term9 _120869 s x s') = (term14 _120869 s s' x).
Proof. exact (MK_COMB (@lem5774093 _120869 s x) (@lem5774099 _120869 s' x)). Qed.
Lemma lem5774103 {_120869 : Type'} (s : _120869 -> Prop) (s' : _120869 -> Prop) (x : _120869) : (term8 _120869 x s s') = (term14 _120869 s s' x).
Proof. exact (TRANS (@lem5774085 _120869 s x s') (@lem5774100 _120869 s s' x)). Qed.
Lemma lem5774104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774105 {_120869 : Type'} (s : _120869 -> Prop) (s' : _120869 -> Prop) (x : _120869) : (term15 _120869 x s s') = (term16 _120869 s s' x).
Proof. exact (MK_COMB (@lem5774104) (@lem5774103 _120869 s s' x)). Qed.
Lemma lem5774107 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5774108 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) (t : _120869 -> Prop) : (term8 _120869 x s t) = (term9 _120869 s x t).
Proof. exact (@lem5774107 _120869 s x t). Qed.
Lemma lem5774109 {_120869 : Type'} (s' : _120869 -> Prop) (x : _120869) (s : _120869 -> Prop) : (term8 _120869 x s' s) = (term9 _120869 s' x s).
Proof. exact (@lem5774108 _120869 s' x s). Qed.
Lemma lem5774113 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774114 {_120869 : Type'} (P : _120869 -> Prop) (x : _120869) : (@IN _120869 x P) = (P x).
Proof. exact (@lem5774113 _120869 P x). Qed.
Lemma lem5774115 {_120869 : Type'} (s' : _120869 -> Prop) (x : _120869) : (@IN _120869 x s') = (s' x).
Proof. exact (@lem5774114 _120869 s' x). Qed.
Lemma lem5774116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774117 {_120869 : Type'} (s' : _120869 -> Prop) (x : _120869) : (term10 _120869 x s') = (term11 _120869 s' x).
Proof. exact (MK_COMB (@lem5774116) (@lem5774115 _120869 s' x)). Qed.
Lemma lem5774119 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774120 {_120869 : Type'} (P : _120869 -> Prop) (x : _120869) : (@IN _120869 x P) = (P x).
Proof. exact (@lem5774119 _120869 P x). Qed.
Lemma lem5774121 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) : (@IN _120869 x s) = (s x).
Proof. exact (@lem5774120 _120869 s x). Qed.
Lemma lem5774122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5774123 {_120869 : Type'} (s : _120869 -> Prop) (x : _120869) : (term12 _120869 x s) = (term13 _120869 s x).
Proof. exact (MK_COMB (@lem5774122) (@lem5774121 _120869 s x)). Qed.
Lemma lem5774124 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : (term9 _120869 s' x s) = (term14 _120869 s' s x).
Proof. exact (MK_COMB (@lem5774117 _120869 s' x) (@lem5774123 _120869 s x)). Qed.
Lemma lem5774127 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : (term8 _120869 x s' s) = (term14 _120869 s' s x).
Proof. exact (TRANS (@lem5774109 _120869 s' x s) (@lem5774124 _120869 s' s x)). Qed.
Lemma lem5774128 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : (term81 _120869 x s' s) = (term82 _120869 s' s x).
Proof. exact (MK_COMB (@lem5774105 _120869 s s' x) (@lem5774127 _120869 s' s x)). Qed.
Lemma lem5774131 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : (term80 _120869 x s' s) = (term82 _120869 s' s x).
Proof. exact (TRANS (@lem5774079 _120869 x s' s) (@lem5774128 _120869 s' s x)). Qed.
Lemma lem5774132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5774133 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : (term83 _120869 x s' s) = (term84 _120869 s' s x).
Proof. exact (MK_COMB (@lem5774132) (@lem5774131 _120869 s' s x)). Qed.
Lemma lem5774135 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5774136 {_120869 : Type'} (x : _120869) : (@IN _120869 x (@EMPTY _120869)) = False.
Proof. exact (@lem5774135 _120869 x). Qed.
Lemma lem5774137 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : ((term80 _120869 x s' s) = (@IN _120869 x (@EMPTY _120869))) = ((term82 _120869 s' s x) = False).
Proof. exact (MK_COMB (@lem5774133 _120869 s' s x) (@lem5774136 _120869 x)). Qed.
Lemma lem5774139 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5774140 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : ((term82 _120869 s' s x) = False) = (term85 _120869 s' s x).
Proof. exact (@lem5774139 (term82 _120869 s' s x)). Qed.
Lemma lem5774147 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : ((term80 _120869 x s' s) = (@IN _120869 x (@EMPTY _120869))) = (term85 _120869 s' s x).
Proof. exact (TRANS (@lem5774137 _120869 s' s x) (@lem5774140 _120869 s' s x)). Qed.
Lemma lem5774148 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term86 _120869 s' s) = (term87 _120869 s' s).
Proof. exact (fun_ext (fun x : _120869 => @lem5774147 _120869 s' s x)). Qed.
Lemma lem5774149 {_120869 : Type'} : (@all _120869) = (@all _120869).
Proof. exact (eq_refl (@all _120869)). Qed.
Lemma lem5774150 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term79 _120869 s' s) = (term88 _120869 s' s).
Proof. exact (MK_COMB (@lem5774149 _120869) (@lem5774148 _120869 s' s)). Qed.
Lemma lem5774155 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term88 _120869 s' s) = (term79 _120869 s' s).
Proof. exact (SYM (@lem5774150 _120869 s' s)). Qed.
Lemma lem5774157 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5774158 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term88 _120869 s' s) = (term89 _120869 s' s).
Proof. exact (@lem5774157 (term88 _120869 s' s)). Qed.
Lemma lem5774159 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term89 _120869 s' s) = (term88 _120869 s' s).
Proof. exact (SYM (@lem5774158 _120869 s' s)). Qed.
Lemma lem5774160 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term90 _120869 s' s) : term90 _120869 s' s.
Proof. exact (h1). Qed.
Lemma lem5774163 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term89 _120869 s' s) : term89 _120869 s' s.
Proof. exact (h1). Qed.
Lemma lem5774164 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term91 _120869 s' s.
Proof. exact (fun h0 : term89 _120869 s' s => @lem5774163 _120869 s' s h0). Qed.
Lemma lem5774165 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term91 _120869 s' s) : term91 _120869 s' s.
Proof. exact (h1). Qed.
Lemma lem5774166 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term89 _120869 s' s) : term89 _120869 s' s.
Proof. exact (h1). Qed.
Lemma lem5774167 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term89 _120869 s' s) (h2 : term91 _120869 s' s) : term89 _120869 s' s.
Proof. exact (@lem5774165 _120869 s' s h2 (@lem5774166 _120869 s' s h1)). Qed.
Lemma lem5774168 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term89 _120869 s' s) : term92 _120869 s' s.
Proof. exact (fun h0 : term91 _120869 s' s => @lem5774167 _120869 s' s h1 h0). Qed.
Lemma lem5774169 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term91 _120869 s' s) : term91 _120869 s' s.
Proof. exact (h1). Qed.
Lemma lem5774170 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term89 _120869 s' s) (h2 : term91 _120869 s' s) : term89 _120869 s' s.
Proof. exact (@lem5774168 _120869 s' s h1 (@lem5774169 _120869 s' s h2)). Qed.
Lemma lem5774171 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term91 _120869 s' s) : term91 _120869 s' s.
Proof. exact (fun h0 : term89 _120869 s' s => @lem5774170 _120869 s' s h0 h1). Qed.
Lemma lem5774172 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term93 _120869 s' s.
Proof. exact (fun h0 : term91 _120869 s' s => @lem5774171 _120869 s' s h0). Qed.
Lemma lem5774175 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term91 _120869 s' s.
Proof. exact (@lem5774172 _120869 s' s (@lem5774164 _120869 s' s)). Qed.
Lemma lem5774176 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term91 _120869 s' s.
Proof. exact (@lem5774175 _120869 s' s). Qed.
Lemma lem5774186 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5774187 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term89 _120869 s' s) = (term94 _120869 s' s).
Proof. exact (@lem5774186 (term90 _120869 s' s)). Qed.
Lemma lem5774189 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5774190 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term94 _120869 s' s) = (term88 _120869 s' s).
Proof. exact (@lem5774189 (term88 _120869 s' s)). Qed.
Lemma lem5774195 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term89 _120869 s' s) = (term88 _120869 s' s).
Proof. exact (TRANS (@lem5774187 _120869 s' s) (@lem5774190 _120869 s' s)). Qed.
Lemma lem5774202 {_120869 : Type'} (s : _120869 -> Prop) : (term95 _120869 s) = (term96 _120869 s).
Proof. exact (fun_ext (fun s' : _120869 -> Prop => @lem5774195 _120869 s' s)). Qed.
Lemma lem5774203 {_120869 : Type'} : (@all (_120869 -> Prop)) = (@all (_120869 -> Prop)).
Proof. exact (eq_refl (@all (_120869 -> Prop))). Qed.
Lemma lem5774204 {_120869 : Type'} (s : _120869 -> Prop) : (term97 _120869 s) = (term98 _120869 s).
Proof. exact (MK_COMB (@lem5774203 _120869) (@lem5774202 _120869 s)). Qed.
Lemma lem5774209 {_120869 : Type'} : (term99 _120869) = (term100 _120869).
Proof. exact (fun_ext (fun s : _120869 -> Prop => @lem5774204 _120869 s)). Qed.
Lemma lem5774210 {_120869 : Type'} : (@all (_120869 -> Prop)) = (@all (_120869 -> Prop)).
Proof. exact (eq_refl (@all (_120869 -> Prop))). Qed.
Lemma lem5774219 {_120869 : Type'} : (term101 _120869) = (term102 _120869).
Proof. exact (MK_COMB (@lem5774210 _120869) (@lem5774209 _120869)). Qed.
Lemma lem5774238 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : (term85 _120869 s' s x) = (term85 _120869 s' s x).
Proof. exact (eq_refl (term85 _120869 s' s x)). Qed.
Lemma lem5774239 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term87 _120869 s' s) = (term87 _120869 s' s).
Proof. exact (fun_ext (fun x : _120869 => @lem5774238 _120869 s' s x)). Qed.
Lemma lem5774240 {_120869 : Type'} : (@all _120869) = (@all _120869).
Proof. exact (eq_refl (@all _120869)). Qed.
Lemma lem5774241 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term88 _120869 s' s) = (term88 _120869 s' s).
Proof. exact (MK_COMB (@lem5774240 _120869) (@lem5774239 _120869 s' s)). Qed.
Lemma lem5774242 {_120869 : Type'} (s : _120869 -> Prop) : (term96 _120869 s) = (term96 _120869 s).
Proof. exact (fun_ext (fun s' : _120869 -> Prop => @lem5774241 _120869 s' s)). Qed.
Lemma lem5774243 {_120869 : Type'} : (@all (_120869 -> Prop)) = (@all (_120869 -> Prop)).
Proof. exact (eq_refl (@all (_120869 -> Prop))). Qed.
Lemma lem5774244 {_120869 : Type'} (s : _120869 -> Prop) : (term98 _120869 s) = (term98 _120869 s).
Proof. exact (MK_COMB (@lem5774243 _120869) (@lem5774242 _120869 s)). Qed.
Lemma lem5774245 {_120869 : Type'} : (term100 _120869) = (term100 _120869).
Proof. exact (fun_ext (fun s : _120869 -> Prop => @lem5774244 _120869 s)). Qed.
Lemma lem5774246 {_120869 : Type'} : (@all (_120869 -> Prop)) = (@all (_120869 -> Prop)).
Proof. exact (eq_refl (@all (_120869 -> Prop))). Qed.
Lemma lem5774247 {_120869 : Type'} : (term102 _120869) = (term102 _120869).
Proof. exact (MK_COMB (@lem5774246 _120869) (@lem5774245 _120869)). Qed.
Lemma lem5774274 {_120869 : Type'} : (term101 _120869) = (term102 _120869).
Proof. exact (TRANS (@lem5774219 _120869) (@lem5774247 _120869)). Qed.
Lemma lem5774275 {_120869 : Type'} : (term102 _120869) = (term101 _120869).
Proof. exact (SYM (@lem5774274 _120869)). Qed.
Lemma lem5774294 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term82 _120869 s' s x.
Proof. exact (h1). Qed.
Lemma lem5774320 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term82 _120869 s' s x.
Proof. exact (h1). Qed.
Lemma lem5774321 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term14 _120869 s' s x.
Proof. exact (proj2 (@lem5774320 _120869 s' s x h1)). Qed.
Lemma lem5774322 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term14 _120869 s s' x.
Proof. exact (proj1 (@lem5774320 _120869 s' s x h1)). Qed.
Lemma lem5774350 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term13 _120869 s' x.
Proof. exact (proj2 (@lem5774322 _120869 s' s x h1)). Qed.
Lemma lem5774352 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : s' x.
Proof. exact (proj1 (@lem5774321 _120869 s' s x h1)). Qed.
Lemma lem5774353 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term41 _120869 s' x.
Proof. exact (fun h0 : term13 _120869 s' x => @lem5774352 _120869 s' s x h1). Qed.
Lemma lem5774355 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5774356 {_120869 : Type'} (s' : _120869 -> Prop) (x : _120869) : (term41 _120869 s' x) = (s' x).
Proof. exact (@lem5774355 (s' x)). Qed.
Lemma lem5774357 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : s' x.
Proof. exact (EQ_MP (@lem5774356 _120869 s' x) (@lem5774353 _120869 s' s x h1)). Qed.
Lemma lem5774360 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5774362 {_120869 : Type'} (s' : _120869 -> Prop) (x : _120869) : (term13 _120869 s' x) = (term43 _120869 s' x).
Proof. exact (@lem5774360 (s' x)). Qed.
Lemma lem5774365 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term43 _120869 s' x.
Proof. exact (EQ_MP (@lem5774362 _120869 s' x) (@lem5774350 _120869 s' s x h1)). Qed.
Lemma lem5774368 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : False.
Proof. exact (@lem5774365 _120869 s' s x h1 (@lem5774357 _120869 s' s x h1)). Qed.
Lemma lem5774369 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : term44.
Proof. exact (fun h0 : ~ False => @lem5774368 _120869 s' s x h1). Qed.
Lemma lem5774371 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5774372 : term44 = False.
Proof. exact (@lem5774371 False). Qed.
Lemma lem5774373 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : False.
Proof. exact (EQ_MP (@lem5774372) (@lem5774369 _120869 s' s x h1)). Qed.
Lemma lem5774374 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : (term82 _120869 s' s x) = False.
Proof. exact (prop_ext (fun h2 : term82 _120869 s' s x => @lem5774373 _120869 s' s x h1) (fun h2 : False => @lem5774320 _120869 s' s x h1)). Qed.
Lemma lem5774375 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : False.
Proof. exact (EQ_MP (@lem5774374 _120869 s' s x h1) (@lem5774320 _120869 s' s x h1)). Qed.
Lemma lem5774376 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : (term82 _120869 s' s x) = False.
Proof. exact (prop_ext (fun h2 : term82 _120869 s' s x => @lem5774375 _120869 s' s x h1) (fun h2 : False => @lem5774294 _120869 s' s x h1)). Qed.
Lemma lem5774377 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) (h1 : term82 _120869 s' s x) : False.
Proof. exact (EQ_MP (@lem5774376 _120869 s' s x h1) (@lem5774294 _120869 s' s x h1)). Qed.
Lemma lem5774378 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : term103 _120869 s' s x.
Proof. exact (fun h0 : term82 _120869 s' s x => @lem5774377 _120869 s' s x h0). Qed.
Lemma lem5774379 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : (term103 _120869 s' s x) = (term85 _120869 s' s x).
Proof. exact (@lem69 (term82 _120869 s' s x)). Qed.
Lemma lem5774380 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (x : _120869) : term85 _120869 s' s x.
Proof. exact (EQ_MP (@lem5774379 _120869 s' s x) (@lem5774378 _120869 s' s x)). Qed.
Lemma lem5774385 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term88 _120869 s' s.
Proof. exact (fun x : _120869 => @lem5774380 _120869 s' s x). Qed.
Lemma lem5774390 {_120869 : Type'} (s : _120869 -> Prop) : term98 _120869 s.
Proof. exact (fun s' : _120869 -> Prop => @lem5774385 _120869 s' s). Qed.
Lemma lem5774395 {_120869 : Type'} : term102 _120869.
Proof. exact (fun s : _120869 -> Prop => @lem5774390 _120869 s). Qed.
Lemma lem5774396 {_120869 : Type'} : term101 _120869.
Proof. exact (EQ_MP (@lem5774275 _120869) (@lem5774395 _120869)). Qed.
Lemma lem5774397 {_120869 : Type'} (s : _120869 -> Prop) : term104 _120869 s.
Proof. exact (@lem5774396 _120869 s). Qed.
Lemma lem5774398 {_120869 : Type'} (s : _120869 -> Prop) : (term104 _120869 s) = (term97 _120869 s).
Proof. exact (eq_refl (term104 _120869 s)). Qed.
Lemma lem5774399 {_120869 : Type'} (s : _120869 -> Prop) : term97 _120869 s.
Proof. exact (EQ_MP (@lem5774398 _120869 s) (@lem5774397 _120869 s)). Qed.
Lemma lem5774400 {_120869 : Type'} (s : _120869 -> Prop) (s' : _120869 -> Prop) : term105 _120869 s s'.
Proof. exact (@lem5774399 _120869 s s'). Qed.
Lemma lem5774401 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term105 _120869 s s') = (term89 _120869 s' s).
Proof. exact (eq_refl (term105 _120869 s s')). Qed.
Lemma lem5774402 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term89 _120869 s' s.
Proof. exact (EQ_MP (@lem5774401 _120869 s' s) (@lem5774400 _120869 s s')). Qed.
Lemma lem5774404 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term89 _120869 s' s.
Proof. exact (@lem5774176 _120869 s' s (@lem5774402 _120869 s' s)). Qed.
Lemma lem5774405 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term90 _120869 s' s) : False.
Proof. exact (@lem5774404 _120869 s' s (@lem5774160 _120869 s' s h1)). Qed.
Lemma lem5774406 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term90 _120869 s' s) : (term90 _120869 s' s) = False.
Proof. exact (prop_ext (fun h2 : term90 _120869 s' s => @lem5774405 _120869 s' s h1) (fun h2 : False => @lem5774160 _120869 s' s h1)). Qed.
Lemma lem5774407 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) (h1 : term90 _120869 s' s) : False.
Proof. exact (EQ_MP (@lem5774406 _120869 s' s h1) (@lem5774160 _120869 s' s h1)). Qed.
Lemma lem5774408 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term89 _120869 s' s.
Proof. exact (fun h0 : term90 _120869 s' s => @lem5774407 _120869 s' s h0). Qed.
Lemma lem5774409 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term88 _120869 s' s.
Proof. exact (EQ_MP (@lem5774159 _120869 s' s) (@lem5774408 _120869 s' s)). Qed.
Lemma lem5774410 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term79 _120869 s' s.
Proof. exact (EQ_MP (@lem5774155 _120869 s' s) (@lem5774409 _120869 s' s)). Qed.
Lemma lem5774411 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : term77 _120869 s' s.
Proof. exact (EQ_MP (@lem5774069 _120869 s' s) (@lem5774410 _120869 s' s)). Qed.
Lemma lem5774423 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem5774424 {_120885 : Type'} (s : _120885 -> Prop) (t : _120885 -> Prop) : (@DISJOINT _120885 s t) = ((@INTER _120885 s t) = (@EMPTY _120885)).
Proof. exact (@lem5774423 _120885 s t). Qed.
Lemma lem5774425 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term106 _120885 s s') = ((term107 _120885 s s') = (@EMPTY _120885)).
Proof. exact (@lem5774424 _120885 (term108 _120885 s' s) (@INTER _120885 s s')). Qed.
Lemma lem5774429 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5774430 {_120885 : Type'} (s : _120885 -> Prop) (t : _120885 -> Prop) : (s = t) = (term2 _120885 s t).
Proof. exact (@lem5774429 _120885 s t). Qed.
Lemma lem5774431 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : ((term107 _120885 s s') = (@EMPTY _120885)) = (term109 _120885 s s').
Proof. exact (@lem5774430 _120885 (term107 _120885 s s') (@EMPTY _120885)). Qed.
Lemma lem5774436 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term106 _120885 s s') = (term109 _120885 s s').
Proof. exact (TRANS (@lem5774425 _120885 s s') (@lem5774431 _120885 s s')). Qed.
Lemma lem5774441 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term109 _120885 s s') = (term106 _120885 s s').
Proof. exact (SYM (@lem5774436 _120885 s s')). Qed.
Lemma lem5774449 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5774450 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) (t : _120885 -> Prop) : (term4 _120885 x s t) = (term5 _120885 s x t).
Proof. exact (@lem5774449 _120885 s x t). Qed.
Lemma lem5774451 {_120885 : Type'} (x : _120885) (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term110 _120885 x s s') = (term111 _120885 x s s').
Proof. exact (@lem5774450 _120885 (term108 _120885 s' s) x (@INTER _120885 s s')). Qed.
Lemma lem5774455 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5774456 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) (t : _120885 -> Prop) : (term112 _120885 x s t) = (term113 _120885 s x t).
Proof. exact (@lem5774455 _120885 s x t). Qed.
Lemma lem5774457 {_120885 : Type'} (x : _120885) (s' : _120885 -> Prop) (s : _120885 -> Prop) : (term114 _120885 x s' s) = (term115 _120885 x s' s).
Proof. exact (@lem5774456 _120885 (@DIFF _120885 s s') x (@DIFF _120885 s' s)). Qed.
Lemma lem5774461 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5774462 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) (t : _120885 -> Prop) : (term8 _120885 x s t) = (term9 _120885 s x t).
Proof. exact (@lem5774461 _120885 s x t). Qed.
Lemma lem5774463 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) (s' : _120885 -> Prop) : (term8 _120885 x s s') = (term9 _120885 s x s').
Proof. exact (@lem5774462 _120885 s x s'). Qed.
Lemma lem5774467 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774468 {_120885 : Type'} (P : _120885 -> Prop) (x : _120885) : (@IN _120885 x P) = (P x).
Proof. exact (@lem5774467 _120885 P x). Qed.
Lemma lem5774469 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (@IN _120885 x s) = (s x).
Proof. exact (@lem5774468 _120885 s x). Qed.
Lemma lem5774470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774471 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (term10 _120885 x s) = (term11 _120885 s x).
Proof. exact (MK_COMB (@lem5774470) (@lem5774469 _120885 s x)). Qed.
Lemma lem5774473 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774474 {_120885 : Type'} (P : _120885 -> Prop) (x : _120885) : (@IN _120885 x P) = (P x).
Proof. exact (@lem5774473 _120885 P x). Qed.
Lemma lem5774475 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) : (@IN _120885 x s') = (s' x).
Proof. exact (@lem5774474 _120885 s' x). Qed.
Lemma lem5774476 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5774477 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) : (term12 _120885 x s') = (term13 _120885 s' x).
Proof. exact (MK_COMB (@lem5774476) (@lem5774475 _120885 s' x)). Qed.
Lemma lem5774478 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term9 _120885 s x s') = (term14 _120885 s s' x).
Proof. exact (MK_COMB (@lem5774471 _120885 s x) (@lem5774477 _120885 s' x)). Qed.
Lemma lem5774481 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term8 _120885 x s s') = (term14 _120885 s s' x).
Proof. exact (TRANS (@lem5774463 _120885 s x s') (@lem5774478 _120885 s s' x)). Qed.
Lemma lem5774482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5774483 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term116 _120885 x s s') = (term117 _120885 s s' x).
Proof. exact (MK_COMB (@lem5774482) (@lem5774481 _120885 s s' x)). Qed.
Lemma lem5774485 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5774486 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) (t : _120885 -> Prop) : (term8 _120885 x s t) = (term9 _120885 s x t).
Proof. exact (@lem5774485 _120885 s x t). Qed.
Lemma lem5774487 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) (s : _120885 -> Prop) : (term8 _120885 x s' s) = (term9 _120885 s' x s).
Proof. exact (@lem5774486 _120885 s' x s). Qed.
Lemma lem5774491 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774492 {_120885 : Type'} (P : _120885 -> Prop) (x : _120885) : (@IN _120885 x P) = (P x).
Proof. exact (@lem5774491 _120885 P x). Qed.
Lemma lem5774493 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) : (@IN _120885 x s') = (s' x).
Proof. exact (@lem5774492 _120885 s' x). Qed.
Lemma lem5774494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774495 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) : (term10 _120885 x s') = (term11 _120885 s' x).
Proof. exact (MK_COMB (@lem5774494) (@lem5774493 _120885 s' x)). Qed.
Lemma lem5774497 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774498 {_120885 : Type'} (P : _120885 -> Prop) (x : _120885) : (@IN _120885 x P) = (P x).
Proof. exact (@lem5774497 _120885 P x). Qed.
Lemma lem5774499 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (@IN _120885 x s) = (s x).
Proof. exact (@lem5774498 _120885 s x). Qed.
Lemma lem5774500 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5774501 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (term12 _120885 x s) = (term13 _120885 s x).
Proof. exact (MK_COMB (@lem5774500) (@lem5774499 _120885 s x)). Qed.
Lemma lem5774502 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) : (term9 _120885 s' x s) = (term14 _120885 s' s x).
Proof. exact (MK_COMB (@lem5774495 _120885 s' x) (@lem5774501 _120885 s x)). Qed.
Lemma lem5774505 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) : (term8 _120885 x s' s) = (term14 _120885 s' s x).
Proof. exact (TRANS (@lem5774487 _120885 s' x s) (@lem5774502 _120885 s' s x)). Qed.
Lemma lem5774506 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) : (term115 _120885 x s' s) = (term118 _120885 s' s x).
Proof. exact (MK_COMB (@lem5774483 _120885 s s' x) (@lem5774505 _120885 s' s x)). Qed.
Lemma lem5774509 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) : (term114 _120885 x s' s) = (term118 _120885 s' s x).
Proof. exact (TRANS (@lem5774457 _120885 x s' s) (@lem5774506 _120885 s' s x)). Qed.
Lemma lem5774510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774511 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) : (term119 _120885 x s' s) = (term120 _120885 s' s x).
Proof. exact (MK_COMB (@lem5774510) (@lem5774509 _120885 s' s x)). Qed.
Lemma lem5774513 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5774514 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) (t : _120885 -> Prop) : (term4 _120885 x s t) = (term5 _120885 s x t).
Proof. exact (@lem5774513 _120885 s x t). Qed.
Lemma lem5774515 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) (s' : _120885 -> Prop) : (term4 _120885 x s s') = (term5 _120885 s x s').
Proof. exact (@lem5774514 _120885 s x s'). Qed.
Lemma lem5774519 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774520 {_120885 : Type'} (P : _120885 -> Prop) (x : _120885) : (@IN _120885 x P) = (P x).
Proof. exact (@lem5774519 _120885 P x). Qed.
Lemma lem5774521 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (@IN _120885 x s) = (s x).
Proof. exact (@lem5774520 _120885 s x). Qed.
Lemma lem5774522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774523 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (term10 _120885 x s) = (term11 _120885 s x).
Proof. exact (MK_COMB (@lem5774522) (@lem5774521 _120885 s x)). Qed.
Lemma lem5774525 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774526 {_120885 : Type'} (P : _120885 -> Prop) (x : _120885) : (@IN _120885 x P) = (P x).
Proof. exact (@lem5774525 _120885 P x). Qed.
Lemma lem5774527 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) : (@IN _120885 x s') = (s' x).
Proof. exact (@lem5774526 _120885 s' x). Qed.
Lemma lem5774528 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term5 _120885 s x s') = (term17 _120885 s s' x).
Proof. exact (MK_COMB (@lem5774523 _120885 s x) (@lem5774527 _120885 s' x)). Qed.
Lemma lem5774531 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term4 _120885 x s s') = (term17 _120885 s s' x).
Proof. exact (TRANS (@lem5774515 _120885 s x s') (@lem5774528 _120885 s s' x)). Qed.
Lemma lem5774532 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term111 _120885 x s s') = (term121 _120885 s s' x).
Proof. exact (MK_COMB (@lem5774511 _120885 s' s x) (@lem5774531 _120885 s s' x)). Qed.
Lemma lem5774535 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term110 _120885 x s s') = (term121 _120885 s s' x).
Proof. exact (TRANS (@lem5774451 _120885 x s s') (@lem5774532 _120885 s s' x)). Qed.
Lemma lem5774536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5774537 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term122 _120885 x s s') = (term123 _120885 s s' x).
Proof. exact (MK_COMB (@lem5774536) (@lem5774535 _120885 s s' x)). Qed.
Lemma lem5774539 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5774540 {_120885 : Type'} (x : _120885) : (@IN _120885 x (@EMPTY _120885)) = False.
Proof. exact (@lem5774539 _120885 x). Qed.
Lemma lem5774541 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : ((term110 _120885 x s s') = (@IN _120885 x (@EMPTY _120885))) = ((term121 _120885 s s' x) = False).
Proof. exact (MK_COMB (@lem5774537 _120885 s s' x) (@lem5774540 _120885 x)). Qed.
Lemma lem5774543 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5774544 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : ((term121 _120885 s s' x) = False) = (term124 _120885 s s' x).
Proof. exact (@lem5774543 (term121 _120885 s s' x)). Qed.
Lemma lem5774555 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : ((term110 _120885 x s s') = (@IN _120885 x (@EMPTY _120885))) = (term124 _120885 s s' x).
Proof. exact (TRANS (@lem5774541 _120885 s s' x) (@lem5774544 _120885 s s' x)). Qed.
Lemma lem5774556 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term125 _120885 s s') = (term126 _120885 s s').
Proof. exact (fun_ext (fun x : _120885 => @lem5774555 _120885 s s' x)). Qed.
Lemma lem5774557 {_120885 : Type'} : (@all _120885) = (@all _120885).
Proof. exact (eq_refl (@all _120885)). Qed.
Lemma lem5774558 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term109 _120885 s s') = (term127 _120885 s s').
Proof. exact (MK_COMB (@lem5774557 _120885) (@lem5774556 _120885 s s')). Qed.
Lemma lem5774563 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term127 _120885 s s') = (term109 _120885 s s').
Proof. exact (SYM (@lem5774558 _120885 s s')). Qed.
Lemma lem5774565 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5774566 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term127 _120885 s s') = (term128 _120885 s s').
Proof. exact (@lem5774565 (term127 _120885 s s')). Qed.
Lemma lem5774567 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term128 _120885 s s') = (term127 _120885 s s').
Proof. exact (SYM (@lem5774566 _120885 s s')). Qed.
Lemma lem5774568 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term129 _120885 s s') : term129 _120885 s s'.
Proof. exact (h1). Qed.
Lemma lem5774571 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term128 _120885 s s') : term128 _120885 s s'.
Proof. exact (h1). Qed.
Lemma lem5774572 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term130 _120885 s s'.
Proof. exact (fun h0 : term128 _120885 s s' => @lem5774571 _120885 s s' h0). Qed.
Lemma lem5774573 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term130 _120885 s s') : term130 _120885 s s'.
Proof. exact (h1). Qed.
Lemma lem5774574 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term128 _120885 s s') : term128 _120885 s s'.
Proof. exact (h1). Qed.
Lemma lem5774575 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term128 _120885 s s') (h2 : term130 _120885 s s') : term128 _120885 s s'.
Proof. exact (@lem5774573 _120885 s s' h2 (@lem5774574 _120885 s s' h1)). Qed.
Lemma lem5774576 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term128 _120885 s s') : term131 _120885 s s'.
Proof. exact (fun h0 : term130 _120885 s s' => @lem5774575 _120885 s s' h1 h0). Qed.
Lemma lem5774577 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term130 _120885 s s') : term130 _120885 s s'.
Proof. exact (h1). Qed.
Lemma lem5774578 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term128 _120885 s s') (h2 : term130 _120885 s s') : term128 _120885 s s'.
Proof. exact (@lem5774576 _120885 s s' h1 (@lem5774577 _120885 s s' h2)). Qed.
Lemma lem5774579 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term130 _120885 s s') : term130 _120885 s s'.
Proof. exact (fun h0 : term128 _120885 s s' => @lem5774578 _120885 s s' h0 h1). Qed.
Lemma lem5774580 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term132 _120885 s s'.
Proof. exact (fun h0 : term130 _120885 s s' => @lem5774579 _120885 s s' h0). Qed.
Lemma lem5774583 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term130 _120885 s s'.
Proof. exact (@lem5774580 _120885 s s' (@lem5774572 _120885 s s')). Qed.
Lemma lem5774584 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term130 _120885 s s'.
Proof. exact (@lem5774583 _120885 s s'). Qed.
Lemma lem5774594 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5774595 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term128 _120885 s s') = (term133 _120885 s s').
Proof. exact (@lem5774594 (term129 _120885 s s')). Qed.
Lemma lem5774597 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5774598 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term133 _120885 s s') = (term127 _120885 s s').
Proof. exact (@lem5774597 (term127 _120885 s s')). Qed.
Lemma lem5774603 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term128 _120885 s s') = (term127 _120885 s s').
Proof. exact (TRANS (@lem5774595 _120885 s s') (@lem5774598 _120885 s s')). Qed.
Lemma lem5774614 {_120885 : Type'} (s' : _120885 -> Prop) : (term134 _120885 s') = (term135 _120885 s').
Proof. exact (fun_ext (fun s : _120885 -> Prop => @lem5774603 _120885 s s')). Qed.
Lemma lem5774615 {_120885 : Type'} : (@all (_120885 -> Prop)) = (@all (_120885 -> Prop)).
Proof. exact (eq_refl (@all (_120885 -> Prop))). Qed.
Lemma lem5774616 {_120885 : Type'} (s' : _120885 -> Prop) : (term136 _120885 s') = (term137 _120885 s').
Proof. exact (MK_COMB (@lem5774615 _120885) (@lem5774614 _120885 s')). Qed.
Lemma lem5774621 {_120885 : Type'} : (term138 _120885) = (term139 _120885).
Proof. exact (fun_ext (fun s' : _120885 -> Prop => @lem5774616 _120885 s')). Qed.
Lemma lem5774622 {_120885 : Type'} : (@all (_120885 -> Prop)) = (@all (_120885 -> Prop)).
Proof. exact (eq_refl (@all (_120885 -> Prop))). Qed.
Lemma lem5774631 {_120885 : Type'} : (term140 _120885) = (term141 _120885).
Proof. exact (MK_COMB (@lem5774622 _120885) (@lem5774621 _120885)). Qed.
Lemma lem5774658 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term124 _120885 s s' x) = (term124 _120885 s s' x).
Proof. exact (eq_refl (term124 _120885 s s' x)). Qed.
Lemma lem5774659 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term126 _120885 s s') = (term126 _120885 s s').
Proof. exact (fun_ext (fun x : _120885 => @lem5774658 _120885 s s' x)). Qed.
Lemma lem5774660 {_120885 : Type'} : (@all _120885) = (@all _120885).
Proof. exact (eq_refl (@all _120885)). Qed.
Lemma lem5774661 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term127 _120885 s s') = (term127 _120885 s s').
Proof. exact (MK_COMB (@lem5774660 _120885) (@lem5774659 _120885 s s')). Qed.
Lemma lem5774662 {_120885 : Type'} (s' : _120885 -> Prop) : (term135 _120885 s') = (term135 _120885 s').
Proof. exact (fun_ext (fun s : _120885 -> Prop => @lem5774661 _120885 s s')). Qed.
Lemma lem5774663 {_120885 : Type'} : (@all (_120885 -> Prop)) = (@all (_120885 -> Prop)).
Proof. exact (eq_refl (@all (_120885 -> Prop))). Qed.
Lemma lem5774664 {_120885 : Type'} (s' : _120885 -> Prop) : (term137 _120885 s') = (term137 _120885 s').
Proof. exact (MK_COMB (@lem5774663 _120885) (@lem5774662 _120885 s')). Qed.
Lemma lem5774665 {_120885 : Type'} : (term139 _120885) = (term139 _120885).
Proof. exact (fun_ext (fun s' : _120885 -> Prop => @lem5774664 _120885 s')). Qed.
Lemma lem5774666 {_120885 : Type'} : (@all (_120885 -> Prop)) = (@all (_120885 -> Prop)).
Proof. exact (eq_refl (@all (_120885 -> Prop))). Qed.
Lemma lem5774667 {_120885 : Type'} : (term141 _120885) = (term141 _120885).
Proof. exact (MK_COMB (@lem5774666 _120885) (@lem5774665 _120885)). Qed.
Lemma lem5774698 {_120885 : Type'} : (term140 _120885) = (term141 _120885).
Proof. exact (TRANS (@lem5774631 _120885) (@lem5774667 _120885)). Qed.
Lemma lem5774699 {_120885 : Type'} : (term141 _120885) = (term140 _120885).
Proof. exact (SYM (@lem5774698 _120885)). Qed.
Lemma lem5774726 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : term121 _120885 s s' x.
Proof. exact (h1). Qed.
Lemma lem5774764 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : term121 _120885 s s' x.
Proof. exact (h1). Qed.
Lemma lem5774765 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : term17 _120885 s s' x.
Proof. exact (proj2 (@lem5774764 _120885 s s' x h1)). Qed.
Lemma lem5774766 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : term118 _120885 s' s x.
Proof. exact (proj1 (@lem5774764 _120885 s s' x h1)). Qed.
Lemma lem5774769 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s s' x) : term14 _120885 s s' x.
Proof. exact (h1). Qed.
Lemma lem5774770 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s' s x) : term14 _120885 s' s x.
Proof. exact (h1). Qed.
Lemma lem5774814 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s s' x) : term13 _120885 s' x.
Proof. exact (proj2 (@lem5774769 _120885 s s' x h1)). Qed.
Lemma lem5774822 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s' s x) : term13 _120885 s x.
Proof. exact (proj2 (@lem5774770 _120885 s' s x h1)). Qed.
Lemma lem5774824 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : s' x.
Proof. exact (proj2 (@lem5774765 _120885 s s' x h1)). Qed.
Lemma lem5774825 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : term41 _120885 s' x.
Proof. exact (fun h0 : term13 _120885 s' x => @lem5774824 _120885 s s' x h1). Qed.
Lemma lem5774827 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5774828 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) : (term41 _120885 s' x) = (s' x).
Proof. exact (@lem5774827 (s' x)). Qed.
Lemma lem5774829 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : s' x.
Proof. exact (EQ_MP (@lem5774828 _120885 s' x) (@lem5774825 _120885 s s' x h1)). Qed.
Lemma lem5774832 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5774834 {_120885 : Type'} (s' : _120885 -> Prop) (x : _120885) : (term13 _120885 s' x) = (term43 _120885 s' x).
Proof. exact (@lem5774832 (s' x)). Qed.
Lemma lem5774837 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s s' x) : term43 _120885 s' x.
Proof. exact (EQ_MP (@lem5774834 _120885 s' x) (@lem5774814 _120885 s s' x h1)). Qed.
Lemma lem5774840 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s s' x) (h2 : term121 _120885 s s' x) : False.
Proof. exact (@lem5774837 _120885 s s' x h1 (@lem5774829 _120885 s s' x h2)). Qed.
Lemma lem5774841 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s s' x) (h2 : term121 _120885 s s' x) : term44.
Proof. exact (fun h0 : ~ False => @lem5774840 _120885 s s' x h1 h2). Qed.
Lemma lem5774843 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5774844 : term44 = False.
Proof. exact (@lem5774843 False). Qed.
Lemma lem5774845 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s s' x) (h2 : term121 _120885 s s' x) : False.
Proof. exact (EQ_MP (@lem5774844) (@lem5774841 _120885 s s' x h1 h2)). Qed.
Lemma lem5774847 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : s x.
Proof. exact (proj1 (@lem5774765 _120885 s s' x h1)). Qed.
Lemma lem5774848 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : term41 _120885 s x.
Proof. exact (fun h0 : term13 _120885 s x => @lem5774847 _120885 s s' x h1). Qed.
Lemma lem5774850 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5774851 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (term41 _120885 s x) = (s x).
Proof. exact (@lem5774850 (s x)). Qed.
Lemma lem5774852 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : s x.
Proof. exact (EQ_MP (@lem5774851 _120885 s x) (@lem5774848 _120885 s s' x h1)). Qed.
Lemma lem5774855 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5774857 {_120885 : Type'} (s : _120885 -> Prop) (x : _120885) : (term13 _120885 s x) = (term43 _120885 s x).
Proof. exact (@lem5774855 (s x)). Qed.
Lemma lem5774860 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s' s x) : term43 _120885 s x.
Proof. exact (EQ_MP (@lem5774857 _120885 s x) (@lem5774822 _120885 s' s x h1)). Qed.
Lemma lem5774863 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s' s x) (h2 : term121 _120885 s s' x) : False.
Proof. exact (@lem5774860 _120885 s' s x h1 (@lem5774852 _120885 s s' x h2)). Qed.
Lemma lem5774864 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s' s x) (h2 : term121 _120885 s s' x) : term44.
Proof. exact (fun h0 : ~ False => @lem5774863 _120885 s s' x h1 h2). Qed.
Lemma lem5774866 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5774867 : term44 = False.
Proof. exact (@lem5774866 False). Qed.
Lemma lem5774868 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term14 _120885 s' s x) (h2 : term121 _120885 s s' x) : False.
Proof. exact (EQ_MP (@lem5774867) (@lem5774864 _120885 s s' x h1 h2)). Qed.
Lemma lem5774869 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : False.
Proof. exact (or_elim (@lem5774766 _120885 s s' x h1) (fun h0 : term14 _120885 s s' x => @lem5774845 _120885 s s' x h0 h1) (fun h0 : term14 _120885 s' s x => @lem5774868 _120885 s s' x h0 h1)). Qed.
Lemma lem5774870 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : (term121 _120885 s s' x) = False.
Proof. exact (prop_ext (fun h2 : term121 _120885 s s' x => @lem5774869 _120885 s s' x h1) (fun h2 : False => @lem5774764 _120885 s s' x h1)). Qed.
Lemma lem5774871 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : False.
Proof. exact (EQ_MP (@lem5774870 _120885 s s' x h1) (@lem5774764 _120885 s s' x h1)). Qed.
Lemma lem5774872 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : (term121 _120885 s s' x) = False.
Proof. exact (prop_ext (fun h2 : term121 _120885 s s' x => @lem5774871 _120885 s s' x h1) (fun h2 : False => @lem5774726 _120885 s s' x h1)). Qed.
Lemma lem5774873 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) (h1 : term121 _120885 s s' x) : False.
Proof. exact (EQ_MP (@lem5774872 _120885 s s' x h1) (@lem5774726 _120885 s s' x h1)). Qed.
Lemma lem5774874 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : term142 _120885 s s' x.
Proof. exact (fun h0 : term121 _120885 s s' x => @lem5774873 _120885 s s' x h0). Qed.
Lemma lem5774875 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : (term142 _120885 s s' x) = (term124 _120885 s s' x).
Proof. exact (@lem69 (term121 _120885 s s' x)). Qed.
Lemma lem5774876 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (x : _120885) : term124 _120885 s s' x.
Proof. exact (EQ_MP (@lem5774875 _120885 s s' x) (@lem5774874 _120885 s s' x)). Qed.
Lemma lem5774881 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term127 _120885 s s'.
Proof. exact (fun x : _120885 => @lem5774876 _120885 s s' x). Qed.
Lemma lem5774886 {_120885 : Type'} (s' : _120885 -> Prop) : term137 _120885 s'.
Proof. exact (fun s : _120885 -> Prop => @lem5774881 _120885 s s'). Qed.
Lemma lem5774891 {_120885 : Type'} : term141 _120885.
Proof. exact (fun s' : _120885 -> Prop => @lem5774886 _120885 s'). Qed.
Lemma lem5774892 {_120885 : Type'} : term140 _120885.
Proof. exact (EQ_MP (@lem5774699 _120885) (@lem5774891 _120885)). Qed.
Lemma lem5774893 {_120885 : Type'} (s' : _120885 -> Prop) : term143 _120885 s'.
Proof. exact (@lem5774892 _120885 s'). Qed.
Lemma lem5774894 {_120885 : Type'} (s' : _120885 -> Prop) : (term143 _120885 s') = (term136 _120885 s').
Proof. exact (eq_refl (term143 _120885 s')). Qed.
Lemma lem5774895 {_120885 : Type'} (s' : _120885 -> Prop) : term136 _120885 s'.
Proof. exact (EQ_MP (@lem5774894 _120885 s') (@lem5774893 _120885 s')). Qed.
Lemma lem5774896 {_120885 : Type'} (s' : _120885 -> Prop) (s : _120885 -> Prop) : term144 _120885 s' s.
Proof. exact (@lem5774895 _120885 s' s). Qed.
Lemma lem5774897 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term144 _120885 s' s) = (term128 _120885 s s').
Proof. exact (eq_refl (term144 _120885 s' s)). Qed.
Lemma lem5774898 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term128 _120885 s s'.
Proof. exact (EQ_MP (@lem5774897 _120885 s s') (@lem5774896 _120885 s' s)). Qed.
Lemma lem5774900 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term128 _120885 s s'.
Proof. exact (@lem5774584 _120885 s s' (@lem5774898 _120885 s s')). Qed.
Lemma lem5774901 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term129 _120885 s s') : False.
Proof. exact (@lem5774900 _120885 s s' (@lem5774568 _120885 s s' h1)). Qed.
Lemma lem5774902 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term129 _120885 s s') : (term129 _120885 s s') = False.
Proof. exact (prop_ext (fun h2 : term129 _120885 s s' => @lem5774901 _120885 s s' h1) (fun h2 : False => @lem5774568 _120885 s s' h1)). Qed.
Lemma lem5774903 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) (h1 : term129 _120885 s s') : False.
Proof. exact (EQ_MP (@lem5774902 _120885 s s' h1) (@lem5774568 _120885 s s' h1)). Qed.
Lemma lem5774904 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term128 _120885 s s'.
Proof. exact (fun h0 : term129 _120885 s s' => @lem5774903 _120885 s s' h0). Qed.
Lemma lem5774905 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term127 _120885 s s'.
Proof. exact (EQ_MP (@lem5774567 _120885 s s') (@lem5774904 _120885 s s')). Qed.
Lemma lem5774906 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term109 _120885 s s'.
Proof. exact (EQ_MP (@lem5774563 _120885 s s') (@lem5774905 _120885 s s')). Qed.
Lemma lem5774907 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : term106 _120885 s s'.
Proof. exact (EQ_MP (@lem5774441 _120885 s s') (@lem5774906 _120885 s s')). Qed.
Lemma lem5774921 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5774922 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem5774921 A s t). Qed.
Lemma lem5774923 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (t = (term145 A s t)) = (term146 A s t).
Proof. exact (@lem5774922 A t (term145 A s t)). Qed.
Lemma lem5774932 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term146 A s t) = (t = (term145 A s t)).
Proof. exact (SYM (@lem5774923 A s t)). Qed.
Lemma lem5774940 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774941 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5774940 A P x). Qed.
Lemma lem5774942 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5774941 A t x). Qed.
Lemma lem5774943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5774944 {A : Type'} (t : A -> Prop) (x : A) : (term147 A x t) = (term148 A t x).
Proof. exact (MK_COMB (@lem5774943) (@lem5774942 A t x)). Qed.
Lemma lem5774946 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5774947 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (@lem5774946 A s x t). Qed.
Lemma lem5774948 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term149 A x s t) = (term150 A x s t).
Proof. exact (@lem5774947 A (@DIFF A t s) x (@INTER A s t)). Qed.
Lemma lem5774952 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5774953 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (@lem5774952 A s x t). Qed.
Lemma lem5774954 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term8 A x t s) = (term9 A t x s).
Proof. exact (@lem5774953 A t x s). Qed.
Lemma lem5774958 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774959 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5774958 A P x). Qed.
Lemma lem5774960 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5774959 A t x). Qed.
Lemma lem5774961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774962 {A : Type'} (t : A -> Prop) (x : A) : (term10 A x t) = (term11 A t x).
Proof. exact (MK_COMB (@lem5774961) (@lem5774960 A t x)). Qed.
Lemma lem5774964 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774965 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5774964 A P x). Qed.
Lemma lem5774966 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5774965 A s x). Qed.
Lemma lem5774967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5774968 {A : Type'} (s : A -> Prop) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (MK_COMB (@lem5774967) (@lem5774966 A s x)). Qed.
Lemma lem5774969 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term9 A t x s) = (term14 A t s x).
Proof. exact (MK_COMB (@lem5774962 A t x) (@lem5774968 A s x)). Qed.
Lemma lem5774972 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term8 A x t s) = (term14 A t s x).
Proof. exact (TRANS (@lem5774954 A t x s) (@lem5774969 A t s x)). Qed.
Lemma lem5774973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5774974 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term116 A x t s) = (term117 A t s x).
Proof. exact (MK_COMB (@lem5774973) (@lem5774972 A t s x)). Qed.
Lemma lem5774976 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5774977 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (@lem5774976 A s x t). Qed.
Lemma lem5774981 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774982 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5774981 A P x). Qed.
Lemma lem5774983 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5774982 A s x). Qed.
Lemma lem5774984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5774985 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem5774984) (@lem5774983 A s x)). Qed.
Lemma lem5774987 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5774988 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5774987 A P x). Qed.
Lemma lem5774989 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5774988 A t x). Qed.
Lemma lem5774990 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term5 A s x t) = (term17 A s t x).
Proof. exact (MK_COMB (@lem5774985 A s x) (@lem5774989 A t x)). Qed.
Lemma lem5774993 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term4 A x s t) = (term17 A s t x).
Proof. exact (TRANS (@lem5774977 A s x t) (@lem5774990 A s t x)). Qed.
Lemma lem5774994 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term150 A x s t) = (term151 A s t x).
Proof. exact (MK_COMB (@lem5774974 A t s x) (@lem5774993 A s t x)). Qed.
Lemma lem5774997 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term149 A x s t) = (term151 A s t x).
Proof. exact (TRANS (@lem5774948 A x s t) (@lem5774994 A s t x)). Qed.
Lemma lem5774998 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x t) = (term149 A x s t)) = ((t x) = (term151 A s t x)).
Proof. exact (MK_COMB (@lem5774944 A t x) (@lem5774997 A s t x)). Qed.
Lemma lem5775001 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A s t) = (term153 A s t).
Proof. exact (fun_ext (fun x : A => @lem5774998 A s t x)). Qed.
Lemma lem5775002 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5775003 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term146 A s t) = (term154 A s t).
Proof. exact (MK_COMB (@lem5775002 A) (@lem5775001 A s t)). Qed.
Lemma lem5775008 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term146 A s t).
Proof. exact (SYM (@lem5775003 A s t)). Qed.
Lemma lem5775010 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5775011 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term155 A s t).
Proof. exact (@lem5775010 (term154 A s t)). Qed.
Lemma lem5775012 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term155 A s t) = (term154 A s t).
Proof. exact (SYM (@lem5775011 A s t)). Qed.
Lemma lem5775013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term156 A s t) : term156 A s t.
Proof. exact (h1). Qed.
Lemma lem5775016 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term155 A s t) : term155 A s t.
Proof. exact (h1). Qed.
Lemma lem5775017 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term157 A s t.
Proof. exact (fun h0 : term155 A s t => @lem5775016 A s t h0). Qed.
Lemma lem5775018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term157 A s t) : term157 A s t.
Proof. exact (h1). Qed.
Lemma lem5775019 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term155 A s t) : term155 A s t.
Proof. exact (h1). Qed.
Lemma lem5775020 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term155 A s t) (h2 : term157 A s t) : term155 A s t.
Proof. exact (@lem5775018 A s t h2 (@lem5775019 A s t h1)). Qed.
Lemma lem5775021 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term155 A s t) : term158 A s t.
Proof. exact (fun h0 : term157 A s t => @lem5775020 A s t h1 h0). Qed.
Lemma lem5775022 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term157 A s t) : term157 A s t.
Proof. exact (h1). Qed.
Lemma lem5775023 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term155 A s t) (h2 : term157 A s t) : term155 A s t.
Proof. exact (@lem5775021 A s t h1 (@lem5775022 A s t h2)). Qed.
Lemma lem5775024 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term157 A s t) : term157 A s t.
Proof. exact (fun h0 : term155 A s t => @lem5775023 A s t h0 h1). Qed.
Lemma lem5775025 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term159 A s t.
Proof. exact (fun h0 : term157 A s t => @lem5775024 A s t h0). Qed.
Lemma lem5775028 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term157 A s t.
Proof. exact (@lem5775025 A s t (@lem5775017 A s t)). Qed.
Lemma lem5775029 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term157 A s t.
Proof. exact (@lem5775028 A s t). Qed.
Lemma lem5775039 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5775040 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term155 A s t) = (term160 A s t).
Proof. exact (@lem5775039 (term156 A s t)). Qed.
Lemma lem5775042 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5775043 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term160 A s t) = (term154 A s t).
Proof. exact (@lem5775042 (term154 A s t)). Qed.
Lemma lem5775048 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term155 A s t) = (term154 A s t).
Proof. exact (TRANS (@lem5775040 A s t) (@lem5775043 A s t)). Qed.
Lemma lem5775055 {A : Type'} (t : A -> Prop) : (term161 A t) = (term162 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5775048 A s t)). Qed.
Lemma lem5775056 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775057 {A : Type'} (t : A -> Prop) : (term163 A t) = (term164 A t).
Proof. exact (MK_COMB (@lem5775056 A) (@lem5775055 A t)). Qed.
Lemma lem5775062 {A : Type'} : (term165 A) = (term166 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5775057 A t)). Qed.
Lemma lem5775063 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775072 {A : Type'} : (term167 A) = (term168 A).
Proof. exact (MK_COMB (@lem5775063 A) (@lem5775062 A)). Qed.
Lemma lem5775091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((t x) = (term151 A s t x)) = ((t x) = (term151 A s t x)).
Proof. exact (eq_refl ((t x) = (term151 A s t x))). Qed.
Lemma lem5775092 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term153 A s t) = (term153 A s t).
Proof. exact (fun_ext (fun x : A => @lem5775091 A s t x)). Qed.
Lemma lem5775093 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5775094 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term154 A s t).
Proof. exact (MK_COMB (@lem5775093 A) (@lem5775092 A s t)). Qed.
Lemma lem5775095 {A : Type'} (t : A -> Prop) : (term162 A t) = (term162 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5775094 A s t)). Qed.
Lemma lem5775096 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775097 {A : Type'} (t : A -> Prop) : (term164 A t) = (term164 A t).
Proof. exact (MK_COMB (@lem5775096 A) (@lem5775095 A t)). Qed.
Lemma lem5775098 {A : Type'} : (term166 A) = (term166 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5775097 A t)). Qed.
Lemma lem5775099 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775100 {A : Type'} : (term168 A) = (term168 A).
Proof. exact (MK_COMB (@lem5775099 A) (@lem5775098 A)). Qed.
Lemma lem5775127 {A : Type'} : (term167 A) = (term168 A).
Proof. exact (TRANS (@lem5775072 A) (@lem5775100 A)). Qed.
Lemma lem5775128 {A : Type'} : (term168 A) = (term167 A).
Proof. exact (SYM (@lem5775127 A)). Qed.
Lemma lem5775130 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5775131 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((t x) = (term151 A s t x)) = (term169 A s t x).
Proof. exact (@lem5775130 ((t x) = (term151 A s t x))). Qed.
Lemma lem5775132 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term169 A s t x) = ((t x) = (term151 A s t x)).
Proof. exact (SYM (@lem5775131 A s t x)). Qed.
Lemma lem5775133 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term170 A s t x) : term170 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775141 {A : Type'} (s : A -> Prop) (x : A) : (term171 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem5775143 {A : Type'} (t : A -> Prop) (x : A) : (term172 A t x) = (term172 A t x).
Proof. exact (eq_refl (term172 A t x)). Qed.
Lemma lem5775144 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term173 A t s x) = (term174 A t s x).
Proof. exact (MK_COMB (@lem5775143 A t x) (@lem5775141 A s x)). Qed.
Lemma lem5775145 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term175 A t s x) = (term173 A t s x).
Proof. exact (@lem17045 (t x) (term13 A s x)). Qed.
Lemma lem5775146 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term175 A t s x) = (term174 A t s x).
Proof. exact (TRANS (@lem5775145 A t s x) (@lem5775144 A t s x)). Qed.
Lemma lem5775158 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term176 A s t x) = (term177 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem5775162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5775163 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term178 A t s x) = (term179 A t s x).
Proof. exact (MK_COMB (@lem5775162) (@lem5775146 A t s x)). Qed.
Lemma lem5775164 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term180 A s t x) = (term181 A s t x).
Proof. exact (MK_COMB (@lem5775163 A t s x) (@lem5775158 A s t x)). Qed.
Lemma lem5775165 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term182 A s t x) = (term180 A s t x).
Proof. exact (@lem17160 (term14 A t s x) (term17 A s t x)). Qed.
Lemma lem5775166 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term182 A s t x) = (term181 A s t x).
Proof. exact (TRANS (@lem5775165 A s t x) (@lem5775164 A s t x)). Qed.
Lemma lem5775172 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term183 A s t x) = (term183 A s t x).
Proof. exact (eq_refl (term183 A s t x)). Qed.
Lemma lem5775174 {A : Type'} (t : A -> Prop) (x : A) : (term11 A t x) = (term11 A t x).
Proof. exact (eq_refl (term11 A t x)). Qed.
Lemma lem5775175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term184 A s t x) = (term185 A s t x).
Proof. exact (MK_COMB (@lem5775174 A t x) (@lem5775166 A s t x)). Qed.
Lemma lem5775176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5775177 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term186 A s t x) = (term187 A s t x).
Proof. exact (MK_COMB (@lem5775176) (@lem5775175 A s t x)). Qed.
Lemma lem5775178 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term188 A s t x) = (term189 A s t x).
Proof. exact (MK_COMB (@lem5775177 A s t x) (@lem5775172 A s t x)). Qed.
Lemma lem5775179 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term170 A s t x) = (term188 A s t x).
Proof. exact (@lem17646 (t x) (term151 A s t x)). Qed.
Lemma lem5775184 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term170 A s t x) = (term189 A s t x).
Proof. exact (TRANS (@lem5775179 A s t x) (@lem5775178 A s t x)). Qed.
Lemma lem5775253 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term170 A s t x) : term189 A s t x.
Proof. exact (EQ_MP (@lem5775184 A s t x) (@lem5775133 A s t x h1)). Qed.
Lemma lem5775254 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : term185 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775255 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) : term183 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775256 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : term181 A s t x.
Proof. exact (proj2 (@lem5775254 A s t x h1)). Qed.
Lemma lem5775258 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : term177 A s t x.
Proof. exact (proj2 (@lem5775256 A s t x h1)). Qed.
Lemma lem5775259 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : term174 A t s x.
Proof. exact (proj1 (@lem5775256 A s t x h1)). Qed.
Lemma lem5775266 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) : term151 A s t x.
Proof. exact (proj2 (@lem5775255 A s t x h1)). Qed.
Lemma lem5775268 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term14 A t s x) : term14 A t s x.
Proof. exact (h1). Qed.
Lemma lem5775269 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : term17 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775285 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775293 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5775297 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5775305 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775309 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775317 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775351 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775355 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5775357 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5775361 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775363 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775367 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5775371 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) : term13 A t x.
Proof. exact (proj1 (@lem5775255 A s t x h1)). Qed.
Lemma lem5775377 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) : term13 A t x.
Proof. exact (proj1 (@lem5775255 A s t x h1)). Qed.
Lemma lem5775383 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : t x.
Proof. exact (proj1 (@lem5775254 A s t x h1)). Qed.
Lemma lem5775384 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : term41 A t x.
Proof. exact (fun h0 : term13 A t x => @lem5775383 A s t x h1). Qed.
Lemma lem5775386 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775387 {A : Type'} (t : A -> Prop) (x : A) : (term41 A t x) = (t x).
Proof. exact (@lem5775386 (t x)). Qed.
Lemma lem5775388 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : t x.
Proof. exact (EQ_MP (@lem5775387 A t x) (@lem5775384 A s t x h1)). Qed.
Lemma lem5775391 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5775393 {A : Type'} (t : A -> Prop) (x : A) : (term13 A t x) = (term43 A t x).
Proof. exact (@lem5775391 (t x)). Qed.
Lemma lem5775396 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term43 A t x.
Proof. exact (EQ_MP (@lem5775393 A t x) (@lem5775351 A t x h1)). Qed.
Lemma lem5775399 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (@lem5775396 A t x h1 (@lem5775388 A s t x h2)). Qed.
Lemma lem5775400 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5775399 A s t x h1 h2). Qed.
Lemma lem5775402 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775403 : term44 = False.
Proof. exact (@lem5775402 False). Qed.
Lemma lem5775404 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775403) (@lem5775400 A s t x h1 h2)). Qed.
Lemma lem5775406 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem5775407 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term41 A s x.
Proof. exact (fun h0 : term13 A s x => @lem5775406 A s x h1). Qed.
Lemma lem5775409 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775410 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (s x).
Proof. exact (@lem5775409 (s x)). Qed.
Lemma lem5775411 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem5775410 A s x) (@lem5775407 A s x h1)). Qed.
Lemma lem5775414 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5775416 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term43 A s x).
Proof. exact (@lem5775414 (s x)). Qed.
Lemma lem5775419 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term43 A s x.
Proof. exact (EQ_MP (@lem5775416 A s x) (@lem5775355 A s x h1)). Qed.
Lemma lem5775422 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (@lem5775419 A s x h1 (@lem5775411 A s x h2)). Qed.
Lemma lem5775423 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : term44.
Proof. exact (fun h0 : ~ False => @lem5775422 A s x h1 h2). Qed.
Lemma lem5775425 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775426 : term44 = False.
Proof. exact (@lem5775425 False). Qed.
Lemma lem5775427 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem5775426) (@lem5775423 A s x h1 h2)). Qed.
Lemma lem5775429 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : t x.
Proof. exact (proj1 (@lem5775254 A s t x h1)). Qed.
Lemma lem5775430 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : term41 A t x.
Proof. exact (fun h0 : term13 A t x => @lem5775429 A s t x h1). Qed.
Lemma lem5775432 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775433 {A : Type'} (t : A -> Prop) (x : A) : (term41 A t x) = (t x).
Proof. exact (@lem5775432 (t x)). Qed.
Lemma lem5775434 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : t x.
Proof. exact (EQ_MP (@lem5775433 A t x) (@lem5775430 A s t x h1)). Qed.
Lemma lem5775437 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5775439 {A : Type'} (t : A -> Prop) (x : A) : (term13 A t x) = (term43 A t x).
Proof. exact (@lem5775437 (t x)). Qed.
Lemma lem5775442 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term43 A t x.
Proof. exact (EQ_MP (@lem5775439 A t x) (@lem5775361 A t x h1)). Qed.
Lemma lem5775445 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (@lem5775442 A t x h1 (@lem5775434 A s t x h2)). Qed.
Lemma lem5775446 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5775445 A s t x h1 h2). Qed.
Lemma lem5775448 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775449 : term44 = False.
Proof. exact (@lem5775448 False). Qed.
Lemma lem5775450 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775449) (@lem5775446 A s t x h1 h2)). Qed.
Lemma lem5775452 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : t x.
Proof. exact (proj1 (@lem5775254 A s t x h1)). Qed.
Lemma lem5775453 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : term41 A t x.
Proof. exact (fun h0 : term13 A t x => @lem5775452 A s t x h1). Qed.
Lemma lem5775455 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775456 {A : Type'} (t : A -> Prop) (x : A) : (term41 A t x) = (t x).
Proof. exact (@lem5775455 (t x)). Qed.
Lemma lem5775457 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : t x.
Proof. exact (EQ_MP (@lem5775456 A t x) (@lem5775453 A s t x h1)). Qed.
Lemma lem5775460 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5775462 {A : Type'} (t : A -> Prop) (x : A) : (term13 A t x) = (term43 A t x).
Proof. exact (@lem5775460 (t x)). Qed.
Lemma lem5775465 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term43 A t x.
Proof. exact (EQ_MP (@lem5775462 A t x) (@lem5775367 A t x h1)). Qed.
Lemma lem5775468 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (@lem5775465 A t x h1 (@lem5775457 A s t x h2)). Qed.
Lemma lem5775469 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5775468 A s t x h1 h2). Qed.
Lemma lem5775471 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775472 : term44 = False.
Proof. exact (@lem5775471 False). Qed.
Lemma lem5775473 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775472) (@lem5775469 A s t x h1 h2)). Qed.
Lemma lem5775475 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term14 A t s x) : t x.
Proof. exact (proj1 (@lem5775268 A t s x h1)). Qed.
Lemma lem5775476 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term14 A t s x) : term41 A t x.
Proof. exact (fun h0 : term13 A t x => @lem5775475 A t s x h1). Qed.
Lemma lem5775478 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775479 {A : Type'} (t : A -> Prop) (x : A) : (term41 A t x) = (t x).
Proof. exact (@lem5775478 (t x)). Qed.
Lemma lem5775480 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term14 A t s x) : t x.
Proof. exact (EQ_MP (@lem5775479 A t x) (@lem5775476 A t s x h1)). Qed.
Lemma lem5775483 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5775485 {A : Type'} (t : A -> Prop) (x : A) : (term13 A t x) = (term43 A t x).
Proof. exact (@lem5775483 (t x)). Qed.
Lemma lem5775488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) : term43 A t x.
Proof. exact (EQ_MP (@lem5775485 A t x) (@lem5775371 A s t x h1)). Qed.
Lemma lem5775491 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term183 A s t x) (h2 : term14 A t s x) : False.
Proof. exact (@lem5775488 A s t x h1 (@lem5775480 A t s x h2)). Qed.
Lemma lem5775492 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term183 A s t x) (h2 : term14 A t s x) : term44.
Proof. exact (fun h0 : ~ False => @lem5775491 A t s x h1 h2). Qed.
Lemma lem5775494 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775495 : term44 = False.
Proof. exact (@lem5775494 False). Qed.
Lemma lem5775496 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term183 A s t x) (h2 : term14 A t s x) : False.
Proof. exact (EQ_MP (@lem5775495) (@lem5775492 A t s x h1 h2)). Qed.
Lemma lem5775498 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : t x.
Proof. exact (proj2 (@lem5775269 A s t x h1)). Qed.
Lemma lem5775499 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : term41 A t x.
Proof. exact (fun h0 : term13 A t x => @lem5775498 A s t x h1). Qed.
Lemma lem5775501 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775502 {A : Type'} (t : A -> Prop) (x : A) : (term41 A t x) = (t x).
Proof. exact (@lem5775501 (t x)). Qed.
Lemma lem5775503 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : t x.
Proof. exact (EQ_MP (@lem5775502 A t x) (@lem5775499 A s t x h1)). Qed.
Lemma lem5775506 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5775508 {A : Type'} (t : A -> Prop) (x : A) : (term13 A t x) = (term43 A t x).
Proof. exact (@lem5775506 (t x)). Qed.
Lemma lem5775511 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) : term43 A t x.
Proof. exact (EQ_MP (@lem5775508 A t x) (@lem5775377 A s t x h1)). Qed.
Lemma lem5775514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) (h2 : term17 A s t x) : False.
Proof. exact (@lem5775511 A s t x h1 (@lem5775503 A s t x h2)). Qed.
Lemma lem5775515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) (h2 : term17 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5775514 A s t x h1 h2). Qed.
Lemma lem5775517 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5775518 : term44 = False.
Proof. exact (@lem5775517 False). Qed.
Lemma lem5775519 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) (h2 : term17 A s t x) : False.
Proof. exact (EQ_MP (@lem5775518) (@lem5775515 A s t x h1 h2)). Qed.
Lemma lem5775520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775473 A s t x h1 h2) (fun h3 : False => @lem5775367 A t x h1)). Qed.
Lemma lem5775521 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775520 A s t x h1 h2) (@lem5775367 A t x h1)). Qed.
Lemma lem5775522 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775450 A s t x h1 h2) (fun h3 : False => @lem5775363 A t x h1)). Qed.
Lemma lem5775523 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775522 A s t x h1 h2) (@lem5775363 A t x h1)). Qed.
Lemma lem5775524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775523 A s t x h1 h2) (fun h3 : False => @lem5775361 A t x h1)). Qed.
Lemma lem5775525 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775524 A s t x h1 h2) (@lem5775361 A t x h1)). Qed.
Lemma lem5775526 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5775427 A s x h1 h2) (fun h3 : False => @lem5775357 A s x h2)). Qed.
Lemma lem5775527 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem5775526 A s x h1 h2) (@lem5775357 A s x h2)). Qed.
Lemma lem5775528 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5775527 A s x h1 h2) (fun h3 : False => @lem5775355 A s x h1)). Qed.
Lemma lem5775529 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem5775528 A s x h1 h2) (@lem5775355 A s x h1)). Qed.
Lemma lem5775530 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775404 A s t x h1 h2) (fun h3 : False => @lem5775351 A t x h1)). Qed.
Lemma lem5775531 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775530 A s t x h1 h2) (@lem5775351 A t x h1)). Qed.
Lemma lem5775532 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775521 A s t x h1 h2) (fun h3 : False => @lem5775317 A t x h1)). Qed.
Lemma lem5775533 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775532 A s t x h1 h2) (@lem5775317 A t x h1)). Qed.
Lemma lem5775534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775525 A s t x h1 h2) (fun h3 : False => @lem5775309 A t x h1)). Qed.
Lemma lem5775535 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775534 A s t x h1 h2) (@lem5775309 A t x h1)). Qed.
Lemma lem5775536 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775535 A s t x h1 h2) (fun h3 : False => @lem5775305 A t x h1)). Qed.
Lemma lem5775537 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775536 A s t x h1 h2) (@lem5775305 A t x h1)). Qed.
Lemma lem5775538 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5775529 A s x h1 h2) (fun h3 : False => @lem5775297 A s x h2)). Qed.
Lemma lem5775539 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem5775538 A s x h1 h2) (@lem5775297 A s x h2)). Qed.
Lemma lem5775540 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5775539 A s x h1 h2) (fun h3 : False => @lem5775293 A s x h1)). Qed.
Lemma lem5775541 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem5775540 A s x h1 h2) (@lem5775293 A s x h1)). Qed.
Lemma lem5775542 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775531 A s t x h1 h2) (fun h3 : False => @lem5775285 A t x h1)). Qed.
Lemma lem5775543 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775542 A s t x h1 h2) (@lem5775285 A t x h1)). Qed.
Lemma lem5775544 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775533 A s t x h1 h2) (fun h3 : False => @lem5775317 A t x h1)). Qed.
Lemma lem5775545 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775544 A s t x h1 h2) (@lem5775317 A t x h1)). Qed.
Lemma lem5775546 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775537 A s t x h1 h2) (fun h3 : False => @lem5775309 A t x h1)). Qed.
Lemma lem5775547 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775546 A s t x h1 h2) (@lem5775309 A t x h1)). Qed.
Lemma lem5775548 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775547 A s t x h1 h2) (fun h3 : False => @lem5775305 A t x h1)). Qed.
Lemma lem5775549 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775548 A s t x h1 h2) (@lem5775305 A t x h1)). Qed.
Lemma lem5775550 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem5775541 A s x h1 h2) (fun h3 : False => @lem5775297 A s x h2)). Qed.
Lemma lem5775551 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem5775550 A s x h1 h2) (@lem5775297 A s x h2)). Qed.
Lemma lem5775552 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5775551 A s x h1 h2) (fun h3 : False => @lem5775293 A s x h1)). Qed.
Lemma lem5775553 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem5775552 A s x h1 h2) (@lem5775293 A s x h1)). Qed.
Lemma lem5775554 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5775543 A s t x h1 h2) (fun h3 : False => @lem5775285 A t x h1)). Qed.
Lemma lem5775555 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (EQ_MP (@lem5775554 A s t x h1 h2) (@lem5775285 A t x h1)). Qed.
Lemma lem5775556 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term183 A s t x) : False.
Proof. exact (or_elim (@lem5775266 A s t x h1) (fun h0 : term14 A t s x => @lem5775496 A t s x h1 h0) (fun h0 : term17 A s t x => @lem5775519 A s t x h1 h0)). Qed.
Lemma lem5775557 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term185 A s t x) : False.
Proof. exact (or_elim (@lem5775259 A s t x h2) (fun h0 : term13 A t x => @lem5775549 A s t x h1 h2) (fun h0 : s x => @lem5775545 A s t x h1 h2)). Qed.
Lemma lem5775558 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term185 A s t x) : False.
Proof. exact (or_elim (@lem5775259 A s t x h2) (fun h0 : term13 A t x => @lem5775555 A s t x h0 h2) (fun h0 : s x => @lem5775553 A s x h1 h0)). Qed.
Lemma lem5775559 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term185 A s t x) : False.
Proof. exact (or_elim (@lem5775258 A s t x h1) (fun h0 : term13 A s x => @lem5775558 A s t x h0 h1) (fun h0 : term13 A t x => @lem5775557 A s t x h0 h1)). Qed.
Lemma lem5775560 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term170 A s t x) : False.
Proof. exact (or_elim (@lem5775253 A s t x h1) (fun h0 : term185 A s t x => @lem5775559 A s t x h0) (fun h0 : term183 A s t x => @lem5775556 A s t x h0)). Qed.
Lemma lem5775561 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term170 A s t x) : (term170 A s t x) = False.
Proof. exact (prop_ext (fun h2 : term170 A s t x => @lem5775560 A s t x h1) (fun h2 : False => @lem5775133 A s t x h1)). Qed.
Lemma lem5775562 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term170 A s t x) : False.
Proof. exact (EQ_MP (@lem5775561 A s t x h1) (@lem5775133 A s t x h1)). Qed.
Lemma lem5775563 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term169 A s t x.
Proof. exact (fun h0 : term170 A s t x => @lem5775562 A s t x h0). Qed.
Lemma lem5775564 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (t x) = (term151 A s t x).
Proof. exact (EQ_MP (@lem5775132 A s t x) (@lem5775563 A s t x)). Qed.
Lemma lem5775569 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term154 A s t.
Proof. exact (fun x : A => @lem5775564 A s t x). Qed.
Lemma lem5775574 {A : Type'} (t : A -> Prop) : term164 A t.
Proof. exact (fun s : A -> Prop => @lem5775569 A s t). Qed.
Lemma lem5775579 {A : Type'} : term168 A.
Proof. exact (fun t : A -> Prop => @lem5775574 A t). Qed.
Lemma lem5775580 {A : Type'} : term167 A.
Proof. exact (EQ_MP (@lem5775128 A) (@lem5775579 A)). Qed.
Lemma lem5775581 {A : Type'} (t : A -> Prop) : term190 A t.
Proof. exact (@lem5775580 A t). Qed.
Lemma lem5775582 {A : Type'} (t : A -> Prop) : (term190 A t) = (term163 A t).
Proof. exact (eq_refl (term190 A t)). Qed.
Lemma lem5775583 {A : Type'} (t : A -> Prop) : term163 A t.
Proof. exact (EQ_MP (@lem5775582 A t) (@lem5775581 A t)). Qed.
Lemma lem5775584 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term191 A t s.
Proof. exact (@lem5775583 A t s). Qed.
Lemma lem5775585 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term191 A t s) = (term155 A s t).
Proof. exact (eq_refl (term191 A t s)). Qed.
Lemma lem5775586 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term155 A s t.
Proof. exact (EQ_MP (@lem5775585 A s t) (@lem5775584 A t s)). Qed.
Lemma lem5775588 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term155 A s t.
Proof. exact (@lem5775029 A s t (@lem5775586 A s t)). Qed.
Lemma lem5775589 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term156 A s t) : False.
Proof. exact (@lem5775588 A s t (@lem5775013 A s t h1)). Qed.
Lemma lem5775590 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term156 A s t) : (term156 A s t) = False.
Proof. exact (prop_ext (fun h2 : term156 A s t => @lem5775589 A s t h1) (fun h2 : False => @lem5775013 A s t h1)). Qed.
Lemma lem5775591 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term156 A s t) : False.
Proof. exact (EQ_MP (@lem5775590 A s t h1) (@lem5775013 A s t h1)). Qed.
Lemma lem5775592 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term155 A s t.
Proof. exact (fun h0 : term156 A s t => @lem5775591 A s t h0). Qed.
Lemma lem5775593 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term154 A s t.
Proof. exact (EQ_MP (@lem5775012 A s t) (@lem5775592 A s t)). Qed.
Lemma lem5775594 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term146 A s t.
Proof. exact (EQ_MP (@lem5775008 A s t) (@lem5775593 A s t)). Qed.
Lemma lem5775609 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5775610 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (@lem5775609 A s t). Qed.
Lemma lem5775611 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term192 A s t)) = (term193 A s t).
Proof. exact (@lem5775610 A s (term192 A s t)). Qed.
Lemma lem5775620 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term193 A s t) = (s = (term192 A s t)).
Proof. exact (SYM (@lem5775611 A s t)). Qed.
Lemma lem5775628 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5775629 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5775628 A P x). Qed.
Lemma lem5775630 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5775629 A s x). Qed.
Lemma lem5775631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5775632 {A : Type'} (s : A -> Prop) (x : A) : (term147 A x s) = (term148 A s x).
Proof. exact (MK_COMB (@lem5775631) (@lem5775630 A s x)). Qed.
Lemma lem5775634 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5775635 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (@lem5775634 A s x t). Qed.
Lemma lem5775636 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term194 A x s t) = (term195 A x s t).
Proof. exact (@lem5775635 A (@DIFF A s t) x (@INTER A s t)). Qed.
Lemma lem5775640 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5775641 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (@lem5775640 A s x t). Qed.
Lemma lem5775645 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5775646 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5775645 A P x). Qed.
Lemma lem5775647 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5775646 A s x). Qed.
Lemma lem5775648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5775649 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem5775648) (@lem5775647 A s x)). Qed.
Lemma lem5775651 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5775652 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5775651 A P x). Qed.
Lemma lem5775653 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5775652 A t x). Qed.
Lemma lem5775654 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5775655 {A : Type'} (t : A -> Prop) (x : A) : (term12 A x t) = (term13 A t x).
Proof. exact (MK_COMB (@lem5775654) (@lem5775653 A t x)). Qed.
Lemma lem5775656 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term9 A s x t) = (term14 A s t x).
Proof. exact (MK_COMB (@lem5775649 A s x) (@lem5775655 A t x)). Qed.
Lemma lem5775659 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term8 A x s t) = (term14 A s t x).
Proof. exact (TRANS (@lem5775641 A s x t) (@lem5775656 A s t x)). Qed.
Lemma lem5775660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5775661 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term116 A x s t) = (term117 A s t x).
Proof. exact (MK_COMB (@lem5775660) (@lem5775659 A s t x)). Qed.
Lemma lem5775663 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5775664 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (@lem5775663 A s x t). Qed.
Lemma lem5775668 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5775669 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5775668 A P x). Qed.
Lemma lem5775670 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5775669 A s x). Qed.
Lemma lem5775671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5775672 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem5775671) (@lem5775670 A s x)). Qed.
Lemma lem5775674 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5775675 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5775674 A P x). Qed.
Lemma lem5775676 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5775675 A t x). Qed.
Lemma lem5775677 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term5 A s x t) = (term17 A s t x).
Proof. exact (MK_COMB (@lem5775672 A s x) (@lem5775676 A t x)). Qed.
Lemma lem5775680 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term4 A x s t) = (term17 A s t x).
Proof. exact (TRANS (@lem5775664 A s x t) (@lem5775677 A s t x)). Qed.
Lemma lem5775681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term195 A x s t) = (term196 A s t x).
Proof. exact (MK_COMB (@lem5775661 A s t x) (@lem5775680 A s t x)). Qed.
Lemma lem5775684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term194 A x s t) = (term196 A s t x).
Proof. exact (TRANS (@lem5775636 A x s t) (@lem5775681 A s t x)). Qed.
Lemma lem5775685 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (term194 A x s t)) = ((s x) = (term196 A s t x)).
Proof. exact (MK_COMB (@lem5775632 A s x) (@lem5775684 A s t x)). Qed.
Lemma lem5775688 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term197 A s t) = (term198 A s t).
Proof. exact (fun_ext (fun x : A => @lem5775685 A s t x)). Qed.
Lemma lem5775689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5775690 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term193 A s t) = (term199 A s t).
Proof. exact (MK_COMB (@lem5775689 A) (@lem5775688 A s t)). Qed.
Lemma lem5775695 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term199 A s t) = (term193 A s t).
Proof. exact (SYM (@lem5775690 A s t)). Qed.
Lemma lem5775697 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5775698 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term199 A s t) = (term200 A s t).
Proof. exact (@lem5775697 (term199 A s t)). Qed.
Lemma lem5775699 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term200 A s t) = (term199 A s t).
Proof. exact (SYM (@lem5775698 A s t)). Qed.
Lemma lem5775700 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term201 A s t) : term201 A s t.
Proof. exact (h1). Qed.
Lemma lem5775703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term200 A s t) : term200 A s t.
Proof. exact (h1). Qed.
Lemma lem5775704 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term202 A s t.
Proof. exact (fun h0 : term200 A s t => @lem5775703 A s t h0). Qed.
Lemma lem5775705 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term202 A s t) : term202 A s t.
Proof. exact (h1). Qed.
Lemma lem5775706 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term200 A s t) : term200 A s t.
Proof. exact (h1). Qed.
Lemma lem5775707 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term200 A s t) (h2 : term202 A s t) : term200 A s t.
Proof. exact (@lem5775705 A s t h2 (@lem5775706 A s t h1)). Qed.
Lemma lem5775708 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term200 A s t) : term203 A s t.
Proof. exact (fun h0 : term202 A s t => @lem5775707 A s t h1 h0). Qed.
Lemma lem5775709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term202 A s t) : term202 A s t.
Proof. exact (h1). Qed.
Lemma lem5775710 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term200 A s t) (h2 : term202 A s t) : term200 A s t.
Proof. exact (@lem5775708 A s t h1 (@lem5775709 A s t h2)). Qed.
Lemma lem5775711 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term202 A s t) : term202 A s t.
Proof. exact (fun h0 : term200 A s t => @lem5775710 A s t h0 h1). Qed.
Lemma lem5775712 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term204 A s t.
Proof. exact (fun h0 : term202 A s t => @lem5775711 A s t h0). Qed.
Lemma lem5775715 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term202 A s t.
Proof. exact (@lem5775712 A s t (@lem5775704 A s t)). Qed.
Lemma lem5775716 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term202 A s t.
Proof. exact (@lem5775715 A s t). Qed.
Lemma lem5775726 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5775727 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term200 A s t) = (term205 A s t).
Proof. exact (@lem5775726 (term201 A s t)). Qed.
Lemma lem5775729 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5775730 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term205 A s t) = (term199 A s t).
Proof. exact (@lem5775729 (term199 A s t)). Qed.
Lemma lem5775735 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term200 A s t) = (term199 A s t).
Proof. exact (TRANS (@lem5775727 A s t) (@lem5775730 A s t)). Qed.
Lemma lem5775742 {A : Type'} (t : A -> Prop) : (term206 A t) = (term207 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5775735 A s t)). Qed.
Lemma lem5775743 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775744 {A : Type'} (t : A -> Prop) : (term208 A t) = (term209 A t).
Proof. exact (MK_COMB (@lem5775743 A) (@lem5775742 A t)). Qed.
Lemma lem5775749 {A : Type'} : (term210 A) = (term211 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5775744 A t)). Qed.
Lemma lem5775750 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775759 {A : Type'} : (term212 A) = (term213 A).
Proof. exact (MK_COMB (@lem5775750 A) (@lem5775749 A)). Qed.
Lemma lem5775778 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (term196 A s t x)) = ((s x) = (term196 A s t x)).
Proof. exact (eq_refl ((s x) = (term196 A s t x))). Qed.
Lemma lem5775779 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term198 A s t) = (term198 A s t).
Proof. exact (fun_ext (fun x : A => @lem5775778 A s t x)). Qed.
Lemma lem5775780 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5775781 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term199 A s t) = (term199 A s t).
Proof. exact (MK_COMB (@lem5775780 A) (@lem5775779 A s t)). Qed.
Lemma lem5775782 {A : Type'} (t : A -> Prop) : (term207 A t) = (term207 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5775781 A s t)). Qed.
Lemma lem5775783 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775784 {A : Type'} (t : A -> Prop) : (term209 A t) = (term209 A t).
Proof. exact (MK_COMB (@lem5775783 A) (@lem5775782 A t)). Qed.
Lemma lem5775785 {A : Type'} : (term211 A) = (term211 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5775784 A t)). Qed.
Lemma lem5775786 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5775787 {A : Type'} : (term213 A) = (term213 A).
Proof. exact (MK_COMB (@lem5775786 A) (@lem5775785 A)). Qed.
Lemma lem5775814 {A : Type'} : (term212 A) = (term213 A).
Proof. exact (TRANS (@lem5775759 A) (@lem5775787 A)). Qed.
Lemma lem5775815 {A : Type'} : (term213 A) = (term212 A).
Proof. exact (SYM (@lem5775814 A)). Qed.
Lemma lem5775817 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5775818 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (term196 A s t x)) = (term214 A s t x).
Proof. exact (@lem5775817 ((s x) = (term196 A s t x))). Qed.
Lemma lem5775819 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term214 A s t x) = ((s x) = (term196 A s t x)).
Proof. exact (SYM (@lem5775818 A s t x)). Qed.
Lemma lem5775820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term215 A s t x) : term215 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775828 {A : Type'} (t : A -> Prop) (x : A) : (term171 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem5775830 {A : Type'} (s : A -> Prop) (x : A) : (term172 A s x) = (term172 A s x).
Proof. exact (eq_refl (term172 A s x)). Qed.
Lemma lem5775831 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term173 A s t x) = (term174 A s t x).
Proof. exact (MK_COMB (@lem5775830 A s x) (@lem5775828 A t x)). Qed.
Lemma lem5775832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term175 A s t x) = (term173 A s t x).
Proof. exact (@lem17045 (s x) (term13 A t x)). Qed.
Lemma lem5775833 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term175 A s t x) = (term174 A s t x).
Proof. exact (TRANS (@lem5775832 A s t x) (@lem5775831 A s t x)). Qed.
Lemma lem5775845 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term176 A s t x) = (term177 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem5775849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5775850 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term178 A s t x) = (term179 A s t x).
Proof. exact (MK_COMB (@lem5775849) (@lem5775833 A s t x)). Qed.
Lemma lem5775851 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term216 A s t x) = (term217 A s t x).
Proof. exact (MK_COMB (@lem5775850 A s t x) (@lem5775845 A s t x)). Qed.
Lemma lem5775852 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term218 A s t x) = (term216 A s t x).
Proof. exact (@lem17160 (term14 A s t x) (term17 A s t x)). Qed.
Lemma lem5775853 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term218 A s t x) = (term217 A s t x).
Proof. exact (TRANS (@lem5775852 A s t x) (@lem5775851 A s t x)). Qed.
Lemma lem5775859 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term219 A s t x) = (term219 A s t x).
Proof. exact (eq_refl (term219 A s t x)). Qed.
Lemma lem5775861 {A : Type'} (s : A -> Prop) (x : A) : (term11 A s x) = (term11 A s x).
Proof. exact (eq_refl (term11 A s x)). Qed.
Lemma lem5775862 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term220 A s t x) = (term221 A s t x).
Proof. exact (MK_COMB (@lem5775861 A s x) (@lem5775853 A s t x)). Qed.
Lemma lem5775863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5775864 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term222 A s t x) = (term223 A s t x).
Proof. exact (MK_COMB (@lem5775863) (@lem5775862 A s t x)). Qed.
Lemma lem5775865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term224 A s t x) = (term225 A s t x).
Proof. exact (MK_COMB (@lem5775864 A s t x) (@lem5775859 A s t x)). Qed.
Lemma lem5775866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term215 A s t x) = (term224 A s t x).
Proof. exact (@lem17646 (s x) (term196 A s t x)). Qed.
Lemma lem5775871 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term215 A s t x) = (term225 A s t x).
Proof. exact (TRANS (@lem5775866 A s t x) (@lem5775865 A s t x)). Qed.
Lemma lem5775940 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term215 A s t x) : term225 A s t x.
Proof. exact (EQ_MP (@lem5775871 A s t x) (@lem5775820 A s t x h1)). Qed.
Lemma lem5775941 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : term221 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775942 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) : term219 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775943 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : term217 A s t x.
Proof. exact (proj2 (@lem5775941 A s t x h1)). Qed.
Lemma lem5775945 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : term177 A s t x.
Proof. exact (proj2 (@lem5775943 A s t x h1)). Qed.
Lemma lem5775946 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : term174 A s t x.
Proof. exact (proj1 (@lem5775943 A s t x h1)). Qed.
Lemma lem5775953 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) : term196 A s t x.
Proof. exact (proj2 (@lem5775942 A s t x h1)). Qed.
Lemma lem5775955 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term14 A s t x) : term14 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775956 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : term17 A s t x.
Proof. exact (h1). Qed.
Lemma lem5775968 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5775972 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5775980 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5775996 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5776004 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5776008 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5776036 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5776038 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5776042 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5776050 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term13 A s x.
Proof. exact (h1). Qed.
Lemma lem5776054 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term13 A t x.
Proof. exact (h1). Qed.
Lemma lem5776056 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5776058 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) : term13 A s x.
Proof. exact (proj1 (@lem5775942 A s t x h1)). Qed.
Lemma lem5776064 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) : term13 A s x.
Proof. exact (proj1 (@lem5775942 A s t x h1)). Qed.
Lemma lem5776070 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : s x.
Proof. exact (proj1 (@lem5775941 A s t x h1)). Qed.
Lemma lem5776071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : term41 A s x.
Proof. exact (fun h0 : term13 A s x => @lem5776070 A s t x h1). Qed.
Lemma lem5776073 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776074 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (s x).
Proof. exact (@lem5776073 (s x)). Qed.
Lemma lem5776075 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : s x.
Proof. exact (EQ_MP (@lem5776074 A s x) (@lem5776071 A s t x h1)). Qed.
Lemma lem5776078 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5776080 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term43 A s x).
Proof. exact (@lem5776078 (s x)). Qed.
Lemma lem5776083 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term43 A s x.
Proof. exact (EQ_MP (@lem5776080 A s x) (@lem5776036 A s x h1)). Qed.
Lemma lem5776086 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (@lem5776083 A s x h1 (@lem5776075 A s t x h2)). Qed.
Lemma lem5776087 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5776086 A s t x h1 h2). Qed.
Lemma lem5776089 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776090 : term44 = False.
Proof. exact (@lem5776089 False). Qed.
Lemma lem5776091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776090) (@lem5776087 A s t x h1 h2)). Qed.
Lemma lem5776093 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : s x.
Proof. exact (proj1 (@lem5775941 A s t x h1)). Qed.
Lemma lem5776094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : term41 A s x.
Proof. exact (fun h0 : term13 A s x => @lem5776093 A s t x h1). Qed.
Lemma lem5776096 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776097 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (s x).
Proof. exact (@lem5776096 (s x)). Qed.
Lemma lem5776098 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : s x.
Proof. exact (EQ_MP (@lem5776097 A s x) (@lem5776094 A s t x h1)). Qed.
Lemma lem5776101 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5776103 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term43 A s x).
Proof. exact (@lem5776101 (s x)). Qed.
Lemma lem5776106 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term43 A s x.
Proof. exact (EQ_MP (@lem5776103 A s x) (@lem5776042 A s x h1)). Qed.
Lemma lem5776109 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (@lem5776106 A s x h1 (@lem5776098 A s t x h2)). Qed.
Lemma lem5776110 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5776109 A s t x h1 h2). Qed.
Lemma lem5776112 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776113 : term44 = False.
Proof. exact (@lem5776112 False). Qed.
Lemma lem5776114 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776113) (@lem5776110 A s t x h1 h2)). Qed.
Lemma lem5776116 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : s x.
Proof. exact (proj1 (@lem5775941 A s t x h1)). Qed.
Lemma lem5776117 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : term41 A s x.
Proof. exact (fun h0 : term13 A s x => @lem5776116 A s t x h1). Qed.
Lemma lem5776119 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776120 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (s x).
Proof. exact (@lem5776119 (s x)). Qed.
Lemma lem5776121 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : s x.
Proof. exact (EQ_MP (@lem5776120 A s x) (@lem5776117 A s t x h1)). Qed.
Lemma lem5776124 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5776126 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term43 A s x).
Proof. exact (@lem5776124 (s x)). Qed.
Lemma lem5776129 {A : Type'} (s : A -> Prop) (x : A) (h1 : term13 A s x) : term43 A s x.
Proof. exact (EQ_MP (@lem5776126 A s x) (@lem5776050 A s x h1)). Qed.
Lemma lem5776132 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (@lem5776129 A s x h1 (@lem5776121 A s t x h2)). Qed.
Lemma lem5776133 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5776132 A s t x h1 h2). Qed.
Lemma lem5776135 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776136 : term44 = False.
Proof. exact (@lem5776135 False). Qed.
Lemma lem5776137 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776136) (@lem5776133 A s t x h1 h2)). Qed.
Lemma lem5776139 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem5776140 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term41 A t x.
Proof. exact (fun h0 : term13 A t x => @lem5776139 A t x h1). Qed.
Lemma lem5776142 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776143 {A : Type'} (t : A -> Prop) (x : A) : (term41 A t x) = (t x).
Proof. exact (@lem5776142 (t x)). Qed.
Lemma lem5776144 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem5776143 A t x) (@lem5776140 A t x h1)). Qed.
Lemma lem5776147 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5776149 {A : Type'} (t : A -> Prop) (x : A) : (term13 A t x) = (term43 A t x).
Proof. exact (@lem5776147 (t x)). Qed.
Lemma lem5776152 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) : term43 A t x.
Proof. exact (EQ_MP (@lem5776149 A t x) (@lem5776054 A t x h1)). Qed.
Lemma lem5776155 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (@lem5776152 A t x h1 (@lem5776144 A t x h2)). Qed.
Lemma lem5776156 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5776155 A t x h1 h2). Qed.
Lemma lem5776158 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776159 : term44 = False.
Proof. exact (@lem5776158 False). Qed.
Lemma lem5776160 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem5776159) (@lem5776156 A t x h1 h2)). Qed.
Lemma lem5776162 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term14 A s t x) : s x.
Proof. exact (proj1 (@lem5775955 A s t x h1)). Qed.
Lemma lem5776163 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term14 A s t x) : term41 A s x.
Proof. exact (fun h0 : term13 A s x => @lem5776162 A s t x h1). Qed.
Lemma lem5776165 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776166 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (s x).
Proof. exact (@lem5776165 (s x)). Qed.
Lemma lem5776167 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term14 A s t x) : s x.
Proof. exact (EQ_MP (@lem5776166 A s x) (@lem5776163 A s t x h1)). Qed.
Lemma lem5776170 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5776172 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term43 A s x).
Proof. exact (@lem5776170 (s x)). Qed.
Lemma lem5776175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) : term43 A s x.
Proof. exact (EQ_MP (@lem5776172 A s x) (@lem5776058 A s t x h1)). Qed.
Lemma lem5776178 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) (h2 : term14 A s t x) : False.
Proof. exact (@lem5776175 A s t x h1 (@lem5776167 A s t x h2)). Qed.
Lemma lem5776179 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) (h2 : term14 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5776178 A s t x h1 h2). Qed.
Lemma lem5776181 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776182 : term44 = False.
Proof. exact (@lem5776181 False). Qed.
Lemma lem5776183 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) (h2 : term14 A s t x) : False.
Proof. exact (EQ_MP (@lem5776182) (@lem5776179 A s t x h1 h2)). Qed.
Lemma lem5776185 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : s x.
Proof. exact (proj1 (@lem5775956 A s t x h1)). Qed.
Lemma lem5776186 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : term41 A s x.
Proof. exact (fun h0 : term13 A s x => @lem5776185 A s t x h1). Qed.
Lemma lem5776188 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776189 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (s x).
Proof. exact (@lem5776188 (s x)). Qed.
Lemma lem5776190 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term17 A s t x) : s x.
Proof. exact (EQ_MP (@lem5776189 A s x) (@lem5776186 A s t x h1)). Qed.
Lemma lem5776193 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5776195 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term43 A s x).
Proof. exact (@lem5776193 (s x)). Qed.
Lemma lem5776198 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) : term43 A s x.
Proof. exact (EQ_MP (@lem5776195 A s x) (@lem5776064 A s t x h1)). Qed.
Lemma lem5776201 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) (h2 : term17 A s t x) : False.
Proof. exact (@lem5776198 A s t x h1 (@lem5776190 A s t x h2)). Qed.
Lemma lem5776202 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) (h2 : term17 A s t x) : term44.
Proof. exact (fun h0 : ~ False => @lem5776201 A s t x h1 h2). Qed.
Lemma lem5776204 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5776205 : term44 = False.
Proof. exact (@lem5776204 False). Qed.
Lemma lem5776206 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) (h2 : term17 A s t x) : False.
Proof. exact (EQ_MP (@lem5776205) (@lem5776202 A s t x h1 h2)). Qed.
Lemma lem5776207 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem5776160 A t x h1 h2) (fun h3 : False => @lem5776056 A t x h2)). Qed.
Lemma lem5776208 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem5776207 A t x h1 h2) (@lem5776056 A t x h2)). Qed.
Lemma lem5776209 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5776208 A t x h1 h2) (fun h3 : False => @lem5776054 A t x h1)). Qed.
Lemma lem5776210 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem5776209 A t x h1 h2) (@lem5776054 A t x h1)). Qed.
Lemma lem5776211 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776137 A s t x h1 h2) (fun h3 : False => @lem5776050 A s x h1)). Qed.
Lemma lem5776212 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776211 A s t x h1 h2) (@lem5776050 A s x h1)). Qed.
Lemma lem5776213 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776114 A s t x h1 h2) (fun h3 : False => @lem5776042 A s x h1)). Qed.
Lemma lem5776214 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776213 A s t x h1 h2) (@lem5776042 A s x h1)). Qed.
Lemma lem5776215 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776091 A s t x h1 h2) (fun h3 : False => @lem5776038 A s x h1)). Qed.
Lemma lem5776216 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776215 A s t x h1 h2) (@lem5776038 A s x h1)). Qed.
Lemma lem5776217 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776216 A s t x h1 h2) (fun h3 : False => @lem5776036 A s x h1)). Qed.
Lemma lem5776218 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776217 A s t x h1 h2) (@lem5776036 A s x h1)). Qed.
Lemma lem5776219 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem5776210 A t x h1 h2) (fun h3 : False => @lem5776008 A t x h2)). Qed.
Lemma lem5776220 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem5776219 A t x h1 h2) (@lem5776008 A t x h2)). Qed.
Lemma lem5776221 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5776220 A t x h1 h2) (fun h3 : False => @lem5776004 A t x h1)). Qed.
Lemma lem5776222 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem5776221 A t x h1 h2) (@lem5776004 A t x h1)). Qed.
Lemma lem5776223 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776212 A s t x h1 h2) (fun h3 : False => @lem5775996 A s x h1)). Qed.
Lemma lem5776224 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776223 A s t x h1 h2) (@lem5775996 A s x h1)). Qed.
Lemma lem5776225 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776214 A s t x h1 h2) (fun h3 : False => @lem5775980 A s x h1)). Qed.
Lemma lem5776226 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776225 A s t x h1 h2) (@lem5775980 A s x h1)). Qed.
Lemma lem5776227 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776218 A s t x h1 h2) (fun h3 : False => @lem5775972 A s x h1)). Qed.
Lemma lem5776228 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776227 A s t x h1 h2) (@lem5775972 A s x h1)). Qed.
Lemma lem5776229 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776228 A s t x h1 h2) (fun h3 : False => @lem5775968 A s x h1)). Qed.
Lemma lem5776230 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776229 A s t x h1 h2) (@lem5775968 A s x h1)). Qed.
Lemma lem5776231 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem5776222 A t x h1 h2) (fun h3 : False => @lem5776008 A t x h2)). Qed.
Lemma lem5776232 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem5776231 A t x h1 h2) (@lem5776008 A t x h2)). Qed.
Lemma lem5776233 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : (term13 A t x) = False.
Proof. exact (prop_ext (fun h3 : term13 A t x => @lem5776232 A t x h1 h2) (fun h3 : False => @lem5776004 A t x h1)). Qed.
Lemma lem5776234 {A : Type'} (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem5776233 A t x h1 h2) (@lem5776004 A t x h1)). Qed.
Lemma lem5776235 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776224 A s t x h1 h2) (fun h3 : False => @lem5775996 A s x h1)). Qed.
Lemma lem5776236 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776235 A s t x h1 h2) (@lem5775996 A s x h1)). Qed.
Lemma lem5776237 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776226 A s t x h1 h2) (fun h3 : False => @lem5775980 A s x h1)). Qed.
Lemma lem5776238 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776237 A s t x h1 h2) (@lem5775980 A s x h1)). Qed.
Lemma lem5776239 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776230 A s t x h1 h2) (fun h3 : False => @lem5775972 A s x h1)). Qed.
Lemma lem5776240 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776239 A s t x h1 h2) (@lem5775972 A s x h1)). Qed.
Lemma lem5776241 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : (term13 A s x) = False.
Proof. exact (prop_ext (fun h3 : term13 A s x => @lem5776240 A s t x h1 h2) (fun h3 : False => @lem5775968 A s x h1)). Qed.
Lemma lem5776242 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (EQ_MP (@lem5776241 A s t x h1 h2) (@lem5775968 A s x h1)). Qed.
Lemma lem5776243 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term219 A s t x) : False.
Proof. exact (or_elim (@lem5775953 A s t x h1) (fun h0 : term14 A s t x => @lem5776183 A s t x h1 h0) (fun h0 : term17 A s t x => @lem5776206 A s t x h1 h0)). Qed.
Lemma lem5776244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A t x) (h2 : term221 A s t x) : False.
Proof. exact (or_elim (@lem5775946 A s t x h2) (fun h0 : term13 A s x => @lem5776236 A s t x h0 h2) (fun h0 : t x => @lem5776234 A t x h1 h0)). Qed.
Lemma lem5776245 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term13 A s x) (h2 : term221 A s t x) : False.
Proof. exact (or_elim (@lem5775946 A s t x h2) (fun h0 : term13 A s x => @lem5776242 A s t x h1 h2) (fun h0 : t x => @lem5776238 A s t x h1 h2)). Qed.
Lemma lem5776246 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term221 A s t x) : False.
Proof. exact (or_elim (@lem5775945 A s t x h1) (fun h0 : term13 A s x => @lem5776245 A s t x h0 h1) (fun h0 : term13 A t x => @lem5776244 A s t x h0 h1)). Qed.
Lemma lem5776247 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term215 A s t x) : False.
Proof. exact (or_elim (@lem5775940 A s t x h1) (fun h0 : term221 A s t x => @lem5776246 A s t x h0) (fun h0 : term219 A s t x => @lem5776243 A s t x h0)). Qed.
Lemma lem5776248 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term215 A s t x) : (term215 A s t x) = False.
Proof. exact (prop_ext (fun h2 : term215 A s t x => @lem5776247 A s t x h1) (fun h2 : False => @lem5775820 A s t x h1)). Qed.
Lemma lem5776249 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term215 A s t x) : False.
Proof. exact (EQ_MP (@lem5776248 A s t x h1) (@lem5775820 A s t x h1)). Qed.
Lemma lem5776250 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term214 A s t x.
Proof. exact (fun h0 : term215 A s t x => @lem5776249 A s t x h0). Qed.
Lemma lem5776251 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (s x) = (term196 A s t x).
Proof. exact (EQ_MP (@lem5775819 A s t x) (@lem5776250 A s t x)). Qed.
Lemma lem5776256 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term199 A s t.
Proof. exact (fun x : A => @lem5776251 A s t x). Qed.
Lemma lem5776261 {A : Type'} (t : A -> Prop) : term209 A t.
Proof. exact (fun s : A -> Prop => @lem5776256 A s t). Qed.
Lemma lem5776266 {A : Type'} : term213 A.
Proof. exact (fun t : A -> Prop => @lem5776261 A t). Qed.
Lemma lem5776267 {A : Type'} : term212 A.
Proof. exact (EQ_MP (@lem5775815 A) (@lem5776266 A)). Qed.
Lemma lem5776268 {A : Type'} (t : A -> Prop) : term226 A t.
Proof. exact (@lem5776267 A t). Qed.
Lemma lem5776269 {A : Type'} (t : A -> Prop) : (term226 A t) = (term208 A t).
Proof. exact (eq_refl (term226 A t)). Qed.
Lemma lem5776270 {A : Type'} (t : A -> Prop) : term208 A t.
Proof. exact (EQ_MP (@lem5776269 A t) (@lem5776268 A t)). Qed.
Lemma lem5776271 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term227 A t s.
Proof. exact (@lem5776270 A t s). Qed.
Lemma lem5776272 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term227 A t s) = (term200 A s t).
Proof. exact (eq_refl (term227 A t s)). Qed.
Lemma lem5776273 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term200 A s t.
Proof. exact (EQ_MP (@lem5776272 A s t) (@lem5776271 A t s)). Qed.
Lemma lem5776275 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term200 A s t.
Proof. exact (@lem5775716 A s t (@lem5776273 A s t)). Qed.
Lemma lem5776276 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term201 A s t) : False.
Proof. exact (@lem5776275 A s t (@lem5775700 A s t h1)). Qed.
Lemma lem5776277 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term201 A s t) : (term201 A s t) = False.
Proof. exact (prop_ext (fun h2 : term201 A s t => @lem5776276 A s t h1) (fun h2 : False => @lem5775700 A s t h1)). Qed.
Lemma lem5776278 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term201 A s t) : False.
Proof. exact (EQ_MP (@lem5776277 A s t h1) (@lem5775700 A s t h1)). Qed.
Lemma lem5776279 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term200 A s t.
Proof. exact (fun h0 : term201 A s t => @lem5776278 A s t h0). Qed.
Lemma lem5776280 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term199 A s t.
Proof. exact (EQ_MP (@lem5775699 A s t) (@lem5776279 A s t)). Qed.
Lemma lem5776281 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term193 A s t.
Proof. exact (EQ_MP (@lem5775695 A s t) (@lem5776280 A s t)). Qed.
Lemma lem5776296 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5776297 {_120933 : Type'} (s : _120933 -> Prop) (t : _120933 -> Prop) : (s = t) = (term2 _120933 s t).
Proof. exact (@lem5776296 _120933 s t). Qed.
Lemma lem5776298 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : ((@UNION _120933 a b) = (term228 _120933 a b)) = (term229 _120933 a b).
Proof. exact (@lem5776297 _120933 (@UNION _120933 a b) (term228 _120933 a b)). Qed.
Lemma lem5776307 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term229 _120933 a b) = ((@UNION _120933 a b) = (term228 _120933 a b)).
Proof. exact (SYM (@lem5776298 _120933 a b)). Qed.
Lemma lem5776315 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5776316 {_120933 : Type'} (s : _120933 -> Prop) (x : _120933) (t : _120933 -> Prop) : (term112 _120933 x s t) = (term113 _120933 s x t).
Proof. exact (@lem5776315 _120933 s x t). Qed.
Lemma lem5776317 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (b : _120933 -> Prop) : (term112 _120933 x a b) = (term113 _120933 a x b).
Proof. exact (@lem5776316 _120933 a x b). Qed.
Lemma lem5776321 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776322 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776321 _120933 P x). Qed.
Lemma lem5776323 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (@IN _120933 x a) = (a x).
Proof. exact (@lem5776322 _120933 a x). Qed.
Lemma lem5776324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5776325 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term230 _120933 x a) = (term231 _120933 a x).
Proof. exact (MK_COMB (@lem5776324) (@lem5776323 _120933 a x)). Qed.
Lemma lem5776327 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776328 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776327 _120933 P x). Qed.
Lemma lem5776329 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (@IN _120933 x b) = (b x).
Proof. exact (@lem5776328 _120933 b x). Qed.
Lemma lem5776330 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term113 _120933 a x b) = (term232 _120933 a b x).
Proof. exact (MK_COMB (@lem5776325 _120933 a x) (@lem5776329 _120933 b x)). Qed.
Lemma lem5776333 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term112 _120933 x a b) = (term232 _120933 a b x).
Proof. exact (TRANS (@lem5776317 _120933 a x b) (@lem5776330 _120933 a b x)). Qed.
Lemma lem5776334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5776335 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term233 _120933 x a b) = (term234 _120933 a b x).
Proof. exact (MK_COMB (@lem5776334) (@lem5776333 _120933 a b x)). Qed.
Lemma lem5776337 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5776338 {_120933 : Type'} (s : _120933 -> Prop) (x : _120933) (t : _120933 -> Prop) : (term112 _120933 x s t) = (term113 _120933 s x t).
Proof. exact (@lem5776337 _120933 s x t). Qed.
Lemma lem5776339 {_120933 : Type'} (x : _120933) (a : _120933 -> Prop) (b : _120933 -> Prop) : (term235 _120933 x a b) = (term236 _120933 x a b).
Proof. exact (@lem5776338 _120933 (term108 _120933 b a) x (@INTER _120933 a b)). Qed.
Lemma lem5776343 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term112 A x s t) = (term113 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5776344 {_120933 : Type'} (s : _120933 -> Prop) (x : _120933) (t : _120933 -> Prop) : (term112 _120933 x s t) = (term113 _120933 s x t).
Proof. exact (@lem5776343 _120933 s x t). Qed.
Lemma lem5776345 {_120933 : Type'} (x : _120933) (b : _120933 -> Prop) (a : _120933 -> Prop) : (term114 _120933 x b a) = (term115 _120933 x b a).
Proof. exact (@lem5776344 _120933 (@DIFF _120933 a b) x (@DIFF _120933 b a)). Qed.
Lemma lem5776349 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5776350 {_120933 : Type'} (s : _120933 -> Prop) (x : _120933) (t : _120933 -> Prop) : (term8 _120933 x s t) = (term9 _120933 s x t).
Proof. exact (@lem5776349 _120933 s x t). Qed.
Lemma lem5776351 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (b : _120933 -> Prop) : (term8 _120933 x a b) = (term9 _120933 a x b).
Proof. exact (@lem5776350 _120933 a x b). Qed.
Lemma lem5776355 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776356 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776355 _120933 P x). Qed.
Lemma lem5776357 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (@IN _120933 x a) = (a x).
Proof. exact (@lem5776356 _120933 a x). Qed.
Lemma lem5776358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5776359 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term10 _120933 x a) = (term11 _120933 a x).
Proof. exact (MK_COMB (@lem5776358) (@lem5776357 _120933 a x)). Qed.
Lemma lem5776361 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776362 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776361 _120933 P x). Qed.
Lemma lem5776363 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (@IN _120933 x b) = (b x).
Proof. exact (@lem5776362 _120933 b x). Qed.
Lemma lem5776364 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5776365 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term12 _120933 x b) = (term13 _120933 b x).
Proof. exact (MK_COMB (@lem5776364) (@lem5776363 _120933 b x)). Qed.
Lemma lem5776366 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term9 _120933 a x b) = (term14 _120933 a b x).
Proof. exact (MK_COMB (@lem5776359 _120933 a x) (@lem5776365 _120933 b x)). Qed.
Lemma lem5776369 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term8 _120933 x a b) = (term14 _120933 a b x).
Proof. exact (TRANS (@lem5776351 _120933 a x b) (@lem5776366 _120933 a b x)). Qed.
Lemma lem5776370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5776371 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term116 _120933 x a b) = (term117 _120933 a b x).
Proof. exact (MK_COMB (@lem5776370) (@lem5776369 _120933 a b x)). Qed.
Lemma lem5776373 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem5776374 {_120933 : Type'} (s : _120933 -> Prop) (x : _120933) (t : _120933 -> Prop) : (term8 _120933 x s t) = (term9 _120933 s x t).
Proof. exact (@lem5776373 _120933 s x t). Qed.
Lemma lem5776375 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (a : _120933 -> Prop) : (term8 _120933 x b a) = (term9 _120933 b x a).
Proof. exact (@lem5776374 _120933 b x a). Qed.
Lemma lem5776379 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776380 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776379 _120933 P x). Qed.
Lemma lem5776381 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (@IN _120933 x b) = (b x).
Proof. exact (@lem5776380 _120933 b x). Qed.
Lemma lem5776382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5776383 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term10 _120933 x b) = (term11 _120933 b x).
Proof. exact (MK_COMB (@lem5776382) (@lem5776381 _120933 b x)). Qed.
Lemma lem5776385 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776386 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776385 _120933 P x). Qed.
Lemma lem5776387 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (@IN _120933 x a) = (a x).
Proof. exact (@lem5776386 _120933 a x). Qed.
Lemma lem5776388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5776389 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term12 _120933 x a) = (term13 _120933 a x).
Proof. exact (MK_COMB (@lem5776388) (@lem5776387 _120933 a x)). Qed.
Lemma lem5776390 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term9 _120933 b x a) = (term14 _120933 b a x).
Proof. exact (MK_COMB (@lem5776383 _120933 b x) (@lem5776389 _120933 a x)). Qed.
Lemma lem5776393 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term8 _120933 x b a) = (term14 _120933 b a x).
Proof. exact (TRANS (@lem5776375 _120933 b x a) (@lem5776390 _120933 b a x)). Qed.
Lemma lem5776394 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term115 _120933 x b a) = (term118 _120933 b a x).
Proof. exact (MK_COMB (@lem5776371 _120933 a b x) (@lem5776393 _120933 b a x)). Qed.
Lemma lem5776397 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term114 _120933 x b a) = (term118 _120933 b a x).
Proof. exact (TRANS (@lem5776345 _120933 x b a) (@lem5776394 _120933 b a x)). Qed.
Lemma lem5776398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5776399 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term237 _120933 x b a) = (term238 _120933 b a x).
Proof. exact (MK_COMB (@lem5776398) (@lem5776397 _120933 b a x)). Qed.
Lemma lem5776401 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A x s t) = (term5 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem5776402 {_120933 : Type'} (s : _120933 -> Prop) (x : _120933) (t : _120933 -> Prop) : (term4 _120933 x s t) = (term5 _120933 s x t).
Proof. exact (@lem5776401 _120933 s x t). Qed.
Lemma lem5776403 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (b : _120933 -> Prop) : (term4 _120933 x a b) = (term5 _120933 a x b).
Proof. exact (@lem5776402 _120933 a x b). Qed.
Lemma lem5776407 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776408 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776407 _120933 P x). Qed.
Lemma lem5776409 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (@IN _120933 x a) = (a x).
Proof. exact (@lem5776408 _120933 a x). Qed.
Lemma lem5776410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5776411 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term10 _120933 x a) = (term11 _120933 a x).
Proof. exact (MK_COMB (@lem5776410) (@lem5776409 _120933 a x)). Qed.
Lemma lem5776413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5776414 {_120933 : Type'} (P : _120933 -> Prop) (x : _120933) : (@IN _120933 x P) = (P x).
Proof. exact (@lem5776413 _120933 P x). Qed.
Lemma lem5776415 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (@IN _120933 x b) = (b x).
Proof. exact (@lem5776414 _120933 b x). Qed.
Lemma lem5776416 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term5 _120933 a x b) = (term17 _120933 a b x).
Proof. exact (MK_COMB (@lem5776411 _120933 a x) (@lem5776415 _120933 b x)). Qed.
Lemma lem5776419 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term4 _120933 x a b) = (term17 _120933 a b x).
Proof. exact (TRANS (@lem5776403 _120933 a x b) (@lem5776416 _120933 a b x)). Qed.
Lemma lem5776420 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term236 _120933 x a b) = (term239 _120933 a b x).
Proof. exact (MK_COMB (@lem5776399 _120933 b a x) (@lem5776419 _120933 a b x)). Qed.
Lemma lem5776423 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term235 _120933 x a b) = (term239 _120933 a b x).
Proof. exact (TRANS (@lem5776339 _120933 x a b) (@lem5776420 _120933 a b x)). Qed.
Lemma lem5776424 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : ((term112 _120933 x a b) = (term235 _120933 x a b)) = ((term232 _120933 a b x) = (term239 _120933 a b x)).
Proof. exact (MK_COMB (@lem5776335 _120933 a b x) (@lem5776423 _120933 a b x)). Qed.
Lemma lem5776427 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term240 _120933 a b) = (term241 _120933 a b).
Proof. exact (fun_ext (fun x : _120933 => @lem5776424 _120933 a b x)). Qed.
Lemma lem5776428 {_120933 : Type'} : (@all _120933) = (@all _120933).
Proof. exact (eq_refl (@all _120933)). Qed.
Lemma lem5776429 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term229 _120933 a b) = (term242 _120933 a b).
Proof. exact (MK_COMB (@lem5776428 _120933) (@lem5776427 _120933 a b)). Qed.
Lemma lem5776434 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term242 _120933 a b) = (term229 _120933 a b).
Proof. exact (SYM (@lem5776429 _120933 a b)). Qed.
Lemma lem5776436 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5776437 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term242 _120933 a b) = (term243 _120933 a b).
Proof. exact (@lem5776436 (term242 _120933 a b)). Qed.
Lemma lem5776438 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term243 _120933 a b) = (term242 _120933 a b).
Proof. exact (SYM (@lem5776437 _120933 a b)). Qed.
Lemma lem5776439 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term244 _120933 a b) : term244 _120933 a b.
Proof. exact (h1). Qed.
Lemma lem5776442 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term243 _120933 a b) : term243 _120933 a b.
Proof. exact (h1). Qed.
Lemma lem5776443 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term245 _120933 a b.
Proof. exact (fun h0 : term243 _120933 a b => @lem5776442 _120933 a b h0). Qed.
Lemma lem5776444 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term245 _120933 a b) : term245 _120933 a b.
Proof. exact (h1). Qed.
Lemma lem5776445 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term243 _120933 a b) : term243 _120933 a b.
Proof. exact (h1). Qed.
Lemma lem5776446 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term243 _120933 a b) (h2 : term245 _120933 a b) : term243 _120933 a b.
Proof. exact (@lem5776444 _120933 a b h2 (@lem5776445 _120933 a b h1)). Qed.
Lemma lem5776447 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term243 _120933 a b) : term246 _120933 a b.
Proof. exact (fun h0 : term245 _120933 a b => @lem5776446 _120933 a b h1 h0). Qed.
Lemma lem5776448 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term245 _120933 a b) : term245 _120933 a b.
Proof. exact (h1). Qed.
Lemma lem5776449 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term243 _120933 a b) (h2 : term245 _120933 a b) : term243 _120933 a b.
Proof. exact (@lem5776447 _120933 a b h1 (@lem5776448 _120933 a b h2)). Qed.
Lemma lem5776450 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term245 _120933 a b) : term245 _120933 a b.
Proof. exact (fun h0 : term243 _120933 a b => @lem5776449 _120933 a b h0 h1). Qed.
Lemma lem5776451 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term247 _120933 a b.
Proof. exact (fun h0 : term245 _120933 a b => @lem5776450 _120933 a b h0). Qed.
Lemma lem5776454 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term245 _120933 a b.
Proof. exact (@lem5776451 _120933 a b (@lem5776443 _120933 a b)). Qed.
Lemma lem5776455 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term245 _120933 a b.
Proof. exact (@lem5776454 _120933 a b). Qed.
Lemma lem5776465 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5776466 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term243 _120933 a b) = (term248 _120933 a b).
Proof. exact (@lem5776465 (term244 _120933 a b)). Qed.
Lemma lem5776468 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5776469 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term248 _120933 a b) = (term242 _120933 a b).
Proof. exact (@lem5776468 (term242 _120933 a b)). Qed.
Lemma lem5776474 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term243 _120933 a b) = (term242 _120933 a b).
Proof. exact (TRANS (@lem5776466 _120933 a b) (@lem5776469 _120933 a b)). Qed.
Lemma lem5776487 {_120933 : Type'} (b : _120933 -> Prop) : (term249 _120933 b) = (term250 _120933 b).
Proof. exact (fun_ext (fun a : _120933 -> Prop => @lem5776474 _120933 a b)). Qed.
Lemma lem5776488 {_120933 : Type'} : (@all (_120933 -> Prop)) = (@all (_120933 -> Prop)).
Proof. exact (eq_refl (@all (_120933 -> Prop))). Qed.
Lemma lem5776489 {_120933 : Type'} (b : _120933 -> Prop) : (term251 _120933 b) = (term252 _120933 b).
Proof. exact (MK_COMB (@lem5776488 _120933) (@lem5776487 _120933 b)). Qed.
Lemma lem5776494 {_120933 : Type'} : (term253 _120933) = (term254 _120933).
Proof. exact (fun_ext (fun b : _120933 -> Prop => @lem5776489 _120933 b)). Qed.
Lemma lem5776495 {_120933 : Type'} : (@all (_120933 -> Prop)) = (@all (_120933 -> Prop)).
Proof. exact (eq_refl (@all (_120933 -> Prop))). Qed.
Lemma lem5776504 {_120933 : Type'} : (term255 _120933) = (term256 _120933).
Proof. exact (MK_COMB (@lem5776495 _120933) (@lem5776494 _120933)). Qed.
Lemma lem5776537 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : ((term232 _120933 a b x) = (term239 _120933 a b x)) = ((term232 _120933 a b x) = (term239 _120933 a b x)).
Proof. exact (eq_refl ((term232 _120933 a b x) = (term239 _120933 a b x))). Qed.
Lemma lem5776538 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term241 _120933 a b) = (term241 _120933 a b).
Proof. exact (fun_ext (fun x : _120933 => @lem5776537 _120933 a b x)). Qed.
Lemma lem5776539 {_120933 : Type'} : (@all _120933) = (@all _120933).
Proof. exact (eq_refl (@all _120933)). Qed.
Lemma lem5776540 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term242 _120933 a b) = (term242 _120933 a b).
Proof. exact (MK_COMB (@lem5776539 _120933) (@lem5776538 _120933 a b)). Qed.
Lemma lem5776541 {_120933 : Type'} (b : _120933 -> Prop) : (term250 _120933 b) = (term250 _120933 b).
Proof. exact (fun_ext (fun a : _120933 -> Prop => @lem5776540 _120933 a b)). Qed.
Lemma lem5776542 {_120933 : Type'} : (@all (_120933 -> Prop)) = (@all (_120933 -> Prop)).
Proof. exact (eq_refl (@all (_120933 -> Prop))). Qed.
Lemma lem5776543 {_120933 : Type'} (b : _120933 -> Prop) : (term252 _120933 b) = (term252 _120933 b).
Proof. exact (MK_COMB (@lem5776542 _120933) (@lem5776541 _120933 b)). Qed.
Lemma lem5776544 {_120933 : Type'} : (term254 _120933) = (term254 _120933).
Proof. exact (fun_ext (fun b : _120933 -> Prop => @lem5776543 _120933 b)). Qed.
Lemma lem5776545 {_120933 : Type'} : (@all (_120933 -> Prop)) = (@all (_120933 -> Prop)).
Proof. exact (eq_refl (@all (_120933 -> Prop))). Qed.
Lemma lem5776546 {_120933 : Type'} : (term256 _120933) = (term256 _120933).
Proof. exact (MK_COMB (@lem5776545 _120933) (@lem5776544 _120933)). Qed.
Lemma lem5776579 {_120933 : Type'} : (term255 _120933) = (term256 _120933).
Proof. exact (TRANS (@lem5776504 _120933) (@lem5776546 _120933)). Qed.
Lemma lem5776580 {_120933 : Type'} : (term256 _120933) = (term255 _120933).
Proof. exact (SYM (@lem5776579 _120933)). Qed.
Lemma lem5776582 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5776583 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : ((term232 _120933 a b x) = (term239 _120933 a b x)) = (term257 _120933 a b x).
Proof. exact (@lem5776582 ((term232 _120933 a b x) = (term239 _120933 a b x))). Qed.
Lemma lem5776584 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term257 _120933 a b x) = ((term232 _120933 a b x) = (term239 _120933 a b x)).
Proof. exact (SYM (@lem5776583 _120933 a b x)). Qed.
Lemma lem5776585 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term258 _120933 a b x) : term258 _120933 a b x.
Proof. exact (h1). Qed.
Lemma lem5776594 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term259 _120933 a b x) = (term260 _120933 a b x).
Proof. exact (@lem17160 (a x) (b x)). Qed.
Lemma lem5776603 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term171 _120933 b x) = (b x).
Proof. exact (@lem16933 (b x)). Qed.
Lemma lem5776605 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term172 _120933 a x) = (term172 _120933 a x).
Proof. exact (eq_refl (term172 _120933 a x)). Qed.
Lemma lem5776606 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term173 _120933 a b x) = (term174 _120933 a b x).
Proof. exact (MK_COMB (@lem5776605 _120933 a x) (@lem5776603 _120933 b x)). Qed.
Lemma lem5776607 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term175 _120933 a b x) = (term173 _120933 a b x).
Proof. exact (@lem17045 (a x) (term13 _120933 b x)). Qed.
Lemma lem5776608 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term175 _120933 a b x) = (term174 _120933 a b x).
Proof. exact (TRANS (@lem5776607 _120933 a b x) (@lem5776606 _120933 a b x)). Qed.
Lemma lem5776617 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term171 _120933 a x) = (a x).
Proof. exact (@lem16933 (a x)). Qed.
Lemma lem5776619 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term172 _120933 b x) = (term172 _120933 b x).
Proof. exact (eq_refl (term172 _120933 b x)). Qed.
Lemma lem5776620 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term173 _120933 b a x) = (term174 _120933 b a x).
Proof. exact (MK_COMB (@lem5776619 _120933 b x) (@lem5776617 _120933 a x)). Qed.
Lemma lem5776621 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term175 _120933 b a x) = (term173 _120933 b a x).
Proof. exact (@lem17045 (b x) (term13 _120933 a x)). Qed.
Lemma lem5776622 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term175 _120933 b a x) = (term174 _120933 b a x).
Proof. exact (TRANS (@lem5776621 _120933 b a x) (@lem5776620 _120933 b a x)). Qed.
Lemma lem5776626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5776627 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term178 _120933 a b x) = (term179 _120933 a b x).
Proof. exact (MK_COMB (@lem5776626) (@lem5776608 _120933 a b x)). Qed.
Lemma lem5776628 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term261 _120933 b a x) = (term262 _120933 b a x).
Proof. exact (MK_COMB (@lem5776627 _120933 a b x) (@lem5776622 _120933 b a x)). Qed.
Lemma lem5776629 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term263 _120933 b a x) = (term261 _120933 b a x).
Proof. exact (@lem17160 (term14 _120933 a b x) (term14 _120933 b a x)). Qed.
Lemma lem5776630 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term263 _120933 b a x) = (term262 _120933 b a x).
Proof. exact (TRANS (@lem5776629 _120933 b a x) (@lem5776628 _120933 b a x)). Qed.
Lemma lem5776642 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term176 _120933 a b x) = (term177 _120933 a b x).
Proof. exact (@lem17045 (a x) (b x)). Qed.
Lemma lem5776646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5776647 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) : (term264 _120933 b a x) = (term265 _120933 b a x).
Proof. exact (MK_COMB (@lem5776646) (@lem5776630 _120933 b a x)). Qed.
Lemma lem5776648 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term266 _120933 a b x) = (term267 _120933 a b x).
Proof. exact (MK_COMB (@lem5776647 _120933 b a x) (@lem5776642 _120933 a b x)). Qed.
Lemma lem5776649 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term268 _120933 a b x) = (term266 _120933 a b x).
Proof. exact (@lem17160 (term118 _120933 b a x) (term17 _120933 a b x)). Qed.
Lemma lem5776650 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term268 _120933 a b x) = (term267 _120933 a b x).
Proof. exact (TRANS (@lem5776649 _120933 a b x) (@lem5776648 _120933 a b x)). Qed.
Lemma lem5776653 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term239 _120933 a b x) = (term239 _120933 a b x).
Proof. exact (eq_refl (term239 _120933 a b x)). Qed.
Lemma lem5776654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5776655 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term269 _120933 a b x) = (term270 _120933 a b x).
Proof. exact (MK_COMB (@lem5776654) (@lem5776594 _120933 a b x)). Qed.
Lemma lem5776656 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term271 _120933 a b x) = (term272 _120933 a b x).
Proof. exact (MK_COMB (@lem5776655 _120933 a b x) (@lem5776653 _120933 a b x)). Qed.
Lemma lem5776658 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term273 _120933 a b x) = (term273 _120933 a b x).
Proof. exact (eq_refl (term273 _120933 a b x)). Qed.
Lemma lem5776659 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term274 _120933 a b x) = (term275 _120933 a b x).
Proof. exact (MK_COMB (@lem5776658 _120933 a b x) (@lem5776650 _120933 a b x)). Qed.
Lemma lem5776660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5776661 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term276 _120933 a b x) = (term277 _120933 a b x).
Proof. exact (MK_COMB (@lem5776660) (@lem5776659 _120933 a b x)). Qed.
Lemma lem5776662 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term278 _120933 a b x) = (term279 _120933 a b x).
Proof. exact (MK_COMB (@lem5776661 _120933 a b x) (@lem5776656 _120933 a b x)). Qed.
Lemma lem5776663 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term258 _120933 a b x) = (term278 _120933 a b x).
Proof. exact (@lem17646 (term232 _120933 a b x) (term239 _120933 a b x)). Qed.
Lemma lem5776668 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term258 _120933 a b x) = (term279 _120933 a b x).
Proof. exact (TRANS (@lem5776663 _120933 a b x) (@lem5776662 _120933 a b x)). Qed.
Lemma lem5776779 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term258 _120933 a b x) : term279 _120933 a b x.
Proof. exact (EQ_MP (@lem5776668 _120933 a b x) (@lem5776585 _120933 a b x h1)). Qed.
Lemma lem5776780 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : term275 _120933 a b x.
Proof. exact (h1). Qed.
Lemma lem5776781 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term272 _120933 a b x.
Proof. exact (h1). Qed.
Lemma lem5776782 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : term267 _120933 a b x.
Proof. exact (proj2 (@lem5776780 _120933 a b x h1)). Qed.
Lemma lem5776783 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : term232 _120933 a b x.
Proof. exact (proj1 (@lem5776780 _120933 a b x h1)). Qed.
Lemma lem5776784 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : term177 _120933 a b x.
Proof. exact (proj2 (@lem5776782 _120933 a b x h1)). Qed.
Lemma lem5776785 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : term262 _120933 b a x.
Proof. exact (proj1 (@lem5776782 _120933 a b x h1)). Qed.
Lemma lem5776786 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : term174 _120933 b a x.
Proof. exact (proj2 (@lem5776785 _120933 a b x h1)). Qed.
Lemma lem5776787 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : term174 _120933 a b x.
Proof. exact (proj1 (@lem5776785 _120933 a b x h1)). Qed.
Lemma lem5776818 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term239 _120933 a b x.
Proof. exact (proj2 (@lem5776781 _120933 a b x h1)). Qed.
Lemma lem5776819 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term260 _120933 a b x.
Proof. exact (proj1 (@lem5776781 _120933 a b x h1)). Qed.
Lemma lem5776822 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) (h1 : term118 _120933 b a x) : term118 _120933 b a x.
Proof. exact (h1). Qed.
Lemma lem5776823 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term17 _120933 a b x) : term17 _120933 a b x.
Proof. exact (h1). Qed.
Lemma lem5776824 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 a b x) : term14 _120933 a b x.
Proof. exact (h1). Qed.
Lemma lem5776825 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 b a x) : term14 _120933 b a x.
Proof. exact (h1). Qed.
Lemma lem5776839 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776843 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776847 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5776851 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776863 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5776871 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776879 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5776883 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776891 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776895 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5776907 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776911 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5776915 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776919 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5776927 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5776931 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776935 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5776939 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776947 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776951 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5776955 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5776959 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5776963 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5776967 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776971 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776975 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5776979 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5776983 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776987 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5776995 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5776999 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777007 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777019 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777023 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777027 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777035 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777039 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777043 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777051 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777063 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777067 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777079 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777083 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777087 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777139 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777141 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777143 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777145 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777151 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777155 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777159 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777161 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777165 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777167 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777173 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777175 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777177 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777179 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777183 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777185 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777187 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777189 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777193 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777195 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777197 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777199 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777201 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777203 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777205 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777207 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777209 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777211 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777213 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777217 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777219 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777223 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777229 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777231 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777233 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777237 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777239 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777241 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777245 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term13 _120933 a x.
Proof. exact (h1). Qed.
Lemma lem5777251 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777253 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777259 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777261 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term13 _120933 b x.
Proof. exact (h1). Qed.
Lemma lem5777263 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777265 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term13 _120933 a x.
Proof. exact (proj1 (@lem5776819 _120933 a b x h1)). Qed.
Lemma lem5777275 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term13 _120933 b x.
Proof. exact (proj2 (@lem5776819 _120933 a b x h1)). Qed.
Lemma lem5777283 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term13 _120933 b x.
Proof. exact (proj2 (@lem5776819 _120933 a b x h1)). Qed.
Lemma lem5777289 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777290 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777289 _120933 a x h1). Qed.
Lemma lem5777292 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777293 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777292 (a x)). Qed.
Lemma lem5777294 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777293 _120933 a x) (@lem5777290 _120933 a x h1)). Qed.
Lemma lem5777297 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777299 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777297 (a x)). Qed.
Lemma lem5777302 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777299 _120933 a x) (@lem5777139 _120933 a x h1)). Qed.
Lemma lem5777305 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777302 _120933 a x h1 (@lem5777294 _120933 a x h2)). Qed.
Lemma lem5777306 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777305 _120933 a x h1 h2). Qed.
Lemma lem5777308 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777309 : term44 = False.
Proof. exact (@lem5777308 False). Qed.
Lemma lem5777310 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777309) (@lem5777306 _120933 a x h1 h2)). Qed.
Lemma lem5777312 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777313 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777312 _120933 b x h1). Qed.
Lemma lem5777315 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777316 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777315 (b x)). Qed.
Lemma lem5777317 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777316 _120933 b x) (@lem5777313 _120933 b x h1)). Qed.
Lemma lem5777320 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777322 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777320 (b x)). Qed.
Lemma lem5777325 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777322 _120933 b x) (@lem5777145 _120933 b x h1)). Qed.
Lemma lem5777328 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777325 _120933 b x h1 (@lem5777317 _120933 b x h2)). Qed.
Lemma lem5777329 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777328 _120933 b x h1 h2). Qed.
Lemma lem5777331 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777332 : term44 = False.
Proof. exact (@lem5777331 False). Qed.
Lemma lem5777333 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777332) (@lem5777329 _120933 b x h1 h2)). Qed.
Lemma lem5777335 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777336 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777335 _120933 a x h1). Qed.
Lemma lem5777338 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777339 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777338 (a x)). Qed.
Lemma lem5777340 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777339 _120933 a x) (@lem5777336 _120933 a x h1)). Qed.
Lemma lem5777343 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777345 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777343 (a x)). Qed.
Lemma lem5777348 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777345 _120933 a x) (@lem5777155 _120933 a x h1)). Qed.
Lemma lem5777351 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777348 _120933 a x h1 (@lem5777340 _120933 a x h2)). Qed.
Lemma lem5777352 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777351 _120933 a x h1 h2). Qed.
Lemma lem5777354 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777355 : term44 = False.
Proof. exact (@lem5777354 False). Qed.
Lemma lem5777356 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777355) (@lem5777352 _120933 a x h1 h2)). Qed.
Lemma lem5777358 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777359 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777358 _120933 b x h1). Qed.
Lemma lem5777361 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777362 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777361 (b x)). Qed.
Lemma lem5777363 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777362 _120933 b x) (@lem5777359 _120933 b x h1)). Qed.
Lemma lem5777366 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777368 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777366 (b x)). Qed.
Lemma lem5777371 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777368 _120933 b x) (@lem5777161 _120933 b x h1)). Qed.
Lemma lem5777374 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777371 _120933 b x h1 (@lem5777363 _120933 b x h2)). Qed.
Lemma lem5777375 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777374 _120933 b x h1 h2). Qed.
Lemma lem5777377 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777378 : term44 = False.
Proof. exact (@lem5777377 False). Qed.
Lemma lem5777379 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777378) (@lem5777375 _120933 b x h1 h2)). Qed.
Lemma lem5777381 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777382 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777381 _120933 a x h1). Qed.
Lemma lem5777384 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777385 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777384 (a x)). Qed.
Lemma lem5777386 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777385 _120933 a x) (@lem5777382 _120933 a x h1)). Qed.
Lemma lem5777389 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777391 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777389 (a x)). Qed.
Lemma lem5777394 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777391 _120933 a x) (@lem5777173 _120933 a x h1)). Qed.
Lemma lem5777397 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777394 _120933 a x h1 (@lem5777386 _120933 a x h2)). Qed.
Lemma lem5777398 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777397 _120933 a x h1 h2). Qed.
Lemma lem5777400 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777401 : term44 = False.
Proof. exact (@lem5777400 False). Qed.
Lemma lem5777402 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777401) (@lem5777398 _120933 a x h1 h2)). Qed.
Lemma lem5777404 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777405 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777404 _120933 b x h1). Qed.
Lemma lem5777407 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777408 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777407 (b x)). Qed.
Lemma lem5777409 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777408 _120933 b x) (@lem5777405 _120933 b x h1)). Qed.
Lemma lem5777412 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777414 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777412 (b x)). Qed.
Lemma lem5777417 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777414 _120933 b x) (@lem5777177 _120933 b x h1)). Qed.
Lemma lem5777420 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777417 _120933 b x h1 (@lem5777409 _120933 b x h2)). Qed.
Lemma lem5777421 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777420 _120933 b x h1 h2). Qed.
Lemma lem5777423 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777424 : term44 = False.
Proof. exact (@lem5777423 False). Qed.
Lemma lem5777425 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777424) (@lem5777421 _120933 b x h1 h2)). Qed.
Lemma lem5777427 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777428 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777427 _120933 b x h1). Qed.
Lemma lem5777430 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777431 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777430 (b x)). Qed.
Lemma lem5777432 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777431 _120933 b x) (@lem5777428 _120933 b x h1)). Qed.
Lemma lem5777435 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777437 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777435 (b x)). Qed.
Lemma lem5777440 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777437 _120933 b x) (@lem5777185 _120933 b x h1)). Qed.
Lemma lem5777443 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777440 _120933 b x h1 (@lem5777432 _120933 b x h2)). Qed.
Lemma lem5777444 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777443 _120933 b x h1 h2). Qed.
Lemma lem5777446 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777447 : term44 = False.
Proof. exact (@lem5777446 False). Qed.
Lemma lem5777448 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777447) (@lem5777444 _120933 b x h1 h2)). Qed.
Lemma lem5777450 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777451 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777450 _120933 b x h1). Qed.
Lemma lem5777453 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777454 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777453 (b x)). Qed.
Lemma lem5777455 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777454 _120933 b x) (@lem5777451 _120933 b x h1)). Qed.
Lemma lem5777458 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777460 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777458 (b x)). Qed.
Lemma lem5777463 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777460 _120933 b x) (@lem5777193 _120933 b x h1)). Qed.
Lemma lem5777466 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777463 _120933 b x h1 (@lem5777455 _120933 b x h2)). Qed.
Lemma lem5777467 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777466 _120933 b x h1 h2). Qed.
Lemma lem5777469 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777470 : term44 = False.
Proof. exact (@lem5777469 False). Qed.
Lemma lem5777471 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777470) (@lem5777467 _120933 b x h1 h2)). Qed.
Lemma lem5777473 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777474 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777473 _120933 a x h1). Qed.
Lemma lem5777476 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777477 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777476 (a x)). Qed.
Lemma lem5777478 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777477 _120933 a x) (@lem5777474 _120933 a x h1)). Qed.
Lemma lem5777481 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777483 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777481 (a x)). Qed.
Lemma lem5777486 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777483 _120933 a x) (@lem5777203 _120933 a x h1)). Qed.
Lemma lem5777489 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777486 _120933 a x h1 (@lem5777478 _120933 a x h2)). Qed.
Lemma lem5777490 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777489 _120933 a x h1 h2). Qed.
Lemma lem5777492 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777493 : term44 = False.
Proof. exact (@lem5777492 False). Qed.
Lemma lem5777494 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777493) (@lem5777490 _120933 a x h1 h2)). Qed.
Lemma lem5777496 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777497 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777496 _120933 a x h1). Qed.
Lemma lem5777499 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777500 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777499 (a x)). Qed.
Lemma lem5777501 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777500 _120933 a x) (@lem5777497 _120933 a x h1)). Qed.
Lemma lem5777504 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777506 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777504 (a x)). Qed.
Lemma lem5777509 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777506 _120933 a x) (@lem5777211 _120933 a x h1)). Qed.
Lemma lem5777512 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777509 _120933 a x h1 (@lem5777501 _120933 a x h2)). Qed.
Lemma lem5777513 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777512 _120933 a x h1 h2). Qed.
Lemma lem5777515 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777516 : term44 = False.
Proof. exact (@lem5777515 False). Qed.
Lemma lem5777517 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777516) (@lem5777513 _120933 a x h1 h2)). Qed.
Lemma lem5777519 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777520 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777519 _120933 a x h1). Qed.
Lemma lem5777522 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777523 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777522 (a x)). Qed.
Lemma lem5777524 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777523 _120933 a x) (@lem5777520 _120933 a x h1)). Qed.
Lemma lem5777527 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777529 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777527 (a x)). Qed.
Lemma lem5777532 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777529 _120933 a x) (@lem5777219 _120933 a x h1)). Qed.
Lemma lem5777535 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777532 _120933 a x h1 (@lem5777524 _120933 a x h2)). Qed.
Lemma lem5777536 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777535 _120933 a x h1 h2). Qed.
Lemma lem5777538 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777539 : term44 = False.
Proof. exact (@lem5777538 False). Qed.
Lemma lem5777540 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777539) (@lem5777536 _120933 a x h1 h2)). Qed.
Lemma lem5777542 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777543 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777542 _120933 b x h1). Qed.
Lemma lem5777545 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777546 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777545 (b x)). Qed.
Lemma lem5777547 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777546 _120933 b x) (@lem5777543 _120933 b x h1)). Qed.
Lemma lem5777550 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777552 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777550 (b x)). Qed.
Lemma lem5777555 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777552 _120933 b x) (@lem5777229 _120933 b x h1)). Qed.
Lemma lem5777558 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777555 _120933 b x h1 (@lem5777547 _120933 b x h2)). Qed.
Lemma lem5777559 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777558 _120933 b x h1 h2). Qed.
Lemma lem5777561 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777562 : term44 = False.
Proof. exact (@lem5777561 False). Qed.
Lemma lem5777563 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777562) (@lem5777559 _120933 b x h1 h2)). Qed.
Lemma lem5777565 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777566 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777565 _120933 a x h1). Qed.
Lemma lem5777568 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777569 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777568 (a x)). Qed.
Lemma lem5777570 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777569 _120933 a x) (@lem5777566 _120933 a x h1)). Qed.
Lemma lem5777573 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777575 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777573 (a x)). Qed.
Lemma lem5777578 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777575 _120933 a x) (@lem5777237 _120933 a x h1)). Qed.
Lemma lem5777581 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777578 _120933 a x h1 (@lem5777570 _120933 a x h2)). Qed.
Lemma lem5777582 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777581 _120933 a x h1 h2). Qed.
Lemma lem5777584 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777585 : term44 = False.
Proof. exact (@lem5777584 False). Qed.
Lemma lem5777586 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777585) (@lem5777582 _120933 a x h1 h2)). Qed.
Lemma lem5777588 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem5777589 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777588 _120933 a x h1). Qed.
Lemma lem5777591 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777592 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777591 (a x)). Qed.
Lemma lem5777593 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem5777592 _120933 a x) (@lem5777589 _120933 a x h1)). Qed.
Lemma lem5777596 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777598 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777596 (a x)). Qed.
Lemma lem5777601 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777598 _120933 a x) (@lem5777245 _120933 a x h1)). Qed.
Lemma lem5777604 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (@lem5777601 _120933 a x h1 (@lem5777593 _120933 a x h2)). Qed.
Lemma lem5777605 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777604 _120933 a x h1 h2). Qed.
Lemma lem5777607 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777608 : term44 = False.
Proof. exact (@lem5777607 False). Qed.
Lemma lem5777609 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777608) (@lem5777605 _120933 a x h1 h2)). Qed.
Lemma lem5777611 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777612 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777611 _120933 b x h1). Qed.
Lemma lem5777614 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777615 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777614 (b x)). Qed.
Lemma lem5777616 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777615 _120933 b x) (@lem5777612 _120933 b x h1)). Qed.
Lemma lem5777619 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777621 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777619 (b x)). Qed.
Lemma lem5777624 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777621 _120933 b x) (@lem5777253 _120933 b x h1)). Qed.
Lemma lem5777627 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777624 _120933 b x h1 (@lem5777616 _120933 b x h2)). Qed.
Lemma lem5777628 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777627 _120933 b x h1 h2). Qed.
Lemma lem5777630 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777631 : term44 = False.
Proof. exact (@lem5777630 False). Qed.
Lemma lem5777632 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777631) (@lem5777628 _120933 b x h1 h2)). Qed.
Lemma lem5777634 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem5777635 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777634 _120933 b x h1). Qed.
Lemma lem5777637 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777638 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777637 (b x)). Qed.
Lemma lem5777639 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem5777638 _120933 b x) (@lem5777635 _120933 b x h1)). Qed.
Lemma lem5777642 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777644 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777642 (b x)). Qed.
Lemma lem5777647 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777644 _120933 b x) (@lem5777261 _120933 b x h1)). Qed.
Lemma lem5777650 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (@lem5777647 _120933 b x h1 (@lem5777639 _120933 b x h2)). Qed.
Lemma lem5777651 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777650 _120933 b x h1 h2). Qed.
Lemma lem5777653 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777654 : term44 = False.
Proof. exact (@lem5777653 False). Qed.
Lemma lem5777655 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777654) (@lem5777651 _120933 b x h1 h2)). Qed.
Lemma lem5777657 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 a b x) : a x.
Proof. exact (proj1 (@lem5776824 _120933 a b x h1)). Qed.
Lemma lem5777658 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 a b x) : term41 _120933 a x.
Proof. exact (fun h0 : term13 _120933 a x => @lem5777657 _120933 a b x h1). Qed.
Lemma lem5777660 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777661 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term41 _120933 a x) = (a x).
Proof. exact (@lem5777660 (a x)). Qed.
Lemma lem5777662 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 a b x) : a x.
Proof. exact (EQ_MP (@lem5777661 _120933 a x) (@lem5777658 _120933 a b x h1)). Qed.
Lemma lem5777665 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777667 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) : (term13 _120933 a x) = (term43 _120933 a x).
Proof. exact (@lem5777665 (a x)). Qed.
Lemma lem5777670 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term43 _120933 a x.
Proof. exact (EQ_MP (@lem5777667 _120933 a x) (@lem5777265 _120933 a b x h1)). Qed.
Lemma lem5777673 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 a b x) (h2 : term272 _120933 a b x) : False.
Proof. exact (@lem5777670 _120933 a b x h2 (@lem5777662 _120933 a b x h1)). Qed.
Lemma lem5777674 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 a b x) (h2 : term272 _120933 a b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777673 _120933 a b x h1 h2). Qed.
Lemma lem5777676 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777677 : term44 = False.
Proof. exact (@lem5777676 False). Qed.
Lemma lem5777678 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 a b x) (h2 : term272 _120933 a b x) : False.
Proof. exact (EQ_MP (@lem5777677) (@lem5777674 _120933 a b x h1 h2)). Qed.
Lemma lem5777680 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 b a x) : b x.
Proof. exact (proj1 (@lem5776825 _120933 b a x h1)). Qed.
Lemma lem5777681 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 b a x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777680 _120933 b a x h1). Qed.
Lemma lem5777683 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777684 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777683 (b x)). Qed.
Lemma lem5777685 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 b a x) : b x.
Proof. exact (EQ_MP (@lem5777684 _120933 b x) (@lem5777681 _120933 b a x h1)). Qed.
Lemma lem5777688 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777690 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777688 (b x)). Qed.
Lemma lem5777693 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777690 _120933 b x) (@lem5777275 _120933 a b x h1)). Qed.
Lemma lem5777696 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 b a x) (h2 : term272 _120933 a b x) : False.
Proof. exact (@lem5777693 _120933 a b x h2 (@lem5777685 _120933 b a x h1)). Qed.
Lemma lem5777697 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 b a x) (h2 : term272 _120933 a b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777696 _120933 a b x h1 h2). Qed.
Lemma lem5777699 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777700 : term44 = False.
Proof. exact (@lem5777699 False). Qed.
Lemma lem5777701 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term14 _120933 b a x) (h2 : term272 _120933 a b x) : False.
Proof. exact (EQ_MP (@lem5777700) (@lem5777697 _120933 a b x h1 h2)). Qed.
Lemma lem5777703 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term17 _120933 a b x) : b x.
Proof. exact (proj2 (@lem5776823 _120933 a b x h1)). Qed.
Lemma lem5777704 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term17 _120933 a b x) : term41 _120933 b x.
Proof. exact (fun h0 : term13 _120933 b x => @lem5777703 _120933 a b x h1). Qed.
Lemma lem5777706 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777707 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term41 _120933 b x) = (b x).
Proof. exact (@lem5777706 (b x)). Qed.
Lemma lem5777708 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term17 _120933 a b x) : b x.
Proof. exact (EQ_MP (@lem5777707 _120933 b x) (@lem5777704 _120933 a b x h1)). Qed.
Lemma lem5777711 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5777713 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) : (term13 _120933 b x) = (term43 _120933 b x).
Proof. exact (@lem5777711 (b x)). Qed.
Lemma lem5777716 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : term43 _120933 b x.
Proof. exact (EQ_MP (@lem5777713 _120933 b x) (@lem5777283 _120933 a b x h1)). Qed.
Lemma lem5777719 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term17 _120933 a b x) (h2 : term272 _120933 a b x) : False.
Proof. exact (@lem5777716 _120933 a b x h2 (@lem5777708 _120933 a b x h1)). Qed.
Lemma lem5777720 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term17 _120933 a b x) (h2 : term272 _120933 a b x) : term44.
Proof. exact (fun h0 : ~ False => @lem5777719 _120933 a b x h1 h2). Qed.
Lemma lem5777722 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5777723 : term44 = False.
Proof. exact (@lem5777722 False). Qed.
Lemma lem5777724 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term17 _120933 a b x) (h2 : term272 _120933 a b x) : False.
Proof. exact (EQ_MP (@lem5777723) (@lem5777720 _120933 a b x h1 h2)). Qed.
Lemma lem5777725 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777655 _120933 b x h1 h2) (fun h3 : False => @lem5777263 _120933 b x h2)). Qed.
Lemma lem5777726 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777725 _120933 b x h1 h2) (@lem5777263 _120933 b x h2)). Qed.
Lemma lem5777727 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777726 _120933 b x h1 h2) (fun h3 : False => @lem5777261 _120933 b x h1)). Qed.
Lemma lem5777728 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777727 _120933 b x h1 h2) (@lem5777261 _120933 b x h1)). Qed.
Lemma lem5777729 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777728 _120933 b x h1 h2) (fun h3 : False => @lem5777259 _120933 b x h2)). Qed.
Lemma lem5777730 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777729 _120933 b x h1 h2) (@lem5777259 _120933 b x h2)). Qed.
Lemma lem5777731 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777632 _120933 b x h1 h2) (fun h3 : False => @lem5777253 _120933 b x h1)). Qed.
Lemma lem5777732 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777731 _120933 b x h1 h2) (@lem5777253 _120933 b x h1)). Qed.
Lemma lem5777733 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777732 _120933 b x h1 h2) (fun h3 : False => @lem5777251 _120933 b x h2)). Qed.
Lemma lem5777734 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777733 _120933 b x h1 h2) (@lem5777251 _120933 b x h2)). Qed.
Lemma lem5777735 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777609 _120933 a x h1 h2) (fun h3 : False => @lem5777245 _120933 a x h1)). Qed.
Lemma lem5777736 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777735 _120933 a x h1 h2) (@lem5777245 _120933 a x h1)). Qed.
Lemma lem5777737 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777736 _120933 a x h1 h2) (fun h3 : False => @lem5777241 _120933 a x h2)). Qed.
Lemma lem5777738 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777737 _120933 a x h1 h2) (@lem5777241 _120933 a x h2)). Qed.
Lemma lem5777739 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777586 _120933 a x h1 h2) (fun h3 : False => @lem5777239 _120933 a x h2)). Qed.
Lemma lem5777740 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777739 _120933 a x h1 h2) (@lem5777239 _120933 a x h2)). Qed.
Lemma lem5777741 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777740 _120933 a x h1 h2) (fun h3 : False => @lem5777237 _120933 a x h1)). Qed.
Lemma lem5777742 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777741 _120933 a x h1 h2) (@lem5777237 _120933 a x h1)). Qed.
Lemma lem5777743 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777742 _120933 a x h1 h2) (fun h3 : False => @lem5777233 _120933 a x h2)). Qed.
Lemma lem5777744 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777743 _120933 a x h1 h2) (@lem5777233 _120933 a x h2)). Qed.
Lemma lem5777745 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777563 _120933 b x h1 h2) (fun h3 : False => @lem5777231 _120933 b x h2)). Qed.
Lemma lem5777746 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777745 _120933 b x h1 h2) (@lem5777231 _120933 b x h2)). Qed.
Lemma lem5777747 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777746 _120933 b x h1 h2) (fun h3 : False => @lem5777229 _120933 b x h1)). Qed.
Lemma lem5777748 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777747 _120933 b x h1 h2) (@lem5777229 _120933 b x h1)). Qed.
Lemma lem5777749 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777540 _120933 a x h1 h2) (fun h3 : False => @lem5777223 _120933 a x h2)). Qed.
Lemma lem5777750 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777749 _120933 a x h1 h2) (@lem5777223 _120933 a x h2)). Qed.
Lemma lem5777751 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777750 _120933 a x h1 h2) (fun h3 : False => @lem5777219 _120933 a x h1)). Qed.
Lemma lem5777752 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777751 _120933 a x h1 h2) (@lem5777219 _120933 a x h1)). Qed.
Lemma lem5777753 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777752 _120933 a x h1 h2) (fun h3 : False => @lem5777217 _120933 a x h2)). Qed.
Lemma lem5777754 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777753 _120933 a x h1 h2) (@lem5777217 _120933 a x h2)). Qed.
Lemma lem5777755 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777517 _120933 a x h1 h2) (fun h3 : False => @lem5777213 _120933 a x h1)). Qed.
Lemma lem5777756 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777755 _120933 a x h1 h2) (@lem5777213 _120933 a x h1)). Qed.
Lemma lem5777757 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777756 _120933 a x h1 h2) (fun h3 : False => @lem5777211 _120933 a x h1)). Qed.
Lemma lem5777758 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777757 _120933 a x h1 h2) (@lem5777211 _120933 a x h1)). Qed.
Lemma lem5777759 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777758 _120933 a x h1 h2) (fun h3 : False => @lem5777209 _120933 a x h2)). Qed.
Lemma lem5777760 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777759 _120933 a x h1 h2) (@lem5777209 _120933 a x h2)). Qed.
Lemma lem5777761 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777494 _120933 a x h1 h2) (fun h3 : False => @lem5777207 _120933 a x h2)). Qed.
Lemma lem5777762 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777761 _120933 a x h1 h2) (@lem5777207 _120933 a x h2)). Qed.
Lemma lem5777763 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777762 _120933 a x h1 h2) (fun h3 : False => @lem5777205 _120933 a x h1)). Qed.
Lemma lem5777764 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777763 _120933 a x h1 h2) (@lem5777205 _120933 a x h1)). Qed.
Lemma lem5777765 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777764 _120933 a x h1 h2) (fun h3 : False => @lem5777203 _120933 a x h1)). Qed.
Lemma lem5777766 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777765 _120933 a x h1 h2) (@lem5777203 _120933 a x h1)). Qed.
Lemma lem5777767 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777766 _120933 a x h1 h2) (fun h3 : False => @lem5777201 _120933 a x h2)). Qed.
Lemma lem5777768 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777767 _120933 a x h1 h2) (@lem5777201 _120933 a x h2)). Qed.
Lemma lem5777769 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777471 _120933 b x h1 h2) (fun h3 : False => @lem5777199 _120933 b x h2)). Qed.
Lemma lem5777770 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777769 _120933 b x h1 h2) (@lem5777199 _120933 b x h2)). Qed.
Lemma lem5777771 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777770 _120933 b x h1 h2) (fun h3 : False => @lem5777197 _120933 b x h1)). Qed.
Lemma lem5777772 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777771 _120933 b x h1 h2) (@lem5777197 _120933 b x h1)). Qed.
Lemma lem5777773 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777772 _120933 b x h1 h2) (fun h3 : False => @lem5777195 _120933 b x h2)). Qed.
Lemma lem5777774 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777773 _120933 b x h1 h2) (@lem5777195 _120933 b x h2)). Qed.
Lemma lem5777775 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777774 _120933 b x h1 h2) (fun h3 : False => @lem5777193 _120933 b x h1)). Qed.
Lemma lem5777776 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777775 _120933 b x h1 h2) (@lem5777193 _120933 b x h1)). Qed.
Lemma lem5777777 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777448 _120933 b x h1 h2) (fun h3 : False => @lem5777189 _120933 b x h1)). Qed.
Lemma lem5777778 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777777 _120933 b x h1 h2) (@lem5777189 _120933 b x h1)). Qed.
Lemma lem5777779 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777778 _120933 b x h1 h2) (fun h3 : False => @lem5777187 _120933 b x h2)). Qed.
Lemma lem5777780 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777779 _120933 b x h1 h2) (@lem5777187 _120933 b x h2)). Qed.
Lemma lem5777781 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777780 _120933 b x h1 h2) (fun h3 : False => @lem5777185 _120933 b x h1)). Qed.
Lemma lem5777782 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777781 _120933 b x h1 h2) (@lem5777185 _120933 b x h1)). Qed.
Lemma lem5777783 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777425 _120933 b x h1 h2) (fun h3 : False => @lem5777183 _120933 b x h2)). Qed.
Lemma lem5777784 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777783 _120933 b x h1 h2) (@lem5777183 _120933 b x h2)). Qed.
Lemma lem5777785 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777784 _120933 b x h1 h2) (fun h3 : False => @lem5777179 _120933 b x h2)). Qed.
Lemma lem5777786 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777785 _120933 b x h1 h2) (@lem5777179 _120933 b x h2)). Qed.
Lemma lem5777787 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777786 _120933 b x h1 h2) (fun h3 : False => @lem5777177 _120933 b x h1)). Qed.
Lemma lem5777788 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777787 _120933 b x h1 h2) (@lem5777177 _120933 b x h1)). Qed.
Lemma lem5777789 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777402 _120933 a x h1 h2) (fun h3 : False => @lem5777175 _120933 a x h2)). Qed.
Lemma lem5777790 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777789 _120933 a x h1 h2) (@lem5777175 _120933 a x h2)). Qed.
Lemma lem5777791 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777790 _120933 a x h1 h2) (fun h3 : False => @lem5777173 _120933 a x h1)). Qed.
Lemma lem5777792 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777791 _120933 a x h1 h2) (@lem5777173 _120933 a x h1)). Qed.
Lemma lem5777793 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777379 _120933 b x h1 h2) (fun h3 : False => @lem5777167 _120933 b x h2)). Qed.
Lemma lem5777794 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777793 _120933 b x h1 h2) (@lem5777167 _120933 b x h2)). Qed.
Lemma lem5777795 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777794 _120933 b x h1 h2) (fun h3 : False => @lem5777165 _120933 b x h1)). Qed.
Lemma lem5777796 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777795 _120933 b x h1 h2) (@lem5777165 _120933 b x h1)). Qed.
Lemma lem5777797 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777796 _120933 b x h1 h2) (fun h3 : False => @lem5777161 _120933 b x h1)). Qed.
Lemma lem5777798 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777797 _120933 b x h1 h2) (@lem5777161 _120933 b x h1)). Qed.
Lemma lem5777799 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777356 _120933 a x h1 h2) (fun h3 : False => @lem5777159 _120933 a x h2)). Qed.
Lemma lem5777800 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777799 _120933 a x h1 h2) (@lem5777159 _120933 a x h2)). Qed.
Lemma lem5777801 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777800 _120933 a x h1 h2) (fun h3 : False => @lem5777155 _120933 a x h1)). Qed.
Lemma lem5777802 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777801 _120933 a x h1 h2) (@lem5777155 _120933 a x h1)). Qed.
Lemma lem5777803 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777333 _120933 b x h1 h2) (fun h3 : False => @lem5777151 _120933 b x h2)). Qed.
Lemma lem5777804 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777803 _120933 b x h1 h2) (@lem5777151 _120933 b x h2)). Qed.
Lemma lem5777805 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777804 _120933 b x h1 h2) (fun h3 : False => @lem5777145 _120933 b x h1)). Qed.
Lemma lem5777806 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777805 _120933 b x h1 h2) (@lem5777145 _120933 b x h1)). Qed.
Lemma lem5777807 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777310 _120933 a x h1 h2) (fun h3 : False => @lem5777143 _120933 a x h2)). Qed.
Lemma lem5777808 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777807 _120933 a x h1 h2) (@lem5777143 _120933 a x h2)). Qed.
Lemma lem5777809 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777808 _120933 a x h1 h2) (fun h3 : False => @lem5777141 _120933 a x h1)). Qed.
Lemma lem5777810 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777809 _120933 a x h1 h2) (@lem5777141 _120933 a x h1)). Qed.
Lemma lem5777811 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777810 _120933 a x h1 h2) (fun h3 : False => @lem5777139 _120933 a x h1)). Qed.
Lemma lem5777812 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777811 _120933 a x h1 h2) (@lem5777139 _120933 a x h1)). Qed.
Lemma lem5777813 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777730 _120933 b x h1 h2) (fun h3 : False => @lem5777087 _120933 b x h2)). Qed.
Lemma lem5777814 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777813 _120933 b x h1 h2) (@lem5777087 _120933 b x h2)). Qed.
Lemma lem5777815 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777814 _120933 b x h1 h2) (fun h3 : False => @lem5777083 _120933 b x h1)). Qed.
Lemma lem5777816 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777815 _120933 b x h1 h2) (@lem5777083 _120933 b x h1)). Qed.
Lemma lem5777817 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777816 _120933 b x h1 h2) (fun h3 : False => @lem5777079 _120933 b x h2)). Qed.
Lemma lem5777818 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777817 _120933 b x h1 h2) (@lem5777079 _120933 b x h2)). Qed.
Lemma lem5777819 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777734 _120933 b x h1 h2) (fun h3 : False => @lem5777067 _120933 b x h1)). Qed.
Lemma lem5777820 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777819 _120933 b x h1 h2) (@lem5777067 _120933 b x h1)). Qed.
Lemma lem5777821 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777820 _120933 b x h1 h2) (fun h3 : False => @lem5777063 _120933 b x h2)). Qed.
Lemma lem5777822 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777821 _120933 b x h1 h2) (@lem5777063 _120933 b x h2)). Qed.
Lemma lem5777823 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777738 _120933 a x h1 h2) (fun h3 : False => @lem5777051 _120933 a x h1)). Qed.
Lemma lem5777824 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777823 _120933 a x h1 h2) (@lem5777051 _120933 a x h1)). Qed.
Lemma lem5777825 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777824 _120933 a x h1 h2) (fun h3 : False => @lem5777043 _120933 a x h2)). Qed.
Lemma lem5777826 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777825 _120933 a x h1 h2) (@lem5777043 _120933 a x h2)). Qed.
Lemma lem5777827 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777744 _120933 a x h1 h2) (fun h3 : False => @lem5777039 _120933 a x h2)). Qed.
Lemma lem5777828 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777827 _120933 a x h1 h2) (@lem5777039 _120933 a x h2)). Qed.
Lemma lem5777829 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777828 _120933 a x h1 h2) (fun h3 : False => @lem5777035 _120933 a x h1)). Qed.
Lemma lem5777830 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777829 _120933 a x h1 h2) (@lem5777035 _120933 a x h1)). Qed.
Lemma lem5777831 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777830 _120933 a x h1 h2) (fun h3 : False => @lem5777027 _120933 a x h2)). Qed.
Lemma lem5777832 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777831 _120933 a x h1 h2) (@lem5777027 _120933 a x h2)). Qed.
Lemma lem5777833 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777748 _120933 b x h1 h2) (fun h3 : False => @lem5777023 _120933 b x h2)). Qed.
Lemma lem5777834 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777833 _120933 b x h1 h2) (@lem5777023 _120933 b x h2)). Qed.
Lemma lem5777835 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777834 _120933 b x h1 h2) (fun h3 : False => @lem5777019 _120933 b x h1)). Qed.
Lemma lem5777836 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777835 _120933 b x h1 h2) (@lem5777019 _120933 b x h1)). Qed.
Lemma lem5777837 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777754 _120933 a x h1 h2) (fun h3 : False => @lem5777007 _120933 a x h2)). Qed.
Lemma lem5777838 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777837 _120933 a x h1 h2) (@lem5777007 _120933 a x h2)). Qed.
Lemma lem5777839 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777838 _120933 a x h1 h2) (fun h3 : False => @lem5776999 _120933 a x h1)). Qed.
Lemma lem5777840 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777839 _120933 a x h1 h2) (@lem5776999 _120933 a x h1)). Qed.
Lemma lem5777841 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777840 _120933 a x h1 h2) (fun h3 : False => @lem5776995 _120933 a x h2)). Qed.
Lemma lem5777842 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777841 _120933 a x h1 h2) (@lem5776995 _120933 a x h2)). Qed.
Lemma lem5777843 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777760 _120933 a x h1 h2) (fun h3 : False => @lem5776987 _120933 a x h1)). Qed.
Lemma lem5777844 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777843 _120933 a x h1 h2) (@lem5776987 _120933 a x h1)). Qed.
Lemma lem5777845 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777844 _120933 a x h1 h2) (fun h3 : False => @lem5776983 _120933 a x h1)). Qed.
Lemma lem5777846 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777845 _120933 a x h1 h2) (@lem5776983 _120933 a x h1)). Qed.
Lemma lem5777847 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777846 _120933 a x h1 h2) (fun h3 : False => @lem5776979 _120933 a x h2)). Qed.
Lemma lem5777848 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777847 _120933 a x h1 h2) (@lem5776979 _120933 a x h2)). Qed.
Lemma lem5777849 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777768 _120933 a x h1 h2) (fun h3 : False => @lem5776975 _120933 a x h2)). Qed.
Lemma lem5777850 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777849 _120933 a x h1 h2) (@lem5776975 _120933 a x h2)). Qed.
Lemma lem5777851 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777850 _120933 a x h1 h2) (fun h3 : False => @lem5776971 _120933 a x h1)). Qed.
Lemma lem5777852 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777851 _120933 a x h1 h2) (@lem5776971 _120933 a x h1)). Qed.
Lemma lem5777853 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777852 _120933 a x h1 h2) (fun h3 : False => @lem5776967 _120933 a x h1)). Qed.
Lemma lem5777854 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777853 _120933 a x h1 h2) (@lem5776967 _120933 a x h1)). Qed.
Lemma lem5777855 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777854 _120933 a x h1 h2) (fun h3 : False => @lem5776963 _120933 a x h2)). Qed.
Lemma lem5777856 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777855 _120933 a x h1 h2) (@lem5776963 _120933 a x h2)). Qed.
Lemma lem5777857 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777776 _120933 b x h1 h2) (fun h3 : False => @lem5776959 _120933 b x h2)). Qed.
Lemma lem5777858 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777857 _120933 b x h1 h2) (@lem5776959 _120933 b x h2)). Qed.
Lemma lem5777859 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777858 _120933 b x h1 h2) (fun h3 : False => @lem5776955 _120933 b x h1)). Qed.
Lemma lem5777860 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777859 _120933 b x h1 h2) (@lem5776955 _120933 b x h1)). Qed.
Lemma lem5777861 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777860 _120933 b x h1 h2) (fun h3 : False => @lem5776951 _120933 b x h2)). Qed.
Lemma lem5777862 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777861 _120933 b x h1 h2) (@lem5776951 _120933 b x h2)). Qed.
Lemma lem5777863 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777862 _120933 b x h1 h2) (fun h3 : False => @lem5776947 _120933 b x h1)). Qed.
Lemma lem5777864 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777863 _120933 b x h1 h2) (@lem5776947 _120933 b x h1)). Qed.
Lemma lem5777865 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777782 _120933 b x h1 h2) (fun h3 : False => @lem5776939 _120933 b x h1)). Qed.
Lemma lem5777866 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777865 _120933 b x h1 h2) (@lem5776939 _120933 b x h1)). Qed.
Lemma lem5777867 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777866 _120933 b x h1 h2) (fun h3 : False => @lem5776935 _120933 b x h2)). Qed.
Lemma lem5777868 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777867 _120933 b x h1 h2) (@lem5776935 _120933 b x h2)). Qed.
Lemma lem5777869 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777868 _120933 b x h1 h2) (fun h3 : False => @lem5776931 _120933 b x h1)). Qed.
Lemma lem5777870 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777869 _120933 b x h1 h2) (@lem5776931 _120933 b x h1)). Qed.
Lemma lem5777871 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777788 _120933 b x h1 h2) (fun h3 : False => @lem5776927 _120933 b x h2)). Qed.
Lemma lem5777872 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777871 _120933 b x h1 h2) (@lem5776927 _120933 b x h2)). Qed.
Lemma lem5777873 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777872 _120933 b x h1 h2) (fun h3 : False => @lem5776919 _120933 b x h2)). Qed.
Lemma lem5777874 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777873 _120933 b x h1 h2) (@lem5776919 _120933 b x h2)). Qed.
Lemma lem5777875 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777874 _120933 b x h1 h2) (fun h3 : False => @lem5776915 _120933 b x h1)). Qed.
Lemma lem5777876 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777875 _120933 b x h1 h2) (@lem5776915 _120933 b x h1)). Qed.
Lemma lem5777877 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777792 _120933 a x h1 h2) (fun h3 : False => @lem5776911 _120933 a x h2)). Qed.
Lemma lem5777878 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777877 _120933 a x h1 h2) (@lem5776911 _120933 a x h2)). Qed.
Lemma lem5777879 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777878 _120933 a x h1 h2) (fun h3 : False => @lem5776907 _120933 a x h1)). Qed.
Lemma lem5777880 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777879 _120933 a x h1 h2) (@lem5776907 _120933 a x h1)). Qed.
Lemma lem5777881 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777798 _120933 b x h1 h2) (fun h3 : False => @lem5776895 _120933 b x h2)). Qed.
Lemma lem5777882 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777881 _120933 b x h1 h2) (@lem5776895 _120933 b x h2)). Qed.
Lemma lem5777883 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777882 _120933 b x h1 h2) (fun h3 : False => @lem5776891 _120933 b x h1)). Qed.
Lemma lem5777884 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777883 _120933 b x h1 h2) (@lem5776891 _120933 b x h1)). Qed.
Lemma lem5777885 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777884 _120933 b x h1 h2) (fun h3 : False => @lem5776883 _120933 b x h1)). Qed.
Lemma lem5777886 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777885 _120933 b x h1 h2) (@lem5776883 _120933 b x h1)). Qed.
Lemma lem5777887 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777802 _120933 a x h1 h2) (fun h3 : False => @lem5776879 _120933 a x h2)). Qed.
Lemma lem5777888 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777887 _120933 a x h1 h2) (@lem5776879 _120933 a x h2)). Qed.
Lemma lem5777889 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777888 _120933 a x h1 h2) (fun h3 : False => @lem5776871 _120933 a x h1)). Qed.
Lemma lem5777890 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777889 _120933 a x h1 h2) (@lem5776871 _120933 a x h1)). Qed.
Lemma lem5777891 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777806 _120933 b x h1 h2) (fun h3 : False => @lem5776863 _120933 b x h2)). Qed.
Lemma lem5777892 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777891 _120933 b x h1 h2) (@lem5776863 _120933 b x h2)). Qed.
Lemma lem5777893 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777892 _120933 b x h1 h2) (fun h3 : False => @lem5776851 _120933 b x h1)). Qed.
Lemma lem5777894 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777893 _120933 b x h1 h2) (@lem5776851 _120933 b x h1)). Qed.
Lemma lem5777895 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777812 _120933 a x h1 h2) (fun h3 : False => @lem5776847 _120933 a x h2)). Qed.
Lemma lem5777896 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777895 _120933 a x h1 h2) (@lem5776847 _120933 a x h2)). Qed.
Lemma lem5777897 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777896 _120933 a x h1 h2) (fun h3 : False => @lem5776843 _120933 a x h1)). Qed.
Lemma lem5777898 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777897 _120933 a x h1 h2) (@lem5776843 _120933 a x h1)). Qed.
Lemma lem5777899 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777898 _120933 a x h1 h2) (fun h3 : False => @lem5776839 _120933 a x h1)). Qed.
Lemma lem5777900 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777899 _120933 a x h1 h2) (@lem5776839 _120933 a x h1)). Qed.
Lemma lem5777901 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777818 _120933 b x h1 h2) (fun h3 : False => @lem5777087 _120933 b x h2)). Qed.
Lemma lem5777902 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777901 _120933 b x h1 h2) (@lem5777087 _120933 b x h2)). Qed.
Lemma lem5777903 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777902 _120933 b x h1 h2) (fun h3 : False => @lem5777083 _120933 b x h1)). Qed.
Lemma lem5777904 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777903 _120933 b x h1 h2) (@lem5777083 _120933 b x h1)). Qed.
Lemma lem5777905 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777904 _120933 b x h1 h2) (fun h3 : False => @lem5777079 _120933 b x h2)). Qed.
Lemma lem5777906 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777905 _120933 b x h1 h2) (@lem5777079 _120933 b x h2)). Qed.
Lemma lem5777907 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777822 _120933 b x h1 h2) (fun h3 : False => @lem5777067 _120933 b x h1)). Qed.
Lemma lem5777908 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777907 _120933 b x h1 h2) (@lem5777067 _120933 b x h1)). Qed.
Lemma lem5777909 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777908 _120933 b x h1 h2) (fun h3 : False => @lem5777063 _120933 b x h2)). Qed.
Lemma lem5777910 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777909 _120933 b x h1 h2) (@lem5777063 _120933 b x h2)). Qed.
Lemma lem5777911 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777826 _120933 a x h1 h2) (fun h3 : False => @lem5777051 _120933 a x h1)). Qed.
Lemma lem5777912 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777911 _120933 a x h1 h2) (@lem5777051 _120933 a x h1)). Qed.
Lemma lem5777913 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777912 _120933 a x h1 h2) (fun h3 : False => @lem5777043 _120933 a x h2)). Qed.
Lemma lem5777914 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777913 _120933 a x h1 h2) (@lem5777043 _120933 a x h2)). Qed.
Lemma lem5777915 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777832 _120933 a x h1 h2) (fun h3 : False => @lem5777039 _120933 a x h2)). Qed.
Lemma lem5777916 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777915 _120933 a x h1 h2) (@lem5777039 _120933 a x h2)). Qed.
Lemma lem5777917 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777916 _120933 a x h1 h2) (fun h3 : False => @lem5777035 _120933 a x h1)). Qed.
Lemma lem5777918 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777917 _120933 a x h1 h2) (@lem5777035 _120933 a x h1)). Qed.
Lemma lem5777919 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777918 _120933 a x h1 h2) (fun h3 : False => @lem5777027 _120933 a x h2)). Qed.
Lemma lem5777920 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777919 _120933 a x h1 h2) (@lem5777027 _120933 a x h2)). Qed.
Lemma lem5777921 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777836 _120933 b x h1 h2) (fun h3 : False => @lem5777023 _120933 b x h2)). Qed.
Lemma lem5777922 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777921 _120933 b x h1 h2) (@lem5777023 _120933 b x h2)). Qed.
Lemma lem5777923 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777922 _120933 b x h1 h2) (fun h3 : False => @lem5777019 _120933 b x h1)). Qed.
Lemma lem5777924 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777923 _120933 b x h1 h2) (@lem5777019 _120933 b x h1)). Qed.
Lemma lem5777925 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777842 _120933 a x h1 h2) (fun h3 : False => @lem5777007 _120933 a x h2)). Qed.
Lemma lem5777926 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777925 _120933 a x h1 h2) (@lem5777007 _120933 a x h2)). Qed.
Lemma lem5777927 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777926 _120933 a x h1 h2) (fun h3 : False => @lem5776999 _120933 a x h1)). Qed.
Lemma lem5777928 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777927 _120933 a x h1 h2) (@lem5776999 _120933 a x h1)). Qed.
Lemma lem5777929 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777928 _120933 a x h1 h2) (fun h3 : False => @lem5776995 _120933 a x h2)). Qed.
Lemma lem5777930 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777929 _120933 a x h1 h2) (@lem5776995 _120933 a x h2)). Qed.
Lemma lem5777931 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777848 _120933 a x h1 h2) (fun h3 : False => @lem5776987 _120933 a x h1)). Qed.
Lemma lem5777932 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777931 _120933 a x h1 h2) (@lem5776987 _120933 a x h1)). Qed.
Lemma lem5777933 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777932 _120933 a x h1 h2) (fun h3 : False => @lem5776983 _120933 a x h1)). Qed.
Lemma lem5777934 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777933 _120933 a x h1 h2) (@lem5776983 _120933 a x h1)). Qed.
Lemma lem5777935 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777934 _120933 a x h1 h2) (fun h3 : False => @lem5776979 _120933 a x h2)). Qed.
Lemma lem5777936 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777935 _120933 a x h1 h2) (@lem5776979 _120933 a x h2)). Qed.
Lemma lem5777937 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777856 _120933 a x h1 h2) (fun h3 : False => @lem5776975 _120933 a x h2)). Qed.
Lemma lem5777938 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777937 _120933 a x h1 h2) (@lem5776975 _120933 a x h2)). Qed.
Lemma lem5777939 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777938 _120933 a x h1 h2) (fun h3 : False => @lem5776971 _120933 a x h1)). Qed.
Lemma lem5777940 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777939 _120933 a x h1 h2) (@lem5776971 _120933 a x h1)). Qed.
Lemma lem5777941 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777940 _120933 a x h1 h2) (fun h3 : False => @lem5776967 _120933 a x h1)). Qed.
Lemma lem5777942 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777941 _120933 a x h1 h2) (@lem5776967 _120933 a x h1)). Qed.
Lemma lem5777943 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777942 _120933 a x h1 h2) (fun h3 : False => @lem5776963 _120933 a x h2)). Qed.
Lemma lem5777944 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777943 _120933 a x h1 h2) (@lem5776963 _120933 a x h2)). Qed.
Lemma lem5777945 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777864 _120933 b x h1 h2) (fun h3 : False => @lem5776959 _120933 b x h2)). Qed.
Lemma lem5777946 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777945 _120933 b x h1 h2) (@lem5776959 _120933 b x h2)). Qed.
Lemma lem5777947 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777946 _120933 b x h1 h2) (fun h3 : False => @lem5776955 _120933 b x h1)). Qed.
Lemma lem5777948 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777947 _120933 b x h1 h2) (@lem5776955 _120933 b x h1)). Qed.
Lemma lem5777949 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777948 _120933 b x h1 h2) (fun h3 : False => @lem5776951 _120933 b x h2)). Qed.
Lemma lem5777950 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777949 _120933 b x h1 h2) (@lem5776951 _120933 b x h2)). Qed.
Lemma lem5777951 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777950 _120933 b x h1 h2) (fun h3 : False => @lem5776947 _120933 b x h1)). Qed.
Lemma lem5777952 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777951 _120933 b x h1 h2) (@lem5776947 _120933 b x h1)). Qed.
Lemma lem5777953 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777870 _120933 b x h1 h2) (fun h3 : False => @lem5776939 _120933 b x h1)). Qed.
Lemma lem5777954 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777953 _120933 b x h1 h2) (@lem5776939 _120933 b x h1)). Qed.
Lemma lem5777955 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777954 _120933 b x h1 h2) (fun h3 : False => @lem5776935 _120933 b x h2)). Qed.
Lemma lem5777956 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777955 _120933 b x h1 h2) (@lem5776935 _120933 b x h2)). Qed.
Lemma lem5777957 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777956 _120933 b x h1 h2) (fun h3 : False => @lem5776931 _120933 b x h1)). Qed.
Lemma lem5777958 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777957 _120933 b x h1 h2) (@lem5776931 _120933 b x h1)). Qed.
Lemma lem5777959 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777876 _120933 b x h1 h2) (fun h3 : False => @lem5776927 _120933 b x h2)). Qed.
Lemma lem5777960 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777959 _120933 b x h1 h2) (@lem5776927 _120933 b x h2)). Qed.
Lemma lem5777961 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777960 _120933 b x h1 h2) (fun h3 : False => @lem5776919 _120933 b x h2)). Qed.
Lemma lem5777962 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777961 _120933 b x h1 h2) (@lem5776919 _120933 b x h2)). Qed.
Lemma lem5777963 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777962 _120933 b x h1 h2) (fun h3 : False => @lem5776915 _120933 b x h1)). Qed.
Lemma lem5777964 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777963 _120933 b x h1 h2) (@lem5776915 _120933 b x h1)). Qed.
Lemma lem5777965 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777880 _120933 a x h1 h2) (fun h3 : False => @lem5776911 _120933 a x h2)). Qed.
Lemma lem5777966 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777965 _120933 a x h1 h2) (@lem5776911 _120933 a x h2)). Qed.
Lemma lem5777967 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777966 _120933 a x h1 h2) (fun h3 : False => @lem5776907 _120933 a x h1)). Qed.
Lemma lem5777968 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777967 _120933 a x h1 h2) (@lem5776907 _120933 a x h1)). Qed.
Lemma lem5777969 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777886 _120933 b x h1 h2) (fun h3 : False => @lem5776895 _120933 b x h2)). Qed.
Lemma lem5777970 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777969 _120933 b x h1 h2) (@lem5776895 _120933 b x h2)). Qed.
Lemma lem5777971 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777970 _120933 b x h1 h2) (fun h3 : False => @lem5776891 _120933 b x h1)). Qed.
Lemma lem5777972 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777971 _120933 b x h1 h2) (@lem5776891 _120933 b x h1)). Qed.
Lemma lem5777973 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777972 _120933 b x h1 h2) (fun h3 : False => @lem5776883 _120933 b x h1)). Qed.
Lemma lem5777974 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777973 _120933 b x h1 h2) (@lem5776883 _120933 b x h1)). Qed.
Lemma lem5777975 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777890 _120933 a x h1 h2) (fun h3 : False => @lem5776879 _120933 a x h2)). Qed.
Lemma lem5777976 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777975 _120933 a x h1 h2) (@lem5776879 _120933 a x h2)). Qed.
Lemma lem5777977 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777976 _120933 a x h1 h2) (fun h3 : False => @lem5776871 _120933 a x h1)). Qed.
Lemma lem5777978 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777977 _120933 a x h1 h2) (@lem5776871 _120933 a x h1)). Qed.
Lemma lem5777979 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem5777894 _120933 b x h1 h2) (fun h3 : False => @lem5776863 _120933 b x h2)). Qed.
Lemma lem5777980 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777979 _120933 b x h1 h2) (@lem5776863 _120933 b x h2)). Qed.
Lemma lem5777981 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : (term13 _120933 b x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 b x => @lem5777980 _120933 b x h1 h2) (fun h3 : False => @lem5776851 _120933 b x h1)). Qed.
Lemma lem5777982 {_120933 : Type'} (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem5777981 _120933 b x h1 h2) (@lem5776851 _120933 b x h1)). Qed.
Lemma lem5777983 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem5777900 _120933 a x h1 h2) (fun h3 : False => @lem5776847 _120933 a x h2)). Qed.
Lemma lem5777984 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777983 _120933 a x h1 h2) (@lem5776847 _120933 a x h2)). Qed.
Lemma lem5777985 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777984 _120933 a x h1 h2) (fun h3 : False => @lem5776843 _120933 a x h1)). Qed.
Lemma lem5777986 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777985 _120933 a x h1 h2) (@lem5776843 _120933 a x h1)). Qed.
Lemma lem5777987 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : (term13 _120933 a x) = False.
Proof. exact (prop_ext (fun h3 : term13 _120933 a x => @lem5777986 _120933 a x h1 h2) (fun h3 : False => @lem5776839 _120933 a x h1)). Qed.
Lemma lem5777988 {_120933 : Type'} (a : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem5777987 _120933 a x h1 h2) (@lem5776839 _120933 a x h1)). Qed.
Lemma lem5777989 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) (h2 : term118 _120933 b a x) : False.
Proof. exact (or_elim (@lem5776822 _120933 b a x h2) (fun h0 : term14 _120933 a b x => @lem5777678 _120933 a b x h0 h1) (fun h0 : term14 _120933 b a x => @lem5777701 _120933 a b x h0 h1)). Qed.
Lemma lem5777990 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term272 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776818 _120933 a b x h1) (fun h0 : term118 _120933 b a x => @lem5777989 _120933 b a x h1 h0) (fun h0 : term17 _120933 a b x => @lem5777724 _120933 a b x h0 h1)). Qed.
Lemma lem5777991 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777910 _120933 b x h1 h2) (fun h0 : b x => @lem5777906 _120933 b x h1 h2)). Qed.
Lemma lem5777992 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777920 _120933 a x h1 h2) (fun h0 : b x => @lem5777914 _120933 a x h1 h2)). Qed.
Lemma lem5777993 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : a x) (h2 : b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776784 _120933 a b x h3) (fun h0 : term13 _120933 a x => @lem5777992 _120933 a b x h0 h1 h3) (fun h0 : term13 _120933 b x => @lem5777991 _120933 a b x h0 h2 h3)). Qed.
Lemma lem5777994 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : term13 _120933 b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777930 _120933 a x h1 h0) (fun h0 : b x => @lem5777924 _120933 b x h2 h0)). Qed.
Lemma lem5777995 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777944 _120933 a x h1 h2) (fun h0 : b x => @lem5777936 _120933 a x h1 h2)). Qed.
Lemma lem5777996 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : a x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776784 _120933 a b x h3) (fun h0 : term13 _120933 a x => @lem5777995 _120933 a b x h1 h2 h3) (fun h0 : term13 _120933 b x => @lem5777994 _120933 a b x h1 h0 h3)). Qed.
Lemma lem5777997 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : a x) (h2 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776787 _120933 a b x h2) (fun h0 : term13 _120933 a x => @lem5777996 _120933 a b x h0 h1 h2) (fun h0 : b x => @lem5777993 _120933 a b x h1 h0 h2)). Qed.
Lemma lem5777998 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777958 _120933 b x h1 h2) (fun h0 : b x => @lem5777952 _120933 b x h1 h2)). Qed.
Lemma lem5777999 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : term13 _120933 b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777968 _120933 a x h1 h0) (fun h0 : b x => @lem5777964 _120933 b x h2 h0)). Qed.
Lemma lem5778000 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776784 _120933 a b x h3) (fun h0 : term13 _120933 a x => @lem5777999 _120933 a b x h0 h1 h3) (fun h0 : term13 _120933 b x => @lem5777998 _120933 a b x h1 h2 h3)). Qed.
Lemma lem5778001 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : term13 _120933 b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777978 _120933 a x h1 h0) (fun h0 : b x => @lem5777974 _120933 b x h2 h0)). Qed.
Lemma lem5778002 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : term13 _120933 b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776783 _120933 a b x h3) (fun h0 : a x => @lem5777988 _120933 a x h1 h0) (fun h0 : b x => @lem5777982 _120933 b x h2 h0)). Qed.
Lemma lem5778003 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 a x) (h2 : term13 _120933 b x) (h3 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776784 _120933 a b x h3) (fun h0 : term13 _120933 a x => @lem5778002 _120933 a b x h1 h2 h3) (fun h0 : term13 _120933 b x => @lem5778001 _120933 a b x h1 h2 h3)). Qed.
Lemma lem5778004 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term13 _120933 b x) (h2 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776787 _120933 a b x h2) (fun h0 : term13 _120933 a x => @lem5778003 _120933 a b x h0 h1 h2) (fun h0 : b x => @lem5778000 _120933 a b x h1 h0 h2)). Qed.
Lemma lem5778005 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term275 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776786 _120933 a b x h1) (fun h0 : term13 _120933 b x => @lem5778004 _120933 a b x h0 h1) (fun h0 : a x => @lem5777997 _120933 a b x h0 h1)). Qed.
Lemma lem5778006 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term258 _120933 a b x) : False.
Proof. exact (or_elim (@lem5776779 _120933 a b x h1) (fun h0 : term275 _120933 a b x => @lem5778005 _120933 a b x h0) (fun h0 : term272 _120933 a b x => @lem5777990 _120933 a b x h0)). Qed.
Lemma lem5778007 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term258 _120933 a b x) : (term258 _120933 a b x) = False.
Proof. exact (prop_ext (fun h2 : term258 _120933 a b x => @lem5778006 _120933 a b x h1) (fun h2 : False => @lem5776585 _120933 a b x h1)). Qed.
Lemma lem5778008 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) (h1 : term258 _120933 a b x) : False.
Proof. exact (EQ_MP (@lem5778007 _120933 a b x h1) (@lem5776585 _120933 a b x h1)). Qed.
Lemma lem5778009 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : term257 _120933 a b x.
Proof. exact (fun h0 : term258 _120933 a b x => @lem5778008 _120933 a b x h0). Qed.
Lemma lem5778010 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (x : _120933) : (term232 _120933 a b x) = (term239 _120933 a b x).
Proof. exact (EQ_MP (@lem5776584 _120933 a b x) (@lem5778009 _120933 a b x)). Qed.
Lemma lem5778015 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term242 _120933 a b.
Proof. exact (fun x : _120933 => @lem5778010 _120933 a b x). Qed.
Lemma lem5778020 {_120933 : Type'} (b : _120933 -> Prop) : term252 _120933 b.
Proof. exact (fun a : _120933 -> Prop => @lem5778015 _120933 a b). Qed.
Lemma lem5778025 {_120933 : Type'} : term256 _120933.
Proof. exact (fun b : _120933 -> Prop => @lem5778020 _120933 b). Qed.
Lemma lem5778026 {_120933 : Type'} : term255 _120933.
Proof. exact (EQ_MP (@lem5776580 _120933) (@lem5778025 _120933)). Qed.
Lemma lem5778027 {_120933 : Type'} (b : _120933 -> Prop) : term280 _120933 b.
Proof. exact (@lem5778026 _120933 b). Qed.
Lemma lem5778028 {_120933 : Type'} (b : _120933 -> Prop) : (term280 _120933 b) = (term251 _120933 b).
Proof. exact (eq_refl (term280 _120933 b)). Qed.
Lemma lem5778029 {_120933 : Type'} (b : _120933 -> Prop) : term251 _120933 b.
Proof. exact (EQ_MP (@lem5778028 _120933 b) (@lem5778027 _120933 b)). Qed.
Lemma lem5778030 {_120933 : Type'} (b : _120933 -> Prop) (a : _120933 -> Prop) : term281 _120933 b a.
Proof. exact (@lem5778029 _120933 b a). Qed.
Lemma lem5778031 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (term281 _120933 b a) = (term243 _120933 a b).
Proof. exact (eq_refl (term281 _120933 b a)). Qed.
Lemma lem5778032 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term243 _120933 a b.
Proof. exact (EQ_MP (@lem5778031 _120933 a b) (@lem5778030 _120933 b a)). Qed.
Lemma lem5778034 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term243 _120933 a b.
Proof. exact (@lem5776455 _120933 a b (@lem5778032 _120933 a b)). Qed.
Lemma lem5778035 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term244 _120933 a b) : False.
Proof. exact (@lem5778034 _120933 a b (@lem5776439 _120933 a b h1)). Qed.
Lemma lem5778036 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term244 _120933 a b) : (term244 _120933 a b) = False.
Proof. exact (prop_ext (fun h2 : term244 _120933 a b => @lem5778035 _120933 a b h1) (fun h2 : False => @lem5776439 _120933 a b h1)). Qed.
Lemma lem5778037 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) (h1 : term244 _120933 a b) : False.
Proof. exact (EQ_MP (@lem5778036 _120933 a b h1) (@lem5776439 _120933 a b h1)). Qed.
Lemma lem5778038 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term243 _120933 a b.
Proof. exact (fun h0 : term244 _120933 a b => @lem5778037 _120933 a b h0). Qed.
Lemma lem5778039 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term242 _120933 a b.
Proof. exact (EQ_MP (@lem5776438 _120933 a b) (@lem5778038 _120933 a b)). Qed.
Lemma lem5778040 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : term229 _120933 a b.
Proof. exact (EQ_MP (@lem5776434 _120933 a b) (@lem5778039 _120933 a b)). Qed.
Lemma lem5778042 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : @monoidal _120978 op.
Proof. exact (h1). Qed.
Lemma lem5778043 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : term282 _120960 s t) : term282 _120960 s t.
Proof. exact (h1). Qed.
Lemma lem5778044 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : @FINITE _120960 t.
Proof. exact (h1). Qed.
Lemma lem5778045 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : @FINITE _120960 s.
Proof. exact (h1). Qed.
Lemma lem5778049 {_120933 : Type'} (a : _120933 -> Prop) (b : _120933 -> Prop) : (@UNION _120933 a b) = (term228 _120933 a b).
Proof. exact (EQ_MP (@lem5776307 _120933 a b) (@lem5778040 _120933 a b)). Qed.
Lemma lem5778050 {_120960 : Type'} (a : _120960 -> Prop) (b : _120960 -> Prop) : (@UNION _120960 a b) = (term228 _120960 a b).
Proof. exact (@lem5778049 _120960 a b). Qed.
Lemma lem5778051 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : (@UNION _120960 s t) = (term228 _120960 s t).
Proof. exact (@lem5778050 _120960 s t). Qed.
Lemma lem5778052 {_120960 _120978 : Type'} (op : type1400 _120978) : (@iterate _120978 _120960 op) = (@iterate _120978 _120960 op).
Proof. exact (eq_refl (@iterate _120978 _120960 op)). Qed.
Lemma lem5778053 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) : (term283 _120960 _120978 op s t) = (term284 _120960 _120978 op s t).
Proof. exact (MK_COMB (@lem5778052 _120960 _120978 op) (@lem5778051 _120960 s t)). Qed.
Lemma lem5778054 {_120960 _120978 : Type'} (f : _120960 -> _120978) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5778055 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term285 _120960 _120978 op s t f) = (term286 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778053 _120960 _120978 op s t) (@lem5778054 _120960 _120978 f)). Qed.
Lemma lem5778056 {_120978 : Type'} (op : type1400 _120978) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5778057 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term287 _120960 _120978 op s t f) = (term288 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778056 _120978 op) (@lem5778055 _120960 _120978 op s t f)). Qed.
Lemma lem5778058 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term289 _120960 _120978 op s t f) = (term289 _120960 _120978 op s t f).
Proof. exact (eq_refl (term289 _120960 _120978 op s t f)). Qed.
Lemma lem5778059 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term290 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778057 _120960 _120978 op s t f) (@lem5778058 _120960 _120978 op s t f)). Qed.
Lemma lem5778060 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term292 _120960 _120978 s op t f) = (term292 _120960 _120978 s op t f).
Proof. exact (eq_refl (term292 _120960 _120978 s op t f)). Qed.
Lemma lem5778061 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : ((term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f)) = ((term293 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)).
Proof. exact (MK_COMB (@lem5778060 _120960 _120978 s op t f) (@lem5778059 _120960 _120978 op s t f)). Qed.
Lemma lem5778062 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : ((term293 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)) = ((term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f)).
Proof. exact (SYM (@lem5778061 _120960 _120978 op s t f)). Qed.
Lemma lem5778074 {A : Type'} (s : A -> Prop) (t : A -> Prop) : s = (term192 A s t).
Proof. exact (EQ_MP (@lem5775620 A s t) (@lem5776281 A s t)). Qed.
Lemma lem5778075 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : s = (term192 _120960 s t).
Proof. exact (@lem5778074 _120960 s t). Qed.
Lemma lem5778076 {_120960 _120978 : Type'} (op : type1400 _120978) : (@iterate _120978 _120960 op) = (@iterate _120978 _120960 op).
Proof. exact (eq_refl (@iterate _120978 _120960 op)). Qed.
Lemma lem5778077 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) : (@iterate _120978 _120960 op s) = (term294 _120960 _120978 op s t).
Proof. exact (MK_COMB (@lem5778076 _120960 _120978 op) (@lem5778075 _120960 s t)). Qed.
Lemma lem5778080 {_120960 _120978 : Type'} (f : _120960 -> _120978) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5778081 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (@iterate _120978 _120960 op s f) = (term295 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778077 _120960 _120978 op s t) (@lem5778080 _120960 _120978 f)). Qed.
Lemma lem5778082 {_120978 : Type'} (op : type1400 _120978) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5778083 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term296 _120960 _120978 op s f) = (term297 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778082 _120978 op) (@lem5778081 _120960 _120978 op s t f)). Qed.
Lemma lem5778084 {_120960 _120978 : Type'} (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : (@iterate _120978 _120960 op t f) = (@iterate _120978 _120960 op t f).
Proof. exact (eq_refl (@iterate _120978 _120960 op t f)). Qed.
Lemma lem5778085 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term293 _120960 _120978 s op t f) = (term298 _120960 _120978 s op t f).
Proof. exact (MK_COMB (@lem5778083 _120960 _120978 op s t f) (@lem5778084 _120960 _120978 op t f)). Qed.
Lemma lem5778086 {_120978 : Type'} : (@eq _120978) = (@eq _120978).
Proof. exact (eq_refl (@eq _120978)). Qed.
Lemma lem5778087 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term292 _120960 _120978 s op t f) = (term299 _120960 _120978 s op t f).
Proof. exact (MK_COMB (@lem5778086 _120978) (@lem5778085 _120960 _120978 s op t f)). Qed.
Lemma lem5778088 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term291 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f).
Proof. exact (eq_refl (term291 _120960 _120978 op s t f)). Qed.
Lemma lem5778089 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : ((term293 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)) = ((term298 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)).
Proof. exact (MK_COMB (@lem5778087 _120960 _120978 s op t f) (@lem5778088 _120960 _120978 op s t f)). Qed.
Lemma lem5778090 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : ((term298 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)) = ((term293 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)).
Proof. exact (SYM (@lem5778089 _120960 _120978 op s t f)). Qed.
Lemma lem5778102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : t = (term145 A s t).
Proof. exact (EQ_MP (@lem5774932 A s t) (@lem5775594 A s t)). Qed.
Lemma lem5778103 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : t = (term145 _120960 s t).
Proof. exact (@lem5778102 _120960 s t). Qed.
Lemma lem5778104 {_120960 _120978 : Type'} (op : type1400 _120978) : (@iterate _120978 _120960 op) = (@iterate _120978 _120960 op).
Proof. exact (eq_refl (@iterate _120978 _120960 op)). Qed.
Lemma lem5778105 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) : (@iterate _120978 _120960 op t) = (term300 _120960 _120978 op s t).
Proof. exact (MK_COMB (@lem5778104 _120960 _120978 op) (@lem5778103 _120960 s t)). Qed.
Lemma lem5778108 {_120960 _120978 : Type'} (f : _120960 -> _120978) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5778109 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (@iterate _120978 _120960 op t f) = (term301 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778105 _120960 _120978 op s t) (@lem5778108 _120960 _120978 f)). Qed.
Lemma lem5778110 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term297 _120960 _120978 op s t f) = (term297 _120960 _120978 op s t f).
Proof. exact (eq_refl (term297 _120960 _120978 op s t f)). Qed.
Lemma lem5778111 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term298 _120960 _120978 s op t f) = (term302 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778110 _120960 _120978 op s t f) (@lem5778109 _120960 _120978 op s t f)). Qed.
Lemma lem5778112 {_120978 : Type'} : (@eq _120978) = (@eq _120978).
Proof. exact (eq_refl (@eq _120978)). Qed.
Lemma lem5778113 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term299 _120960 _120978 s op t f) = (term303 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778112 _120978) (@lem5778111 _120960 _120978 op s t f)). Qed.
Lemma lem5778114 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term291 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f).
Proof. exact (eq_refl (term291 _120960 _120978 op s t f)). Qed.
Lemma lem5778115 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : ((term298 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)) = ((term302 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f)).
Proof. exact (MK_COMB (@lem5778113 _120960 _120978 op s t f) (@lem5778114 _120960 _120978 op s t f)). Qed.
Lemma lem5778116 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : ((term302 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f)) = ((term298 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f)).
Proof. exact (SYM (@lem5778115 _120960 _120978 op s t f)). Qed.
Lemma lem5778117 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term0 _120849 s s') = ((term0 _120849 s s') = True).
Proof. exact (@lem7 (term0 _120849 s s')). Qed.
Lemma lem5778119 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term48 _120859 s' s) = ((term48 _120859 s' s) = True).
Proof. exact (@lem7 (term48 _120859 s' s)). Qed.
Lemma lem5778121 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term77 _120869 s' s) = ((term77 _120869 s' s) = True).
Proof. exact (@lem7 (term77 _120869 s' s)). Qed.
Lemma lem5778123 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term106 _120885 s s') = ((term106 _120885 s s') = True).
Proof. exact (@lem7 (term106 _120885 s s')). Qed.
Lemma lem5778125 {A : Type'} (s : A -> Prop) : term304 A s.
Proof. exact (@lem3607909 A s). Qed.
Lemma lem5778126 {A : Type'} (s : A -> Prop) : (term304 A s) = (term305 A s).
Proof. exact (eq_refl (term304 A s)). Qed.
Lemma lem5778127 {A : Type'} (s : A -> Prop) : term305 A s.
Proof. exact (EQ_MP (@lem5778126 A s) (@lem5778125 A s)). Qed.
Lemma lem5778128 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term306 A s t.
Proof. exact (@lem5778127 A s t). Qed.
Lemma lem5778129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term306 A s t) = (term307 A s t).
Proof. exact (eq_refl (term306 A s t)). Qed.
Lemma lem5778130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term307 A s t.
Proof. exact (EQ_MP (@lem5778129 A s t) (@lem5778128 A s t)). Qed.
Lemma lem5778131 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term308 A s t) : term308 A s t.
Proof. exact (h1). Qed.
Lemma lem5778132 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term308 A s t) : term309 A s t.
Proof. exact (@lem5778130 A s t (@lem5778131 A s t h1)). Qed.
Lemma lem5778133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term309 A s t) = ((term309 A s t) = True).
Proof. exact (@lem7 (term309 A s t)). Qed.
Lemma lem5778134 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term308 A s t) : (term309 A s t) = True.
Proof. exact (EQ_MP (@lem5778133 A s t) (@lem5778132 A s t h1)). Qed.
Lemma lem5778140 {_97970 : Type'} (s : _97970 -> Prop) : term310 _97970 s.
Proof. exact (@lem3734933 _97970 s). Qed.
Lemma lem5778141 {_97970 : Type'} (s : _97970 -> Prop) : (term310 _97970 s) = (term311 _97970 s).
Proof. exact (eq_refl (term310 _97970 s)). Qed.
Lemma lem5778142 {_97970 : Type'} (s : _97970 -> Prop) : term311 _97970 s.
Proof. exact (EQ_MP (@lem5778141 _97970 s) (@lem5778140 _97970 s)). Qed.
Lemma lem5778143 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term312 _97970 s t.
Proof. exact (@lem5778142 _97970 s t). Qed.
Lemma lem5778144 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term312 _97970 s t) = (term313 _97970 s t).
Proof. exact (eq_refl (term312 _97970 s t)). Qed.
Lemma lem5778145 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term313 _97970 s t.
Proof. exact (EQ_MP (@lem5778144 _97970 s t) (@lem5778143 _97970 s t)). Qed.
Lemma lem5778146 {_97970 : Type'} (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : @FINITE _97970 s.
Proof. exact (h1). Qed.
Lemma lem5778147 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : term314 _97970 s t.
Proof. exact (@lem5778145 _97970 s t (@lem5778146 _97970 s h1)). Qed.
Lemma lem5778148 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term314 _97970 s t) = ((term314 _97970 s t) = True).
Proof. exact (@lem7 (term314 _97970 s t)). Qed.
Lemma lem5778149 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : (term314 _97970 s t) = True.
Proof. exact (EQ_MP (@lem5778148 _97970 s t) (@lem5778147 _97970 t s h1)). Qed.
Lemma lem5778155 {A : Type'} (s : A -> Prop) : term315 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem5778156 {A : Type'} (s : A -> Prop) : (term315 A s) = (term316 A s).
Proof. exact (eq_refl (term315 A s)). Qed.
Lemma lem5778157 {A : Type'} (s : A -> Prop) : term316 A s.
Proof. exact (EQ_MP (@lem5778156 A s) (@lem5778155 A s)). Qed.
Lemma lem5778158 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term317 A s t.
Proof. exact (@lem5778157 A s t). Qed.
Lemma lem5778159 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term317 A s t) = ((term318 A s t) = (term282 A s t)).
Proof. exact (eq_refl (term317 A s t)). Qed.
Lemma lem5778161 {_120592 _120607 : Type'} (op : type1400 _120607) : term319 _120592 _120607 op.
Proof. exact (@lem5764203 _120592 _120607 op). Qed.
Lemma lem5778162 {_120592 _120607 : Type'} (op : type1400 _120607) : (term319 _120592 _120607 op) = (term320 _120592 _120607 op).
Proof. exact (eq_refl (term319 _120592 _120607 op)). Qed.
Lemma lem5778163 {_120592 _120607 : Type'} (op : type1400 _120607) : term320 _120592 _120607 op.
Proof. exact (EQ_MP (@lem5778162 _120592 _120607 op) (@lem5778161 _120592 _120607 op)). Qed.
Lemma lem5778164 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @monoidal _120607 op.
Proof. exact (h1). Qed.
Lemma lem5778165 {_120592 _120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term321 _120592 _120607 op.
Proof. exact (@lem5778163 _120592 _120607 op (@lem5778164 _120607 op h1)). Qed.
Lemma lem5778166 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term322 _120592 _120607 op f.
Proof. exact (@lem5778165 _120592 _120607 op h1 f). Qed.
Lemma lem5778167 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term322 _120592 _120607 op f) = (term323 _120592 _120607 op f).
Proof. exact (eq_refl (term322 _120592 _120607 op f)). Qed.
Lemma lem5778168 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term323 _120592 _120607 op f.
Proof. exact (EQ_MP (@lem5778167 _120592 _120607 op f) (@lem5778166 _120592 _120607 f op h1)). Qed.
Lemma lem5778169 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term324 _120592 _120607 op f s.
Proof. exact (@lem5778168 _120592 _120607 f op h1 s). Qed.
Lemma lem5778170 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term324 _120592 _120607 op f s) = (term325 _120592 _120607 s op f).
Proof. exact (eq_refl (term324 _120592 _120607 op f s)). Qed.
Lemma lem5778171 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term325 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5778170 _120592 _120607 s op f) (@lem5778169 _120592 _120607 f s op h1)). Qed.
Lemma lem5778172 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (t : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term326 _120592 _120607 s op f t.
Proof. exact (@lem5778171 _120592 _120607 s f op h1 t). Qed.
Lemma lem5778173 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term326 _120592 _120607 s op f t) = (term327 _120592 _120607 s op t f).
Proof. exact (eq_refl (term326 _120592 _120607 s op f t)). Qed.
Lemma lem5778174 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term327 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem5778173 _120592 _120607 s op t f) (@lem5778172 _120592 _120607 s f t op h1)). Qed.
Lemma lem5778175 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term328 _120592 s t) : term328 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem5778176 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term328 _120592 s t) : (term285 _120592 _120607 op s t f) = (term293 _120592 _120607 s op t f).
Proof. exact (@lem5778174 _120592 _120607 s t f op h1 (@lem5778175 _120592 s t h2)). Qed.
Lemma lem5778177 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term327 _120592 _120607 s op t f.
Proof. exact (fun h0 : term328 _120592 s t => @lem5778176 _120592 _120607 f op s t h1 h0). Qed.
Lemma lem5778178 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term329 _120592 _120607 s op t f.
Proof. exact (fun h0 : @monoidal _120607 op => @lem5778177 _120592 _120607 s t f op h0). Qed.
Lemma lem5778180 (p : Prop) (q : Prop) (r : Prop) : (term330 p q r) = (term331 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5778185 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term329 _120592 _120607 s op t f) = (term332 _120592 _120607 s op t f).
Proof. exact (@lem5778180 (@monoidal _120607 op) (term328 _120592 s t) ((term285 _120592 _120607 op s t f) = (term293 _120592 _120607 s op t f))). Qed.
Lemma lem5778187 {_120978 : Type'} (op : type1400 _120978) : (@monoidal _120978 op) = ((@monoidal _120978 op) = True).
Proof. exact (@lem7 (@monoidal _120978 op)). Qed.
Lemma lem5778189 {_120960 : Type'} (s : _120960 -> Prop) : (@FINITE _120960 s) = ((@FINITE _120960 s) = True).
Proof. exact (@lem7 (@FINITE _120960 s)). Qed.
Lemma lem5778191 {_120960 : Type'} (t : _120960 -> Prop) : (@FINITE _120960 t) = ((@FINITE _120960 t) = True).
Proof. exact (@lem7 (@FINITE _120960 t)). Qed.
Lemma lem5778196 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term332 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem5778185 _120592 _120607 s op t f) (@lem5778178 _120592 _120607 s op t f)). Qed.
Lemma lem5778197 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : term332 _120960 _120978 s op t f.
Proof. exact (@lem5778196 _120960 _120978 s op t f). Qed.
Lemma lem5778198 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : term333 _120960 _120978 op s t f.
Proof. exact (@lem5778197 _120960 _120978 (@DIFF _120960 s t) op (@INTER _120960 s t) f). Qed.
Lemma lem5778202 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (@monoidal _120978 op) = True.
Proof. exact (EQ_MP (@lem5778187 _120978 op) (@lem5778042 _120978 op h1)). Qed.
Lemma lem5778203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778204 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term334 _120978 op) = (and True).
Proof. exact (MK_COMB (@lem5778203) (@lem5778202 _120978 op h1)). Qed.
Lemma lem5778208 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term335 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem5778149 _97970 t s h0). Qed.
Lemma lem5778209 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term335 _120960 s t.
Proof. exact (@lem5778208 _120960 s t). Qed.
Lemma lem5778211 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (@FINITE _120960 s) = True.
Proof. exact (EQ_MP (@lem5778189 _120960 s) (@lem5778045 _120960 s h1)). Qed.
Lemma lem5778212 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : True = (@FINITE _120960 s).
Proof. exact (SYM (@lem5778211 _120960 s h1)). Qed.
Lemma lem5778213 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : @FINITE _120960 s.
Proof. exact (EQ_MP (@lem5778212 _120960 s h1) (@lem0)). Qed.
Lemma lem5778214 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term314 _120960 s t) = True.
Proof. exact (@lem5778209 _120960 s t (@lem5778213 _120960 s h1)). Qed.
Lemma lem5778215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778216 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term336 _120960 s t) = (and True).
Proof. exact (MK_COMB (@lem5778215) (@lem5778214 _120960 t s h1)). Qed.
Lemma lem5778220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term337 A s t.
Proof. exact (fun h0 : term308 A s t => @lem5778134 A s t h0). Qed.
Lemma lem5778221 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term337 _120960 s t.
Proof. exact (@lem5778220 _120960 s t). Qed.
Lemma lem5778225 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (@FINITE _120960 s) = True.
Proof. exact (EQ_MP (@lem5778189 _120960 s) (@lem5778045 _120960 s h1)). Qed.
Lemma lem5778226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5778227 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term338 _120960 s) = (or True).
Proof. exact (MK_COMB (@lem5778226) (@lem5778225 _120960 s h1)). Qed.
Lemma lem5778229 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (@FINITE _120960 t) = True.
Proof. exact (EQ_MP (@lem5778191 _120960 t) (@lem5778044 _120960 t h1)). Qed.
Lemma lem5778230 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term308 _120960 s t) = (True \/ True).
Proof. exact (MK_COMB (@lem5778227 _120960 s h1) (@lem5778229 _120960 t h2)). Qed.
Lemma lem5778232 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5778233 : (True \/ True) = True.
Proof. exact (@lem5778232 True). Qed.
Lemma lem5778234 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term308 _120960 s t) = True.
Proof. exact (TRANS (@lem5778230 _120960 s t h1 h2) (@lem5778233)). Qed.
Lemma lem5778235 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : True = (term308 _120960 s t).
Proof. exact (SYM (@lem5778234 _120960 s t h1 h2)). Qed.
Lemma lem5778236 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : term308 _120960 s t.
Proof. exact (EQ_MP (@lem5778235 _120960 s t h1 h2) (@lem0)). Qed.
Lemma lem5778237 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term309 _120960 s t) = True.
Proof. exact (@lem5778221 _120960 s t (@lem5778236 _120960 s t h1 h2)). Qed.
Lemma lem5778238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778239 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term339 _120960 s t) = (and True).
Proof. exact (MK_COMB (@lem5778238) (@lem5778237 _120960 s t h1 h2)). Qed.
Lemma lem5778241 {_120849 : Type'} (s : _120849 -> Prop) (s' : _120849 -> Prop) : (term0 _120849 s s') = True.
Proof. exact (EQ_MP (@lem5778117 _120849 s s') (@lem5773673 _120849 s s')). Qed.
Lemma lem5778242 {_120960 : Type'} (s : _120960 -> Prop) (s' : _120960 -> Prop) : (term0 _120960 s s') = True.
Proof. exact (@lem5778241 _120960 s s'). Qed.
Lemma lem5778243 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : (term0 _120960 s t) = True.
Proof. exact (@lem5778242 _120960 s t). Qed.
Lemma lem5778244 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term340 _120960 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778239 _120960 s t h1 h2) (@lem5778243 _120960 s t)). Qed.
Lemma lem5778246 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778247 : (True /\ True) = True.
Proof. exact (@lem5778246 True). Qed.
Lemma lem5778248 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term340 _120960 s t) = True.
Proof. exact (TRANS (@lem5778244 _120960 s t h1 h2) (@lem5778247)). Qed.
Lemma lem5778249 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term341 _120960 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778216 _120960 t s h1) (@lem5778248 _120960 s t h1 h2)). Qed.
Lemma lem5778251 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778252 : (True /\ True) = True.
Proof. exact (@lem5778251 True). Qed.
Lemma lem5778253 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term341 _120960 s t) = True.
Proof. exact (TRANS (@lem5778249 _120960 s t h1 h2) (@lem5778252)). Qed.
Lemma lem5778254 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term342 _120960 _120978 op s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778204 _120978 op h3) (@lem5778253 _120960 s t h1 h2)). Qed.
Lemma lem5778256 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778257 : (True /\ True) = True.
Proof. exact (@lem5778256 True). Qed.
Lemma lem5778258 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term342 _120960 _120978 op s t) = True.
Proof. exact (TRANS (@lem5778254 _120960 _120978 s t op h1 h2 h3) (@lem5778257)). Qed.
Lemma lem5778259 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : True = (term342 _120960 _120978 op s t).
Proof. exact (SYM (@lem5778258 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778260 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : term342 _120960 _120978 op s t.
Proof. exact (EQ_MP (@lem5778259 _120960 _120978 s t op h1 h2 h3) (@lem0)). Qed.
Lemma lem5778261 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term295 _120960 _120978 op s t f) = (term343 _120960 _120978 op s t f).
Proof. exact (@lem5778198 _120960 _120978 op s t f (@lem5778260 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778262 {_120978 : Type'} (op : type1400 _120978) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5778263 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term297 _120960 _120978 op s t f) = (term344 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778262 _120978 op) (@lem5778261 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778265 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term332 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem5778185 _120592 _120607 s op t f) (@lem5778178 _120592 _120607 s op t f)). Qed.
Lemma lem5778266 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : term332 _120960 _120978 s op t f.
Proof. exact (@lem5778265 _120960 _120978 s op t f). Qed.
Lemma lem5778267 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : term345 _120960 _120978 op s t f.
Proof. exact (@lem5778266 _120960 _120978 (@DIFF _120960 t s) op (@INTER _120960 s t) f). Qed.
Lemma lem5778271 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (@monoidal _120978 op) = True.
Proof. exact (EQ_MP (@lem5778187 _120978 op) (@lem5778042 _120978 op h1)). Qed.
Lemma lem5778272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778273 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term334 _120978 op) = (and True).
Proof. exact (MK_COMB (@lem5778272) (@lem5778271 _120978 op h1)). Qed.
Lemma lem5778277 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term335 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem5778149 _97970 t s h0). Qed.
Lemma lem5778278 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term335 _120960 s t.
Proof. exact (@lem5778277 _120960 s t). Qed.
Lemma lem5778279 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) : term335 _120960 t s.
Proof. exact (@lem5778278 _120960 t s). Qed.
Lemma lem5778281 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (@FINITE _120960 t) = True.
Proof. exact (EQ_MP (@lem5778191 _120960 t) (@lem5778044 _120960 t h1)). Qed.
Lemma lem5778282 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : True = (@FINITE _120960 t).
Proof. exact (SYM (@lem5778281 _120960 t h1)). Qed.
Lemma lem5778283 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : @FINITE _120960 t.
Proof. exact (EQ_MP (@lem5778282 _120960 t h1) (@lem0)). Qed.
Lemma lem5778284 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (term314 _120960 t s) = True.
Proof. exact (@lem5778279 _120960 t s (@lem5778283 _120960 t h1)). Qed.
Lemma lem5778285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778286 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (term336 _120960 t s) = (and True).
Proof. exact (MK_COMB (@lem5778285) (@lem5778284 _120960 s t h1)). Qed.
Lemma lem5778290 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term337 A s t.
Proof. exact (fun h0 : term308 A s t => @lem5778134 A s t h0). Qed.
Lemma lem5778291 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term337 _120960 s t.
Proof. exact (@lem5778290 _120960 s t). Qed.
Lemma lem5778295 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (@FINITE _120960 s) = True.
Proof. exact (EQ_MP (@lem5778189 _120960 s) (@lem5778045 _120960 s h1)). Qed.
Lemma lem5778296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5778297 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term338 _120960 s) = (or True).
Proof. exact (MK_COMB (@lem5778296) (@lem5778295 _120960 s h1)). Qed.
Lemma lem5778299 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (@FINITE _120960 t) = True.
Proof. exact (EQ_MP (@lem5778191 _120960 t) (@lem5778044 _120960 t h1)). Qed.
Lemma lem5778300 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term308 _120960 s t) = (True \/ True).
Proof. exact (MK_COMB (@lem5778297 _120960 s h1) (@lem5778299 _120960 t h2)). Qed.
Lemma lem5778302 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5778303 : (True \/ True) = True.
Proof. exact (@lem5778302 True). Qed.
Lemma lem5778304 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term308 _120960 s t) = True.
Proof. exact (TRANS (@lem5778300 _120960 s t h1 h2) (@lem5778303)). Qed.
Lemma lem5778305 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : True = (term308 _120960 s t).
Proof. exact (SYM (@lem5778304 _120960 s t h1 h2)). Qed.
Lemma lem5778306 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : term308 _120960 s t.
Proof. exact (EQ_MP (@lem5778305 _120960 s t h1 h2) (@lem0)). Qed.
Lemma lem5778307 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term309 _120960 s t) = True.
Proof. exact (@lem5778291 _120960 s t (@lem5778306 _120960 s t h1 h2)). Qed.
Lemma lem5778308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778309 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term339 _120960 s t) = (and True).
Proof. exact (MK_COMB (@lem5778308) (@lem5778307 _120960 s t h1 h2)). Qed.
Lemma lem5778313 {_120859 : Type'} (s' : _120859 -> Prop) (s : _120859 -> Prop) : (term48 _120859 s' s) = True.
Proof. exact (EQ_MP (@lem5778119 _120859 s' s) (@lem5774039 _120859 s' s)). Qed.
Lemma lem5778314 {_120960 : Type'} (s' : _120960 -> Prop) (s : _120960 -> Prop) : (term48 _120960 s' s) = True.
Proof. exact (@lem5778313 _120960 s' s). Qed.
Lemma lem5778315 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : (term48 _120960 s t) = True.
Proof. exact (@lem5778314 _120960 s t). Qed.
Lemma lem5778316 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term346 _120960 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778309 _120960 s t h1 h2) (@lem5778315 _120960 s t)). Qed.
Lemma lem5778318 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778319 : (True /\ True) = True.
Proof. exact (@lem5778318 True). Qed.
Lemma lem5778320 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term346 _120960 s t) = True.
Proof. exact (TRANS (@lem5778316 _120960 s t h1 h2) (@lem5778319)). Qed.
Lemma lem5778321 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term347 _120960 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778286 _120960 s t h2) (@lem5778320 _120960 s t h1 h2)). Qed.
Lemma lem5778323 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778324 : (True /\ True) = True.
Proof. exact (@lem5778323 True). Qed.
Lemma lem5778325 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term347 _120960 s t) = True.
Proof. exact (TRANS (@lem5778321 _120960 s t h1 h2) (@lem5778324)). Qed.
Lemma lem5778326 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term348 _120960 _120978 op s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778273 _120978 op h3) (@lem5778325 _120960 s t h1 h2)). Qed.
Lemma lem5778328 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778329 : (True /\ True) = True.
Proof. exact (@lem5778328 True). Qed.
Lemma lem5778330 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term348 _120960 _120978 op s t) = True.
Proof. exact (TRANS (@lem5778326 _120960 _120978 s t op h1 h2 h3) (@lem5778329)). Qed.
Lemma lem5778331 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : True = (term348 _120960 _120978 op s t).
Proof. exact (SYM (@lem5778330 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778332 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : term348 _120960 _120978 op s t.
Proof. exact (EQ_MP (@lem5778331 _120960 _120978 s t op h1 h2 h3) (@lem0)). Qed.
Lemma lem5778333 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term301 _120960 _120978 op s t f) = (term349 _120960 _120978 op s t f).
Proof. exact (@lem5778267 _120960 _120978 op s t f (@lem5778332 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778334 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term302 _120960 _120978 op s t f) = (term350 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778263 _120960 _120978 f s t op h1 h2 h3) (@lem5778333 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778335 {_120978 : Type'} : (@eq _120978) = (@eq _120978).
Proof. exact (eq_refl (@eq _120978)). Qed.
Lemma lem5778336 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term303 _120960 _120978 op s t f) = (term351 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778335 _120978) (@lem5778334 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778338 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term332 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem5778185 _120592 _120607 s op t f) (@lem5778178 _120592 _120607 s op t f)). Qed.
Lemma lem5778339 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : term332 _120960 _120978 s op t f.
Proof. exact (@lem5778338 _120960 _120978 s op t f). Qed.
Lemma lem5778340 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : term352 _120960 _120978 op s t f.
Proof. exact (@lem5778339 _120960 _120978 (term108 _120960 t s) op (@INTER _120960 s t) f). Qed.
Lemma lem5778344 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (@monoidal _120978 op) = True.
Proof. exact (EQ_MP (@lem5778187 _120978 op) (@lem5778042 _120978 op h1)). Qed.
Lemma lem5778345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778346 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term334 _120978 op) = (and True).
Proof. exact (MK_COMB (@lem5778345) (@lem5778344 _120978 op h1)). Qed.
Lemma lem5778350 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (term282 A s t).
Proof. exact (EQ_MP (@lem5778159 A s t) (@lem5778158 A s t)). Qed.
Lemma lem5778351 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : (term318 _120960 s t) = (term282 _120960 s t).
Proof. exact (@lem5778350 _120960 s t). Qed.
Lemma lem5778352 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) : (term353 _120960 t s) = (term354 _120960 t s).
Proof. exact (@lem5778351 _120960 (@DIFF _120960 s t) (@DIFF _120960 t s)). Qed.
Lemma lem5778356 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term335 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem5778149 _97970 t s h0). Qed.
Lemma lem5778357 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term335 _120960 s t.
Proof. exact (@lem5778356 _120960 s t). Qed.
Lemma lem5778359 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (@FINITE _120960 s) = True.
Proof. exact (EQ_MP (@lem5778189 _120960 s) (@lem5778045 _120960 s h1)). Qed.
Lemma lem5778360 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : True = (@FINITE _120960 s).
Proof. exact (SYM (@lem5778359 _120960 s h1)). Qed.
Lemma lem5778361 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : @FINITE _120960 s.
Proof. exact (EQ_MP (@lem5778360 _120960 s h1) (@lem0)). Qed.
Lemma lem5778362 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term314 _120960 s t) = True.
Proof. exact (@lem5778357 _120960 s t (@lem5778361 _120960 s h1)). Qed.
Lemma lem5778363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778364 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term336 _120960 s t) = (and True).
Proof. exact (MK_COMB (@lem5778363) (@lem5778362 _120960 t s h1)). Qed.
Lemma lem5778366 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term335 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem5778149 _97970 t s h0). Qed.
Lemma lem5778367 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term335 _120960 s t.
Proof. exact (@lem5778366 _120960 s t). Qed.
Lemma lem5778368 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) : term335 _120960 t s.
Proof. exact (@lem5778367 _120960 t s). Qed.
Lemma lem5778370 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (@FINITE _120960 t) = True.
Proof. exact (EQ_MP (@lem5778191 _120960 t) (@lem5778044 _120960 t h1)). Qed.
Lemma lem5778371 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : True = (@FINITE _120960 t).
Proof. exact (SYM (@lem5778370 _120960 t h1)). Qed.
Lemma lem5778372 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : @FINITE _120960 t.
Proof. exact (EQ_MP (@lem5778371 _120960 t h1) (@lem0)). Qed.
Lemma lem5778373 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (term314 _120960 t s) = True.
Proof. exact (@lem5778368 _120960 t s (@lem5778372 _120960 t h1)). Qed.
Lemma lem5778374 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term354 _120960 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem5778364 _120960 t s h1) (@lem5778373 _120960 s t h2)). Qed.
Lemma lem5778376 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778377 : (True /\ True) = True.
Proof. exact (@lem5778376 True). Qed.
Lemma lem5778378 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term354 _120960 t s) = True.
Proof. exact (TRANS (@lem5778374 _120960 s t h1 h2) (@lem5778377)). Qed.
Lemma lem5778379 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term353 _120960 t s) = True.
Proof. exact (TRANS (@lem5778352 _120960 t s) (@lem5778378 _120960 s t h1 h2)). Qed.
Lemma lem5778380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778381 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term355 _120960 t s) = (and True).
Proof. exact (MK_COMB (@lem5778380) (@lem5778379 _120960 s t h1 h2)). Qed.
Lemma lem5778385 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term337 A s t.
Proof. exact (fun h0 : term308 A s t => @lem5778134 A s t h0). Qed.
Lemma lem5778386 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term337 _120960 s t.
Proof. exact (@lem5778385 _120960 s t). Qed.
Lemma lem5778390 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (@FINITE _120960 s) = True.
Proof. exact (EQ_MP (@lem5778189 _120960 s) (@lem5778045 _120960 s h1)). Qed.
Lemma lem5778391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5778392 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term338 _120960 s) = (or True).
Proof. exact (MK_COMB (@lem5778391) (@lem5778390 _120960 s h1)). Qed.
Lemma lem5778394 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (@FINITE _120960 t) = True.
Proof. exact (EQ_MP (@lem5778191 _120960 t) (@lem5778044 _120960 t h1)). Qed.
Lemma lem5778395 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term308 _120960 s t) = (True \/ True).
Proof. exact (MK_COMB (@lem5778392 _120960 s h1) (@lem5778394 _120960 t h2)). Qed.
Lemma lem5778397 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5778398 : (True \/ True) = True.
Proof. exact (@lem5778397 True). Qed.
Lemma lem5778399 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term308 _120960 s t) = True.
Proof. exact (TRANS (@lem5778395 _120960 s t h1 h2) (@lem5778398)). Qed.
Lemma lem5778400 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : True = (term308 _120960 s t).
Proof. exact (SYM (@lem5778399 _120960 s t h1 h2)). Qed.
Lemma lem5778401 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : term308 _120960 s t.
Proof. exact (EQ_MP (@lem5778400 _120960 s t h1 h2) (@lem0)). Qed.
Lemma lem5778402 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term309 _120960 s t) = True.
Proof. exact (@lem5778386 _120960 s t (@lem5778401 _120960 s t h1 h2)). Qed.
Lemma lem5778403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778404 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term339 _120960 s t) = (and True).
Proof. exact (MK_COMB (@lem5778403) (@lem5778402 _120960 s t h1 h2)). Qed.
Lemma lem5778406 {_120885 : Type'} (s : _120885 -> Prop) (s' : _120885 -> Prop) : (term106 _120885 s s') = True.
Proof. exact (EQ_MP (@lem5778123 _120885 s s') (@lem5774907 _120885 s s')). Qed.
Lemma lem5778407 {_120960 : Type'} (s : _120960 -> Prop) (s' : _120960 -> Prop) : (term106 _120960 s s') = True.
Proof. exact (@lem5778406 _120960 s s'). Qed.
Lemma lem5778408 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : (term106 _120960 s t) = True.
Proof. exact (@lem5778407 _120960 s t). Qed.
Lemma lem5778409 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term356 _120960 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778404 _120960 s t h1 h2) (@lem5778408 _120960 s t)). Qed.
Lemma lem5778411 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778412 : (True /\ True) = True.
Proof. exact (@lem5778411 True). Qed.
Lemma lem5778413 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term356 _120960 s t) = True.
Proof. exact (TRANS (@lem5778409 _120960 s t h1 h2) (@lem5778412)). Qed.
Lemma lem5778414 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term357 _120960 s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778381 _120960 s t h1 h2) (@lem5778413 _120960 s t h1 h2)). Qed.
Lemma lem5778416 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778417 : (True /\ True) = True.
Proof. exact (@lem5778416 True). Qed.
Lemma lem5778418 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term357 _120960 s t) = True.
Proof. exact (TRANS (@lem5778414 _120960 s t h1 h2) (@lem5778417)). Qed.
Lemma lem5778419 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term358 _120960 _120978 op s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5778346 _120978 op h3) (@lem5778418 _120960 s t h1 h2)). Qed.
Lemma lem5778421 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778422 : (True /\ True) = True.
Proof. exact (@lem5778421 True). Qed.
Lemma lem5778423 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term358 _120960 _120978 op s t) = True.
Proof. exact (TRANS (@lem5778419 _120960 _120978 s t op h1 h2 h3) (@lem5778422)). Qed.
Lemma lem5778424 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : True = (term358 _120960 _120978 op s t).
Proof. exact (SYM (@lem5778423 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778425 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : term358 _120960 _120978 op s t.
Proof. exact (EQ_MP (@lem5778424 _120960 _120978 s t op h1 h2 h3) (@lem0)). Qed.
Lemma lem5778426 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term286 _120960 _120978 op s t f) = (term359 _120960 _120978 op s t f).
Proof. exact (@lem5778340 _120960 _120978 op s t f (@lem5778425 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778428 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term332 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem5778185 _120592 _120607 s op t f) (@lem5778178 _120592 _120607 s op t f)). Qed.
Lemma lem5778429 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (t : _120960 -> Prop) (f : _120960 -> _120978) : term332 _120960 _120978 s op t f.
Proof. exact (@lem5778428 _120960 _120978 s op t f). Qed.
Lemma lem5778430 {_120960 _120978 : Type'} (op : type1400 _120978) (t : _120960 -> Prop) (s : _120960 -> Prop) (f : _120960 -> _120978) : term360 _120960 _120978 op t s f.
Proof. exact (@lem5778429 _120960 _120978 (@DIFF _120960 s t) op (@DIFF _120960 t s) f). Qed.
Lemma lem5778434 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (@monoidal _120978 op) = True.
Proof. exact (EQ_MP (@lem5778187 _120978 op) (@lem5778042 _120978 op h1)). Qed.
Lemma lem5778435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778436 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term334 _120978 op) = (and True).
Proof. exact (MK_COMB (@lem5778435) (@lem5778434 _120978 op h1)). Qed.
Lemma lem5778440 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term335 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem5778149 _97970 t s h0). Qed.
Lemma lem5778441 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term335 _120960 s t.
Proof. exact (@lem5778440 _120960 s t). Qed.
Lemma lem5778443 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (@FINITE _120960 s) = True.
Proof. exact (EQ_MP (@lem5778189 _120960 s) (@lem5778045 _120960 s h1)). Qed.
Lemma lem5778444 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : True = (@FINITE _120960 s).
Proof. exact (SYM (@lem5778443 _120960 s h1)). Qed.
Lemma lem5778445 {_120960 : Type'} (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : @FINITE _120960 s.
Proof. exact (EQ_MP (@lem5778444 _120960 s h1) (@lem0)). Qed.
Lemma lem5778446 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term314 _120960 s t) = True.
Proof. exact (@lem5778441 _120960 s t (@lem5778445 _120960 s h1)). Qed.
Lemma lem5778447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778448 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) (h1 : @FINITE _120960 s) : (term336 _120960 s t) = (and True).
Proof. exact (MK_COMB (@lem5778447) (@lem5778446 _120960 t s h1)). Qed.
Lemma lem5778452 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term335 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem5778149 _97970 t s h0). Qed.
Lemma lem5778453 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) : term335 _120960 s t.
Proof. exact (@lem5778452 _120960 s t). Qed.
Lemma lem5778454 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) : term335 _120960 t s.
Proof. exact (@lem5778453 _120960 t s). Qed.
Lemma lem5778456 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (@FINITE _120960 t) = True.
Proof. exact (EQ_MP (@lem5778191 _120960 t) (@lem5778044 _120960 t h1)). Qed.
Lemma lem5778457 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : True = (@FINITE _120960 t).
Proof. exact (SYM (@lem5778456 _120960 t h1)). Qed.
Lemma lem5778458 {_120960 : Type'} (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : @FINITE _120960 t.
Proof. exact (EQ_MP (@lem5778457 _120960 t h1) (@lem0)). Qed.
Lemma lem5778459 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (term314 _120960 t s) = True.
Proof. exact (@lem5778454 _120960 t s (@lem5778458 _120960 t h1)). Qed.
Lemma lem5778460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778461 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (term336 _120960 t s) = (and True).
Proof. exact (MK_COMB (@lem5778460) (@lem5778459 _120960 s t h1)). Qed.
Lemma lem5778463 {_120869 : Type'} (s' : _120869 -> Prop) (s : _120869 -> Prop) : (term77 _120869 s' s) = True.
Proof. exact (EQ_MP (@lem5778121 _120869 s' s) (@lem5774411 _120869 s' s)). Qed.
Lemma lem5778464 {_120960 : Type'} (s' : _120960 -> Prop) (s : _120960 -> Prop) : (term77 _120960 s' s) = True.
Proof. exact (@lem5778463 _120960 s' s). Qed.
Lemma lem5778465 {_120960 : Type'} (t : _120960 -> Prop) (s : _120960 -> Prop) : (term77 _120960 t s) = True.
Proof. exact (@lem5778464 _120960 t s). Qed.
Lemma lem5778466 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (term361 _120960 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem5778461 _120960 s t h1) (@lem5778465 _120960 t s)). Qed.
Lemma lem5778468 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778469 : (True /\ True) = True.
Proof. exact (@lem5778468 True). Qed.
Lemma lem5778470 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 t) : (term361 _120960 t s) = True.
Proof. exact (TRANS (@lem5778466 _120960 s t h1) (@lem5778469)). Qed.
Lemma lem5778471 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term362 _120960 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem5778448 _120960 t s h1) (@lem5778470 _120960 s t h2)). Qed.
Lemma lem5778473 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778474 : (True /\ True) = True.
Proof. exact (@lem5778473 True). Qed.
Lemma lem5778475 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) : (term362 _120960 t s) = True.
Proof. exact (TRANS (@lem5778471 _120960 s t h1 h2) (@lem5778474)). Qed.
Lemma lem5778476 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term363 _120960 _120978 op t s) = (True /\ True).
Proof. exact (MK_COMB (@lem5778436 _120978 op h3) (@lem5778475 _120960 s t h1 h2)). Qed.
Lemma lem5778478 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5778479 : (True /\ True) = True.
Proof. exact (@lem5778478 True). Qed.
Lemma lem5778480 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term363 _120960 _120978 op t s) = True.
Proof. exact (TRANS (@lem5778476 _120960 _120978 s t op h1 h2 h3) (@lem5778479)). Qed.
Lemma lem5778481 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : True = (term363 _120960 _120978 op t s).
Proof. exact (SYM (@lem5778480 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778482 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : term363 _120960 _120978 op t s.
Proof. exact (EQ_MP (@lem5778481 _120960 _120978 s t op h1 h2 h3) (@lem0)). Qed.
Lemma lem5778483 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term364 _120960 _120978 op t s f) = (term365 _120960 _120978 op t s f).
Proof. exact (@lem5778430 _120960 _120978 op t s f (@lem5778482 _120960 _120978 s t op h1 h2 h3)). Qed.
Lemma lem5778484 {_120978 : Type'} (op : type1400 _120978) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5778485 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term366 _120960 _120978 op t s f) = (term367 _120960 _120978 op t s f).
Proof. exact (MK_COMB (@lem5778484 _120978 op) (@lem5778483 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778486 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term289 _120960 _120978 op s t f) = (term289 _120960 _120978 op s t f).
Proof. exact (eq_refl (term289 _120960 _120978 op s t f)). Qed.
Lemma lem5778487 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term359 _120960 _120978 op s t f) = (term368 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778485 _120960 _120978 f s t op h1 h2 h3) (@lem5778486 _120960 _120978 op s t f)). Qed.
Lemma lem5778488 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term286 _120960 _120978 op s t f) = (term368 _120960 _120978 op s t f).
Proof. exact (TRANS (@lem5778426 _120960 _120978 f s t op h1 h2 h3) (@lem5778487 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778489 {_120978 : Type'} (op : type1400 _120978) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5778490 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term288 _120960 _120978 op s t f) = (term369 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778489 _120978 op) (@lem5778488 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778491 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term289 _120960 _120978 op s t f) = (term289 _120960 _120978 op s t f).
Proof. exact (eq_refl (term289 _120960 _120978 op s t f)). Qed.
Lemma lem5778492 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term291 _120960 _120978 op s t f) = (term370 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778490 _120960 _120978 f s t op h1 h2 h3) (@lem5778491 _120960 _120978 op s t f)). Qed.
Lemma lem5778493 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : ((term302 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f)) = ((term350 _120960 _120978 op s t f) = (term370 _120960 _120978 op s t f)).
Proof. exact (MK_COMB (@lem5778336 _120960 _120978 f s t op h1 h2 h3) (@lem5778492 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778496 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : ((term350 _120960 _120978 op s t f) = (term370 _120960 _120978 op s t f)) = ((term302 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f)).
Proof. exact (SYM (@lem5778493 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778507 {_119721 : Type'} (op : type1400 _119721) : term371 _119721 op.
Proof. exact (@lem5715484 _119721 op). Qed.
Lemma lem5778508 {_119721 : Type'} (op : type1400 _119721) : (term371 _119721 op) = (term372 _119721 op).
Proof. exact (eq_refl (term371 _119721 op)). Qed.
Lemma lem5778511 {_119721 : Type'} (op : type1400 _119721) : term372 _119721 op.
Proof. exact (EQ_MP (@lem5778508 _119721 op) (@lem5778507 _119721 op)). Qed.
Lemma lem5778512 {_120978 : Type'} (op : type1400 _120978) : term372 _120978 op.
Proof. exact (@lem5778511 _120978 op). Qed.
Lemma lem5778513 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term373 _120978 op.
Proof. exact (@lem5778512 _120978 op (@lem5778042 _120978 op h1)). Qed.
Lemma lem5778514 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term374 _120978 op.
Proof. exact (proj2 (@lem5778513 _120978 op h1)). Qed.
Lemma lem5778515 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term375 _120978 op.
Proof. exact (proj2 (@lem5778514 _120978 op h1)). Qed.
Lemma lem5778516 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term376 _120978 op.
Proof. exact (proj2 (@lem5778515 _120978 op h1)). Qed.
Lemma lem5778517 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term377 _120978 op.
Proof. exact (proj2 (@lem5778516 _120978 op h1)). Qed.
Lemma lem5778518 {_120978 : Type'} (a : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term378 _120978 op a.
Proof. exact (@lem5778517 _120978 op h1 a). Qed.
Lemma lem5778519 {_120978 : Type'} (op : type1400 _120978) (a : _120978) : (term378 _120978 op a) = (term379 _120978 op a).
Proof. exact (eq_refl (term378 _120978 op a)). Qed.
Lemma lem5778520 {_120978 : Type'} (a : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term379 _120978 op a.
Proof. exact (EQ_MP (@lem5778519 _120978 op a) (@lem5778518 _120978 a op h1)). Qed.
Lemma lem5778521 {_120978 : Type'} (a : _120978) (b : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term380 _120978 op a b.
Proof. exact (@lem5778520 _120978 a op h1 b). Qed.
Lemma lem5778522 {_120978 : Type'} (b : _120978) (op : type1400 _120978) (a : _120978) : (term380 _120978 op a b) = (term381 _120978 b op a).
Proof. exact (eq_refl (term380 _120978 op a b)). Qed.
Lemma lem5778523 {_120978 : Type'} (b : _120978) (a : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term381 _120978 b op a.
Proof. exact (EQ_MP (@lem5778522 _120978 b op a) (@lem5778521 _120978 a b op h1)). Qed.
Lemma lem5778524 {_120978 : Type'} (b : _120978) (a : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term382 _120978 b op a c.
Proof. exact (@lem5778523 _120978 b a op h1 c). Qed.
Lemma lem5778525 {_120978 : Type'} (b : _120978) (op : type1400 _120978) (a : _120978) (c : _120978) : (term382 _120978 b op a c) = ((term383 _120978 a op b c) = (term383 _120978 b op a c)).
Proof. exact (eq_refl (term382 _120978 b op a c)). Qed.
Lemma lem5778527 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term384 _120978 op.
Proof. exact (proj1 (@lem5778516 _120978 op h1)). Qed.
Lemma lem5778528 {_120978 : Type'} (a : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term385 _120978 op a.
Proof. exact (@lem5778527 _120978 op h1 a). Qed.
Lemma lem5778529 {_120978 : Type'} (a : _120978) (op : type1400 _120978) : (term385 _120978 op a) = (term386 _120978 a op).
Proof. exact (eq_refl (term385 _120978 op a)). Qed.
Lemma lem5778530 {_120978 : Type'} (a : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term386 _120978 a op.
Proof. exact (EQ_MP (@lem5778529 _120978 a op) (@lem5778528 _120978 a op h1)). Qed.
Lemma lem5778531 {_120978 : Type'} (a : _120978) (b : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term387 _120978 a op b.
Proof. exact (@lem5778530 _120978 a op h1 b). Qed.
Lemma lem5778532 {_120978 : Type'} (a : _120978) (op : type1400 _120978) (b : _120978) : (term387 _120978 a op b) = (term388 _120978 a op b).
Proof. exact (eq_refl (term387 _120978 a op b)). Qed.
Lemma lem5778533 {_120978 : Type'} (a : _120978) (b : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term388 _120978 a op b.
Proof. exact (EQ_MP (@lem5778532 _120978 a op b) (@lem5778531 _120978 a b op h1)). Qed.
Lemma lem5778534 {_120978 : Type'} (a : _120978) (b : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term389 _120978 a op b c.
Proof. exact (@lem5778533 _120978 a b op h1 c). Qed.
Lemma lem5778535 {_120978 : Type'} (a : _120978) (op : type1400 _120978) (b : _120978) (c : _120978) : (term389 _120978 a op b c) = ((term390 _120978 op a b c) = (term383 _120978 a op b c)).
Proof. exact (eq_refl (term389 _120978 a op b c)). Qed.
Lemma lem5778555 {_120978 : Type'} (a : _120978) (b : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term390 _120978 op a b c) = (term383 _120978 a op b c).
Proof. exact (EQ_MP (@lem5778535 _120978 a op b c) (@lem5778534 _120978 a b c op h1)). Qed.
Lemma lem5778556 {_120978 : Type'} (a : _120978) (b : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term390 _120978 op a b c) = (term383 _120978 a op b c).
Proof. exact (@lem5778555 _120978 a b c op h1). Qed.
Lemma lem5778557 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term350 _120960 _120978 op s t f) = (term391 _120960 _120978 op s t f).
Proof. exact (@lem5778556 _120978 (term392 _120960 _120978 op s t f) (term289 _120960 _120978 op s t f) (term349 _120960 _120978 op s t f) op h1). Qed.
Lemma lem5778567 {_120978 : Type'} (b : _120978) (a : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term383 _120978 a op b c) = (term383 _120978 b op a c).
Proof. exact (EQ_MP (@lem5778525 _120978 b op a c) (@lem5778524 _120978 b a c op h1)). Qed.
Lemma lem5778568 {_120978 : Type'} (b : _120978) (a : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term383 _120978 a op b c) = (term383 _120978 b op a c).
Proof. exact (@lem5778567 _120978 b a c op h1). Qed.
Lemma lem5778569 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term393 _120960 _120978 op s t f) = (term394 _120960 _120978 op s t f).
Proof. exact (@lem5778568 _120978 (term392 _120960 _120978 op t s f) (term289 _120960 _120978 op s t f) (term289 _120960 _120978 op s t f) op h1). Qed.
Lemma lem5778582 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : (term395 _120960 _120978 op s t f) = (term395 _120960 _120978 op s t f).
Proof. exact (eq_refl (term395 _120960 _120978 op s t f)). Qed.
Lemma lem5778583 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term391 _120960 _120978 op s t f) = (term396 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778582 _120960 _120978 op s t f) (@lem5778569 _120960 _120978 s t f op h1)). Qed.
Lemma lem5778592 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term350 _120960 _120978 op s t f) = (term396 _120960 _120978 op s t f).
Proof. exact (TRANS (@lem5778557 _120960 _120978 s t f op h1) (@lem5778583 _120960 _120978 s t f op h1)). Qed.
Lemma lem5778593 {_120978 : Type'} : (@eq _120978) = (@eq _120978).
Proof. exact (eq_refl (@eq _120978)). Qed.
Lemma lem5778594 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term351 _120960 _120978 op s t f) = (term397 _120960 _120978 op s t f).
Proof. exact (MK_COMB (@lem5778593 _120978) (@lem5778592 _120960 _120978 s t f op h1)). Qed.
Lemma lem5778596 {_120978 : Type'} (a : _120978) (b : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term390 _120978 op a b c) = (term383 _120978 a op b c).
Proof. exact (EQ_MP (@lem5778535 _120978 a op b c) (@lem5778534 _120978 a b c op h1)). Qed.
Lemma lem5778597 {_120978 : Type'} (a : _120978) (b : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term390 _120978 op a b c) = (term383 _120978 a op b c).
Proof. exact (@lem5778596 _120978 a b c op h1). Qed.
Lemma lem5778598 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term370 _120960 _120978 op s t f) = (term398 _120960 _120978 op s t f).
Proof. exact (@lem5778597 _120978 (term365 _120960 _120978 op t s f) (term289 _120960 _120978 op s t f) (term289 _120960 _120978 op s t f) op h1). Qed.
Lemma lem5778600 {_120978 : Type'} (a : _120978) (b : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term390 _120978 op a b c) = (term383 _120978 a op b c).
Proof. exact (EQ_MP (@lem5778535 _120978 a op b c) (@lem5778534 _120978 a b c op h1)). Qed.
Lemma lem5778601 {_120978 : Type'} (a : _120978) (b : _120978) (c : _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term390 _120978 op a b c) = (term383 _120978 a op b c).
Proof. exact (@lem5778600 _120978 a b c op h1). Qed.
Lemma lem5778602 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term398 _120960 _120978 op s t f) = (term396 _120960 _120978 op s t f).
Proof. exact (@lem5778601 _120978 (term392 _120960 _120978 op s t f) (term392 _120960 _120978 op t s f) (term399 _120960 _120978 op s t f) op h1). Qed.
Lemma lem5778611 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term370 _120960 _120978 op s t f) = (term396 _120960 _120978 op s t f).
Proof. exact (TRANS (@lem5778598 _120960 _120978 s t f op h1) (@lem5778602 _120960 _120978 s t f op h1)). Qed.
Lemma lem5778624 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : ((term350 _120960 _120978 op s t f) = (term370 _120960 _120978 op s t f)) = ((term396 _120960 _120978 op s t f) = (term396 _120960 _120978 op s t f)).
Proof. exact (MK_COMB (@lem5778594 _120960 _120978 s t f op h1) (@lem5778611 _120960 _120978 s t f op h1)). Qed.
Lemma lem5778626 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5778627 {_120978 : Type'} (x : _120978) : (x = x) = True.
Proof. exact (@lem5778626 _120978 x). Qed.
Lemma lem5778628 {_120960 _120978 : Type'} (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) : ((term396 _120960 _120978 op s t f) = (term396 _120960 _120978 op s t f)) = True.
Proof. exact (@lem5778627 _120978 (term396 _120960 _120978 op s t f)). Qed.
Lemma lem5778629 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : ((term350 _120960 _120978 op s t f) = (term370 _120960 _120978 op s t f)) = True.
Proof. exact (TRANS (@lem5778624 _120960 _120978 s t f op h1) (@lem5778628 _120960 _120978 op s t f)). Qed.
Lemma lem5778630 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : True = ((term350 _120960 _120978 op s t f) = (term370 _120960 _120978 op s t f)).
Proof. exact (SYM (@lem5778629 _120960 _120978 s t f op h1)). Qed.
Lemma lem5778631 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : (term350 _120960 _120978 op s t f) = (term370 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778630 _120960 _120978 s t f op h1) (@lem0)). Qed.
Lemma lem5778632 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term302 _120960 _120978 op s t f) = (term291 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778496 _120960 _120978 f s t op h1 h2 h3) (@lem5778631 _120960 _120978 s t f op h3)). Qed.
Lemma lem5778633 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term298 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778116 _120960 _120978 op s t f) (@lem5778632 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778634 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term293 _120960 _120978 s op t f) = (term291 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778090 _120960 _120978 op s t f) (@lem5778633 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778635 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778062 _120960 _120978 op s t f) (@lem5778634 _120960 _120978 f s t op h1 h2 h3)). Qed.
Lemma lem5778636 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : term282 _120960 s t) : @FINITE _120960 t.
Proof. exact (proj2 (@lem5778043 _120960 s t h1)). Qed.
Lemma lem5778637 {_120960 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : term282 _120960 s t) : @FINITE _120960 s.
Proof. exact (proj1 (@lem5778043 _120960 s t h1)). Qed.
Lemma lem5778638 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (@FINITE _120960 t) = ((term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f)).
Proof. exact (prop_ext (fun h4 : @FINITE _120960 t => @lem5778635 _120960 _120978 f s t op h1 h2 h3) (fun h4 : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f) => @lem5778044 _120960 t h2)). Qed.
Lemma lem5778639 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778638 _120960 _120978 f s t op h1 h2 h3) (@lem5778044 _120960 t h2)). Qed.
Lemma lem5778640 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (@FINITE _120960 s) = ((term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f)).
Proof. exact (prop_ext (fun h4 : @FINITE _120960 s => @lem5778639 _120960 _120978 f s t op h1 h2 h3) (fun h4 : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f) => @lem5778045 _120960 s h1)). Qed.
Lemma lem5778641 {_120960 _120978 : Type'} (f : _120960 -> _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @FINITE _120960 s) (h2 : @FINITE _120960 t) (h3 : @monoidal _120978 op) : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778640 _120960 _120978 f s t op h1 h2 h3) (@lem5778045 _120960 s h1)). Qed.
Lemma lem5778642 {_120960 _120978 : Type'} (f : _120960 -> _120978) (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @monoidal _120978 op) (h3 : term282 _120960 s t) : (@FINITE _120960 t) = ((term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f)).
Proof. exact (prop_ext (fun h4 : @FINITE _120960 t => @lem5778641 _120960 _120978 f s t op h1 h4 h2) (fun h4 : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f) => @lem5778636 _120960 s t h3)). Qed.
Lemma lem5778643 {_120960 _120978 : Type'} (f : _120960 -> _120978) (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @FINITE _120960 s) (h2 : @monoidal _120978 op) (h3 : term282 _120960 s t) : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778642 _120960 _120978 f op s t h1 h2 h3) (@lem5778636 _120960 s t h3)). Qed.
Lemma lem5778644 {_120960 _120978 : Type'} (f : _120960 -> _120978) (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @monoidal _120978 op) (h2 : term282 _120960 s t) : (@FINITE _120960 s) = ((term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f)).
Proof. exact (prop_ext (fun h3 : @FINITE _120960 s => @lem5778643 _120960 _120978 f op s t h3 h1 h2) (fun h3 : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f) => @lem5778637 _120960 s t h2)). Qed.
Lemma lem5778645 {_120960 _120978 : Type'} (f : _120960 -> _120978) (op : type1400 _120978) (s : _120960 -> Prop) (t : _120960 -> Prop) (h1 : @monoidal _120978 op) (h2 : term282 _120960 s t) : (term293 _120960 _120978 s op t f) = (term290 _120960 _120978 op s t f).
Proof. exact (EQ_MP (@lem5778644 _120960 _120978 f op s t h1 h2) (@lem5778637 _120960 s t h2)). Qed.
Lemma lem5778646 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (f : _120960 -> _120978) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term400 _120960 _120978 op s t f.
Proof. exact (fun h0 : term282 _120960 s t => @lem5778645 _120960 _120978 f op s t h1 h0). Qed.
Lemma lem5778651 {_120960 _120978 : Type'} (s : _120960 -> Prop) (t : _120960 -> Prop) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term401 _120960 _120978 op s t.
Proof. exact (fun f : _120960 -> _120978 => @lem5778646 _120960 _120978 s t f op h1). Qed.
Lemma lem5778656 {_120960 _120978 : Type'} (s : _120960 -> Prop) (op : type1400 _120978) (h1 : @monoidal _120978 op) : term402 _120960 _120978 op s.
Proof. exact (fun t : _120960 -> Prop => @lem5778651 _120960 _120978 s t op h1). Qed.
Lemma lem5778661 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term403 _120960 _120978 op.
Proof. exact (fun s : _120960 -> Prop => @lem5778656 _120960 _120978 s op h1). Qed.
Lemma lem5778662 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : (@monoidal _120978 op) = (term403 _120960 _120978 op).
Proof. exact (prop_ext (fun h2 : @monoidal _120978 op => @lem5778661 _120960 _120978 op h1) (fun h2 : term403 _120960 _120978 op => @lem5778042 _120978 op h1)). Qed.
Lemma lem5778663 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term403 _120960 _120978 op.
Proof. exact (EQ_MP (@lem5778662 _120960 _120978 op h1) (@lem5778042 _120978 op h1)). Qed.
Lemma lem5778664 {_120960 _120978 : Type'} (op : type1400 _120978) : term404 _120960 _120978 op.
Proof. exact (fun h0 : @monoidal _120978 op => @lem5778663 _120960 _120978 op h0). Qed.
Lemma lem5778669 {_120960 _120978 : Type'} : term405 _120960 _120978.
Proof. exact (fun op : type1400 _120978 => @lem5778664 _120960 _120978 op). Qed.
