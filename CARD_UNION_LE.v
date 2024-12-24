Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_UNION_LE_term_abbrevs.
Require Import CARD_SUBSET_spec.
Require Import CARD_UNION_spec.
Require Import EQ_IMP_LE_spec.
Require Import FINITE_DIFF_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import SUBSET_DIFF_spec.
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
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
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
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem3923339 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3923340 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3923339 A h1 s). Qed.
Lemma lem3923341 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3923342 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3923341 A s) (@lem3923340 A s h1)). Qed.
Lemma lem3923343 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3923342 A s h1 t). Qed.
Lemma lem3923344 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term4 A s t).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3923345 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term4 A s t.
Proof. exact (EQ_MP (@lem3923344 A s t) (@lem3923343 A s t h1)). Qed.
Lemma lem3923346 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3923347 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : (term6 A s t) = (term7 A s t).
Proof. exact (@lem3923345 A s t h1 (@lem3923346 A s t h2)). Qed.
Lemma lem3923348 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term8 A s t.
Proof. exact (fun h0 : term0 A => @lem3923347 A s t h0 h1). Qed.
Lemma lem3923349 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3923350 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : (term6 A s t) = (term7 A s t).
Proof. exact (@lem3923348 A s t h2 (@lem3923349 A h1)). Qed.
Lemma lem3923351 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term4 A s t.
Proof. exact (fun h0 : term5 A s t => @lem3923350 A s t h1 h0). Qed.
Lemma lem3923352 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (fun t : A -> Prop => @lem3923351 A s t h1). Qed.
Lemma lem3923353 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun s : A -> Prop => @lem3923352 A s h1). Qed.
Lemma lem3923354 {A : Type'} : term9 A.
Proof. exact (fun h0 : term0 A => @lem3923353 A h0). Qed.
Lemma lem3923355 {A : Type'} : term0 A.
Proof. exact (@lem3923354 A (@lem3843862 A)). Qed.
Lemma lem3923356 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (@lem3923355 A s). Qed.
Lemma lem3923357 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3923358 {A : Type'} (s : A -> Prop) : term2 A s.
Proof. exact (EQ_MP (@lem3923357 A s) (@lem3923356 A s)). Qed.
Lemma lem3923359 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (@lem3923358 A s t). Qed.
Lemma lem3923360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term4 A s t).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3923375 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3923376 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) : (s = t) = (term10 _101005 s t).
Proof. exact (@lem3923375 _101005 s t). Qed.
Lemma lem3923377 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : ((@UNION _101005 s t) = (term11 _101005 t s)) = (term12 _101005 t s).
Proof. exact (@lem3923376 _101005 (@UNION _101005 s t) (term11 _101005 t s)). Qed.
Lemma lem3923386 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term12 _101005 t s) = ((@UNION _101005 s t) = (term11 _101005 t s)).
Proof. exact (SYM (@lem3923377 _101005 t s)). Qed.
Lemma lem3923394 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A x s t) = (term14 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3923395 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (t : _101005 -> Prop) : (term13 _101005 x s t) = (term14 _101005 s x t).
Proof. exact (@lem3923394 _101005 s x t). Qed.
Lemma lem3923399 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3923400 {_101005 : Type'} (P : _101005 -> Prop) (x : _101005) : (@IN _101005 x P) = (P x).
Proof. exact (@lem3923399 _101005 P x). Qed.
Lemma lem3923401 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (@IN _101005 x s) = (s x).
Proof. exact (@lem3923400 _101005 s x). Qed.
Lemma lem3923402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3923403 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term15 _101005 x s) = (term16 _101005 s x).
Proof. exact (MK_COMB (@lem3923402) (@lem3923401 _101005 s x)). Qed.
Lemma lem3923405 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3923406 {_101005 : Type'} (P : _101005 -> Prop) (x : _101005) : (@IN _101005 x P) = (P x).
Proof. exact (@lem3923405 _101005 P x). Qed.
Lemma lem3923407 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (@IN _101005 x t) = (t x).
Proof. exact (@lem3923406 _101005 t x). Qed.
Lemma lem3923408 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) (x : _101005) : (term14 _101005 s x t) = (term17 _101005 s t x).
Proof. exact (MK_COMB (@lem3923403 _101005 s x) (@lem3923407 _101005 t x)). Qed.
Lemma lem3923411 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) (x : _101005) : (term13 _101005 x s t) = (term17 _101005 s t x).
Proof. exact (TRANS (@lem3923395 _101005 s x t) (@lem3923408 _101005 s t x)). Qed.
Lemma lem3923412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3923413 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) (x : _101005) : (term18 _101005 x s t) = (term19 _101005 s t x).
Proof. exact (MK_COMB (@lem3923412) (@lem3923411 _101005 s t x)). Qed.
Lemma lem3923415 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A x s t) = (term14 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3923416 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (t : _101005 -> Prop) : (term13 _101005 x s t) = (term14 _101005 s x t).
Proof. exact (@lem3923415 _101005 s x t). Qed.
Lemma lem3923417 {_101005 : Type'} (x : _101005) (t : _101005 -> Prop) (s : _101005 -> Prop) : (term20 _101005 x t s) = (term21 _101005 x t s).
Proof. exact (@lem3923416 _101005 s x (@DIFF _101005 t s)). Qed.
Lemma lem3923421 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3923422 {_101005 : Type'} (P : _101005 -> Prop) (x : _101005) : (@IN _101005 x P) = (P x).
Proof. exact (@lem3923421 _101005 P x). Qed.
Lemma lem3923423 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (@IN _101005 x s) = (s x).
Proof. exact (@lem3923422 _101005 s x). Qed.
Lemma lem3923424 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3923425 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term15 _101005 x s) = (term16 _101005 s x).
Proof. exact (MK_COMB (@lem3923424) (@lem3923423 _101005 s x)). Qed.
Lemma lem3923427 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3923428 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (t : _101005 -> Prop) : (term22 _101005 x s t) = (term23 _101005 s x t).
Proof. exact (@lem3923427 _101005 s x t). Qed.
Lemma lem3923429 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (s : _101005 -> Prop) : (term22 _101005 x t s) = (term23 _101005 t x s).
Proof. exact (@lem3923428 _101005 t x s). Qed.
Lemma lem3923433 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3923434 {_101005 : Type'} (P : _101005 -> Prop) (x : _101005) : (@IN _101005 x P) = (P x).
Proof. exact (@lem3923433 _101005 P x). Qed.
Lemma lem3923435 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (@IN _101005 x t) = (t x).
Proof. exact (@lem3923434 _101005 t x). Qed.
Lemma lem3923436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3923437 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (term24 _101005 x t) = (term25 _101005 t x).
Proof. exact (MK_COMB (@lem3923436) (@lem3923435 _101005 t x)). Qed.
Lemma lem3923439 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3923440 {_101005 : Type'} (P : _101005 -> Prop) (x : _101005) : (@IN _101005 x P) = (P x).
Proof. exact (@lem3923439 _101005 P x). Qed.
Lemma lem3923441 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (@IN _101005 x s) = (s x).
Proof. exact (@lem3923440 _101005 s x). Qed.
Lemma lem3923442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3923443 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term26 _101005 x s) = (term27 _101005 s x).
Proof. exact (MK_COMB (@lem3923442) (@lem3923441 _101005 s x)). Qed.
Lemma lem3923444 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term23 _101005 t x s) = (term28 _101005 t s x).
Proof. exact (MK_COMB (@lem3923437 _101005 t x) (@lem3923443 _101005 s x)). Qed.
Lemma lem3923447 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term22 _101005 x t s) = (term28 _101005 t s x).
Proof. exact (TRANS (@lem3923429 _101005 t x s) (@lem3923444 _101005 t s x)). Qed.
Lemma lem3923448 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term21 _101005 x t s) = (term29 _101005 t s x).
Proof. exact (MK_COMB (@lem3923425 _101005 s x) (@lem3923447 _101005 t s x)). Qed.
Lemma lem3923451 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term20 _101005 x t s) = (term29 _101005 t s x).
Proof. exact (TRANS (@lem3923417 _101005 x t s) (@lem3923448 _101005 t s x)). Qed.
Lemma lem3923452 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : ((term13 _101005 x s t) = (term20 _101005 x t s)) = ((term17 _101005 s t x) = (term29 _101005 t s x)).
Proof. exact (MK_COMB (@lem3923413 _101005 s t x) (@lem3923451 _101005 t s x)). Qed.
Lemma lem3923455 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term30 _101005 t s) = (term31 _101005 t s).
Proof. exact (fun_ext (fun x : _101005 => @lem3923452 _101005 t s x)). Qed.
Lemma lem3923456 {_101005 : Type'} : (@all _101005) = (@all _101005).
Proof. exact (eq_refl (@all _101005)). Qed.
Lemma lem3923457 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term12 _101005 t s) = (term32 _101005 t s).
Proof. exact (MK_COMB (@lem3923456 _101005) (@lem3923455 _101005 t s)). Qed.
Lemma lem3923462 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term32 _101005 t s) = (term12 _101005 t s).
Proof. exact (SYM (@lem3923457 _101005 t s)). Qed.
Lemma lem3923464 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3923465 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term32 _101005 t s) = (term34 _101005 t s).
Proof. exact (@lem3923464 (term32 _101005 t s)). Qed.
Lemma lem3923466 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term34 _101005 t s) = (term32 _101005 t s).
Proof. exact (SYM (@lem3923465 _101005 t s)). Qed.
Lemma lem3923467 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term35 _101005 t s) : term35 _101005 t s.
Proof. exact (h1). Qed.
Lemma lem3923470 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term34 _101005 t s) : term34 _101005 t s.
Proof. exact (h1). Qed.
Lemma lem3923471 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term36 _101005 t s.
Proof. exact (fun h0 : term34 _101005 t s => @lem3923470 _101005 t s h0). Qed.
Lemma lem3923472 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term36 _101005 t s) : term36 _101005 t s.
Proof. exact (h1). Qed.
Lemma lem3923473 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term34 _101005 t s) : term34 _101005 t s.
Proof. exact (h1). Qed.
Lemma lem3923474 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term34 _101005 t s) (h2 : term36 _101005 t s) : term34 _101005 t s.
Proof. exact (@lem3923472 _101005 t s h2 (@lem3923473 _101005 t s h1)). Qed.
Lemma lem3923475 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term34 _101005 t s) : term37 _101005 t s.
Proof. exact (fun h0 : term36 _101005 t s => @lem3923474 _101005 t s h1 h0). Qed.
Lemma lem3923476 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term36 _101005 t s) : term36 _101005 t s.
Proof. exact (h1). Qed.
Lemma lem3923477 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term34 _101005 t s) (h2 : term36 _101005 t s) : term34 _101005 t s.
Proof. exact (@lem3923475 _101005 t s h1 (@lem3923476 _101005 t s h2)). Qed.
Lemma lem3923478 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term36 _101005 t s) : term36 _101005 t s.
Proof. exact (fun h0 : term34 _101005 t s => @lem3923477 _101005 t s h0 h1). Qed.
Lemma lem3923479 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term38 _101005 t s.
Proof. exact (fun h0 : term36 _101005 t s => @lem3923478 _101005 t s h0). Qed.
Lemma lem3923482 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term36 _101005 t s.
Proof. exact (@lem3923479 _101005 t s (@lem3923471 _101005 t s)). Qed.
Lemma lem3923483 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term36 _101005 t s.
Proof. exact (@lem3923482 _101005 t s). Qed.
Lemma lem3923493 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3923494 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term34 _101005 t s) = (term39 _101005 t s).
Proof. exact (@lem3923493 (term35 _101005 t s)). Qed.
Lemma lem3923496 (t : Prop) : (term40 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3923497 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term39 _101005 t s) = (term32 _101005 t s).
Proof. exact (@lem3923496 (term32 _101005 t s)). Qed.
Lemma lem3923502 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term34 _101005 t s) = (term32 _101005 t s).
Proof. exact (TRANS (@lem3923494 _101005 t s) (@lem3923497 _101005 t s)). Qed.
Lemma lem3923509 {_101005 : Type'} (s : _101005 -> Prop) : (term41 _101005 s) = (term42 _101005 s).
Proof. exact (fun_ext (fun t : _101005 -> Prop => @lem3923502 _101005 t s)). Qed.
Lemma lem3923510 {_101005 : Type'} : (@all (_101005 -> Prop)) = (@all (_101005 -> Prop)).
Proof. exact (eq_refl (@all (_101005 -> Prop))). Qed.
Lemma lem3923511 {_101005 : Type'} (s : _101005 -> Prop) : (term43 _101005 s) = (term44 _101005 s).
Proof. exact (MK_COMB (@lem3923510 _101005) (@lem3923509 _101005 s)). Qed.
Lemma lem3923516 {_101005 : Type'} : (term45 _101005) = (term46 _101005).
Proof. exact (fun_ext (fun s : _101005 -> Prop => @lem3923511 _101005 s)). Qed.
Lemma lem3923517 {_101005 : Type'} : (@all (_101005 -> Prop)) = (@all (_101005 -> Prop)).
Proof. exact (eq_refl (@all (_101005 -> Prop))). Qed.
Lemma lem3923526 {_101005 : Type'} : (term47 _101005) = (term48 _101005).
Proof. exact (MK_COMB (@lem3923517 _101005) (@lem3923516 _101005)). Qed.
Lemma lem3923545 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : ((term17 _101005 s t x) = (term29 _101005 t s x)) = ((term17 _101005 s t x) = (term29 _101005 t s x)).
Proof. exact (eq_refl ((term17 _101005 s t x) = (term29 _101005 t s x))). Qed.
Lemma lem3923546 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term31 _101005 t s) = (term31 _101005 t s).
Proof. exact (fun_ext (fun x : _101005 => @lem3923545 _101005 t s x)). Qed.
Lemma lem3923547 {_101005 : Type'} : (@all _101005) = (@all _101005).
Proof. exact (eq_refl (@all _101005)). Qed.
Lemma lem3923548 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term32 _101005 t s) = (term32 _101005 t s).
Proof. exact (MK_COMB (@lem3923547 _101005) (@lem3923546 _101005 t s)). Qed.
Lemma lem3923549 {_101005 : Type'} (s : _101005 -> Prop) : (term42 _101005 s) = (term42 _101005 s).
Proof. exact (fun_ext (fun t : _101005 -> Prop => @lem3923548 _101005 t s)). Qed.
Lemma lem3923550 {_101005 : Type'} : (@all (_101005 -> Prop)) = (@all (_101005 -> Prop)).
Proof. exact (eq_refl (@all (_101005 -> Prop))). Qed.
Lemma lem3923551 {_101005 : Type'} (s : _101005 -> Prop) : (term44 _101005 s) = (term44 _101005 s).
Proof. exact (MK_COMB (@lem3923550 _101005) (@lem3923549 _101005 s)). Qed.
Lemma lem3923552 {_101005 : Type'} : (term46 _101005) = (term46 _101005).
Proof. exact (fun_ext (fun s : _101005 -> Prop => @lem3923551 _101005 s)). Qed.
Lemma lem3923553 {_101005 : Type'} : (@all (_101005 -> Prop)) = (@all (_101005 -> Prop)).
Proof. exact (eq_refl (@all (_101005 -> Prop))). Qed.
Lemma lem3923554 {_101005 : Type'} : (term48 _101005) = (term48 _101005).
Proof. exact (MK_COMB (@lem3923553 _101005) (@lem3923552 _101005)). Qed.
Lemma lem3923581 {_101005 : Type'} : (term47 _101005) = (term48 _101005).
Proof. exact (TRANS (@lem3923526 _101005) (@lem3923554 _101005)). Qed.
Lemma lem3923582 {_101005 : Type'} : (term48 _101005) = (term47 _101005).
Proof. exact (SYM (@lem3923581 _101005)). Qed.
Lemma lem3923584 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3923585 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : ((term17 _101005 s t x) = (term29 _101005 t s x)) = (term49 _101005 t s x).
Proof. exact (@lem3923584 ((term17 _101005 s t x) = (term29 _101005 t s x))). Qed.
Lemma lem3923586 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term49 _101005 t s x) = ((term17 _101005 s t x) = (term29 _101005 t s x)).
Proof. exact (SYM (@lem3923585 _101005 t s x)). Qed.
Lemma lem3923587 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term50 _101005 t s x) : term50 _101005 t s x.
Proof. exact (h1). Qed.
Lemma lem3923596 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) (x : _101005) : (term51 _101005 s t x) = (term52 _101005 s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3923607 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term53 _101005 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3923609 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (term54 _101005 t x) = (term54 _101005 t x).
Proof. exact (eq_refl (term54 _101005 t x)). Qed.
Lemma lem3923610 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term55 _101005 t s x) = (term56 _101005 t s x).
Proof. exact (MK_COMB (@lem3923609 _101005 t x) (@lem3923607 _101005 s x)). Qed.
Lemma lem3923611 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term57 _101005 t s x) = (term55 _101005 t s x).
Proof. exact (@lem17045 (t x) (term27 _101005 s x)). Qed.
Lemma lem3923612 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term57 _101005 t s x) = (term56 _101005 t s x).
Proof. exact (TRANS (@lem3923611 _101005 t s x) (@lem3923610 _101005 t s x)). Qed.
Lemma lem3923617 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term58 _101005 s x) = (term58 _101005 s x).
Proof. exact (eq_refl (term58 _101005 s x)). Qed.
Lemma lem3923618 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term59 _101005 t s x) = (term60 _101005 t s x).
Proof. exact (MK_COMB (@lem3923617 _101005 s x) (@lem3923612 _101005 t s x)). Qed.
Lemma lem3923619 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term61 _101005 t s x) = (term59 _101005 t s x).
Proof. exact (@lem17160 (s x) (term28 _101005 t s x)). Qed.
Lemma lem3923620 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term61 _101005 t s x) = (term60 _101005 t s x).
Proof. exact (TRANS (@lem3923619 _101005 t s x) (@lem3923618 _101005 t s x)). Qed.
Lemma lem3923623 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term29 _101005 t s x) = (term29 _101005 t s x).
Proof. exact (eq_refl (term29 _101005 t s x)). Qed.
Lemma lem3923624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3923625 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) (x : _101005) : (term62 _101005 s t x) = (term63 _101005 s t x).
Proof. exact (MK_COMB (@lem3923624) (@lem3923596 _101005 s t x)). Qed.
Lemma lem3923626 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term64 _101005 t s x) = (term65 _101005 t s x).
Proof. exact (MK_COMB (@lem3923625 _101005 s t x) (@lem3923623 _101005 t s x)). Qed.
Lemma lem3923628 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) (x : _101005) : (term66 _101005 s t x) = (term66 _101005 s t x).
Proof. exact (eq_refl (term66 _101005 s t x)). Qed.
Lemma lem3923629 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term67 _101005 t s x) = (term68 _101005 t s x).
Proof. exact (MK_COMB (@lem3923628 _101005 s t x) (@lem3923620 _101005 t s x)). Qed.
Lemma lem3923630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3923631 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term69 _101005 t s x) = (term70 _101005 t s x).
Proof. exact (MK_COMB (@lem3923630) (@lem3923629 _101005 t s x)). Qed.
Lemma lem3923632 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term71 _101005 t s x) = (term72 _101005 t s x).
Proof. exact (MK_COMB (@lem3923631 _101005 t s x) (@lem3923626 _101005 t s x)). Qed.
Lemma lem3923633 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term50 _101005 t s x) = (term71 _101005 t s x).
Proof. exact (@lem17646 (term17 _101005 s t x) (term29 _101005 t s x)). Qed.
Lemma lem3923638 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term50 _101005 t s x) = (term72 _101005 t s x).
Proof. exact (TRANS (@lem3923633 _101005 t s x) (@lem3923632 _101005 t s x)). Qed.
Lemma lem3923707 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term50 _101005 t s x) : term72 _101005 t s x.
Proof. exact (EQ_MP (@lem3923638 _101005 t s x) (@lem3923587 _101005 t s x h1)). Qed.
Lemma lem3923708 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term68 _101005 t s x.
Proof. exact (h1). Qed.
Lemma lem3923709 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : term65 _101005 t s x.
Proof. exact (h1). Qed.
Lemma lem3923710 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term60 _101005 t s x.
Proof. exact (proj2 (@lem3923708 _101005 t s x h1)). Qed.
Lemma lem3923711 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term17 _101005 s t x.
Proof. exact (proj1 (@lem3923708 _101005 t s x h1)). Qed.
Lemma lem3923712 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term56 _101005 t s x.
Proof. exact (proj2 (@lem3923710 _101005 t s x h1)). Qed.
Lemma lem3923720 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : term29 _101005 t s x.
Proof. exact (proj2 (@lem3923709 _101005 t s x h1)). Qed.
Lemma lem3923721 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : term52 _101005 s t x.
Proof. exact (proj1 (@lem3923709 _101005 t s x h1)). Qed.
Lemma lem3923725 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term28 _101005 t s x) : term28 _101005 t s x.
Proof. exact (h1). Qed.
Lemma lem3923739 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923747 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) : term27 _101005 t x.
Proof. exact (h1). Qed.
Lemma lem3923751 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3923759 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923763 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923771 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923787 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923805 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term27 _101005 s x.
Proof. exact (proj1 (@lem3923710 _101005 t s x h1)). Qed.
Lemma lem3923809 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923813 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) : term27 _101005 t x.
Proof. exact (h1). Qed.
Lemma lem3923815 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3923817 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term27 _101005 s x.
Proof. exact (proj1 (@lem3923710 _101005 t s x h1)). Qed.
Lemma lem3923819 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923821 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923823 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term27 _101005 s x.
Proof. exact (proj1 (@lem3923710 _101005 t s x h1)). Qed.
Lemma lem3923825 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923829 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : term27 _101005 s x.
Proof. exact (proj1 (@lem3923721 _101005 t s x h1)). Qed.
Lemma lem3923833 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923837 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : term27 _101005 t x.
Proof. exact (proj2 (@lem3923721 _101005 t s x h1)). Qed.
Lemma lem3923843 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923844 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : term73 _101005 s x.
Proof. exact (fun h0 : term27 _101005 s x => @lem3923843 _101005 s x h1). Qed.
Lemma lem3923846 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923847 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term73 _101005 s x) = (s x).
Proof. exact (@lem3923846 (s x)). Qed.
Lemma lem3923848 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3923847 _101005 s x) (@lem3923844 _101005 s x h1)). Qed.
Lemma lem3923851 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3923853 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term27 _101005 s x) = (term75 _101005 s x).
Proof. exact (@lem3923851 (s x)). Qed.
Lemma lem3923856 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term75 _101005 s x.
Proof. exact (EQ_MP (@lem3923853 _101005 s x) (@lem3923805 _101005 t s x h1)). Qed.
Lemma lem3923859 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (@lem3923856 _101005 t s x h2 (@lem3923848 _101005 s x h1)). Qed.
Lemma lem3923860 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : term76.
Proof. exact (fun h0 : ~ False => @lem3923859 _101005 t s x h1 h2). Qed.
Lemma lem3923862 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923863 : term76 = False.
Proof. exact (@lem3923862 False). Qed.
Lemma lem3923864 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923863) (@lem3923860 _101005 t s x h1 h2)). Qed.
Lemma lem3923866 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3923867 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : t x) : term73 _101005 t x.
Proof. exact (fun h0 : term27 _101005 t x => @lem3923866 _101005 t x h1). Qed.
Lemma lem3923869 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923870 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (term73 _101005 t x) = (t x).
Proof. exact (@lem3923869 (t x)). Qed.
Lemma lem3923871 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3923870 _101005 t x) (@lem3923867 _101005 t x h1)). Qed.
Lemma lem3923874 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3923876 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (term27 _101005 t x) = (term75 _101005 t x).
Proof. exact (@lem3923874 (t x)). Qed.
Lemma lem3923879 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) : term75 _101005 t x.
Proof. exact (EQ_MP (@lem3923876 _101005 t x) (@lem3923813 _101005 t x h1)). Qed.
Lemma lem3923882 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (@lem3923879 _101005 t x h1 (@lem3923871 _101005 t x h2)). Qed.
Lemma lem3923883 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : term76.
Proof. exact (fun h0 : ~ False => @lem3923882 _101005 t x h1 h2). Qed.
Lemma lem3923885 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923886 : term76 = False.
Proof. exact (@lem3923885 False). Qed.
Lemma lem3923887 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3923886) (@lem3923883 _101005 t x h1 h2)). Qed.
Lemma lem3923889 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923890 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : term73 _101005 s x.
Proof. exact (fun h0 : term27 _101005 s x => @lem3923889 _101005 s x h1). Qed.
Lemma lem3923892 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923893 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term73 _101005 s x) = (s x).
Proof. exact (@lem3923892 (s x)). Qed.
Lemma lem3923894 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3923893 _101005 s x) (@lem3923890 _101005 s x h1)). Qed.
Lemma lem3923897 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3923899 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term27 _101005 s x) = (term75 _101005 s x).
Proof. exact (@lem3923897 (s x)). Qed.
Lemma lem3923902 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term75 _101005 s x.
Proof. exact (EQ_MP (@lem3923899 _101005 s x) (@lem3923817 _101005 t s x h1)). Qed.
Lemma lem3923905 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (@lem3923902 _101005 t s x h2 (@lem3923894 _101005 s x h1)). Qed.
Lemma lem3923906 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : term76.
Proof. exact (fun h0 : ~ False => @lem3923905 _101005 t s x h1 h2). Qed.
Lemma lem3923908 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923909 : term76 = False.
Proof. exact (@lem3923908 False). Qed.
Lemma lem3923910 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923909) (@lem3923906 _101005 t s x h1 h2)). Qed.
Lemma lem3923912 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923913 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : term73 _101005 s x.
Proof. exact (fun h0 : term27 _101005 s x => @lem3923912 _101005 s x h1). Qed.
Lemma lem3923915 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923916 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term73 _101005 s x) = (s x).
Proof. exact (@lem3923915 (s x)). Qed.
Lemma lem3923917 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3923916 _101005 s x) (@lem3923913 _101005 s x h1)). Qed.
Lemma lem3923920 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3923922 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term27 _101005 s x) = (term75 _101005 s x).
Proof. exact (@lem3923920 (s x)). Qed.
Lemma lem3923925 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : term75 _101005 s x.
Proof. exact (EQ_MP (@lem3923922 _101005 s x) (@lem3923823 _101005 t s x h1)). Qed.
Lemma lem3923928 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (@lem3923925 _101005 t s x h2 (@lem3923917 _101005 s x h1)). Qed.
Lemma lem3923929 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : term76.
Proof. exact (fun h0 : ~ False => @lem3923928 _101005 t s x h1 h2). Qed.
Lemma lem3923931 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923932 : term76 = False.
Proof. exact (@lem3923931 False). Qed.
Lemma lem3923933 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923932) (@lem3923929 _101005 t s x h1 h2)). Qed.
Lemma lem3923935 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3923936 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : term73 _101005 s x.
Proof. exact (fun h0 : term27 _101005 s x => @lem3923935 _101005 s x h1). Qed.
Lemma lem3923938 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923939 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term73 _101005 s x) = (s x).
Proof. exact (@lem3923938 (s x)). Qed.
Lemma lem3923940 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3923939 _101005 s x) (@lem3923936 _101005 s x h1)). Qed.
Lemma lem3923943 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3923945 {_101005 : Type'} (s : _101005 -> Prop) (x : _101005) : (term27 _101005 s x) = (term75 _101005 s x).
Proof. exact (@lem3923943 (s x)). Qed.
Lemma lem3923948 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : term75 _101005 s x.
Proof. exact (EQ_MP (@lem3923945 _101005 s x) (@lem3923829 _101005 t s x h1)). Qed.
Lemma lem3923951 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : False.
Proof. exact (@lem3923948 _101005 t s x h2 (@lem3923940 _101005 s x h1)). Qed.
Lemma lem3923952 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : term76.
Proof. exact (fun h0 : ~ False => @lem3923951 _101005 t s x h1 h2). Qed.
Lemma lem3923954 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923955 : term76 = False.
Proof. exact (@lem3923954 False). Qed.
Lemma lem3923956 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923955) (@lem3923952 _101005 t s x h1 h2)). Qed.
Lemma lem3923958 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term28 _101005 t s x) : t x.
Proof. exact (proj1 (@lem3923725 _101005 t s x h1)). Qed.
Lemma lem3923959 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term28 _101005 t s x) : term73 _101005 t x.
Proof. exact (fun h0 : term27 _101005 t x => @lem3923958 _101005 t s x h1). Qed.
Lemma lem3923961 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923962 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (term73 _101005 t x) = (t x).
Proof. exact (@lem3923961 (t x)). Qed.
Lemma lem3923963 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term28 _101005 t s x) : t x.
Proof. exact (EQ_MP (@lem3923962 _101005 t x) (@lem3923959 _101005 t s x h1)). Qed.
Lemma lem3923966 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3923968 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) : (term27 _101005 t x) = (term75 _101005 t x).
Proof. exact (@lem3923966 (t x)). Qed.
Lemma lem3923971 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : term75 _101005 t x.
Proof. exact (EQ_MP (@lem3923968 _101005 t x) (@lem3923837 _101005 t s x h1)). Qed.
Lemma lem3923974 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term28 _101005 t s x) (h2 : term65 _101005 t s x) : False.
Proof. exact (@lem3923971 _101005 t s x h2 (@lem3923963 _101005 t s x h1)). Qed.
Lemma lem3923975 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term28 _101005 t s x) (h2 : term65 _101005 t s x) : term76.
Proof. exact (fun h0 : ~ False => @lem3923974 _101005 t s x h1 h2). Qed.
Lemma lem3923977 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3923978 : term76 = False.
Proof. exact (@lem3923977 False). Qed.
Lemma lem3923979 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term28 _101005 t s x) (h2 : term65 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923978) (@lem3923975 _101005 t s x h1 h2)). Qed.
Lemma lem3923980 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923956 _101005 t s x h1 h2) (fun h3 : False => @lem3923833 _101005 s x h1)). Qed.
Lemma lem3923981 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923980 _101005 t s x h1 h2) (@lem3923833 _101005 s x h1)). Qed.
Lemma lem3923982 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923933 _101005 t s x h1 h2) (fun h3 : False => @lem3923825 _101005 s x h1)). Qed.
Lemma lem3923983 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923982 _101005 t s x h1 h2) (@lem3923825 _101005 s x h1)). Qed.
Lemma lem3923984 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923910 _101005 t s x h1 h2) (fun h3 : False => @lem3923821 _101005 s x h1)). Qed.
Lemma lem3923985 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923984 _101005 t s x h1 h2) (@lem3923821 _101005 s x h1)). Qed.
Lemma lem3923986 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923985 _101005 t s x h1 h2) (fun h3 : False => @lem3923819 _101005 s x h1)). Qed.
Lemma lem3923987 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923986 _101005 t s x h1 h2) (@lem3923819 _101005 s x h1)). Qed.
Lemma lem3923988 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3923887 _101005 t x h1 h2) (fun h3 : False => @lem3923815 _101005 t x h2)). Qed.
Lemma lem3923989 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3923988 _101005 t x h1 h2) (@lem3923815 _101005 t x h2)). Qed.
Lemma lem3923990 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : (term27 _101005 t x) = False.
Proof. exact (prop_ext (fun h3 : term27 _101005 t x => @lem3923989 _101005 t x h1 h2) (fun h3 : False => @lem3923813 _101005 t x h1)). Qed.
Lemma lem3923991 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3923990 _101005 t x h1 h2) (@lem3923813 _101005 t x h1)). Qed.
Lemma lem3923992 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923864 _101005 t s x h1 h2) (fun h3 : False => @lem3923809 _101005 s x h1)). Qed.
Lemma lem3923993 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923992 _101005 t s x h1 h2) (@lem3923809 _101005 s x h1)). Qed.
Lemma lem3923994 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923981 _101005 t s x h1 h2) (fun h3 : False => @lem3923787 _101005 s x h1)). Qed.
Lemma lem3923995 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923994 _101005 t s x h1 h2) (@lem3923787 _101005 s x h1)). Qed.
Lemma lem3923996 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923983 _101005 t s x h1 h2) (fun h3 : False => @lem3923771 _101005 s x h1)). Qed.
Lemma lem3923997 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923996 _101005 t s x h1 h2) (@lem3923771 _101005 s x h1)). Qed.
Lemma lem3923998 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923987 _101005 t s x h1 h2) (fun h3 : False => @lem3923763 _101005 s x h1)). Qed.
Lemma lem3923999 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3923998 _101005 t s x h1 h2) (@lem3923763 _101005 s x h1)). Qed.
Lemma lem3924000 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923999 _101005 t s x h1 h2) (fun h3 : False => @lem3923759 _101005 s x h1)). Qed.
Lemma lem3924001 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924000 _101005 t s x h1 h2) (@lem3923759 _101005 s x h1)). Qed.
Lemma lem3924002 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3923991 _101005 t x h1 h2) (fun h3 : False => @lem3923751 _101005 t x h2)). Qed.
Lemma lem3924003 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3924002 _101005 t x h1 h2) (@lem3923751 _101005 t x h2)). Qed.
Lemma lem3924004 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : (term27 _101005 t x) = False.
Proof. exact (prop_ext (fun h3 : term27 _101005 t x => @lem3924003 _101005 t x h1 h2) (fun h3 : False => @lem3923747 _101005 t x h1)). Qed.
Lemma lem3924005 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3924004 _101005 t x h1 h2) (@lem3923747 _101005 t x h1)). Qed.
Lemma lem3924006 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923993 _101005 t s x h1 h2) (fun h3 : False => @lem3923739 _101005 s x h1)). Qed.
Lemma lem3924007 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924006 _101005 t s x h1 h2) (@lem3923739 _101005 s x h1)). Qed.
Lemma lem3924008 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923995 _101005 t s x h1 h2) (fun h3 : False => @lem3923787 _101005 s x h1)). Qed.
Lemma lem3924009 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term65 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924008 _101005 t s x h1 h2) (@lem3923787 _101005 s x h1)). Qed.
Lemma lem3924010 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3923997 _101005 t s x h1 h2) (fun h3 : False => @lem3923771 _101005 s x h1)). Qed.
Lemma lem3924011 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924010 _101005 t s x h1 h2) (@lem3923771 _101005 s x h1)). Qed.
Lemma lem3924012 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3924001 _101005 t s x h1 h2) (fun h3 : False => @lem3923763 _101005 s x h1)). Qed.
Lemma lem3924013 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924012 _101005 t s x h1 h2) (@lem3923763 _101005 s x h1)). Qed.
Lemma lem3924014 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3924013 _101005 t s x h1 h2) (fun h3 : False => @lem3923759 _101005 s x h1)). Qed.
Lemma lem3924015 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924014 _101005 t s x h1 h2) (@lem3923759 _101005 s x h1)). Qed.
Lemma lem3924016 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3924005 _101005 t x h1 h2) (fun h3 : False => @lem3923751 _101005 t x h2)). Qed.
Lemma lem3924017 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3924016 _101005 t x h1 h2) (@lem3923751 _101005 t x h2)). Qed.
Lemma lem3924018 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : (term27 _101005 t x) = False.
Proof. exact (prop_ext (fun h3 : term27 _101005 t x => @lem3924017 _101005 t x h1 h2) (fun h3 : False => @lem3923747 _101005 t x h1)). Qed.
Lemma lem3924019 {_101005 : Type'} (t : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3924018 _101005 t x h1 h2) (@lem3923747 _101005 t x h1)). Qed.
Lemma lem3924020 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3924007 _101005 t s x h1 h2) (fun h3 : False => @lem3923739 _101005 s x h1)). Qed.
Lemma lem3924021 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924020 _101005 t s x h1 h2) (@lem3923739 _101005 s x h1)). Qed.
Lemma lem3924022 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term65 _101005 t s x) : False.
Proof. exact (or_elim (@lem3923720 _101005 t s x h1) (fun h0 : s x => @lem3924009 _101005 t s x h0 h1) (fun h0 : term28 _101005 t s x => @lem3923979 _101005 t s x h0 h1)). Qed.
Lemma lem3924023 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : s x) (h2 : term68 _101005 t s x) : False.
Proof. exact (or_elim (@lem3923711 _101005 t s x h2) (fun h0 : s x => @lem3924015 _101005 t s x h1 h2) (fun h0 : t x => @lem3924011 _101005 t s x h1 h2)). Qed.
Lemma lem3924024 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term27 _101005 t x) (h2 : term68 _101005 t s x) : False.
Proof. exact (or_elim (@lem3923711 _101005 t s x h2) (fun h0 : s x => @lem3924021 _101005 t s x h0 h2) (fun h0 : t x => @lem3924019 _101005 t x h1 h0)). Qed.
Lemma lem3924025 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term68 _101005 t s x) : False.
Proof. exact (or_elim (@lem3923712 _101005 t s x h1) (fun h0 : term27 _101005 t x => @lem3924024 _101005 t s x h0 h1) (fun h0 : s x => @lem3924023 _101005 t s x h0 h1)). Qed.
Lemma lem3924026 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term50 _101005 t s x) : False.
Proof. exact (or_elim (@lem3923707 _101005 t s x h1) (fun h0 : term68 _101005 t s x => @lem3924025 _101005 t s x h0) (fun h0 : term65 _101005 t s x => @lem3924022 _101005 t s x h0)). Qed.
Lemma lem3924027 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term50 _101005 t s x) : (term50 _101005 t s x) = False.
Proof. exact (prop_ext (fun h2 : term50 _101005 t s x => @lem3924026 _101005 t s x h1) (fun h2 : False => @lem3923587 _101005 t s x h1)). Qed.
Lemma lem3924028 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) (h1 : term50 _101005 t s x) : False.
Proof. exact (EQ_MP (@lem3924027 _101005 t s x h1) (@lem3923587 _101005 t s x h1)). Qed.
Lemma lem3924029 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : term49 _101005 t s x.
Proof. exact (fun h0 : term50 _101005 t s x => @lem3924028 _101005 t s x h0). Qed.
Lemma lem3924030 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (x : _101005) : (term17 _101005 s t x) = (term29 _101005 t s x).
Proof. exact (EQ_MP (@lem3923586 _101005 t s x) (@lem3924029 _101005 t s x)). Qed.
Lemma lem3924035 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term32 _101005 t s.
Proof. exact (fun x : _101005 => @lem3924030 _101005 t s x). Qed.
Lemma lem3924040 {_101005 : Type'} (s : _101005 -> Prop) : term44 _101005 s.
Proof. exact (fun t : _101005 -> Prop => @lem3924035 _101005 t s). Qed.
Lemma lem3924045 {_101005 : Type'} : term48 _101005.
Proof. exact (fun s : _101005 -> Prop => @lem3924040 _101005 s). Qed.
Lemma lem3924046 {_101005 : Type'} : term47 _101005.
Proof. exact (EQ_MP (@lem3923582 _101005) (@lem3924045 _101005)). Qed.
Lemma lem3924047 {_101005 : Type'} (s : _101005 -> Prop) : term77 _101005 s.
Proof. exact (@lem3924046 _101005 s). Qed.
Lemma lem3924048 {_101005 : Type'} (s : _101005 -> Prop) : (term77 _101005 s) = (term43 _101005 s).
Proof. exact (eq_refl (term77 _101005 s)). Qed.
Lemma lem3924049 {_101005 : Type'} (s : _101005 -> Prop) : term43 _101005 s.
Proof. exact (EQ_MP (@lem3924048 _101005 s) (@lem3924047 _101005 s)). Qed.
Lemma lem3924050 {_101005 : Type'} (s : _101005 -> Prop) (t : _101005 -> Prop) : term78 _101005 s t.
Proof. exact (@lem3924049 _101005 s t). Qed.
Lemma lem3924051 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (term78 _101005 s t) = (term34 _101005 t s).
Proof. exact (eq_refl (term78 _101005 s t)). Qed.
Lemma lem3924052 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term34 _101005 t s.
Proof. exact (EQ_MP (@lem3924051 _101005 t s) (@lem3924050 _101005 s t)). Qed.
Lemma lem3924054 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term34 _101005 t s.
Proof. exact (@lem3923483 _101005 t s (@lem3924052 _101005 t s)). Qed.
Lemma lem3924055 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term35 _101005 t s) : False.
Proof. exact (@lem3924054 _101005 t s (@lem3923467 _101005 t s h1)). Qed.
Lemma lem3924056 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term35 _101005 t s) : (term35 _101005 t s) = False.
Proof. exact (prop_ext (fun h2 : term35 _101005 t s => @lem3924055 _101005 t s h1) (fun h2 : False => @lem3923467 _101005 t s h1)). Qed.
Lemma lem3924057 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) (h1 : term35 _101005 t s) : False.
Proof. exact (EQ_MP (@lem3924056 _101005 t s h1) (@lem3923467 _101005 t s h1)). Qed.
Lemma lem3924058 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term34 _101005 t s.
Proof. exact (fun h0 : term35 _101005 t s => @lem3924057 _101005 t s h0). Qed.
Lemma lem3924059 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term32 _101005 t s.
Proof. exact (EQ_MP (@lem3923466 _101005 t s) (@lem3924058 _101005 t s)). Qed.
Lemma lem3924060 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : term12 _101005 t s.
Proof. exact (EQ_MP (@lem3923462 _101005 t s) (@lem3924059 _101005 t s)). Qed.
Lemma lem3924062 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem3924063 (m : nat) (h1 : term79) : term80 m.
Proof. exact (@lem3924062 h1 m). Qed.
Lemma lem3924064 (m : nat) : (term80 m) = (term81 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem3924065 (m : nat) (h1 : term79) : term81 m.
Proof. exact (EQ_MP (@lem3924064 m) (@lem3924063 m h1)). Qed.
Lemma lem3924066 (m : nat) (n : nat) (h1 : term79) : term82 m n.
Proof. exact (@lem3924065 m h1 n). Qed.
Lemma lem3924067 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem3924068 (m : nat) (n : nat) (h1 : term79) : term83 m n.
Proof. exact (EQ_MP (@lem3924067 m n) (@lem3924066 m n h1)). Qed.
Lemma lem3924069 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem3924070 (m : nat) (n : nat) (h1 : term79) (h2 : m = n) : Peano.le m n.
Proof. exact (@lem3924068 m n h1 (@lem3924069 m n h2)). Qed.
Lemma lem3924071 (m : nat) (n : nat) (h1 : m = n) : term84 m n.
Proof. exact (fun h0 : term79 => @lem3924070 m n h0 h1). Qed.
Lemma lem3924072 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem3924073 (m : nat) (n : nat) (h1 : term79) (h2 : m = n) : Peano.le m n.
Proof. exact (@lem3924071 m n h2 (@lem3924072 h1)). Qed.
Lemma lem3924074 (m : nat) (n : nat) (h1 : term79) : term83 m n.
Proof. exact (fun h0 : m = n => @lem3924073 m n h1 h0). Qed.
Lemma lem3924075 (m : nat) (h1 : term79) : term81 m.
Proof. exact (fun n : nat => @lem3924074 m n h1). Qed.
Lemma lem3924076 (h1 : term79) : term79.
Proof. exact (fun m : nat => @lem3924075 m h1). Qed.
Lemma lem3924077 : term85.
Proof. exact (fun h0 : term79 => @lem3924076 h0). Qed.
Lemma lem3924078 : term79.
Proof. exact (@lem3924077 (@lem98471)). Qed.
Lemma lem3924079 (m : nat) : term80 m.
Proof. exact (@lem3924078 m). Qed.
Lemma lem3924080 (m : nat) : (term80 m) = (term81 m).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem3924081 (m : nat) : term81 m.
Proof. exact (EQ_MP (@lem3924080 m) (@lem3924079 m)). Qed.
Lemma lem3924082 (m : nat) (n : nat) : term82 m n.
Proof. exact (@lem3924081 m n). Qed.
Lemma lem3924083 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem3924085 (h1 : term86) : term86.
Proof. exact (h1). Qed.
Lemma lem3924086 (m : nat) (h1 : term86) : term87 m.
Proof. exact (@lem3924085 h1 m). Qed.
Lemma lem3924087 (m : nat) : (term87 m) = (term88 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem3924088 (m : nat) (h1 : term86) : term88 m.
Proof. exact (EQ_MP (@lem3924087 m) (@lem3924086 m h1)). Qed.
Lemma lem3924089 (m : nat) (n : nat) (h1 : term86) : term89 m n.
Proof. exact (@lem3924088 m h1 n). Qed.
Lemma lem3924090 (n : nat) (m : nat) : (term89 m n) = (term90 n m).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem3924091 (n : nat) (m : nat) (h1 : term86) : term90 n m.
Proof. exact (EQ_MP (@lem3924090 n m) (@lem3924089 m n h1)). Qed.
Lemma lem3924092 (n : nat) (m : nat) (p : nat) (h1 : term86) : term91 n m p.
Proof. exact (@lem3924091 n m h1 p). Qed.
Lemma lem3924093 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term92 n m p).
Proof. exact (eq_refl (term91 n m p)). Qed.
Lemma lem3924094 (n : nat) (m : nat) (p : nat) (h1 : term86) : term92 n m p.
Proof. exact (EQ_MP (@lem3924093 n m p) (@lem3924092 n m p h1)). Qed.
Lemma lem3924095 (m : nat) (n : nat) (p : nat) (h1 : term93 m n p) : term93 m n p.
Proof. exact (h1). Qed.
Lemma lem3924096 (m : nat) (n : nat) (p : nat) (h1 : term86) (h2 : term93 m n p) : Peano.le m p.
Proof. exact (@lem3924094 n m p h1 (@lem3924095 m n p h2)). Qed.
Lemma lem3924097 (m : nat) (n : nat) (p : nat) (h1 : term93 m n p) : term94 m p.
Proof. exact (fun h0 : term86 => @lem3924096 m n p h0 h1). Qed.
Lemma lem3924098 (m : nat) (p : nat) (h1 : term95 m p) : term95 m p.
Proof. exact (h1). Qed.
Lemma lem3924099 (m : nat) (p : nat) (h1 : term95 m p) : term94 m p.
Proof. exact (ex_elim (@lem3924098 m p h1) (fun n : nat => fun h0 : term96 m p n => @lem3924097 m n p h0)). Qed.
Lemma lem3924100 (h1 : term86) : term86.
Proof. exact (h1). Qed.
Lemma lem3924101 (m : nat) (p : nat) (h1 : term86) (h2 : term95 m p) : Peano.le m p.
Proof. exact (@lem3924099 m p h2 (@lem3924100 h1)). Qed.
Lemma lem3924102 (m : nat) (p : nat) (h1 : term86) : term97 m p.
Proof. exact (fun h0 : term95 m p => @lem3924101 m p h1 h0). Qed.
Lemma lem3924103 (m : nat) (h1 : term86) : term98 m.
Proof. exact (fun p : nat => @lem3924102 m p h1). Qed.
Lemma lem3924104 (h1 : term86) : term99.
Proof. exact (fun m : nat => @lem3924103 m h1). Qed.
Lemma lem3924105 : term100.
Proof. exact (fun h0 : term86 => @lem3924104 h0). Qed.
Lemma lem3924106 : term99.
Proof. exact (@lem3924105 (@lem93743)). Qed.
Lemma lem3924107 (m : nat) : term101 m.
Proof. exact (@lem3924106 m). Qed.
Lemma lem3924108 (m : nat) : (term101 m) = (term98 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem3924109 (m : nat) : term98 m.
Proof. exact (EQ_MP (@lem3924108 m) (@lem3924107 m)). Qed.
Lemma lem3924110 (m : nat) (p : nat) : term102 m p.
Proof. exact (@lem3924109 m p). Qed.
Lemma lem3924111 (m : nat) (p : nat) : (term102 m p) = (term97 m p).
Proof. exact (eq_refl (term102 m p)). Qed.
Lemma lem3924113 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term103 A s t) : term103 A s t.
Proof. exact (h1). Qed.
Lemma lem3924114 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem3924115 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3924117 (m : nat) (p : nat) : term97 m p.
Proof. exact (EQ_MP (@lem3924111 m p) (@lem3924110 m p)). Qed.
Lemma lem3924118 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term104 A s t.
Proof. exact (@lem3924117 (term6 A s t) (term7 A s t)). Qed.
Lemma lem3924134 {_85745 : Type'} (s : _85745 -> Prop) : term105 _85745 s.
Proof. exact (@lem3270702 _85745 s). Qed.
Lemma lem3924135 {_85745 : Type'} (s : _85745 -> Prop) : (term105 _85745 s) = (term106 _85745 s).
Proof. exact (eq_refl (term105 _85745 s)). Qed.
Lemma lem3924136 {_85745 : Type'} (s : _85745 -> Prop) : term106 _85745 s.
Proof. exact (EQ_MP (@lem3924135 _85745 s) (@lem3924134 _85745 s)). Qed.
Lemma lem3924137 {_85745 : Type'} (s : _85745 -> Prop) (t : _85745 -> Prop) : term107 _85745 s t.
Proof. exact (@lem3924136 _85745 s t). Qed.
Lemma lem3924138 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term107 _85745 s t) = (term108 _85745 t s).
Proof. exact (eq_refl (term107 _85745 s t)). Qed.
Lemma lem3924139 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : term108 _85745 t s.
Proof. exact (EQ_MP (@lem3924138 _85745 t s) (@lem3924137 _85745 s t)). Qed.
Lemma lem3924140 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term108 _85745 t s) = ((term108 _85745 t s) = True).
Proof. exact (@lem7 (term108 _85745 t s)). Qed.
Lemma lem3924142 {A : Type'} (a : A -> Prop) : term109 A a.
Proof. exact (@lem3902682 A a). Qed.
Lemma lem3924143 {A : Type'} (a : A -> Prop) : (term109 A a) = (term110 A a).
Proof. exact (eq_refl (term109 A a)). Qed.
Lemma lem3924144 {A : Type'} (a : A -> Prop) : term110 A a.
Proof. exact (EQ_MP (@lem3924143 A a) (@lem3924142 A a)). Qed.
Lemma lem3924145 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term111 A a b.
Proof. exact (@lem3924144 A a b). Qed.
Lemma lem3924146 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term111 A a b) = (term112 A a b).
Proof. exact (eq_refl (term111 A a b)). Qed.
Lemma lem3924147 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term112 A a b.
Proof. exact (EQ_MP (@lem3924146 A a b) (@lem3924145 A a b)). Qed.
Lemma lem3924148 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term113 A a b) : term113 A a b.
Proof. exact (h1). Qed.
Lemma lem3924149 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term113 A a b) : term114 A a b.
Proof. exact (@lem3924147 A a b (@lem3924148 A a b h1)). Qed.
Lemma lem3924150 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term114 A a b) = ((term114 A a b) = True).
Proof. exact (@lem7 (term114 A a b)). Qed.
Lemma lem3924151 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term113 A a b) : (term114 A a b) = True.
Proof. exact (EQ_MP (@lem3924150 A a b) (@lem3924149 A a b h1)). Qed.
Lemma lem3924157 (m : nat) : term115 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem3924158 (m : nat) : (term115 m) = (term116 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem3924159 (m : nat) : term116 m.
Proof. exact (EQ_MP (@lem3924158 m) (@lem3924157 m)). Qed.
Lemma lem3924160 (m : nat) (n : nat) : term117 m n.
Proof. exact (@lem3924159 m n). Qed.
Lemma lem3924161 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (eq_refl (term117 m n)). Qed.
Lemma lem3924162 (m : nat) (n : nat) : term118 m n.
Proof. exact (EQ_MP (@lem3924161 m n) (@lem3924160 m n)). Qed.
Lemma lem3924163 (m : nat) (n : nat) (p : nat) : term119 m n p.
Proof. exact (@lem3924162 m n p). Qed.
Lemma lem3924164 (m : nat) (n : nat) (p : nat) : (term119 m n p) = ((term120 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term119 m n p)). Qed.
Lemma lem3924168 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem3924173 (m : nat) (n : nat) (p : nat) : (term120 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem3924164 m n p) (@lem3924163 m n p)). Qed.
Lemma lem3924174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term121 A s t) = (term122 A s t).
Proof. exact (@lem3924173 (@CARD A s) (term123 A t s) (@CARD A t)). Qed.
Lemma lem3924176 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term124 A a b.
Proof. exact (fun h0 : term113 A a b => @lem3924151 A a b h0). Qed.
Lemma lem3924177 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term124 A a b.
Proof. exact (@lem3924176 A a b). Qed.
Lemma lem3924178 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term125 A s t.
Proof. exact (@lem3924177 A (@DIFF A t s) t). Qed.
Lemma lem3924182 {_85745 : Type'} (t : _85745 -> Prop) (s : _85745 -> Prop) : (term108 _85745 t s) = True.
Proof. exact (EQ_MP (@lem3924140 _85745 t s) (@lem3924139 _85745 t s)). Qed.
Lemma lem3924183 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term108 A t s) = True.
Proof. exact (@lem3924182 A t s). Qed.
Lemma lem3924184 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = True.
Proof. exact (@lem3924183 A s t). Qed.
Lemma lem3924185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3924186 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (and True).
Proof. exact (MK_COMB (@lem3924185) (@lem3924184 A s t)). Qed.
Lemma lem3924188 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem3924168 A t) (@lem3924114 A t h1)). Qed.
Lemma lem3924189 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term127 A s t) = (True /\ True).
Proof. exact (MK_COMB (@lem3924186 A s t) (@lem3924188 A t h1)). Qed.
Lemma lem3924191 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3924192 : (True /\ True) = True.
Proof. exact (@lem3924191 True). Qed.
Lemma lem3924193 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term127 A s t) = True.
Proof. exact (TRANS (@lem3924189 A s t h1) (@lem3924192)). Qed.
Lemma lem3924194 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : True = (term127 A s t).
Proof. exact (SYM (@lem3924193 A s t h1)). Qed.
Lemma lem3924195 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : term127 A s t.
Proof. exact (EQ_MP (@lem3924194 A s t h1) (@lem0)). Qed.
Lemma lem3924196 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term122 A s t) = True.
Proof. exact (@lem3924178 A s t (@lem3924195 A s t h1)). Qed.
Lemma lem3924197 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term121 A s t) = True.
Proof. exact (TRANS (@lem3924174 A s t) (@lem3924196 A s t h1)). Qed.
Lemma lem3924198 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term128 A t s) = (term128 A t s).
Proof. exact (eq_refl (term128 A t s)). Qed.
Lemma lem3924199 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term129 A s t) = (term130 A t s).
Proof. exact (MK_COMB (@lem3924198 A t s) (@lem3924197 A s t h1)). Qed.
Lemma lem3924201 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3924202 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term130 A t s) = (term131 A t s).
Proof. exact (@lem3924201 (term131 A t s)). Qed.
Lemma lem3924203 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term129 A s t) = (term131 A t s).
Proof. exact (TRANS (@lem3924199 A s t h1) (@lem3924202 A t s)). Qed.
Lemma lem3924204 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term131 A t s) = (term129 A s t).
Proof. exact (SYM (@lem3924203 A s t h1)). Qed.
Lemma lem3924206 (m : nat) (n : nat) : term83 m n.
Proof. exact (EQ_MP (@lem3924083 m n) (@lem3924082 m n)). Qed.
Lemma lem3924207 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term132 A t s.
Proof. exact (@lem3924206 (term6 A s t) (term133 A t s)). Qed.
Lemma lem3924211 {_101005 : Type'} (t : _101005 -> Prop) (s : _101005 -> Prop) : (@UNION _101005 s t) = (term11 _101005 t s).
Proof. exact (EQ_MP (@lem3923386 _101005 t s) (@lem3924060 _101005 t s)). Qed.
Lemma lem3924212 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@UNION A s t) = (term11 A t s).
Proof. exact (@lem3924211 A t s). Qed.
Lemma lem3924213 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3924214 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term6 A s t) = (term134 A t s).
Proof. exact (MK_COMB (@lem3924213 A) (@lem3924212 A t s)). Qed.
Lemma lem3924215 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3924216 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term135 A s t) = (term136 A t s).
Proof. exact (MK_COMB (@lem3924215) (@lem3924214 A t s)). Qed.
Lemma lem3924217 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term133 A t s) = (term133 A t s).
Proof. exact (eq_refl (term133 A t s)). Qed.
Lemma lem3924218 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term6 A s t) = (term133 A t s)) = ((term134 A t s) = (term133 A t s)).
Proof. exact (MK_COMB (@lem3924216 A t s) (@lem3924217 A t s)). Qed.
Lemma lem3924219 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term134 A t s) = (term133 A t s)) = ((term6 A s t) = (term133 A t s)).
Proof. exact (SYM (@lem3924218 A t s)). Qed.
Lemma lem3924221 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term4 A s t.
Proof. exact (EQ_MP (@lem3923360 A s t) (@lem3923359 A s t)). Qed.
Lemma lem3924222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term4 A s t.
Proof. exact (@lem3924221 A s t). Qed.
Lemma lem3924223 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term137 A t s.
Proof. exact (@lem3924222 A s (@DIFF A t s)). Qed.
Lemma lem3924224 {_97970 : Type'} (s : _97970 -> Prop) : term138 _97970 s.
Proof. exact (@lem3734933 _97970 s). Qed.
Lemma lem3924225 {_97970 : Type'} (s : _97970 -> Prop) : (term138 _97970 s) = (term139 _97970 s).
Proof. exact (eq_refl (term138 _97970 s)). Qed.
Lemma lem3924226 {_97970 : Type'} (s : _97970 -> Prop) : term139 _97970 s.
Proof. exact (EQ_MP (@lem3924225 _97970 s) (@lem3924224 _97970 s)). Qed.
Lemma lem3924227 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term140 _97970 s t.
Proof. exact (@lem3924226 _97970 s t). Qed.
Lemma lem3924228 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term140 _97970 s t) = (term141 _97970 s t).
Proof. exact (eq_refl (term140 _97970 s t)). Qed.
Lemma lem3924229 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term141 _97970 s t.
Proof. exact (EQ_MP (@lem3924228 _97970 s t) (@lem3924227 _97970 s t)). Qed.
Lemma lem3924230 {_97970 : Type'} (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : @FINITE _97970 s.
Proof. exact (h1). Qed.
Lemma lem3924231 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : term142 _97970 s t.
Proof. exact (@lem3924229 _97970 s t (@lem3924230 _97970 s h1)). Qed.
Lemma lem3924232 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term142 _97970 s t) = ((term142 _97970 s t) = True).
Proof. exact (@lem7 (term142 _97970 s t)). Qed.
Lemma lem3924233 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : (term142 _97970 s t) = True.
Proof. exact (EQ_MP (@lem3924232 _97970 s t) (@lem3924231 _97970 t s h1)). Qed.
Lemma lem3924239 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3924241 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem3924246 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3924239 A s) (@lem3924115 A s h1)). Qed.
Lemma lem3924247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3924248 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term143 A s) = (and True).
Proof. exact (MK_COMB (@lem3924247) (@lem3924246 A s h1)). Qed.
Lemma lem3924252 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term144 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem3924233 _97970 t s h0). Qed.
Lemma lem3924253 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term144 A s t.
Proof. exact (@lem3924252 A s t). Qed.
Lemma lem3924254 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term144 A t s.
Proof. exact (@lem3924253 A t s). Qed.
Lemma lem3924256 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem3924241 A t) (@lem3924114 A t h1)). Qed.
Lemma lem3924257 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : True = (@FINITE A t).
Proof. exact (SYM (@lem3924256 A t h1)). Qed.
Lemma lem3924258 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (EQ_MP (@lem3924257 A t h1) (@lem0)). Qed.
Lemma lem3924259 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term142 A t s) = True.
Proof. exact (@lem3924254 A t s (@lem3924258 A t h1)). Qed.
Lemma lem3924260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3924261 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term145 A t s) = (and True).
Proof. exact (MK_COMB (@lem3924260) (@lem3924259 A s t h1)). Qed.
Lemma lem3924264 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term146 A t s) = (@EMPTY A)) = ((term146 A t s) = (@EMPTY A)).
Proof. exact (eq_refl ((term146 A t s) = (@EMPTY A))). Qed.
Lemma lem3924265 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term147 A t s) = (term148 A t s).
Proof. exact (MK_COMB (@lem3924261 A s t h1) (@lem3924264 A t s)). Qed.
Lemma lem3924267 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3924268 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term148 A t s) = ((term146 A t s) = (@EMPTY A)).
Proof. exact (@lem3924267 ((term146 A t s) = (@EMPTY A))). Qed.
Lemma lem3924271 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term147 A t s) = ((term146 A t s) = (@EMPTY A)).
Proof. exact (TRANS (@lem3924265 A s t h1) (@lem3924268 A t s)). Qed.
Lemma lem3924272 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term149 A t s) = (term148 A t s).
Proof. exact (MK_COMB (@lem3924248 A s h1) (@lem3924271 A s t h2)). Qed.
Lemma lem3924274 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3924275 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term148 A t s) = ((term146 A t s) = (@EMPTY A)).
Proof. exact (@lem3924274 ((term146 A t s) = (@EMPTY A))). Qed.
Lemma lem3924278 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term149 A t s) = ((term146 A t s) = (@EMPTY A)).
Proof. exact (TRANS (@lem3924272 A s t h1 h2) (@lem3924275 A t s)). Qed.
Lemma lem3924279 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : ((term146 A t s) = (@EMPTY A)) = (term149 A t s).
Proof. exact (SYM (@lem3924278 A s t h1 h2)). Qed.
Lemma lem3924283 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3924284 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term10 A s t).
Proof. exact (@lem3924283 A s t). Qed.
Lemma lem3924285 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term146 A t s) = (@EMPTY A)) = (term150 A t s).
Proof. exact (@lem3924284 A (term146 A t s) (@EMPTY A)). Qed.
Lemma lem3924294 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term150 A t s) = ((term146 A t s) = (@EMPTY A)).
Proof. exact (SYM (@lem3924285 A t s)). Qed.
Lemma lem3924302 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term151 A x s t) = (term152 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3924303 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term151 A x s t) = (term152 A s x t).
Proof. exact (@lem3924302 A s x t). Qed.
Lemma lem3924304 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term153 A x t s) = (term154 A x t s).
Proof. exact (@lem3924303 A s x (@DIFF A t s)). Qed.
Lemma lem3924308 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3924309 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3924308 A P x). Qed.
Lemma lem3924310 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3924309 A s x). Qed.
Lemma lem3924311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3924312 {A : Type'} (s : A -> Prop) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (MK_COMB (@lem3924311) (@lem3924310 A s x)). Qed.
Lemma lem3924314 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3924315 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (@lem3924314 A s x t). Qed.
Lemma lem3924316 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term22 A x t s) = (term23 A t x s).
Proof. exact (@lem3924315 A t x s). Qed.
Lemma lem3924320 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3924321 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3924320 A P x). Qed.
Lemma lem3924322 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3924321 A t x). Qed.
Lemma lem3924323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3924324 {A : Type'} (t : A -> Prop) (x : A) : (term24 A x t) = (term25 A t x).
Proof. exact (MK_COMB (@lem3924323) (@lem3924322 A t x)). Qed.
Lemma lem3924326 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3924327 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3924326 A P x). Qed.
Lemma lem3924328 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3924327 A s x). Qed.
Lemma lem3924329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3924330 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3924329) (@lem3924328 A s x)). Qed.
Lemma lem3924331 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term23 A t x s) = (term28 A t s x).
Proof. exact (MK_COMB (@lem3924324 A t x) (@lem3924330 A s x)). Qed.
Lemma lem3924334 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term22 A x t s) = (term28 A t s x).
Proof. exact (TRANS (@lem3924316 A t x s) (@lem3924331 A t s x)). Qed.
Lemma lem3924335 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term154 A x t s) = (term155 A t s x).
Proof. exact (MK_COMB (@lem3924312 A s x) (@lem3924334 A t s x)). Qed.
Lemma lem3924338 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term153 A x t s) = (term155 A t s x).
Proof. exact (TRANS (@lem3924304 A x t s) (@lem3924335 A t s x)). Qed.
Lemma lem3924339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3924340 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term156 A x t s) = (term157 A t s x).
Proof. exact (MK_COMB (@lem3924339) (@lem3924338 A t s x)). Qed.
Lemma lem3924342 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3924343 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3924342 A x). Qed.
Lemma lem3924344 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term153 A x t s) = (@IN A x (@EMPTY A))) = ((term155 A t s x) = False).
Proof. exact (MK_COMB (@lem3924340 A t s x) (@lem3924343 A x)). Qed.
Lemma lem3924346 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3924347 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term155 A t s x) = False) = (term158 A t s x).
Proof. exact (@lem3924346 (term155 A t s x)). Qed.
Lemma lem3924352 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term153 A x t s) = (@IN A x (@EMPTY A))) = (term158 A t s x).
Proof. exact (TRANS (@lem3924344 A t s x) (@lem3924347 A t s x)). Qed.
Lemma lem3924353 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term159 A t s) = (term160 A t s).
Proof. exact (fun_ext (fun x : A => @lem3924352 A t s x)). Qed.
Lemma lem3924354 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3924355 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term150 A t s) = (term161 A t s).
Proof. exact (MK_COMB (@lem3924354 A) (@lem3924353 A t s)). Qed.
Lemma lem3924360 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term161 A t s) = (term150 A t s).
Proof. exact (SYM (@lem3924355 A t s)). Qed.
Lemma lem3924362 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3924363 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term161 A t s) = (term162 A t s).
Proof. exact (@lem3924362 (term161 A t s)). Qed.
Lemma lem3924364 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term162 A t s) = (term161 A t s).
Proof. exact (SYM (@lem3924363 A t s)). Qed.
Lemma lem3924365 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term163 A t s) : term163 A t s.
Proof. exact (h1). Qed.
Lemma lem3924368 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term162 A t s) : term162 A t s.
Proof. exact (h1). Qed.
Lemma lem3924369 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term164 A t s.
Proof. exact (fun h0 : term162 A t s => @lem3924368 A t s h0). Qed.
Lemma lem3924370 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term164 A t s) : term164 A t s.
Proof. exact (h1). Qed.
Lemma lem3924371 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term162 A t s) : term162 A t s.
Proof. exact (h1). Qed.
Lemma lem3924372 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term162 A t s) (h2 : term164 A t s) : term162 A t s.
Proof. exact (@lem3924370 A t s h2 (@lem3924371 A t s h1)). Qed.
Lemma lem3924373 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term162 A t s) : term165 A t s.
Proof. exact (fun h0 : term164 A t s => @lem3924372 A t s h1 h0). Qed.
Lemma lem3924374 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term164 A t s) : term164 A t s.
Proof. exact (h1). Qed.
Lemma lem3924375 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term162 A t s) (h2 : term164 A t s) : term162 A t s.
Proof. exact (@lem3924373 A t s h1 (@lem3924374 A t s h2)). Qed.
Lemma lem3924376 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term164 A t s) : term164 A t s.
Proof. exact (fun h0 : term162 A t s => @lem3924375 A t s h0 h1). Qed.
Lemma lem3924377 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term166 A t s.
Proof. exact (fun h0 : term164 A t s => @lem3924376 A t s h0). Qed.
Lemma lem3924380 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term164 A t s.
Proof. exact (@lem3924377 A t s (@lem3924369 A t s)). Qed.
Lemma lem3924381 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term164 A t s.
Proof. exact (@lem3924380 A t s). Qed.
Lemma lem3924391 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3924392 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term162 A t s) = (term167 A t s).
Proof. exact (@lem3924391 (term163 A t s)). Qed.
Lemma lem3924394 (t : Prop) : (term40 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3924395 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term167 A t s) = (term161 A t s).
Proof. exact (@lem3924394 (term161 A t s)). Qed.
Lemma lem3924400 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term162 A t s) = (term161 A t s).
Proof. exact (TRANS (@lem3924392 A t s) (@lem3924395 A t s)). Qed.
Lemma lem3924405 {A : Type'} (s : A -> Prop) : (term168 A s) = (term169 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3924400 A t s)). Qed.
Lemma lem3924406 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924407 {A : Type'} (s : A -> Prop) : (term170 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem3924406 A) (@lem3924405 A s)). Qed.
Lemma lem3924412 {A : Type'} : (term172 A) = (term173 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3924407 A s)). Qed.
Lemma lem3924413 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924422 {A : Type'} : (term174 A) = (term175 A).
Proof. exact (MK_COMB (@lem3924413 A) (@lem3924412 A)). Qed.
Lemma lem3924435 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term158 A t s x) = (term158 A t s x).
Proof. exact (eq_refl (term158 A t s x)). Qed.
Lemma lem3924436 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term160 A t s) = (term160 A t s).
Proof. exact (fun_ext (fun x : A => @lem3924435 A t s x)). Qed.
Lemma lem3924437 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3924438 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term161 A t s) = (term161 A t s).
Proof. exact (MK_COMB (@lem3924437 A) (@lem3924436 A t s)). Qed.
Lemma lem3924439 {A : Type'} (s : A -> Prop) : (term169 A s) = (term169 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3924438 A t s)). Qed.
Lemma lem3924440 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924441 {A : Type'} (s : A -> Prop) : (term171 A s) = (term171 A s).
Proof. exact (MK_COMB (@lem3924440 A) (@lem3924439 A s)). Qed.
Lemma lem3924442 {A : Type'} : (term173 A) = (term173 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3924441 A s)). Qed.
Lemma lem3924443 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3924444 {A : Type'} : (term175 A) = (term175 A).
Proof. exact (MK_COMB (@lem3924443 A) (@lem3924442 A)). Qed.
Lemma lem3924469 {A : Type'} : (term174 A) = (term175 A).
Proof. exact (TRANS (@lem3924422 A) (@lem3924444 A)). Qed.
Lemma lem3924470 {A : Type'} : (term175 A) = (term174 A).
Proof. exact (SYM (@lem3924469 A)). Qed.
Lemma lem3924485 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : term155 A t s x.
Proof. exact (h1). Qed.
Lemma lem3924503 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : term155 A t s x.
Proof. exact (h1). Qed.
Lemma lem3924504 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : term28 A t s x.
Proof. exact (proj2 (@lem3924503 A t s x h1)). Qed.
Lemma lem3924525 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : term27 A s x.
Proof. exact (proj2 (@lem3924504 A t s x h1)). Qed.
Lemma lem3924527 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : s x.
Proof. exact (proj1 (@lem3924503 A t s x h1)). Qed.
Lemma lem3924528 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : term73 A s x.
Proof. exact (fun h0 : term27 A s x => @lem3924527 A t s x h1). Qed.
Lemma lem3924530 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3924531 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = (s x).
Proof. exact (@lem3924530 (s x)). Qed.
Lemma lem3924532 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : s x.
Proof. exact (EQ_MP (@lem3924531 A s x) (@lem3924528 A t s x h1)). Qed.
Lemma lem3924535 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3924537 {A : Type'} (s : A -> Prop) (x : A) : (term27 A s x) = (term75 A s x).
Proof. exact (@lem3924535 (s x)). Qed.
Lemma lem3924540 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : term75 A s x.
Proof. exact (EQ_MP (@lem3924537 A s x) (@lem3924525 A t s x h1)). Qed.
Lemma lem3924543 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : False.
Proof. exact (@lem3924540 A t s x h1 (@lem3924532 A t s x h1)). Qed.
Lemma lem3924544 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : term76.
Proof. exact (fun h0 : ~ False => @lem3924543 A t s x h1). Qed.
Lemma lem3924546 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3924547 : term76 = False.
Proof. exact (@lem3924546 False). Qed.
Lemma lem3924548 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : False.
Proof. exact (EQ_MP (@lem3924547) (@lem3924544 A t s x h1)). Qed.
Lemma lem3924549 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : (term155 A t s x) = False.
Proof. exact (prop_ext (fun h2 : term155 A t s x => @lem3924548 A t s x h1) (fun h2 : False => @lem3924503 A t s x h1)). Qed.
Lemma lem3924550 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : False.
Proof. exact (EQ_MP (@lem3924549 A t s x h1) (@lem3924503 A t s x h1)). Qed.
Lemma lem3924551 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : (term155 A t s x) = False.
Proof. exact (prop_ext (fun h2 : term155 A t s x => @lem3924550 A t s x h1) (fun h2 : False => @lem3924485 A t s x h1)). Qed.
Lemma lem3924552 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term155 A t s x) : False.
Proof. exact (EQ_MP (@lem3924551 A t s x h1) (@lem3924485 A t s x h1)). Qed.
Lemma lem3924553 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : term176 A t s x.
Proof. exact (fun h0 : term155 A t s x => @lem3924552 A t s x h0). Qed.
Lemma lem3924554 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term176 A t s x) = (term158 A t s x).
Proof. exact (@lem69 (term155 A t s x)). Qed.
Lemma lem3924555 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : term158 A t s x.
Proof. exact (EQ_MP (@lem3924554 A t s x) (@lem3924553 A t s x)). Qed.
Lemma lem3924560 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term161 A t s.
Proof. exact (fun x : A => @lem3924555 A t s x). Qed.
Lemma lem3924565 {A : Type'} (s : A -> Prop) : term171 A s.
Proof. exact (fun t : A -> Prop => @lem3924560 A t s). Qed.
Lemma lem3924570 {A : Type'} : term175 A.
Proof. exact (fun s : A -> Prop => @lem3924565 A s). Qed.
Lemma lem3924571 {A : Type'} : term174 A.
Proof. exact (EQ_MP (@lem3924470 A) (@lem3924570 A)). Qed.
Lemma lem3924572 {A : Type'} (s : A -> Prop) : term177 A s.
Proof. exact (@lem3924571 A s). Qed.
Lemma lem3924573 {A : Type'} (s : A -> Prop) : (term177 A s) = (term170 A s).
Proof. exact (eq_refl (term177 A s)). Qed.
Lemma lem3924574 {A : Type'} (s : A -> Prop) : term170 A s.
Proof. exact (EQ_MP (@lem3924573 A s) (@lem3924572 A s)). Qed.
Lemma lem3924575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term178 A s t.
Proof. exact (@lem3924574 A s t). Qed.
Lemma lem3924576 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term178 A s t) = (term162 A t s).
Proof. exact (eq_refl (term178 A s t)). Qed.
Lemma lem3924577 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term162 A t s.
Proof. exact (EQ_MP (@lem3924576 A t s) (@lem3924575 A s t)). Qed.
Lemma lem3924579 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term162 A t s.
Proof. exact (@lem3924381 A t s (@lem3924577 A t s)). Qed.
Lemma lem3924580 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term163 A t s) : False.
Proof. exact (@lem3924579 A t s (@lem3924365 A t s h1)). Qed.
Lemma lem3924581 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term163 A t s) : (term163 A t s) = False.
Proof. exact (prop_ext (fun h2 : term163 A t s => @lem3924580 A t s h1) (fun h2 : False => @lem3924365 A t s h1)). Qed.
Lemma lem3924582 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term163 A t s) : False.
Proof. exact (EQ_MP (@lem3924581 A t s h1) (@lem3924365 A t s h1)). Qed.
Lemma lem3924583 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term162 A t s.
Proof. exact (fun h0 : term163 A t s => @lem3924582 A t s h0). Qed.
Lemma lem3924584 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term161 A t s.
Proof. exact (EQ_MP (@lem3924364 A t s) (@lem3924583 A t s)). Qed.
Lemma lem3924585 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term150 A t s.
Proof. exact (EQ_MP (@lem3924360 A t s) (@lem3924584 A t s)). Qed.
Lemma lem3924586 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term146 A t s) = (@EMPTY A).
Proof. exact (EQ_MP (@lem3924294 A t s) (@lem3924585 A t s)). Qed.
Lemma lem3924587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term149 A t s.
Proof. exact (EQ_MP (@lem3924279 A s t h1 h2) (@lem3924586 A t s)). Qed.
Lemma lem3924588 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term134 A t s) = (term133 A t s).
Proof. exact (@lem3924223 A t s (@lem3924587 A s t h1 h2)). Qed.
Lemma lem3924589 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term6 A s t) = (term133 A t s).
Proof. exact (EQ_MP (@lem3924219 A t s) (@lem3924588 A s t h1 h2)). Qed.
Lemma lem3924590 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term131 A t s.
Proof. exact (@lem3924207 A t s (@lem3924589 A s t h1 h2)). Qed.
Lemma lem3924591 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term129 A s t.
Proof. exact (EQ_MP (@lem3924204 A s t h2) (@lem3924590 A s t h1 h2)). Qed.
Lemma lem3924592 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term179 A s t.
Proof. exact (ex_intro (term180 A s t) (term133 A t s) (@lem3924591 A s t h1 h2)). Qed.
Lemma lem3924593 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term181 A s t.
Proof. exact (@lem3924118 A s t (@lem3924592 A s t h1 h2)). Qed.
Lemma lem3924594 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term103 A s t) : @FINITE A t.
Proof. exact (proj2 (@lem3924113 A s t h1)). Qed.
Lemma lem3924595 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term103 A s t) : @FINITE A s.
Proof. exact (proj1 (@lem3924113 A s t h1)). Qed.
Lemma lem3924596 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (@FINITE A t) = (term181 A s t).
Proof. exact (prop_ext (fun h3 : @FINITE A t => @lem3924593 A s t h1 h2) (fun h3 : term181 A s t => @lem3924114 A t h2)). Qed.
Lemma lem3924597 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term181 A s t.
Proof. exact (EQ_MP (@lem3924596 A s t h1 h2) (@lem3924114 A t h2)). Qed.
Lemma lem3924598 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (@FINITE A s) = (term181 A s t).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem3924597 A s t h1 h2) (fun h3 : term181 A s t => @lem3924115 A s h1)). Qed.
Lemma lem3924599 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term181 A s t.
Proof. exact (EQ_MP (@lem3924598 A s t h1 h2) (@lem3924115 A s h1)). Qed.
Lemma lem3924600 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : term103 A s t) : (@FINITE A t) = (term181 A s t).
Proof. exact (prop_ext (fun h3 : @FINITE A t => @lem3924599 A s t h1 h3) (fun h3 : term181 A s t => @lem3924594 A s t h2)). Qed.
Lemma lem3924601 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : term103 A s t) : term181 A s t.
Proof. exact (EQ_MP (@lem3924600 A s t h1 h2) (@lem3924594 A s t h2)). Qed.
Lemma lem3924602 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term103 A s t) : (@FINITE A s) = (term181 A s t).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem3924601 A s t h2 h1) (fun h2 : term181 A s t => @lem3924595 A s t h1)). Qed.
Lemma lem3924603 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term103 A s t) : term181 A s t.
Proof. exact (EQ_MP (@lem3924602 A s t h1) (@lem3924595 A s t h1)). Qed.
Lemma lem3924604 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term182 A s t.
Proof. exact (fun h0 : term103 A s t => @lem3924603 A s t h0). Qed.
Lemma lem3924609 {A : Type'} (s : A -> Prop) : term183 A s.
Proof. exact (fun t : A -> Prop => @lem3924604 A s t). Qed.
Lemma lem3924614 {A : Type'} : term184 A.
Proof. exact (fun s : A -> Prop => @lem3924609 A s). Qed.
