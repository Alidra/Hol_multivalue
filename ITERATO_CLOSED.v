Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATO_CLOSED_term_abbrevs.
Require Import ITERATO_INDUCT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem6875383 {A K : Type'} (h1 : term0 A K) : term0 A K.
Proof. exact (h1). Qed.
Lemma lem6875384 {A K : Type'} (dom : A -> Prop) (h1 : term0 A K) : term1 A K dom.
Proof. exact (@lem6875383 A K h1 dom). Qed.
Lemma lem6875385 {A K : Type'} (dom : A -> Prop) : (term1 A K dom) = (term2 A K dom).
Proof. exact (eq_refl (term1 A K dom)). Qed.
Lemma lem6875386 {A K : Type'} (dom : A -> Prop) (h1 : term0 A K) : term2 A K dom.
Proof. exact (EQ_MP (@lem6875385 A K dom) (@lem6875384 A K dom h1)). Qed.
Lemma lem6875387 {A K : Type'} (dom : A -> Prop) (neut : A) (h1 : term0 A K) : term3 A K dom neut.
Proof. exact (@lem6875386 A K dom h1 neut). Qed.
Lemma lem6875388 {A K : Type'} (dom : A -> Prop) (neut : A) : (term3 A K dom neut) = (term4 A K dom neut).
Proof. exact (eq_refl (term3 A K dom neut)). Qed.
Lemma lem6875389 {A K : Type'} (dom : A -> Prop) (neut : A) (h1 : term0 A K) : term4 A K dom neut.
Proof. exact (EQ_MP (@lem6875388 A K dom neut) (@lem6875387 A K dom neut h1)). Qed.
Lemma lem6875390 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (h1 : term0 A K) : term5 A K dom neut op.
Proof. exact (@lem6875389 A K dom neut h1 op). Qed.
Lemma lem6875391 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term5 A K dom neut op) = (term6 A K dom neut op).
Proof. exact (eq_refl (term5 A K dom neut op)). Qed.
Lemma lem6875392 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (h1 : term0 A K) : term6 A K dom neut op.
Proof. exact (EQ_MP (@lem6875391 A K dom neut op) (@lem6875390 A K dom neut op h1)). Qed.
Lemma lem6875393 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (h1 : term0 A K) : term7 A K dom neut op ltle.
Proof. exact (@lem6875392 A K dom neut op h1 ltle). Qed.
Lemma lem6875394 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term7 A K dom neut op ltle) = (term8 A K dom neut op ltle).
Proof. exact (eq_refl (term7 A K dom neut op ltle)). Qed.
Lemma lem6875395 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (h1 : term0 A K) : term8 A K dom neut op ltle.
Proof. exact (EQ_MP (@lem6875394 A K dom neut op ltle) (@lem6875393 A K dom neut op ltle h1)). Qed.
Lemma lem6875396 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (h1 : term0 A K) : term9 A K dom neut op ltle k.
Proof. exact (@lem6875395 A K dom neut op ltle h1 k). Qed.
Lemma lem6875397 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : (term9 A K dom neut op ltle k) = (term10 A K dom neut op ltle k).
Proof. exact (eq_refl (term9 A K dom neut op ltle k)). Qed.
Lemma lem6875398 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (h1 : term0 A K) : term10 A K dom neut op ltle k.
Proof. exact (EQ_MP (@lem6875397 A K dom neut op ltle k) (@lem6875396 A K dom neut op ltle k h1)). Qed.
Lemma lem6875399 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : term0 A K) : term11 A K dom neut op ltle k f.
Proof. exact (@lem6875398 A K dom neut op ltle k h1 f). Qed.
Lemma lem6875400 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term11 A K dom neut op ltle k f) = (term12 A K dom neut op ltle k f).
Proof. exact (eq_refl (term11 A K dom neut op ltle k f)). Qed.
Lemma lem6875401 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : term0 A K) : term12 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875400 A K dom neut op ltle k f) (@lem6875399 A K dom neut op ltle k f h1)). Qed.
Lemma lem6875402 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (P : A -> Prop) (h1 : term0 A K) : term13 A K dom neut op ltle k f P.
Proof. exact (@lem6875401 A K dom neut op ltle k f h1 P). Qed.
Lemma lem6875403 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term13 A K dom neut op ltle k f P) = (term14 A K P dom neut op ltle k f).
Proof. exact (eq_refl (term13 A K dom neut op ltle k f P)). Qed.
Lemma lem6875404 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : term0 A K) : term14 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875403 A K P dom neut op ltle k f) (@lem6875402 A K dom neut op ltle k f P h1)). Qed.
Lemma lem6875405 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (h1 : term15 A K k dom neut P op f) : term15 A K k dom neut P op f.
Proof. exact (h1). Qed.
Lemma lem6875406 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (h1 : term0 A K) (h2 : term15 A K k dom neut P op f) : term16 A K P dom neut op ltle k f.
Proof. exact (@lem6875404 A K P dom neut op ltle k f h1 (@lem6875405 A K k dom neut P op f h2)). Qed.
Lemma lem6875407 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (h1 : term15 A K k dom neut P op f) : term17 A K P dom neut op ltle k f.
Proof. exact (fun h0 : term0 A K => @lem6875406 A K ltle k dom neut P op f h0 h1). Qed.
Lemma lem6875408 {A K : Type'} (h1 : term0 A K) : term0 A K.
Proof. exact (h1). Qed.
Lemma lem6875409 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (h1 : term0 A K) (h2 : term15 A K k dom neut P op f) : term16 A K P dom neut op ltle k f.
Proof. exact (@lem6875407 A K ltle k dom neut P op f h2 (@lem6875408 A K h1)). Qed.
Lemma lem6875410 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : term0 A K) : term14 A K P dom neut op ltle k f.
Proof. exact (fun h0 : term15 A K k dom neut P op f => @lem6875409 A K ltle k dom neut P op f h1 h0). Qed.
Lemma lem6875411 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (h1 : term0 A K) : term18 A K P dom neut op ltle k.
Proof. exact (fun f : K -> A => @lem6875410 A K P dom neut op ltle k f h1). Qed.
Lemma lem6875412 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (h1 : term0 A K) : term19 A K P dom neut op ltle.
Proof. exact (fun k : K -> Prop => @lem6875411 A K P dom neut op ltle k h1). Qed.
Lemma lem6875413 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (h1 : term0 A K) : term20 A K P dom neut op.
Proof. exact (fun ltle : type1402 K => @lem6875412 A K P dom neut op ltle h1). Qed.
Lemma lem6875414 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (h1 : term0 A K) : term21 A K P dom neut.
Proof. exact (fun op : type1400 A => @lem6875413 A K P dom neut op h1). Qed.
Lemma lem6875415 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (h1 : term0 A K) : term22 A K P dom.
Proof. exact (fun neut : A => @lem6875414 A K P dom neut h1). Qed.
Lemma lem6875416 {A K : Type'} (P : A -> Prop) (h1 : term0 A K) : term23 A K P.
Proof. exact (fun dom : A -> Prop => @lem6875415 A K P dom h1). Qed.
Lemma lem6875417 {A K : Type'} (h1 : term0 A K) : term24 A K.
Proof. exact (fun P : A -> Prop => @lem6875416 A K P h1). Qed.
Lemma lem6875418 {A K : Type'} : term25 A K.
Proof. exact (fun h0 : term0 A K => @lem6875417 A K h0). Qed.
Lemma lem6875419 {A K : Type'} : term24 A K.
Proof. exact (@lem6875418 A K (@lem6875382 A K)). Qed.
Lemma lem6875420 {A K : Type'} (P : A -> Prop) : term26 A K P.
Proof. exact (@lem6875419 A K P). Qed.
Lemma lem6875421 {A K : Type'} (P : A -> Prop) : (term26 A K P) = (term23 A K P).
Proof. exact (eq_refl (term26 A K P)). Qed.
Lemma lem6875422 {A K : Type'} (P : A -> Prop) : term23 A K P.
Proof. exact (EQ_MP (@lem6875421 A K P) (@lem6875420 A K P)). Qed.
Lemma lem6875423 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) : term27 A K P dom.
Proof. exact (@lem6875422 A K P dom). Qed.
Lemma lem6875424 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) : (term27 A K P dom) = (term22 A K P dom).
Proof. exact (eq_refl (term27 A K P dom)). Qed.
Lemma lem6875425 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) : term22 A K P dom.
Proof. exact (EQ_MP (@lem6875424 A K P dom) (@lem6875423 A K P dom)). Qed.
Lemma lem6875426 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) : term28 A K P dom neut.
Proof. exact (@lem6875425 A K P dom neut). Qed.
Lemma lem6875427 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) : (term28 A K P dom neut) = (term21 A K P dom neut).
Proof. exact (eq_refl (term28 A K P dom neut)). Qed.
Lemma lem6875428 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) : term21 A K P dom neut.
Proof. exact (EQ_MP (@lem6875427 A K P dom neut) (@lem6875426 A K P dom neut)). Qed.
Lemma lem6875429 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) : term29 A K P dom neut op.
Proof. exact (@lem6875428 A K P dom neut op). Qed.
Lemma lem6875430 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) : (term29 A K P dom neut op) = (term20 A K P dom neut op).
Proof. exact (eq_refl (term29 A K P dom neut op)). Qed.
Lemma lem6875431 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) : term20 A K P dom neut op.
Proof. exact (EQ_MP (@lem6875430 A K P dom neut op) (@lem6875429 A K P dom neut op)). Qed.
Lemma lem6875432 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term30 A K P dom neut op ltle.
Proof. exact (@lem6875431 A K P dom neut op ltle). Qed.
Lemma lem6875433 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term30 A K P dom neut op ltle) = (term19 A K P dom neut op ltle).
Proof. exact (eq_refl (term30 A K P dom neut op ltle)). Qed.
Lemma lem6875434 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term19 A K P dom neut op ltle.
Proof. exact (EQ_MP (@lem6875433 A K P dom neut op ltle) (@lem6875432 A K P dom neut op ltle)). Qed.
Lemma lem6875435 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : term31 A K P dom neut op ltle k.
Proof. exact (@lem6875434 A K P dom neut op ltle k). Qed.
Lemma lem6875436 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : (term31 A K P dom neut op ltle k) = (term18 A K P dom neut op ltle k).
Proof. exact (eq_refl (term31 A K P dom neut op ltle k)). Qed.
Lemma lem6875437 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : term18 A K P dom neut op ltle k.
Proof. exact (EQ_MP (@lem6875436 A K P dom neut op ltle k) (@lem6875435 A K P dom neut op ltle k)). Qed.
Lemma lem6875438 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term32 A K P dom neut op ltle k f.
Proof. exact (@lem6875437 A K P dom neut op ltle k f). Qed.
Lemma lem6875439 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term32 A K P dom neut op ltle k f) = (term14 A K P dom neut op ltle k f).
Proof. exact (eq_refl (term32 A K P dom neut op ltle k f)). Qed.
Lemma lem6875441 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term33 A K op k dom neut P f) : term33 A K op k dom neut P f.
Proof. exact (h1). Qed.
Lemma lem6875442 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term34 A K op k dom neut P f) : term34 A K op k dom neut P f.
Proof. exact (h1). Qed.
Lemma lem6875443 {A : Type'} (P : A -> Prop) (neut : A) (h1 : P neut) : P neut.
Proof. exact (h1). Qed.
Lemma lem6875444 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term35 A K k dom neut P f) : term35 A K k dom neut P f.
Proof. exact (h1). Qed.
Lemma lem6875445 {A : Type'} (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term36 A P op.
Proof. exact (h1). Qed.
Lemma lem6875447 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term14 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875439 A K P dom neut op ltle k f) (@lem6875438 A K P dom neut op ltle k f)). Qed.
Lemma lem6875448 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term14 A K P dom neut op ltle k f.
Proof. exact (@lem6875447 A K P dom neut op ltle k f). Qed.
Lemma lem6875449 {A : Type'} (P : A -> Prop) (neut : A) : (P neut) = ((P neut) = True).
Proof. exact (@lem7 (P neut)). Qed.
Lemma lem6875451 {A : Type'} (x : A) (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term37 A P op x.
Proof. exact (@lem6875445 A P op h1 x). Qed.
Lemma lem6875452 {A : Type'} (P : A -> Prop) (op : type1400 A) (x : A) : (term37 A P op x) = (term38 A P op x).
Proof. exact (eq_refl (term37 A P op x)). Qed.
Lemma lem6875453 {A : Type'} (x : A) (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term38 A P op x.
Proof. exact (EQ_MP (@lem6875452 A P op x) (@lem6875451 A x P op h1)). Qed.
Lemma lem6875454 {A : Type'} (x : A) (y : A) (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term39 A P op x y.
Proof. exact (@lem6875453 A x P op h1 y). Qed.
Lemma lem6875455 {A : Type'} (P : A -> Prop) (op : type1400 A) (x : A) (y : A) : (term39 A P op x y) = (term40 A P op x y).
Proof. exact (eq_refl (term39 A P op x y)). Qed.
Lemma lem6875456 {A : Type'} (x : A) (y : A) (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term40 A P op x y.
Proof. exact (EQ_MP (@lem6875455 A P op x y) (@lem6875454 A x y P op h1)). Qed.
Lemma lem6875457 {A : Type'} (x : A) (P : A -> Prop) (y : A) (h1 : term41 A x P y) : term41 A x P y.
Proof. exact (h1). Qed.
Lemma lem6875458 {A : Type'} (op : type1400 A) (x : A) (P : A -> Prop) (y : A) (h1 : term36 A P op) (h2 : term41 A x P y) : term42 A P op x y.
Proof. exact (@lem6875456 A x y P op h1 (@lem6875457 A x P y h2)). Qed.
Lemma lem6875459 {A : Type'} (P : A -> Prop) (op : type1400 A) (x : A) (y : A) : (term42 A P op x y) = ((term42 A P op x y) = True).
Proof. exact (@lem7 (term42 A P op x y)). Qed.
Lemma lem6875460 {A : Type'} (op : type1400 A) (x : A) (P : A -> Prop) (y : A) (h1 : term36 A P op) (h2 : term41 A x P y) : (term42 A P op x y) = True.
Proof. exact (EQ_MP (@lem6875459 A P op x y) (@lem6875458 A op x P y h1 h2)). Qed.
Lemma lem6875466 {A K : Type'} (i : K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term35 A K k dom neut P f) : term43 A K k dom neut P f i.
Proof. exact (@lem6875444 A K k dom neut P f h1 i). Qed.
Lemma lem6875467 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (i : K) : (term43 A K k dom neut P f i) = (term44 A K k dom neut P f i).
Proof. exact (eq_refl (term43 A K k dom neut P f i)). Qed.
Lemma lem6875468 {A K : Type'} (i : K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term35 A K k dom neut P f) : term44 A K k dom neut P f i.
Proof. exact (EQ_MP (@lem6875467 A K k dom neut P f i) (@lem6875466 A K i k dom neut P f h1)). Qed.
Lemma lem6875469 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term45 A K k dom f i neut) : term45 A K k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6875470 {A K : Type'} (P : A -> Prop) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term35 A K k dom neut P f) (h2 : term45 A K k dom f i neut) : term46 A K P f i.
Proof. exact (@lem6875468 A K i k dom neut P f h1 (@lem6875469 A K k dom f i neut h2)). Qed.
Lemma lem6875471 {A K : Type'} (P : A -> Prop) (f : K -> A) (i : K) : (term46 A K P f i) = ((term46 A K P f i) = True).
Proof. exact (@lem7 (term46 A K P f i)). Qed.
Lemma lem6875472 {A K : Type'} (P : A -> Prop) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term35 A K k dom neut P f) (h2 : term45 A K k dom f i neut) : (term46 A K P f i) = True.
Proof. exact (EQ_MP (@lem6875471 A K P f i) (@lem6875470 A K P k dom f i neut h1 h2)). Qed.
Lemma lem6875481 {A : Type'} (P : A -> Prop) (neut : A) (h1 : P neut) : (P neut) = True.
Proof. exact (EQ_MP (@lem6875449 A P neut) (@lem6875443 A P neut h1)). Qed.
Lemma lem6875482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6875483 {A : Type'} (P : A -> Prop) (neut : A) (h1 : P neut) : (term47 A P neut) = (and True).
Proof. exact (MK_COMB (@lem6875482) (@lem6875481 A P neut h1)). Qed.
Lemma lem6875495 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term48 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6875496 (p : Prop) (q : Prop) (p' : Prop) : term49 p q p'.
Proof. exact (fun q' : Prop => @lem6875495 p q p' q'). Qed.
Lemma lem6875497 (p : Prop) (q : Prop) : term50 p q.
Proof. exact (fun p' : Prop => @lem6875496 p q p'). Qed.
Lemma lem6875498 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (i : K) (x : A) : term51 A K k dom neut P op f i x.
Proof. exact (@lem6875497 (term52 A K k dom f i neut P x) (term53 A K P op f i x)). Qed.
Lemma lem6875499 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (i : K) (x : A) (p' : Prop) : term54 A K k dom neut P op f i x p'.
Proof. exact (@lem6875498 A K k dom neut P op f i x p'). Qed.
Lemma lem6875500 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (i : K) (x : A) (p' : Prop) : (term54 A K k dom neut P op f i x p') = (term55 A K k dom neut P op f i x p').
Proof. exact (eq_refl (term54 A K k dom neut P op f i x p')). Qed.
Lemma lem6875501 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (i : K) (x : A) (p' : Prop) : term55 A K k dom neut P op f i x p'.
Proof. exact (EQ_MP (@lem6875500 A K k dom neut P op f i x p') (@lem6875499 A K k dom neut P op f i x p')). Qed.
Lemma lem6875502 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (i : K) (x : A) (p' : Prop) (q' : Prop) : term56 A K k dom neut P op f i x p' q'.
Proof. exact (@lem6875501 A K k dom neut P op f i x p' q'). Qed.
Lemma lem6875503 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (i : K) (x : A) (p' : Prop) (q' : Prop) : (term56 A K k dom neut P op f i x p' q') = (term57 A K k dom neut P op f i x p' q').
Proof. exact (eq_refl (term56 A K k dom neut P op f i x p' q')). Qed.
Lemma lem6875504 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (op : type1400 A) (f : K -> A) (i : K) (x : A) (p' : Prop) (q' : Prop) : term57 A K k dom neut P op f i x p' q'.
Proof. exact (EQ_MP (@lem6875503 A K k dom neut P op f i x p' q') (@lem6875502 A K k dom neut P op f i x p' q')). Qed.
Lemma lem6875513 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) : (term52 A K k dom f i neut P x) = (term52 A K k dom f i neut P x).
Proof. exact (eq_refl (term52 A K k dom f i neut P x)). Qed.
Lemma lem6875514 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (q' : Prop) : term58 A K op k dom f i neut P x q'.
Proof. exact (@lem6875504 A K k dom neut P op f i x (term52 A K k dom f i neut P x) q'). Qed.
Lemma lem6875515 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (q' : Prop) : term59 A K op k dom f i neut P x q'.
Proof. exact (@lem6875514 A K op k dom f i neut P x q' (@lem6875513 A K k dom f i neut P x)). Qed.
Lemma lem6875516 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : term52 A K k dom f i neut P x.
Proof. exact (h1). Qed.
Lemma lem6875517 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : term60 A K dom f i neut P x.
Proof. exact (proj2 (@lem6875516 A K k dom f i neut P x h1)). Qed.
Lemma lem6875518 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : term61 A K f i neut P x.
Proof. exact (proj2 (@lem6875517 A K k dom f i neut P x h1)). Qed.
Lemma lem6875519 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : P x.
Proof. exact (proj2 (@lem6875518 A K k dom f i neut P x h1)). Qed.
Lemma lem6875520 {A : Type'} (P : A -> Prop) (x : A) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem6875522 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : term62 A K f i neut.
Proof. exact (proj1 (@lem6875518 A K k dom f i neut P x h1)). Qed.
Lemma lem6875523 {A K : Type'} (f : K -> A) (i : K) (neut : A) : term63 A K f i neut.
Proof. exact (@lem82 ((f i) = neut)). Qed.
Lemma lem6875536 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : term64 A K f i dom.
Proof. exact (proj1 (@lem6875517 A K k dom f i neut P x h1)). Qed.
Lemma lem6875537 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) : (term64 A K f i dom) = ((term64 A K f i dom) = True).
Proof. exact (@lem7 (term64 A K f i dom)). Qed.
Lemma lem6875539 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : @IN K i k.
Proof. exact (proj1 (@lem6875516 A K k dom f i neut P x h1)). Qed.
Lemma lem6875540 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem6875543 {A : Type'} (x : A) (y : A) (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term65 A P op x y.
Proof. exact (fun h0 : term41 A x P y => @lem6875460 A op x P y h1 h0). Qed.
Lemma lem6875544 {A : Type'} (x : A) (y : A) (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term65 A P op x y.
Proof. exact (@lem6875543 A x y P op h1). Qed.
Lemma lem6875545 {A K : Type'} (f : K -> A) (i : K) (x : A) (P : A -> Prop) (op : type1400 A) (h1 : term36 A P op) : term66 A K P op f i x.
Proof. exact (@lem6875544 A (f i) x P op h1). Qed.
Lemma lem6875549 {A K : Type'} (i : K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term35 A K k dom neut P f) : term67 A K k dom neut P f i.
Proof. exact (fun h0 : term45 A K k dom f i neut => @lem6875472 A K P k dom f i neut h1 h0). Qed.
Lemma lem6875550 {A K : Type'} (i : K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term35 A K k dom neut P f) : term67 A K k dom neut P f i.
Proof. exact (@lem6875549 A K i k dom neut P f h1). Qed.
Lemma lem6875554 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem6875540 K i k) (@lem6875539 A K k dom f i neut P x h1)). Qed.
Lemma lem6875555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6875556 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term68 K i k) = (and True).
Proof. exact (MK_COMB (@lem6875555) (@lem6875554 A K k dom f i neut P x h1)). Qed.
Lemma lem6875560 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term64 A K f i dom) = True.
Proof. exact (EQ_MP (@lem6875537 A K f i dom) (@lem6875536 A K k dom f i neut P x h1)). Qed.
Lemma lem6875561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6875562 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term69 A K f i dom) = (and True).
Proof. exact (MK_COMB (@lem6875561) (@lem6875560 A K k dom f i neut P x h1)). Qed.
Lemma lem6875564 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : ((f i) = neut) = False.
Proof. exact (@lem6875523 A K f i neut (@lem6875522 A K k dom f i neut P x h1)). Qed.
Lemma lem6875565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6875566 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term62 A K f i neut) = (~ False).
Proof. exact (MK_COMB (@lem6875565) (@lem6875564 A K k dom f i neut P x h1)). Qed.
Lemma lem6875568 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6875569 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term62 A K f i neut) = True.
Proof. exact (TRANS (@lem6875566 A K k dom f i neut P x h1) (@lem6875568)). Qed.
Lemma lem6875570 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term70 A K dom f i neut) = (True /\ True).
Proof. exact (MK_COMB (@lem6875562 A K k dom f i neut P x h1) (@lem6875569 A K k dom f i neut P x h1)). Qed.
Lemma lem6875572 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6875573 : (True /\ True) = True.
Proof. exact (@lem6875572 True). Qed.
Lemma lem6875574 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term70 A K dom f i neut) = True.
Proof. exact (TRANS (@lem6875570 A K k dom f i neut P x h1) (@lem6875573)). Qed.
Lemma lem6875575 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term45 A K k dom f i neut) = (True /\ True).
Proof. exact (MK_COMB (@lem6875556 A K k dom f i neut P x h1) (@lem6875574 A K k dom f i neut P x h1)). Qed.
Lemma lem6875577 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6875578 : (True /\ True) = True.
Proof. exact (@lem6875577 True). Qed.
Lemma lem6875579 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (term45 A K k dom f i neut) = True.
Proof. exact (TRANS (@lem6875575 A K k dom f i neut P x h1) (@lem6875578)). Qed.
Lemma lem6875580 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : True = (term45 A K k dom f i neut).
Proof. exact (SYM (@lem6875579 A K k dom f i neut P x h1)). Qed.
Lemma lem6875581 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : term45 A K k dom f i neut.
Proof. exact (EQ_MP (@lem6875580 A K k dom f i neut P x h1) (@lem0)). Qed.
Lemma lem6875582 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term35 A K k dom neut P f) (h2 : term52 A K k dom f i neut P x) : (term46 A K P f i) = True.
Proof. exact (@lem6875550 A K i k dom neut P f h1 (@lem6875581 A K k dom f i neut P x h2)). Qed.
Lemma lem6875583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6875584 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term35 A K k dom neut P f) (h2 : term52 A K k dom f i neut P x) : (term71 A K P f i) = (and True).
Proof. exact (MK_COMB (@lem6875583) (@lem6875582 A K k dom f i neut P x h1 h2)). Qed.
Lemma lem6875586 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term52 A K k dom f i neut P x) : (P x) = True.
Proof. exact (EQ_MP (@lem6875520 A P x) (@lem6875519 A K k dom f i neut P x h1)). Qed.
Lemma lem6875587 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term35 A K k dom neut P f) (h2 : term52 A K k dom f i neut P x) : (term72 A K f i P x) = (True /\ True).
Proof. exact (MK_COMB (@lem6875584 A K k dom f i neut P x h1 h2) (@lem6875586 A K k dom f i neut P x h2)). Qed.
Lemma lem6875589 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6875590 : (True /\ True) = True.
Proof. exact (@lem6875589 True). Qed.
Lemma lem6875591 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term35 A K k dom neut P f) (h2 : term52 A K k dom f i neut P x) : (term72 A K f i P x) = True.
Proof. exact (TRANS (@lem6875587 A K k dom f i neut P x h1 h2) (@lem6875590)). Qed.
Lemma lem6875592 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term35 A K k dom neut P f) (h2 : term52 A K k dom f i neut P x) : True = (term72 A K f i P x).
Proof. exact (SYM (@lem6875591 A K k dom f i neut P x h1 h2)). Qed.
Lemma lem6875593 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term35 A K k dom neut P f) (h2 : term52 A K k dom f i neut P x) : term72 A K f i P x.
Proof. exact (EQ_MP (@lem6875592 A K k dom f i neut P x h1 h2) (@lem0)). Qed.
Lemma lem6875594 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : term52 A K k dom f i neut P x) : (term53 A K P op f i x) = True.
Proof. exact (@lem6875545 A K f i x P op h1 (@lem6875593 A K k dom f i neut P x h2 h3)). Qed.
Lemma lem6875595 {A K : Type'} (i : K) (x : A) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : term73 A K k dom neut P op f i x.
Proof. exact (fun h0 : term52 A K k dom f i neut P x => @lem6875594 A K op k dom f i neut P x h1 h2 h0). Qed.
Lemma lem6875596 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) : term74 A K op k dom f i neut P x.
Proof. exact (@lem6875515 A K op k dom f i neut P x True). Qed.
Lemma lem6875597 {A K : Type'} (i : K) (x : A) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term75 A K k dom neut P op f i x) = (term76 A K k dom f i neut P x).
Proof. exact (@lem6875596 A K op k dom f i neut P x (@lem6875595 A K i x op k dom neut P f h1 h2)). Qed.
Lemma lem6875599 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6875600 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (P : A -> Prop) (x : A) : (term76 A K k dom f i neut P x) = True.
Proof. exact (@lem6875599 (term52 A K k dom f i neut P x)). Qed.
Lemma lem6875601 {A K : Type'} (i : K) (x : A) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term75 A K k dom neut P op f i x) = True.
Proof. exact (TRANS (@lem6875597 A K i x op k dom neut P f h1 h2) (@lem6875600 A K k dom f i neut P x)). Qed.
Lemma lem6875602 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term77 A K k dom neut P op f i) = (term78 A).
Proof. exact (fun_ext (fun x : A => @lem6875601 A K i x op k dom neut P f h1 h2)). Qed.
Lemma lem6875603 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6875604 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term79 A K k dom neut P op f i) = (term80 A).
Proof. exact (MK_COMB (@lem6875603 A) (@lem6875602 A K i op k dom neut P f h1 h2)). Qed.
Lemma lem6875606 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6875607 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (@lem6875606 A t). Qed.
Lemma lem6875608 {A : Type'} : (term80 A) = True.
Proof. exact (@lem6875607 A True). Qed.
Lemma lem6875609 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term79 A K k dom neut P op f i) = True.
Proof. exact (TRANS (@lem6875604 A K i op k dom neut P f h1 h2) (@lem6875608 A)). Qed.
Lemma lem6875610 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term82 A K k dom neut P op f) = (term78 K).
Proof. exact (fun_ext (fun i : K => @lem6875609 A K i op k dom neut P f h1 h2)). Qed.
Lemma lem6875611 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6875612 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term83 A K k dom neut P op f) = (term80 K).
Proof. exact (MK_COMB (@lem6875611 K) (@lem6875610 A K op k dom neut P f h1 h2)). Qed.
Lemma lem6875614 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6875615 {K : Type'} (t : Prop) : (term81 K t) = t.
Proof. exact (@lem6875614 K t). Qed.
Lemma lem6875616 {K : Type'} : (term80 K) = True.
Proof. exact (@lem6875615 K True). Qed.
Lemma lem6875617 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) : (term83 A K k dom neut P op f) = True.
Proof. exact (TRANS (@lem6875612 A K op k dom neut P f h1 h2) (@lem6875616 K)). Qed.
Lemma lem6875618 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : (term15 A K k dom neut P op f) = (True /\ True).
Proof. exact (MK_COMB (@lem6875483 A P neut h3) (@lem6875617 A K op k dom neut P f h1 h2)). Qed.
Lemma lem6875620 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6875621 : (True /\ True) = True.
Proof. exact (@lem6875620 True). Qed.
Lemma lem6875622 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : (term15 A K k dom neut P op f) = True.
Proof. exact (TRANS (@lem6875618 A K op k dom f P neut h1 h2 h3) (@lem6875621)). Qed.
Lemma lem6875623 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : True = (term15 A K k dom neut P op f).
Proof. exact (SYM (@lem6875622 A K op k dom f P neut h1 h2 h3)). Qed.
Lemma lem6875624 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : term15 A K k dom neut P op f.
Proof. exact (EQ_MP (@lem6875623 A K op k dom f P neut h1 h2 h3) (@lem0)). Qed.
Lemma lem6875625 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : term16 A K P dom neut op ltle k f.
Proof. exact (@lem6875448 A K P dom neut op ltle k f (@lem6875624 A K op k dom f P neut h1 h2 h3)). Qed.
Lemma lem6875626 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term33 A K op k dom neut P f) : term34 A K op k dom neut P f.
Proof. exact (proj2 (@lem6875441 A K op k dom neut P f h1)). Qed.
Lemma lem6875627 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term33 A K op k dom neut P f) : P neut.
Proof. exact (proj1 (@lem6875441 A K op k dom neut P f h1)). Qed.
Lemma lem6875628 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term34 A K op k dom neut P f) : term35 A K k dom neut P f.
Proof. exact (proj2 (@lem6875442 A K op k dom neut P f h1)). Qed.
Lemma lem6875629 {A K : Type'} (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term34 A K op k dom neut P f) : term36 A P op.
Proof. exact (proj1 (@lem6875442 A K op k dom neut P f h1)). Qed.
Lemma lem6875630 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : (term35 A K k dom neut P f) = (term16 A K P dom neut op ltle k f).
Proof. exact (prop_ext (fun h4 : term35 A K k dom neut P f => @lem6875625 A K ltle op k dom f P neut h1 h2 h3) (fun h4 : term16 A K P dom neut op ltle k f => @lem6875444 A K k dom neut P f h2)). Qed.
Lemma lem6875631 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : term16 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875630 A K ltle op k dom f P neut h1 h2 h3) (@lem6875444 A K k dom neut P f h2)). Qed.
Lemma lem6875632 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : (term36 A P op) = (term16 A K P dom neut op ltle k f).
Proof. exact (prop_ext (fun h4 : term36 A P op => @lem6875631 A K ltle op k dom f P neut h1 h2 h3) (fun h4 : term16 A K P dom neut op ltle k f => @lem6875445 A P op h1)). Qed.
Lemma lem6875633 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (P : A -> Prop) (neut : A) (h1 : term36 A P op) (h2 : term35 A K k dom neut P f) (h3 : P neut) : term16 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875632 A K ltle op k dom f P neut h1 h2 h3) (@lem6875445 A P op h1)). Qed.
Lemma lem6875634 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : P neut) (h3 : term34 A K op k dom neut P f) : (term35 A K k dom neut P f) = (term16 A K P dom neut op ltle k f).
Proof. exact (prop_ext (fun h4 : term35 A K k dom neut P f => @lem6875633 A K ltle op k dom f P neut h1 h4 h2) (fun h4 : term16 A K P dom neut op ltle k f => @lem6875628 A K op k dom neut P f h3)). Qed.
Lemma lem6875635 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term36 A P op) (h2 : P neut) (h3 : term34 A K op k dom neut P f) : term16 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875634 A K ltle op k dom neut P f h1 h2 h3) (@lem6875628 A K op k dom neut P f h3)). Qed.
Lemma lem6875636 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : P neut) (h2 : term34 A K op k dom neut P f) : (term36 A P op) = (term16 A K P dom neut op ltle k f).
Proof. exact (prop_ext (fun h3 : term36 A P op => @lem6875635 A K ltle op k dom neut P f h3 h1 h2) (fun h3 : term16 A K P dom neut op ltle k f => @lem6875629 A K op k dom neut P f h2)). Qed.
Lemma lem6875637 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : P neut) (h2 : term34 A K op k dom neut P f) : term16 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875636 A K ltle op k dom neut P f h1 h2) (@lem6875629 A K op k dom neut P f h2)). Qed.
Lemma lem6875638 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : P neut) (h2 : term34 A K op k dom neut P f) : (P neut) = (term16 A K P dom neut op ltle k f).
Proof. exact (prop_ext (fun h3 : P neut => @lem6875637 A K ltle op k dom neut P f h1 h2) (fun h3 : term16 A K P dom neut op ltle k f => @lem6875443 A P neut h1)). Qed.
Lemma lem6875639 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : P neut) (h2 : term34 A K op k dom neut P f) : term16 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875638 A K ltle op k dom neut P f h1 h2) (@lem6875443 A P neut h1)). Qed.
Lemma lem6875640 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : P neut) (h2 : term33 A K op k dom neut P f) : (term34 A K op k dom neut P f) = (term16 A K P dom neut op ltle k f).
Proof. exact (prop_ext (fun h3 : term34 A K op k dom neut P f => @lem6875639 A K ltle op k dom neut P f h1 h3) (fun h3 : term16 A K P dom neut op ltle k f => @lem6875626 A K op k dom neut P f h2)). Qed.
Lemma lem6875641 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : P neut) (h2 : term33 A K op k dom neut P f) : term16 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875640 A K ltle op k dom neut P f h1 h2) (@lem6875626 A K op k dom neut P f h2)). Qed.
Lemma lem6875642 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term33 A K op k dom neut P f) : (P neut) = (term16 A K P dom neut op ltle k f).
Proof. exact (prop_ext (fun h2 : P neut => @lem6875641 A K ltle op k dom neut P f h2 h1) (fun h2 : term16 A K P dom neut op ltle k f => @lem6875627 A K op k dom neut P f h1)). Qed.
Lemma lem6875643 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (dom : A -> Prop) (neut : A) (P : A -> Prop) (f : K -> A) (h1 : term33 A K op k dom neut P f) : term16 A K P dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6875642 A K ltle op k dom neut P f h1) (@lem6875627 A K op k dom neut P f h1)). Qed.
Lemma lem6875644 {A K : Type'} (P : A -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term84 A K P dom neut op ltle k f.
Proof. exact (fun h0 : term33 A K op k dom neut P f => @lem6875643 A K ltle op k dom neut P f h0). Qed.
Lemma lem6875649 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term85 A K dom neut op ltle k f.
Proof. exact (fun P : A -> Prop => @lem6875644 A K P dom neut op ltle k f). Qed.
Lemma lem6875654 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) : term86 A K dom neut op ltle k.
Proof. exact (fun f : K -> A => @lem6875649 A K dom neut op ltle k f). Qed.
Lemma lem6875659 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term87 A K dom neut op ltle.
Proof. exact (fun k : K -> Prop => @lem6875654 A K dom neut op ltle k). Qed.
Lemma lem6875664 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term88 A K dom neut op.
Proof. exact (fun ltle : type1402 K => @lem6875659 A K dom neut op ltle). Qed.
Lemma lem6875669 {A K : Type'} (dom : A -> Prop) (neut : A) : term89 A K dom neut.
Proof. exact (fun op : type1400 A => @lem6875664 A K dom neut op). Qed.
Lemma lem6875674 {A K : Type'} (dom : A -> Prop) : term90 A K dom.
Proof. exact (fun neut : A => @lem6875669 A K dom neut). Qed.
Lemma lem6875679 {A K : Type'} : term91 A K.
Proof. exact (fun dom : A -> Prop => @lem6875674 A K dom). Qed.
