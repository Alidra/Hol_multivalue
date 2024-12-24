Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm322846_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm7058_spec.
Require Import thm7249_spec.
Require Import thm7362_spec.
Require Import thm7400_spec.
Require Import thm9102_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem322349 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : term0 A B a0 a1 H lt2 x R f.
Proof. exact (h1). Qed.
Lemma lem322350 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : term1 A B a1 H lt2 x R f.
Proof. exact (proj2 (@lem322349 A B a0 a1 H lt2 x R f h1)). Qed.
Lemma lem322351 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : a0 = x.
Proof. exact (proj1 (@lem322349 A B a0 a1 H lt2 x R f h1)). Qed.
Lemma lem322352 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : term2 A B lt2 x R f.
Proof. exact (proj2 (@lem322350 A B a0 a1 H lt2 x R f h1)). Qed.
Lemma lem322353 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : a1 = (H f x).
Proof. exact (proj1 (@lem322350 A B a0 a1 H lt2 x R f h1)). Qed.
Lemma lem322354 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term3 A B lt2 R H.
Proof. exact (h1). Qed.
Lemma lem322355 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term4 A B lt2 R H f.
Proof. exact (@lem322354 A B lt2 R H h1 f). Qed.
Lemma lem322356 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (f : A -> B) : (term4 A B lt2 R H f) = (term5 A B lt2 R H f).
Proof. exact (eq_refl (term4 A B lt2 R H f)). Qed.
Lemma lem322357 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term5 A B lt2 R H f.
Proof. exact (EQ_MP (@lem322356 A B lt2 R H f) (@lem322355 A B f lt2 R H h1)). Qed.
Lemma lem322358 {A B : Type'} (f : A -> B) (x : A) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term6 A B lt2 R H f x.
Proof. exact (@lem322357 A B f lt2 R H h1 x). Qed.
Lemma lem322359 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (f : A -> B) (x : A) : (term6 A B lt2 R H f x) = (term7 A B lt2 R H f x).
Proof. exact (eq_refl (term6 A B lt2 R H f x)). Qed.
Lemma lem322360 {A B : Type'} (f : A -> B) (x : A) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term7 A B lt2 R H f x.
Proof. exact (EQ_MP (@lem322359 A B lt2 R H f x) (@lem322358 A B f x lt2 R H h1)). Qed.
Lemma lem322361 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term3 A B lt2 R H) (h2 : term0 A B a0 a1 H lt2 x R f) : term8 A B R H f x.
Proof. exact (@lem322360 A B f x lt2 R H h1 (@lem322352 A B a0 a1 H lt2 x R f h2)). Qed.
Lemma lem322362 {A B : Type'} (R : type1413 A B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem322363 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : (R a0) = (R x).
Proof. exact (MK_COMB (@lem322362 A B R) (@lem322351 A B a0 a1 H lt2 x R f h1)). Qed.
Lemma lem322364 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : (R a0 a1) = (term8 A B R H f x).
Proof. exact (MK_COMB (@lem322363 A B a0 a1 H lt2 x R f h1) (@lem322353 A B a0 a1 H lt2 x R f h1)). Qed.
Lemma lem322365 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term0 A B a0 a1 H lt2 x R f) : (term8 A B R H f x) = (R a0 a1).
Proof. exact (SYM (@lem322364 A B a0 a1 H lt2 x R f h1)). Qed.
Lemma lem322366 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term3 A B lt2 R H) (h2 : term0 A B a0 a1 H lt2 x R f) : R a0 a1.
Proof. exact (EQ_MP (@lem322365 A B a0 a1 H lt2 x R f h2) (@lem322361 A B a0 a1 H lt2 x R f h1 h2)). Qed.
Lemma lem322367 {A B : Type'} (x : A) (f : A -> B) (a0 : A) (a1 : B) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term9 A B H lt2 x f R a0 a1.
Proof. exact (fun h0 : term0 A B a0 a1 H lt2 x R f => @lem322366 A B a0 a1 H lt2 x R f h1 h0). Qed.
Lemma lem322368 {A B : Type'} (f : A -> B) (a0 : A) (a1 : B) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term10 A B H lt2 f R a0 a1.
Proof. exact (@lem322367 A B a0 f a0 a1 lt2 R H h1). Qed.
Lemma lem322369 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term1 A B a1 H lt2 a0 R f) : term1 A B a1 H lt2 a0 R f.
Proof. exact (h1). Qed.
Lemma lem322370 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem322371 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term1 A B a1 H lt2 a0 R f) : term11 A B a1 H lt2 a0 R f.
Proof. exact (conj (@lem322370 A a0) (@lem322369 A B a1 H lt2 a0 R f h1)). Qed.
Lemma lem322372 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term3 A B lt2 R H) (h2 : term1 A B a1 H lt2 a0 R f) : R a0 a1.
Proof. exact (@lem322368 A B f a0 a1 lt2 R H h1 (@lem322371 A B a1 H lt2 a0 R f h2)). Qed.
Lemma lem322373 {A B : Type'} (f : A -> B) (a0 : A) (a1 : B) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term12 A B H lt2 f R a0 a1.
Proof. exact (fun h0 : term1 A B a1 H lt2 a0 R f => @lem322372 A B a1 H lt2 a0 R f h1 h0). Qed.
Lemma lem322374 {A B : Type'} (a0 : A) (a1 : B) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term13 A B H lt2 R a0 a1.
Proof. exact (fun f : A -> B => @lem322373 A B f a0 a1 lt2 R H h1). Qed.
Lemma lem322375 {A B : Type'} (a0 : A) (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term14 A B H lt2 R a0.
Proof. exact (fun a1 : B => @lem322374 A B a0 a1 lt2 R H h1). Qed.
Lemma lem322376 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (h1 : term3 A B lt2 R H) : term15 A B H lt2 R.
Proof. exact (fun a0 : A => @lem322375 A B a0 lt2 R H h1). Qed.
Lemma lem322377 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term15 A B H lt2 R.
Proof. exact (h1). Qed.
Lemma lem322378 {A B : Type'} (x : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term16 A B H lt2 R x.
Proof. exact (@lem322377 A B H lt2 R h1 x). Qed.
Lemma lem322379 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (x : A) : (term16 A B H lt2 R x) = (term14 A B H lt2 R x).
Proof. exact (eq_refl (term16 A B H lt2 R x)). Qed.
Lemma lem322380 {A B : Type'} (x : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term14 A B H lt2 R x.
Proof. exact (EQ_MP (@lem322379 A B H lt2 R x) (@lem322378 A B x H lt2 R h1)). Qed.
Lemma lem322381 {A B : Type'} (f : A -> B) (x : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term17 A B lt2 R H f x.
Proof. exact (@lem322380 A B x H lt2 R h1 (H f x)). Qed.
Lemma lem322382 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (f : A -> B) (x : A) : (term17 A B lt2 R H f x) = (term18 A B lt2 R H f x).
Proof. exact (eq_refl (term17 A B lt2 R H f x)). Qed.
Lemma lem322383 {A B : Type'} (f : A -> B) (x : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term18 A B lt2 R H f x.
Proof. exact (EQ_MP (@lem322382 A B lt2 R H f x) (@lem322381 A B f x H lt2 R h1)). Qed.
Lemma lem322384 {A B : Type'} (x : A) (f : A -> B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term19 A B lt2 R H x f.
Proof. exact (@lem322383 A B f x H lt2 R h1 f). Qed.
Lemma lem322385 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) (f : A -> B) (x : A) : (term19 A B lt2 R H x f) = (term20 A B lt2 R H f x).
Proof. exact (eq_refl (term19 A B lt2 R H x f)). Qed.
Lemma lem322386 {A B : Type'} (f : A -> B) (x : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term20 A B lt2 R H f x.
Proof. exact (EQ_MP (@lem322385 A B lt2 R H f x) (@lem322384 A B x f H lt2 R h1)). Qed.
Lemma lem322387 {A B : Type'} (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term2 A B lt2 x R f) : term2 A B lt2 x R f.
Proof. exact (h1). Qed.
Lemma lem322388 {A B : Type'} (H : type549 A B) (f : A -> B) (x : A) : (H f x) = (H f x).
Proof. exact (eq_refl (H f x)). Qed.
Lemma lem322389 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term2 A B lt2 x R f) : term21 A B H lt2 x R f.
Proof. exact (conj (@lem322388 A B H f x) (@lem322387 A B lt2 x R f h1)). Qed.
Lemma lem322390 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (x : A) (R : type1413 A B) (f : A -> B) (h1 : term15 A B H lt2 R) (h2 : term2 A B lt2 x R f) : term8 A B R H f x.
Proof. exact (@lem322386 A B f x H lt2 R h1 (@lem322389 A B H lt2 x R f h2)). Qed.
Lemma lem322391 {A B : Type'} (f : A -> B) (x : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term7 A B lt2 R H f x.
Proof. exact (fun h0 : term2 A B lt2 x R f => @lem322390 A B H lt2 x R f h1 h0). Qed.
Lemma lem322392 {A B : Type'} (f : A -> B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term5 A B lt2 R H f.
Proof. exact (fun x : A => @lem322391 A B f x H lt2 R h1). Qed.
Lemma lem322393 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term15 A B H lt2 R) : term3 A B lt2 R H.
Proof. exact (fun f : A -> B => @lem322392 A B f H lt2 R h1). Qed.
Lemma lem322394 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) : term22 A B lt2 R H.
Proof. exact (fun h0 : term15 A B H lt2 R => @lem322393 A B H lt2 R h0). Qed.
Lemma lem322395 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : term23 A B H lt2 R.
Proof. exact (fun h0 : term3 A B lt2 R H => @lem322376 A B lt2 R H h0). Qed.
Lemma lem322396 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) : term24 A B lt2 R H.
Proof. exact (conj (@lem322395 A B H lt2 R) (@lem322394 A B lt2 R H)). Qed.
Lemma lem322397 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term24 A B lt2 R H) = ((term3 A B lt2 R H) = (term15 A B H lt2 R)).
Proof. exact (@lem32 (term3 A B lt2 R H) (term15 A B H lt2 R)). Qed.
Lemma lem322398 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term3 A B lt2 R H) = (term15 A B H lt2 R).
Proof. exact (EQ_MP (@lem322397 A B H lt2 R) (@lem322396 A B lt2 R H)). Qed.
Lemma lem322399 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term13 A B H lt2 R a0 a1) : term13 A B H lt2 R a0 a1.
Proof. exact (h1). Qed.
Lemma lem322400 {A B : Type'} (f : A -> B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term13 A B H lt2 R a0 a1) : term25 A B H lt2 R a0 a1 f.
Proof. exact (@lem322399 A B H lt2 R a0 a1 h1 f). Qed.
Lemma lem322401 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (f : A -> B) (R : type1413 A B) (a0 : A) (a1 : B) : (term25 A B H lt2 R a0 a1 f) = (term12 A B H lt2 f R a0 a1).
Proof. exact (eq_refl (term25 A B H lt2 R a0 a1 f)). Qed.
Lemma lem322402 {A B : Type'} (f : A -> B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term13 A B H lt2 R a0 a1) : term12 A B H lt2 f R a0 a1.
Proof. exact (EQ_MP (@lem322401 A B H lt2 f R a0 a1) (@lem322400 A B f H lt2 R a0 a1 h1)). Qed.
Lemma lem322403 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term1 A B a1 H lt2 a0 R f) : term1 A B a1 H lt2 a0 R f.
Proof. exact (h1). Qed.
Lemma lem322404 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term13 A B H lt2 R a0 a1) (h2 : term1 A B a1 H lt2 a0 R f) : R a0 a1.
Proof. exact (@lem322402 A B f H lt2 R a0 a1 h1 (@lem322403 A B a1 H lt2 a0 R f h2)). Qed.
Lemma lem322405 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term1 A B a1 H lt2 a0 R f) : term26 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term13 A B H lt2 R a0 a1 => @lem322404 A B a1 H lt2 a0 R f h0 h1). Qed.
Lemma lem322406 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term27 A B a1 H lt2 a0 R) : term27 A B a1 H lt2 a0 R.
Proof. exact (h1). Qed.
Lemma lem322407 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term27 A B a1 H lt2 a0 R) : term26 A B H lt2 R a0 a1.
Proof. exact (ex_elim (@lem322406 A B a1 H lt2 a0 R h1) (fun f : A -> B => fun h0 : term28 A B a1 H lt2 a0 R f => @lem322405 A B a1 H lt2 a0 R f h0)). Qed.
Lemma lem322408 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term13 A B H lt2 R a0 a1) : term13 A B H lt2 R a0 a1.
Proof. exact (h1). Qed.
Lemma lem322409 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term13 A B H lt2 R a0 a1) (h2 : term27 A B a1 H lt2 a0 R) : R a0 a1.
Proof. exact (@lem322407 A B a1 H lt2 a0 R h2 (@lem322408 A B H lt2 R a0 a1 h1)). Qed.
Lemma lem322410 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term13 A B H lt2 R a0 a1) : term29 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term27 A B a1 H lt2 a0 R => @lem322409 A B a1 H lt2 a0 R h1 h0). Qed.
Lemma lem322411 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term29 A B H lt2 R a0 a1) : term29 A B H lt2 R a0 a1.
Proof. exact (h1). Qed.
Lemma lem322412 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term1 A B a1 H lt2 a0 R f) : term1 A B a1 H lt2 a0 R f.
Proof. exact (h1). Qed.
Lemma lem322413 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (h1 : term1 A B a1 H lt2 a0 R f) : term27 A B a1 H lt2 a0 R.
Proof. exact (ex_intro (term28 A B a1 H lt2 a0 R) f (@lem322412 A B a1 H lt2 a0 R f h1)). Qed.
Lemma lem322414 {A B : Type'} (f : A -> B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term1 A B a1 H lt2 a0 R f) (h2 : term29 A B H lt2 R a0 a1) : R a0 a1.
Proof. exact (@lem322411 A B H lt2 R a0 a1 h2 (@lem322413 A B a1 H lt2 a0 R f h1)). Qed.
Lemma lem322415 {A B : Type'} (f : A -> B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term29 A B H lt2 R a0 a1) : term12 A B H lt2 f R a0 a1.
Proof. exact (fun h0 : term1 A B a1 H lt2 a0 R f => @lem322414 A B f H lt2 R a0 a1 h0 h1). Qed.
Lemma lem322416 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term29 A B H lt2 R a0 a1) : term13 A B H lt2 R a0 a1.
Proof. exact (fun f : A -> B => @lem322415 A B f H lt2 R a0 a1 h1). Qed.
Lemma lem322417 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : term30 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term29 A B H lt2 R a0 a1 => @lem322416 A B H lt2 R a0 a1 h0). Qed.
Lemma lem322418 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : term31 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term13 A B H lt2 R a0 a1 => @lem322410 A B H lt2 R a0 a1 h0). Qed.
Lemma lem322419 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : term32 A B H lt2 R a0 a1.
Proof. exact (conj (@lem322418 A B H lt2 R a0 a1) (@lem322417 A B H lt2 R a0 a1)). Qed.
Lemma lem322420 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : (term32 A B H lt2 R a0 a1) = ((term13 A B H lt2 R a0 a1) = (term29 A B H lt2 R a0 a1)).
Proof. exact (@lem32 (term13 A B H lt2 R a0 a1) (term29 A B H lt2 R a0 a1)). Qed.
Lemma lem322421 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : (term13 A B H lt2 R a0 a1) = (term29 A B H lt2 R a0 a1).
Proof. exact (EQ_MP (@lem322420 A B H lt2 R a0 a1) (@lem322419 A B H lt2 R a0 a1)). Qed.
Lemma lem322422 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term33 A B H lt2 R a0) = (term34 A B H lt2 R a0).
Proof. exact (fun_ext (fun a1 : B => @lem322421 A B H lt2 R a0 a1)). Qed.
Lemma lem322423 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem322424 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term14 A B H lt2 R a0) = (term35 A B H lt2 R a0).
Proof. exact (MK_COMB (@lem322423 B) (@lem322422 A B H lt2 R a0)). Qed.
Lemma lem322425 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term36 A B H lt2 R) = (term37 A B H lt2 R).
Proof. exact (fun_ext (fun a0 : A => @lem322424 A B H lt2 R a0)). Qed.
Lemma lem322426 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem322427 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term15 A B H lt2 R) = (term38 A B H lt2 R).
Proof. exact (MK_COMB (@lem322426 A) (@lem322425 A B H lt2 R)). Qed.
Lemma lem322428 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term3 A B lt2 R H) = (term38 A B H lt2 R).
Proof. exact (TRANS (@lem322398 A B H lt2 R) (@lem322427 A B H lt2 R)). Qed.
Lemma lem322430 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem322431 (x : Prop) : (x = x) = True.
Proof. exact (@lem322430 Prop x). Qed.
Lemma lem322432 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : ((term38 A B H lt2 R) = (term38 A B H lt2 R)) = True.
Proof. exact (@lem322431 (term38 A B H lt2 R)). Qed.
Lemma lem322433 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : True = ((term38 A B H lt2 R) = (term38 A B H lt2 R)).
Proof. exact (SYM (@lem322432 A B H lt2 R)). Qed.
Lemma lem322434 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term38 A B H lt2 R) = (term38 A B H lt2 R).
Proof. exact (EQ_MP (@lem322433 A B H lt2 R) (@lem0)). Qed.
Lemma lem322435 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term3 A B lt2 R H) = (term38 A B H lt2 R).
Proof. exact (TRANS (@lem322428 A B H lt2 R) (@lem322434 A B H lt2 R)). Qed.
Lemma lem322436 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term38 A B H lt2 R.
Proof. exact (h1). Qed.
Lemma lem322437 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term39 A B H lt2 R a0.
Proof. exact (@lem322436 A B H lt2 R h1 a0). Qed.
Lemma lem322438 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term39 A B H lt2 R a0) = (term35 A B H lt2 R a0).
Proof. exact (eq_refl (term39 A B H lt2 R a0)). Qed.
Lemma lem322439 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term35 A B H lt2 R a0.
Proof. exact (EQ_MP (@lem322438 A B H lt2 R a0) (@lem322437 A B a0 H lt2 R h1)). Qed.
Lemma lem322440 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term40 A B H lt2 R a0 a1.
Proof. exact (@lem322439 A B a0 H lt2 R h1 a1). Qed.
Lemma lem322441 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : (term40 A B H lt2 R a0 a1) = (term29 A B H lt2 R a0 a1).
Proof. exact (eq_refl (term40 A B H lt2 R a0 a1)). Qed.
Lemma lem322442 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term29 A B H lt2 R a0 a1.
Proof. exact (EQ_MP (@lem322441 A B H lt2 R a0 a1) (@lem322440 A B a0 a1 H lt2 R h1)). Qed.
Lemma lem322443 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term27 A B a1 H lt2 a0 R) : term27 A B a1 H lt2 a0 R.
Proof. exact (h1). Qed.
Lemma lem322444 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term38 A B H lt2 R) (h2 : term27 A B a1 H lt2 a0 R) : R a0 a1.
Proof. exact (@lem322442 A B a0 a1 H lt2 R h1 (@lem322443 A B a1 H lt2 a0 R h2)). Qed.
Lemma lem322445 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term27 A B a1 H lt2 a0 R) : term41 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term38 A B H lt2 R => @lem322444 A B a1 H lt2 a0 R h0 h1). Qed.
Lemma lem322446 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term38 A B H lt2 R.
Proof. exact (h1). Qed.
Lemma lem322447 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term38 A B H lt2 R) (h2 : term27 A B a1 H lt2 a0 R) : R a0 a1.
Proof. exact (@lem322445 A B a1 H lt2 a0 R h2 (@lem322446 A B H lt2 R h1)). Qed.
Lemma lem322448 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term29 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term27 A B a1 H lt2 a0 R => @lem322447 A B a1 H lt2 a0 R h1 h0). Qed.
Lemma lem322449 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term35 A B H lt2 R a0.
Proof. exact (fun a1 : B => @lem322448 A B a0 a1 H lt2 R h1). Qed.
Lemma lem322450 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term38 A B H lt2 R.
Proof. exact (fun a0 : A => @lem322449 A B a0 H lt2 R h1). Qed.
Lemma lem322451 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term38 A B H lt2 R.
Proof. exact (h1). Qed.
Lemma lem322452 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term39 A B H lt2 R a0.
Proof. exact (@lem322451 A B H lt2 R h1 a0). Qed.
Lemma lem322453 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term39 A B H lt2 R a0) = (term35 A B H lt2 R a0).
Proof. exact (eq_refl (term39 A B H lt2 R a0)). Qed.
Lemma lem322454 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term35 A B H lt2 R a0.
Proof. exact (EQ_MP (@lem322453 A B H lt2 R a0) (@lem322452 A B a0 H lt2 R h1)). Qed.
Lemma lem322455 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term40 A B H lt2 R a0 a1.
Proof. exact (@lem322454 A B a0 H lt2 R h1 a1). Qed.
Lemma lem322456 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : (term40 A B H lt2 R a0 a1) = (term29 A B H lt2 R a0 a1).
Proof. exact (eq_refl (term40 A B H lt2 R a0 a1)). Qed.
Lemma lem322457 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term29 A B H lt2 R a0 a1.
Proof. exact (EQ_MP (@lem322456 A B H lt2 R a0 a1) (@lem322455 A B a0 a1 H lt2 R h1)). Qed.
Lemma lem322458 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term27 A B a1 H lt2 a0 R) : term27 A B a1 H lt2 a0 R.
Proof. exact (h1). Qed.
Lemma lem322459 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term38 A B H lt2 R) (h2 : term27 A B a1 H lt2 a0 R) : R a0 a1.
Proof. exact (@lem322457 A B a0 a1 H lt2 R h1 (@lem322458 A B a1 H lt2 a0 R h2)). Qed.
Lemma lem322460 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term27 A B a1 H lt2 a0 R) : term41 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term38 A B H lt2 R => @lem322459 A B a1 H lt2 a0 R h0 h1). Qed.
Lemma lem322461 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term38 A B H lt2 R.
Proof. exact (h1). Qed.
Lemma lem322462 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term38 A B H lt2 R) (h2 : term27 A B a1 H lt2 a0 R) : R a0 a1.
Proof. exact (@lem322460 A B a1 H lt2 a0 R h2 (@lem322461 A B H lt2 R h1)). Qed.
Lemma lem322463 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term29 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term27 A B a1 H lt2 a0 R => @lem322462 A B a1 H lt2 a0 R h1 h0). Qed.
Lemma lem322464 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term35 A B H lt2 R a0.
Proof. exact (fun a1 : B => @lem322463 A B a0 a1 H lt2 R h1). Qed.
Lemma lem322465 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (h1 : term38 A B H lt2 R) : term38 A B H lt2 R.
Proof. exact (fun a0 : A => @lem322464 A B a0 H lt2 R h1). Qed.
Lemma lem322466 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : term42 A B H lt2 R.
Proof. exact (fun h0 : term38 A B H lt2 R => @lem322465 A B H lt2 R h0). Qed.
Lemma lem322467 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : term42 A B H lt2 R.
Proof. exact (fun h0 : term38 A B H lt2 R => @lem322450 A B H lt2 R h0). Qed.
Lemma lem322468 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : term43 A B H lt2 R.
Proof. exact (conj (@lem322467 A B H lt2 R) (@lem322466 A B H lt2 R)). Qed.
Lemma lem322469 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term43 A B H lt2 R) = ((term38 A B H lt2 R) = (term38 A B H lt2 R)).
Proof. exact (@lem32 (term38 A B H lt2 R) (term38 A B H lt2 R)). Qed.
Lemma lem322470 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term38 A B H lt2 R) = (term38 A B H lt2 R).
Proof. exact (EQ_MP (@lem322469 A B H lt2 R) (@lem322468 A B H lt2 R)). Qed.
Lemma lem322471 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term3 A B lt2 R H) = (term38 A B H lt2 R).
Proof. exact (TRANS (@lem322435 A B H lt2 R) (@lem322470 A B H lt2 R)). Qed.
Lemma lem322472 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) : (term38 A B H lt2 R) = (term3 A B lt2 R H).
Proof. exact (SYM (@lem322471 A B H lt2 R)). Qed.
Lemma lem322473 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : R = (term44 A B H lt2).
Proof. exact (h1). Qed.
Lemma lem322474 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem322475 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (R a0) = (term45 A B H lt2 a0).
Proof. exact (MK_COMB (@lem322473 A B R H lt2 h1) (@lem322474 A a0)). Qed.
Lemma lem322476 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) : (term45 A B H lt2 a0) = (term46 A B H lt2 a0).
Proof. exact (eq_refl (term45 A B H lt2 a0)). Qed.
Lemma lem322477 {A B : Type'} (R : type1413 A B) (a0 : A) : (term47 A B R a0) = (term47 A B R a0).
Proof. exact (eq_refl (term47 A B R a0)). Qed.
Lemma lem322478 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) : ((R a0) = (term45 A B H lt2 a0)) = ((R a0) = (term46 A B H lt2 a0)).
Proof. exact (MK_COMB (@lem322477 A B R a0) (@lem322476 A B H lt2 a0)). Qed.
Lemma lem322479 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (R a0) = (term46 A B H lt2 a0).
Proof. exact (EQ_MP (@lem322478 A B R H lt2 a0) (@lem322475 A B a0 R H lt2 h1)). Qed.
Lemma lem322480 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem322481 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (R a0 a1) = (term48 A B H lt2 a0 a1).
Proof. exact (MK_COMB (@lem322479 A B a0 R H lt2 h1) (@lem322480 B a1)). Qed.
Lemma lem322482 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (a1 : B) : (term48 A B H lt2 a0 a1) = (term49 A B H lt2 a0 a1).
Proof. exact (eq_refl (term48 A B H lt2 a0 a1)). Qed.
Lemma lem322483 {A B : Type'} (R : type1413 A B) (a0 : A) (a1 : B) : (term50 A B R a0 a1) = (term50 A B R a0 a1).
Proof. exact (eq_refl (term50 A B R a0 a1)). Qed.
Lemma lem322484 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (a1 : B) : ((R a0 a1) = (term48 A B H lt2 a0 a1)) = ((R a0 a1) = (term49 A B H lt2 a0 a1)).
Proof. exact (MK_COMB (@lem322483 A B R a0 a1) (@lem322482 A B H lt2 a0 a1)). Qed.
Lemma lem322485 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (R a0 a1) = (term49 A B H lt2 a0 a1).
Proof. exact (EQ_MP (@lem322484 A B R H lt2 a0 a1) (@lem322481 A B a0 a1 R H lt2 h1)). Qed.
Lemma lem322486 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term51 A B R H lt2 a0.
Proof. exact (fun a1 : B => @lem322485 A B a0 a1 R H lt2 h1). Qed.
Lemma lem322487 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term52 A B R H lt2.
Proof. exact (fun a0 : A => @lem322486 A B a0 R H lt2 h1). Qed.
Lemma lem322488 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term53 A B R H lt2 a0.
Proof. exact (@lem322487 A B R H lt2 h1 a0). Qed.
Lemma lem322489 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) : (term53 A B R H lt2 a0) = (term51 A B R H lt2 a0).
Proof. exact (eq_refl (term53 A B R H lt2 a0)). Qed.
Lemma lem322490 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term51 A B R H lt2 a0.
Proof. exact (EQ_MP (@lem322489 A B R H lt2 a0) (@lem322488 A B a0 R H lt2 h1)). Qed.
Lemma lem322491 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term54 A B R H lt2 a0 a1.
Proof. exact (@lem322490 A B a0 R H lt2 h1 a1). Qed.
Lemma lem322492 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (a1 : B) : (term54 A B R H lt2 a0 a1) = ((R a0 a1) = (term49 A B H lt2 a0 a1)).
Proof. exact (eq_refl (term54 A B R H lt2 a0 a1)). Qed.
Lemma lem322493 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (R a0 a1) = (term49 A B H lt2 a0 a1).
Proof. exact (EQ_MP (@lem322492 A B R H lt2 a0 a1) (@lem322491 A B a0 a1 R H lt2 h1)). Qed.
Lemma lem322496 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (a1 : B) : term55 A B R H lt2 a0 a1.
Proof. exact (@lem37 (R a0 a1) (term49 A B H lt2 a0 a1)). Qed.
Lemma lem322497 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term56 A B R H lt2 a0 a1.
Proof. exact (@lem322496 A B R H lt2 a0 a1 (@lem322493 A B a0 a1 R H lt2 h1)). Qed.
Lemma lem322498 {A B : Type'} (R : type1413 A B) (a0 : A) (a1 : B) (h1 : R a0 a1) : R a0 a1.
Proof. exact (h1). Qed.
Lemma lem322499 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : R = (term44 A B H lt2)) (h2 : R a0 a1) : term49 A B H lt2 a0 a1.
Proof. exact (@lem322497 A B a0 a1 R H lt2 h1 (@lem322498 A B R a0 a1 h2)). Qed.
Lemma lem322500 {A B : Type'} (R' : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : R = (term44 A B H lt2)) (h2 : R a0 a1) : term57 A B H lt2 a0 a1 R'.
Proof. exact (@lem322499 A B H lt2 R a0 a1 h1 h2 R'). Qed.
Lemma lem322501 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (a0 : A) (a1 : B) : (term57 A B H lt2 a0 a1 R') = (term41 A B H lt2 R' a0 a1).
Proof. exact (eq_refl (term57 A B H lt2 a0 a1 R')). Qed.
Lemma lem322502 {A B : Type'} (R' : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : R = (term44 A B H lt2)) (h2 : R a0 a1) : term41 A B H lt2 R' a0 a1.
Proof. exact (EQ_MP (@lem322501 A B H lt2 R' a0 a1) (@lem322500 A B R' H lt2 R a0 a1 h1 h2)). Qed.
Lemma lem322503 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (h1 : term38 A B H lt2 R') : term38 A B H lt2 R'.
Proof. exact (h1). Qed.
Lemma lem322504 {A B : Type'} (R' : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) (h1 : term38 A B H lt2 R') (h2 : R = (term44 A B H lt2)) (h3 : R a0 a1) : R' a0 a1.
Proof. exact (@lem322502 A B R' H lt2 R a0 a1 h2 h3 (@lem322503 A B H lt2 R' h1)). Qed.
Lemma lem322505 {A B : Type'} (a0 : A) (a1 : B) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : R = (term44 A B H lt2)) : term58 A B R R' a0 a1.
Proof. exact (fun h0 : R a0 a1 => @lem322504 A B R' H lt2 R a0 a1 h1 h2 h0). Qed.
Lemma lem322506 {A B : Type'} (a0 : A) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : R = (term44 A B H lt2)) : term59 A B R R' a0.
Proof. exact (fun a1 : B => @lem322505 A B a0 a1 R' R H lt2 h1 h2). Qed.
Lemma lem322507 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : R = (term44 A B H lt2)) : term60 A B R R'.
Proof. exact (fun a0 : A => @lem322506 A B a0 R' R H lt2 h1 h2). Qed.
Lemma lem322508 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term61 A B H lt2 R R'.
Proof. exact (fun h0 : term38 A B H lt2 R' => @lem322507 A B R' R H lt2 h0 h1). Qed.
Lemma lem322509 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term62 A B H lt2 R.
Proof. exact (fun R' : type1413 A B => @lem322508 A B R' R H lt2 h1). Qed.
Lemma lem322510 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term63 A B H lt2.
Proof. exact (h1). Qed.
Lemma lem322511 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (h1 : term38 A B H lt2 R') : term38 A B H lt2 R'.
Proof. exact (h1). Qed.
Lemma lem322512 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term64 A B H lt2 R R'.
Proof. exact (@lem322509 A B R H lt2 h1 R'). Qed.
Lemma lem322513 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (R' : type1413 A B) : (term64 A B H lt2 R R') = (term61 A B H lt2 R R').
Proof. exact (eq_refl (term64 A B H lt2 R R')). Qed.
Lemma lem322514 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term61 A B H lt2 R R'.
Proof. exact (EQ_MP (@lem322513 A B H lt2 R R') (@lem322512 A B R' R H lt2 h1)). Qed.
Lemma lem322515 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : R = (term44 A B H lt2)) : term60 A B R R'.
Proof. exact (@lem322514 A B R' R H lt2 h2 (@lem322511 A B H lt2 R' h1)). Qed.
Lemma lem322516 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term65 A B H lt2 R.
Proof. exact (@lem322510 A B H lt2 h1 R). Qed.
Lemma lem322517 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) : (term65 A B H lt2 R) = (term66 A B R H lt2).
Proof. exact (eq_refl (term65 A B H lt2 R)). Qed.
Lemma lem322518 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term66 A B R H lt2.
Proof. exact (EQ_MP (@lem322517 A B R H lt2) (@lem322516 A B R H lt2 h1)). Qed.
Lemma lem322519 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term67 A B R H lt2 R'.
Proof. exact (@lem322518 A B R H lt2 h1 R'). Qed.
Lemma lem322520 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) : (term67 A B R H lt2 R') = (term68 A B R H lt2 R').
Proof. exact (eq_refl (term67 A B R H lt2 R')). Qed.
Lemma lem322521 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term68 A B R H lt2 R'.
Proof. exact (EQ_MP (@lem322520 A B R H lt2 R') (@lem322519 A B R R' H lt2 h1)). Qed.
Lemma lem322522 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : R = (term44 A B H lt2)) : term69 A B R H lt2 R'.
Proof. exact (@lem322521 A B R R' H lt2 h2 (@lem322515 A B R' R H lt2 h1 h3)). Qed.
Lemma lem322523 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (h1 : term38 A B H lt2 R') : term39 A B H lt2 R' a0.
Proof. exact (@lem322511 A B H lt2 R' h1 a0). Qed.
Lemma lem322524 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (a0 : A) : (term39 A B H lt2 R' a0) = (term35 A B H lt2 R' a0).
Proof. exact (eq_refl (term39 A B H lt2 R' a0)). Qed.
Lemma lem322525 {A B : Type'} (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (h1 : term38 A B H lt2 R') : term35 A B H lt2 R' a0.
Proof. exact (EQ_MP (@lem322524 A B H lt2 R' a0) (@lem322523 A B a0 H lt2 R' h1)). Qed.
Lemma lem322526 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (h1 : term38 A B H lt2 R') : term40 A B H lt2 R' a0 a1.
Proof. exact (@lem322525 A B a0 H lt2 R' h1 a1). Qed.
Lemma lem322527 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (a0 : A) (a1 : B) : (term40 A B H lt2 R' a0 a1) = (term29 A B H lt2 R' a0 a1).
Proof. exact (eq_refl (term40 A B H lt2 R' a0 a1)). Qed.
Lemma lem322528 {A B : Type'} (a0 : A) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) (h1 : term38 A B H lt2 R') : term29 A B H lt2 R' a0 a1.
Proof. exact (EQ_MP (@lem322527 A B H lt2 R' a0 a1) (@lem322526 A B a0 a1 H lt2 R' h1)). Qed.
Lemma lem322529 {A B : Type'} (a0 : A) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : R = (term44 A B H lt2)) : term70 A B R H lt2 R' a0.
Proof. exact (@lem322522 A B R' R H lt2 h1 h2 h3 a0). Qed.
Lemma lem322530 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term70 A B R H lt2 R' a0) = (term71 A B R H lt2 a0 R').
Proof. exact (eq_refl (term70 A B R H lt2 R' a0)). Qed.
Lemma lem322531 {A B : Type'} (a0 : A) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : R = (term44 A B H lt2)) : term71 A B R H lt2 a0 R'.
Proof. exact (EQ_MP (@lem322530 A B R H lt2 a0 R') (@lem322529 A B a0 R' R H lt2 h1 h2 h3)). Qed.
Lemma lem322532 {A B : Type'} (a0 : A) (a1 : B) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : R = (term44 A B H lt2)) : term72 A B R H lt2 a0 R' a1.
Proof. exact (@lem322531 A B a0 R' R H lt2 h1 h2 h3 a1). Qed.
Lemma lem322533 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term72 A B R H lt2 a0 R' a1) = (term73 A B R a1 H lt2 a0 R').
Proof. exact (eq_refl (term72 A B R H lt2 a0 R' a1)). Qed.
Lemma lem322534 {A B : Type'} (a1 : B) (a0 : A) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : R = (term44 A B H lt2)) : term73 A B R a1 H lt2 a0 R'.
Proof. exact (EQ_MP (@lem322533 A B R a1 H lt2 a0 R') (@lem322532 A B a0 a1 R' R H lt2 h1 h2 h3)). Qed.
Lemma lem322535 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (R' : type1413 A B) (a0 : A) (a1 : B) : term74 A B H lt2 R R' a0 a1.
Proof. exact (@lem51 (term27 A B a1 H lt2 a0 R') (term27 A B a1 H lt2 a0 R) (R' a0 a1)). Qed.
Lemma lem322536 {A B : Type'} (a0 : A) (a1 : B) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : R = (term44 A B H lt2)) : term75 A B H lt2 R R' a0 a1.
Proof. exact (@lem322535 A B H lt2 R R' a0 a1 (@lem322534 A B a1 a0 R' R H lt2 h1 h2 h3)). Qed.
Lemma lem322537 {A B : Type'} (a0 : A) (a1 : B) (R' : type1413 A B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : R = (term44 A B H lt2)) : term76 A B H lt2 R R' a0 a1.
Proof. exact (@lem322536 A B a0 a1 R' R H lt2 h1 h2 h3 (@lem322528 A B a0 a1 H lt2 R' h1)). Qed.
Lemma lem322538 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (h1 : term27 A B a1 H lt2 a0 R) : term27 A B a1 H lt2 a0 R.
Proof. exact (h1). Qed.
Lemma lem322539 {A B : Type'} (R' : type1413 A B) (a1 : B) (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term38 A B H lt2 R') (h2 : term63 A B H lt2) (h3 : term27 A B a1 H lt2 a0 R) (h4 : R = (term44 A B H lt2)) : R' a0 a1.
Proof. exact (@lem322537 A B a0 a1 R' R H lt2 h1 h2 h4 (@lem322538 A B a1 H lt2 a0 R h3)). Qed.
Lemma lem322540 {A B : Type'} (R' : type1413 A B) (a1 : B) (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : term27 A B a1 H lt2 a0 R) (h3 : R = (term44 A B H lt2)) : term41 A B H lt2 R' a0 a1.
Proof. exact (fun h0 : term38 A B H lt2 R' => @lem322539 A B R' a1 a0 R H lt2 h0 h1 h2 h3). Qed.
Lemma lem322541 {A B : Type'} (a1 : B) (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : term27 A B a1 H lt2 a0 R) (h3 : R = (term44 A B H lt2)) : term49 A B H lt2 a0 a1.
Proof. exact (fun R' : type1413 A B => @lem322540 A B R' a1 a0 R H lt2 h1 h2 h3). Qed.
Lemma lem322542 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term53 A B R H lt2 a0.
Proof. exact (@lem322487 A B R H lt2 h1 a0). Qed.
Lemma lem322543 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) : (term53 A B R H lt2 a0) = (term51 A B R H lt2 a0).
Proof. exact (eq_refl (term53 A B R H lt2 a0)). Qed.
Lemma lem322544 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term51 A B R H lt2 a0.
Proof. exact (EQ_MP (@lem322543 A B R H lt2 a0) (@lem322542 A B a0 R H lt2 h1)). Qed.
Lemma lem322545 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term54 A B R H lt2 a0 a1.
Proof. exact (@lem322544 A B a0 R H lt2 h1 a1). Qed.
Lemma lem322546 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (a1 : B) : (term54 A B R H lt2 a0 a1) = ((R a0 a1) = (term49 A B H lt2 a0 a1)).
Proof. exact (eq_refl (term54 A B R H lt2 a0 a1)). Qed.
Lemma lem322547 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (R a0 a1) = (term49 A B H lt2 a0 a1).
Proof. exact (EQ_MP (@lem322546 A B R H lt2 a0 a1) (@lem322545 A B a0 a1 R H lt2 h1)). Qed.
Lemma lem322548 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (term49 A B H lt2 a0 a1) = (R a0 a1).
Proof. exact (SYM (@lem322547 A B a0 a1 R H lt2 h1)). Qed.
Lemma lem322549 {A B : Type'} (a1 : B) (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : term27 A B a1 H lt2 a0 R) (h3 : R = (term44 A B H lt2)) : R a0 a1.
Proof. exact (EQ_MP (@lem322548 A B a0 a1 R H lt2 h3) (@lem322541 A B a1 a0 R H lt2 h1 h2 h3)). Qed.
Lemma lem322550 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term29 A B H lt2 R a0 a1.
Proof. exact (fun h0 : term27 A B a1 H lt2 a0 R => @lem322549 A B a1 a0 R H lt2 h1 h0 h2). Qed.
Lemma lem322551 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term35 A B H lt2 R a0.
Proof. exact (fun a1 : B => @lem322550 A B a0 a1 R H lt2 h1 h2). Qed.
Lemma lem322552 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term38 A B H lt2 R.
Proof. exact (fun a0 : A => @lem322551 A B a0 R H lt2 h1 h2). Qed.
Lemma lem322555 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term77 A B H lt2 R a0) = (term77 A B H lt2 R a0).
Proof. exact (eq_refl (term77 A B H lt2 R a0)). Qed.
Lemma lem322556 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term77 A B H lt2 R a0) = (term78 A B H lt2 a0 R).
Proof. exact (eq_refl (term77 A B H lt2 R a0)). Qed.
Lemma lem322557 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term79 A B H lt2 R a0) = (term79 A B H lt2 R a0).
Proof. exact (eq_refl (term79 A B H lt2 R a0)). Qed.
Lemma lem322558 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : ((term77 A B H lt2 R a0) = (term77 A B H lt2 R a0)) = ((term77 A B H lt2 R a0) = (term78 A B H lt2 a0 R)).
Proof. exact (MK_COMB (@lem322557 A B H lt2 R a0) (@lem322556 A B H lt2 a0 R)). Qed.
Lemma lem322559 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term77 A B H lt2 R a0) = (term78 A B H lt2 a0 R).
Proof. exact (EQ_MP (@lem322558 A B H lt2 a0 R) (@lem322555 A B H lt2 R a0)). Qed.
Lemma lem322560 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem322561 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (a1 : B) : (term80 A B H lt2 R a0 a1) = (term81 A B H lt2 a0 R a1).
Proof. exact (MK_COMB (@lem322559 A B H lt2 a0 R) (@lem322560 B a1)). Qed.
Lemma lem322562 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term81 A B H lt2 a0 R a1) = (term27 A B a1 H lt2 a0 R).
Proof. exact (eq_refl (term81 A B H lt2 a0 R a1)). Qed.
Lemma lem322563 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : (term82 A B H lt2 R a0 a1) = (term82 A B H lt2 R a0 a1).
Proof. exact (eq_refl (term82 A B H lt2 R a0 a1)). Qed.
Lemma lem322564 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : ((term80 A B H lt2 R a0 a1) = (term81 A B H lt2 a0 R a1)) = ((term80 A B H lt2 R a0 a1) = (term27 A B a1 H lt2 a0 R)).
Proof. exact (MK_COMB (@lem322563 A B H lt2 R a0 a1) (@lem322562 A B a1 H lt2 a0 R)). Qed.
Lemma lem322565 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term80 A B H lt2 R a0 a1) = (term27 A B a1 H lt2 a0 R).
Proof. exact (EQ_MP (@lem322564 A B a1 H lt2 a0 R) (@lem322561 A B H lt2 a0 R a1)). Qed.
Lemma lem322566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322567 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term83 A B H lt2 R a0 a1) = (term84 A B a1 H lt2 a0 R).
Proof. exact (MK_COMB (@lem322566) (@lem322565 A B a1 H lt2 a0 R)). Qed.
Lemma lem322568 {A B : Type'} (R : type1413 A B) (a0 : A) (a1 : B) : (R a0 a1) = (R a0 a1).
Proof. exact (eq_refl (R a0 a1)). Qed.
Lemma lem322569 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : (term85 A B H lt2 R a0 a1) = (term29 A B H lt2 R a0 a1).
Proof. exact (MK_COMB (@lem322567 A B a1 H lt2 a0 R) (@lem322568 A B R a0 a1)). Qed.
Lemma lem322570 {A B : Type'} (a1 : B) (a0 : A) (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term86 A B a1 a0 H lt2 R) = (term86 A B a1 a0 H lt2 R).
Proof. exact (eq_refl (term86 A B a1 a0 H lt2 R)). Qed.
Lemma lem322571 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term87 A B H lt2 R a0 a1) = (term88 A B a1 H lt2 a0 R).
Proof. exact (MK_COMB (@lem322570 A B a1 a0 H lt2 R) (@lem322565 A B a1 H lt2 a0 R)). Qed.
Lemma lem322572 {A B : Type'} (R : type1413 A B) (a0 : A) (a1 : B) : (term89 A B R a0 a1) = (term89 A B R a0 a1).
Proof. exact (eq_refl (term89 A B R a0 a1)). Qed.
Lemma lem322573 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term90 A B H lt2 R a0 a1) = (term91 A B a1 H lt2 a0 R).
Proof. exact (MK_COMB (@lem322572 A B R a0 a1) (@lem322565 A B a1 H lt2 a0 R)). Qed.
Lemma lem322574 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term92 A B H lt2 R a0) = (term93 A B H lt2 a0 R).
Proof. exact (fun_ext (fun a1 : B => @lem322573 A B a1 H lt2 a0 R)). Qed.
Lemma lem322575 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem322576 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term94 A B H lt2 R a0) = (term95 A B H lt2 a0 R).
Proof. exact (MK_COMB (@lem322575 B) (@lem322574 A B H lt2 a0 R)). Qed.
Lemma lem322577 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term96 A B H lt2 R) = (term97 A B H lt2 R).
Proof. exact (fun_ext (fun a0 : A => @lem322576 A B H lt2 a0 R)). Qed.
Lemma lem322578 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem322579 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term98 A B H lt2 R) = (term99 A B H lt2 R).
Proof. exact (MK_COMB (@lem322578 A) (@lem322577 A B H lt2 R)). Qed.
Lemma lem322580 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term100 A B H lt2 R a0) = (term101 A B H lt2 a0 R).
Proof. exact (fun_ext (fun a1 : B => @lem322571 A B a1 H lt2 a0 R)). Qed.
Lemma lem322581 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem322582 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term102 A B H lt2 R a0) = (term103 A B H lt2 a0 R).
Proof. exact (MK_COMB (@lem322581 B) (@lem322580 A B H lt2 a0 R)). Qed.
Lemma lem322583 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term104 A B H lt2 R) = (term105 A B H lt2 R).
Proof. exact (fun_ext (fun a0 : A => @lem322582 A B H lt2 a0 R)). Qed.
Lemma lem322584 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem322585 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term106 A B H lt2 R) = (term107 A B H lt2 R).
Proof. exact (MK_COMB (@lem322584 A) (@lem322583 A B H lt2 R)). Qed.
Lemma lem322586 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term108 A B H lt2 R a0) = (term34 A B H lt2 R a0).
Proof. exact (fun_ext (fun a1 : B => @lem322569 A B H lt2 R a0 a1)). Qed.
Lemma lem322587 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem322588 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term109 A B H lt2 R a0) = (term35 A B H lt2 R a0).
Proof. exact (MK_COMB (@lem322587 B) (@lem322586 A B H lt2 R a0)). Qed.
Lemma lem322589 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term110 A B H lt2 R) = (term37 A B H lt2 R).
Proof. exact (fun_ext (fun a0 : A => @lem322588 A B H lt2 R a0)). Qed.
Lemma lem322590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem322591 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term111 A B H lt2 R) = (term38 A B H lt2 R).
Proof. exact (MK_COMB (@lem322590 A) (@lem322589 A B H lt2 R)). Qed.
Lemma lem322592 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term38 A B H lt2 R) = (term111 A B H lt2 R).
Proof. exact (SYM (@lem322591 A B H lt2 R)). Qed.
Lemma lem322593 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term111 A B H lt2 R.
Proof. exact (EQ_MP (@lem322592 A B H lt2 R) (@lem322552 A B R H lt2 h1 h2)). Qed.
Lemma lem322594 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term112 A B H lt2 R.
Proof. exact (@lem322510 A B H lt2 h1 (term113 A B H lt2 R)). Qed.
Lemma lem322595 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) : (term112 A B H lt2 R) = (term114 A B R H lt2).
Proof. exact (eq_refl (term112 A B H lt2 R)). Qed.
Lemma lem322596 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term114 A B R H lt2.
Proof. exact (EQ_MP (@lem322595 A B R H lt2) (@lem322594 A B R H lt2 h1)). Qed.
Lemma lem322597 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term115 A B H lt2 R.
Proof. exact (@lem322596 A B R H lt2 h1 R). Qed.
Lemma lem322598 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term115 A B H lt2 R) = (term116 A B H lt2 R).
Proof. exact (eq_refl (term115 A B H lt2 R)). Qed.
Lemma lem322599 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) : term116 A B H lt2 R.
Proof. exact (EQ_MP (@lem322598 A B H lt2 R) (@lem322597 A B R H lt2 h1)). Qed.
Lemma lem322600 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term107 A B H lt2 R.
Proof. exact (@lem322599 A B R H lt2 h1 (@lem322593 A B R H lt2 h1 h2)). Qed.
Lemma lem322601 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term107 A B H lt2 R) = (term106 A B H lt2 R).
Proof. exact (SYM (@lem322585 A B H lt2 R)). Qed.
Lemma lem322602 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term106 A B H lt2 R.
Proof. exact (EQ_MP (@lem322601 A B H lt2 R) (@lem322600 A B R H lt2 h1 h2)). Qed.
Lemma lem322603 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term117 A B H lt2 R.
Proof. exact (@lem322509 A B R H lt2 h1 (term113 A B H lt2 R)). Qed.
Lemma lem322604 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term117 A B H lt2 R) = (term118 A B H lt2 R).
Proof. exact (eq_refl (term117 A B H lt2 R)). Qed.
Lemma lem322605 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term118 A B H lt2 R.
Proof. exact (EQ_MP (@lem322604 A B H lt2 R) (@lem322603 A B R H lt2 h1)). Qed.
Lemma lem322606 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term98 A B H lt2 R.
Proof. exact (@lem322605 A B R H lt2 h2 (@lem322602 A B R H lt2 h1 h2)). Qed.
Lemma lem322607 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term99 A B H lt2 R.
Proof. exact (EQ_MP (@lem322579 A B H lt2 R) (@lem322606 A B R H lt2 h1 h2)). Qed.
Lemma lem322608 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term39 A B H lt2 R a0.
Proof. exact (@lem322552 A B R H lt2 h1 h2 a0). Qed.
Lemma lem322609 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) : (term39 A B H lt2 R a0) = (term35 A B H lt2 R a0).
Proof. exact (eq_refl (term39 A B H lt2 R a0)). Qed.
Lemma lem322610 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term35 A B H lt2 R a0.
Proof. exact (EQ_MP (@lem322609 A B H lt2 R a0) (@lem322608 A B a0 R H lt2 h1 h2)). Qed.
Lemma lem322611 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term40 A B H lt2 R a0 a1.
Proof. exact (@lem322610 A B a0 R H lt2 h1 h2 a1). Qed.
Lemma lem322612 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (a0 : A) (a1 : B) : (term40 A B H lt2 R a0 a1) = (term29 A B H lt2 R a0 a1).
Proof. exact (eq_refl (term40 A B H lt2 R a0 a1)). Qed.
Lemma lem322613 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term29 A B H lt2 R a0 a1.
Proof. exact (EQ_MP (@lem322612 A B H lt2 R a0 a1) (@lem322611 A B a0 a1 R H lt2 h1 h2)). Qed.
Lemma lem322614 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term119 A B H lt2 R a0.
Proof. exact (@lem322607 A B R H lt2 h1 h2 a0). Qed.
Lemma lem322615 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term119 A B H lt2 R a0) = (term95 A B H lt2 a0 R).
Proof. exact (eq_refl (term119 A B H lt2 R a0)). Qed.
Lemma lem322616 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term95 A B H lt2 a0 R.
Proof. exact (EQ_MP (@lem322615 A B H lt2 a0 R) (@lem322614 A B a0 R H lt2 h1 h2)). Qed.
Lemma lem322617 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term120 A B H lt2 a0 R a1.
Proof. exact (@lem322616 A B a0 R H lt2 h1 h2 a1). Qed.
Lemma lem322618 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term120 A B H lt2 a0 R a1) = (term91 A B a1 H lt2 a0 R).
Proof. exact (eq_refl (term120 A B H lt2 a0 R a1)). Qed.
Lemma lem322619 {A B : Type'} (a1 : B) (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term91 A B a1 H lt2 a0 R.
Proof. exact (EQ_MP (@lem322618 A B a1 H lt2 a0 R) (@lem322617 A B a0 a1 R H lt2 h1 h2)). Qed.
Lemma lem322620 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term121 A B H lt2 R a0 a1.
Proof. exact (conj (@lem322619 A B a1 a0 R H lt2 h1 h2) (@lem322613 A B a0 a1 R H lt2 h1 h2)). Qed.
Lemma lem322621 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term121 A B H lt2 R a0 a1) = ((R a0 a1) = (term27 A B a1 H lt2 a0 R)).
Proof. exact (@lem32 (R a0 a1) (term27 A B a1 H lt2 a0 R)). Qed.
Lemma lem322622 {A B : Type'} (a1 : B) (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : (R a0 a1) = (term27 A B a1 H lt2 a0 R).
Proof. exact (EQ_MP (@lem322621 A B a1 H lt2 a0 R) (@lem322620 A B a0 a1 R H lt2 h1 h2)). Qed.
Lemma lem322623 {A B : Type'} (a0 : A) (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term122 A B H lt2 a0 R.
Proof. exact (fun a1 : B => @lem322622 A B a1 a0 R H lt2 h1 h2). Qed.
Lemma lem322628 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term38 A B H lt2 R.
Proof. exact (fun a0 : A => @lem322551 A B a0 R H lt2 h1 h2). Qed.
Lemma lem322629 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term123 A B H lt2 R.
Proof. exact (fun a0 : A => @lem322623 A B a0 R H lt2 h1 h2). Qed.
Lemma lem322630 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term62 A B H lt2 R.
Proof. exact (fun R' : type1413 A B => @lem322508 A B R' R H lt2 h2). Qed.
Lemma lem322631 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term3 A B lt2 R H.
Proof. exact (EQ_MP (@lem322472 A B lt2 R H) (@lem322628 A B R H lt2 h1 h2)). Qed.
Lemma lem322645 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) : (term38 A B H lt2 R) = (term3 A B lt2 R H).
Proof. exact (SYM (@lem322471 A B H lt2 R)). Qed.
Lemma lem322646 {A B : Type'} (lt2 : type1402 A) (R : type1413 A B) (H : type549 A B) : (term38 A B H lt2 R) = (term3 A B lt2 R H).
Proof. exact (@lem322645 A B lt2 R H). Qed.
Lemma lem322647 {A B : Type'} (lt2 : type1402 A) (R' : type1413 A B) (H : type549 A B) : (term38 A B H lt2 R') = (term3 A B lt2 R' H).
Proof. exact (@lem322646 A B lt2 R' H). Qed.
Lemma lem322648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322649 {A B : Type'} (lt2 : type1402 A) (R' : type1413 A B) (H : type549 A B) : (term124 A B H lt2 R') = (term125 A B lt2 R' H).
Proof. exact (MK_COMB (@lem322648) (@lem322647 A B lt2 R' H)). Qed.
Lemma lem322688 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term60 A B R R') = (term60 A B R R').
Proof. exact (eq_refl (term60 A B R R')). Qed.
Lemma lem322689 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (R : type1413 A B) (R' : type1413 A B) : (term61 A B H lt2 R R') = (term126 A B lt2 H R R').
Proof. exact (MK_COMB (@lem322649 A B lt2 R' H) (@lem322688 A B R R')). Qed.
Lemma lem322690 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (R : type1413 A B) : (term127 A B H lt2 R) = (term128 A B lt2 H R).
Proof. exact (fun_ext (fun R' : type1413 A B => @lem322689 A B lt2 H R R')). Qed.
Lemma lem322691 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem322692 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (R : type1413 A B) : (term62 A B H lt2 R) = (term129 A B lt2 H R).
Proof. exact (MK_COMB (@lem322691 A B) (@lem322690 A B lt2 H R)). Qed.
Lemma lem322693 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term129 A B lt2 H R.
Proof. exact (EQ_MP (@lem322692 A B lt2 H R) (@lem322630 A B R H lt2 h1 h2)). Qed.
Lemma lem322694 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term130 A B H lt2 R.
Proof. exact (conj (@lem322693 A B R H lt2 h1 h2) (@lem322629 A B R H lt2 h1 h2)). Qed.
Lemma lem322695 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : term63 A B H lt2) (h2 : R = (term44 A B H lt2)) : term131 A B H lt2 R.
Proof. exact (conj (@lem322631 A B R H lt2 h1 h2) (@lem322694 A B R H lt2 h1 h2)). Qed.
Lemma lem322696 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term60 A B R R'.
Proof. exact (h1). Qed.
Lemma lem322698 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term132 A P Q.
Proof. exact (fun h0 : term133 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem322699 {A B : Type'} (P : type572 A B) (Q : type572 A B) : term134 A B P Q.
Proof. exact (@lem322698 (A -> B) P Q). Qed.
Lemma lem322700 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : term135 A B R a1 H lt2 a0 R'.
Proof. exact (@lem322699 A B (term28 A B a1 H lt2 a0 R) (term28 A B a1 H lt2 a0 R')). Qed.
Lemma lem322701 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) : (term136 A B a1 H lt2 a0 R f) = (term1 A B a1 H lt2 a0 R f).
Proof. exact (eq_refl (term136 A B a1 H lt2 a0 R f)). Qed.
Lemma lem322702 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322703 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) : (term137 A B a1 H lt2 a0 R f) = (term138 A B a1 H lt2 a0 R f).
Proof. exact (MK_COMB (@lem322702) (@lem322701 A B a1 H lt2 a0 R f)). Qed.
Lemma lem322704 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term136 A B a1 H lt2 a0 R' f) = (term1 A B a1 H lt2 a0 R' f).
Proof. exact (eq_refl (term136 A B a1 H lt2 a0 R' f)). Qed.
Lemma lem322705 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term139 A B R a1 H lt2 a0 R' f) = (term140 A B R a1 H lt2 a0 R' f).
Proof. exact (MK_COMB (@lem322703 A B a1 H lt2 a0 R f) (@lem322704 A B a1 H lt2 a0 R' f)). Qed.
Lemma lem322706 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term141 A B R a1 H lt2 a0 R') = (term142 A B R a1 H lt2 a0 R').
Proof. exact (fun_ext (fun f : A -> B => @lem322705 A B R a1 H lt2 a0 R' f)). Qed.
Lemma lem322707 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem322708 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term143 A B R a1 H lt2 a0 R') = (term144 A B R a1 H lt2 a0 R').
Proof. exact (MK_COMB (@lem322707 A B) (@lem322706 A B R a1 H lt2 a0 R')). Qed.
Lemma lem322709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322710 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term145 A B R a1 H lt2 a0 R') = (term146 A B R a1 H lt2 a0 R').
Proof. exact (MK_COMB (@lem322709) (@lem322708 A B R a1 H lt2 a0 R')). Qed.
Lemma lem322711 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) : (term136 A B a1 H lt2 a0 R f) = (term1 A B a1 H lt2 a0 R f).
Proof. exact (eq_refl (term136 A B a1 H lt2 a0 R f)). Qed.
Lemma lem322712 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term147 A B a1 H lt2 a0 R) = (term28 A B a1 H lt2 a0 R).
Proof. exact (fun_ext (fun f : A -> B => @lem322711 A B a1 H lt2 a0 R f)). Qed.
Lemma lem322713 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem322714 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term148 A B a1 H lt2 a0 R) = (term27 A B a1 H lt2 a0 R).
Proof. exact (MK_COMB (@lem322713 A B) (@lem322712 A B a1 H lt2 a0 R)). Qed.
Lemma lem322715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322716 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) : (term149 A B a1 H lt2 a0 R) = (term84 A B a1 H lt2 a0 R).
Proof. exact (MK_COMB (@lem322715) (@lem322714 A B a1 H lt2 a0 R)). Qed.
Lemma lem322717 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term136 A B a1 H lt2 a0 R' f) = (term1 A B a1 H lt2 a0 R' f).
Proof. exact (eq_refl (term136 A B a1 H lt2 a0 R' f)). Qed.
Lemma lem322718 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term147 A B a1 H lt2 a0 R') = (term28 A B a1 H lt2 a0 R').
Proof. exact (fun_ext (fun f : A -> B => @lem322717 A B a1 H lt2 a0 R' f)). Qed.
Lemma lem322719 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem322720 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term148 A B a1 H lt2 a0 R') = (term27 A B a1 H lt2 a0 R').
Proof. exact (MK_COMB (@lem322719 A B) (@lem322718 A B a1 H lt2 a0 R')). Qed.
Lemma lem322721 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term150 A B R a1 H lt2 a0 R') = (term73 A B R a1 H lt2 a0 R').
Proof. exact (MK_COMB (@lem322716 A B a1 H lt2 a0 R) (@lem322720 A B a1 H lt2 a0 R')). Qed.
Lemma lem322722 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : (term135 A B R a1 H lt2 a0 R') = (term151 A B R a1 H lt2 a0 R').
Proof. exact (MK_COMB (@lem322710 A B R a1 H lt2 a0 R') (@lem322721 A B R a1 H lt2 a0 R')). Qed.
Lemma lem322725 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term152 A C B D.
Proof. exact (fun h0 : term153 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem322727 {A B : Type'} (a1 : B) (H : type549 A B) (f : A -> B) (a0 : A) : term154 A B a1 H f a0.
Proof. exact (@lem9120 (a1 = (H f a0))). Qed.
Lemma lem322728 {A B : Type'} (a1 : B) (H : type549 A B) (f : A -> B) (a0 : A) : (term154 A B a1 H f a0) = (term155 A B a1 H f a0).
Proof. exact (eq_refl (term154 A B a1 H f a0)). Qed.
Lemma lem322729 {A B : Type'} (a1 : B) (H : type549 A B) (f : A -> B) (a0 : A) : term155 A B a1 H f a0.
Proof. exact (EQ_MP (@lem322728 A B a1 H f a0) (@lem322727 A B a1 H f a0)). Qed.
Lemma lem322731 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term156 A P Q.
Proof. exact (fun h0 : term133 A P Q => @lem7362 A P Q h0). Qed.
Lemma lem322732 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term156 A P Q.
Proof. exact (@lem322731 A P Q). Qed.
Lemma lem322733 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : term157 A B R lt2 a0 R' f.
Proof. exact (@lem322732 A (term158 A B lt2 a0 R f) (term158 A B lt2 a0 R' f)). Qed.
Lemma lem322734 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (z : A) : (term159 A B lt2 a0 R f z) = (term160 A B lt2 a0 R f z).
Proof. exact (eq_refl (term159 A B lt2 a0 R f z)). Qed.
Lemma lem322735 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322736 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (z : A) : (term161 A B lt2 a0 R f z) = (term162 A B lt2 a0 R f z).
Proof. exact (MK_COMB (@lem322735) (@lem322734 A B lt2 a0 R f z)). Qed.
Lemma lem322737 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) (z : A) : (term159 A B lt2 a0 R' f z) = (term160 A B lt2 a0 R' f z).
Proof. exact (eq_refl (term159 A B lt2 a0 R' f z)). Qed.
Lemma lem322738 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) (z : A) : (term163 A B R lt2 a0 R' f z) = (term164 A B R lt2 a0 R' f z).
Proof. exact (MK_COMB (@lem322736 A B lt2 a0 R f z) (@lem322737 A B lt2 a0 R' f z)). Qed.
Lemma lem322739 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term165 A B R lt2 a0 R' f) = (term166 A B R lt2 a0 R' f).
Proof. exact (fun_ext (fun z : A => @lem322738 A B R lt2 a0 R' f z)). Qed.
Lemma lem322740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem322741 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term167 A B R lt2 a0 R' f) = (term168 A B R lt2 a0 R' f).
Proof. exact (MK_COMB (@lem322740 A) (@lem322739 A B R lt2 a0 R' f)). Qed.
Lemma lem322742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322743 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term169 A B R lt2 a0 R' f) = (term170 A B R lt2 a0 R' f).
Proof. exact (MK_COMB (@lem322742) (@lem322741 A B R lt2 a0 R' f)). Qed.
Lemma lem322744 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) (z : A) : (term159 A B lt2 a0 R f z) = (term160 A B lt2 a0 R f z).
Proof. exact (eq_refl (term159 A B lt2 a0 R f z)). Qed.
Lemma lem322745 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) : (term171 A B lt2 a0 R f) = (term158 A B lt2 a0 R f).
Proof. exact (fun_ext (fun z : A => @lem322744 A B lt2 a0 R f z)). Qed.
Lemma lem322746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem322747 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) : (term172 A B lt2 a0 R f) = (term2 A B lt2 a0 R f).
Proof. exact (MK_COMB (@lem322746 A) (@lem322745 A B lt2 a0 R f)). Qed.
Lemma lem322748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322749 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (f : A -> B) : (term173 A B lt2 a0 R f) = (term174 A B lt2 a0 R f).
Proof. exact (MK_COMB (@lem322748) (@lem322747 A B lt2 a0 R f)). Qed.
Lemma lem322750 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) (z : A) : (term159 A B lt2 a0 R' f z) = (term160 A B lt2 a0 R' f z).
Proof. exact (eq_refl (term159 A B lt2 a0 R' f z)). Qed.
Lemma lem322751 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term171 A B lt2 a0 R' f) = (term158 A B lt2 a0 R' f).
Proof. exact (fun_ext (fun z : A => @lem322750 A B lt2 a0 R' f z)). Qed.
Lemma lem322752 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem322753 {A B : Type'} (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term172 A B lt2 a0 R' f) = (term2 A B lt2 a0 R' f).
Proof. exact (MK_COMB (@lem322752 A) (@lem322751 A B lt2 a0 R' f)). Qed.
Lemma lem322754 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term175 A B R lt2 a0 R' f) = (term176 A B R lt2 a0 R' f).
Proof. exact (MK_COMB (@lem322749 A B lt2 a0 R f) (@lem322753 A B lt2 a0 R' f)). Qed.
Lemma lem322755 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : (term157 A B R lt2 a0 R' f) = (term177 A B R lt2 a0 R' f).
Proof. exact (MK_COMB (@lem322743 A B R lt2 a0 R' f) (@lem322754 A B R lt2 a0 R' f)). Qed.
Lemma lem322758 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term178 A C B D.
Proof. exact (fun h0 : term153 B A C D => @lem7249 B A C D h0). Qed.
Lemma lem322760 {A : Type'} (lt2 : type1402 A) (z : A) (a0 : A) : term179 A lt2 z a0.
Proof. exact (@lem9120 (lt2 z a0)). Qed.
Lemma lem322761 {A : Type'} (lt2 : type1402 A) (z : A) (a0 : A) : (term179 A lt2 z a0) = (term180 A lt2 z a0).
Proof. exact (eq_refl (term179 A lt2 z a0)). Qed.
Lemma lem322762 {A : Type'} (lt2 : type1402 A) (z : A) (a0 : A) : term180 A lt2 z a0.
Proof. exact (EQ_MP (@lem322761 A lt2 z a0) (@lem322760 A lt2 z a0)). Qed.
Lemma lem322763 {A B : Type'} (a0 : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term181 A B R R' a0.
Proof. exact (@lem322696 A B R R' h1 a0). Qed.
Lemma lem322764 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (a0 : A) : (term181 A B R R' a0) = (term59 A B R R' a0).
Proof. exact (eq_refl (term181 A B R R' a0)). Qed.
Lemma lem322765 {A B : Type'} (a0 : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term59 A B R R' a0.
Proof. exact (EQ_MP (@lem322764 A B R R' a0) (@lem322763 A B a0 R R' h1)). Qed.
Lemma lem322766 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term182 A B R R' a0 a1.
Proof. exact (@lem322765 A B a0 R R' h1 a1). Qed.
Lemma lem322767 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (a0 : A) (a1 : B) : (term182 A B R R' a0 a1) = (term58 A B R R' a0 a1).
Proof. exact (eq_refl (term182 A B R R' a0 a1)). Qed.
Lemma lem322768 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term58 A B R R' a0 a1.
Proof. exact (EQ_MP (@lem322767 A B R R' a0 a1) (@lem322766 A B a0 a1 R R' h1)). Qed.
Lemma lem322769 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (a0 : A) (a1 : B) : (term58 A B R R' a0 a1) = ((term58 A B R R' a0 a1) = True).
Proof. exact (@lem7 (term58 A B R R' a0 a1)). Qed.
Lemma lem322772 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : (term58 A B R R' a0 a1) = True.
Proof. exact (EQ_MP (@lem322769 A B R R' a0 a1) (@lem322768 A B a0 a1 R R' h1)). Qed.
Lemma lem322773 {A B : Type'} (a0 : A) (a1 : B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : (term58 A B R R' a0 a1) = True.
Proof. exact (@lem322772 A B a0 a1 R R' h1). Qed.
Lemma lem322774 {A B : Type'} (f : A -> B) (z : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : (term183 A B R R' f z) = True.
Proof. exact (@lem322773 A B z (f z) R R' h1). Qed.
Lemma lem322775 {A B : Type'} (f : A -> B) (z : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : True = (term183 A B R R' f z).
Proof. exact (SYM (@lem322774 A B f z R R' h1)). Qed.
Lemma lem322776 {A B : Type'} (f : A -> B) (z : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term183 A B R R' f z.
Proof. exact (EQ_MP (@lem322775 A B f z R R' h1) (@lem0)). Qed.
Lemma lem322777 {A B : Type'} (lt2 : type1402 A) (a0 : A) (f : A -> B) (z : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term184 A B lt2 a0 R R' f z.
Proof. exact (conj (@lem322762 A lt2 z a0) (@lem322776 A B f z R R' h1)). Qed.
Lemma lem322779 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) (z : A) : term185 A B R lt2 a0 R' f z.
Proof. exact (@lem322758 (lt2 z a0) (term186 A B R f z) (lt2 z a0) (term186 A B R' f z)). Qed.
Lemma lem322780 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) (z : A) : term185 A B R lt2 a0 R' f z.
Proof. exact (@lem322779 A B R lt2 a0 R' f z). Qed.
Lemma lem322781 {A B : Type'} (lt2 : type1402 A) (a0 : A) (f : A -> B) (z : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term164 A B R lt2 a0 R' f z.
Proof. exact (@lem322780 A B R lt2 a0 R' f z (@lem322777 A B lt2 a0 f z R R' h1)). Qed.
Lemma lem322786 {A B : Type'} (lt2 : type1402 A) (a0 : A) (f : A -> B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term168 A B R lt2 a0 R' f.
Proof. exact (fun z : A => @lem322781 A B lt2 a0 f z R R' h1). Qed.
Lemma lem322788 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : term177 A B R lt2 a0 R' f.
Proof. exact (EQ_MP (@lem322755 A B R lt2 a0 R' f) (@lem322733 A B R lt2 a0 R' f)). Qed.
Lemma lem322789 {A B : Type'} (R : type1413 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : term177 A B R lt2 a0 R' f.
Proof. exact (@lem322788 A B R lt2 a0 R' f). Qed.
Lemma lem322790 {A B : Type'} (lt2 : type1402 A) (a0 : A) (f : A -> B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term176 A B R lt2 a0 R' f.
Proof. exact (@lem322789 A B R lt2 a0 R' f (@lem322786 A B lt2 a0 f R R' h1)). Qed.
Lemma lem322791 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (f : A -> B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term187 A B a1 H R lt2 a0 R' f.
Proof. exact (conj (@lem322729 A B a1 H f a0) (@lem322790 A B lt2 a0 f R R' h1)). Qed.
Lemma lem322793 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : term188 A B R a1 H lt2 a0 R' f.
Proof. exact (@lem322725 (a1 = (H f a0)) (term2 A B lt2 a0 R f) (a1 = (H f a0)) (term2 A B lt2 a0 R' f)). Qed.
Lemma lem322794 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) (f : A -> B) : term188 A B R a1 H lt2 a0 R' f.
Proof. exact (@lem322793 A B R a1 H lt2 a0 R' f). Qed.
Lemma lem322795 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (f : A -> B) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term140 A B R a1 H lt2 a0 R' f.
Proof. exact (@lem322794 A B R a1 H lt2 a0 R' f (@lem322791 A B a1 H lt2 a0 f R R' h1)). Qed.
Lemma lem322800 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term144 A B R a1 H lt2 a0 R'.
Proof. exact (fun f : A -> B => @lem322795 A B a1 H lt2 a0 f R R' h1). Qed.
Lemma lem322802 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : term151 A B R a1 H lt2 a0 R'.
Proof. exact (EQ_MP (@lem322722 A B R a1 H lt2 a0 R') (@lem322700 A B R a1 H lt2 a0 R')). Qed.
Lemma lem322803 {A B : Type'} (R : type1413 A B) (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R' : type1413 A B) : term151 A B R a1 H lt2 a0 R'.
Proof. exact (@lem322802 A B R a1 H lt2 a0 R'). Qed.
Lemma lem322804 {A B : Type'} (a1 : B) (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term73 A B R a1 H lt2 a0 R'.
Proof. exact (@lem322803 A B R a1 H lt2 a0 R' (@lem322800 A B a1 H lt2 a0 R R' h1)). Qed.
Lemma lem322809 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (a0 : A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term71 A B R H lt2 a0 R'.
Proof. exact (fun a1 : B => @lem322804 A B a1 H lt2 a0 R R' h1). Qed.
Lemma lem322814 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term69 A B R H lt2 R'.
Proof. exact (fun a0 : A => @lem322809 A B H lt2 a0 R R' h1). Qed.
Lemma lem322815 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : (term60 A B R R') = (term69 A B R H lt2 R').
Proof. exact (prop_ext (fun h2 : term60 A B R R' => @lem322814 A B H lt2 R R' h1) (fun h2 : term69 A B R H lt2 R' => @lem322696 A B R R' h1)). Qed.
Lemma lem322816 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) (R' : type1413 A B) (h1 : term60 A B R R') : term69 A B R H lt2 R'.
Proof. exact (EQ_MP (@lem322815 A B H lt2 R R' h1) (@lem322696 A B R R' h1)). Qed.
Lemma lem322817 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (R' : type1413 A B) : term68 A B R H lt2 R'.
Proof. exact (fun h0 : term60 A B R R' => @lem322816 A B H lt2 R R' h0). Qed.
Lemma lem322822 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) : term66 A B R H lt2.
Proof. exact (fun R' : type1413 A B => @lem322817 A B R H lt2 R'). Qed.
Lemma lem322827 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : term63 A B H lt2.
Proof. exact (fun R : type1413 A B => @lem322822 A B R H lt2). Qed.
Lemma lem322828 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : (term63 A B H lt2) = (term131 A B H lt2 R).
Proof. exact (prop_ext (fun h2 : term63 A B H lt2 => @lem322695 A B R H lt2 h2 h1) (fun h2 : term131 A B H lt2 R => @lem322827 A B H lt2)). Qed.
Lemma lem322829 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term131 A B H lt2 R.
Proof. exact (EQ_MP (@lem322828 A B R H lt2 h1) (@lem322827 A B H lt2)). Qed.
Lemma lem322830 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : R = (term44 A B H lt2).
Proof. exact (h1). Qed.
Lemma lem322831 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : term189 A B H lt2 R.
Proof. exact (fun h0 : R = (term44 A B H lt2) => @lem322829 A B R H lt2 h0). Qed.
Lemma lem322832 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : term189 A B H lt2 R.
Proof. exact (@lem322831 A B H lt2 R). Qed.
Lemma lem322833 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term131 A B H lt2 R.
Proof. exact (@lem322832 A B H lt2 R (@lem322830 A B R H lt2 h1)). Qed.
Lemma lem322834 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term190 A B H lt2 R) = (term131 A B H lt2 R).
Proof. exact (eq_refl (term190 A B H lt2 R)). Qed.
Lemma lem322835 {A B : Type'} : term191 A B.
Proof. exact (@lem9102 (type1413 A B)). Qed.
Lemma lem322836 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : term192 A B H lt2.
Proof. exact (@lem322835 A B (term193 A B H lt2)). Qed.
Lemma lem322837 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : (term192 A B H lt2) = (term194 A B H lt2).
Proof. exact (eq_refl (term192 A B H lt2)). Qed.
Lemma lem322838 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : term194 A B H lt2.
Proof. exact (EQ_MP (@lem322837 A B H lt2) (@lem322836 A B H lt2)). Qed.
Lemma lem322839 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : term195 A B H lt2.
Proof. exact (@lem322838 A B H lt2 (term44 A B H lt2)). Qed.
Lemma lem322840 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : (term195 A B H lt2) = (term196 A B H lt2).
Proof. exact (eq_refl (term195 A B H lt2)). Qed.
Lemma lem322841 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : term196 A B H lt2.
Proof. exact (EQ_MP (@lem322840 A B H lt2) (@lem322839 A B H lt2)). Qed.
Lemma lem322842 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : (term131 A B H lt2 R) = (term190 A B H lt2 R).
Proof. exact (SYM (@lem322834 A B H lt2 R)). Qed.
Lemma lem322843 {A B : Type'} (R : type1413 A B) (H : type549 A B) (lt2 : type1402 A) (h1 : R = (term44 A B H lt2)) : term190 A B H lt2 R.
Proof. exact (EQ_MP (@lem322842 A B H lt2 R) (@lem322833 A B R H lt2 h1)). Qed.
Lemma lem322844 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (R : type1413 A B) : term197 A B H lt2 R.
Proof. exact (fun h0 : R = (term44 A B H lt2) => @lem322843 A B R H lt2 h0). Qed.
Lemma lem322845 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : term198 A B H lt2.
Proof. exact (fun R : type1413 A B => @lem322844 A B H lt2 R). Qed.
Lemma lem322846 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) : term199 A B H lt2.
Proof. exact (@lem322841 A B H lt2 (@lem322845 A B H lt2)). Qed.
