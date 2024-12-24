Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9396_term_abbrevs.
Require Import ETA_AX_spec.
Require Import SELECT_AX_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm297_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem9308 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem9309 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem9310 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem9309 A B t) (@lem9308 A B t)). Qed.
Lemma lem9311 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (@lem9221 A P). Qed.
Lemma lem9312 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem9313 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (EQ_MP (@lem9312 A P) (@lem9311 A P)). Qed.
Lemma lem9314 {A : Type'} (P : A -> Prop) (x : A) : term4 A P x.
Proof. exact (@lem9313 A P x). Qed.
Lemma lem9315 {A : Type'} (x : A) (P : A -> Prop) : (term4 A P x) = (term5 A x P).
Proof. exact (eq_refl (term4 A P x)). Qed.
Lemma lem9316 {A : Type'} (x : A) (P : A -> Prop) : term5 A x P.
Proof. exact (EQ_MP (@lem9315 A x P) (@lem9314 A P x)). Qed.
Lemma lem9317 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem9318 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term6 A P.
Proof. exact (@lem9316 A x P (@lem9317 A P x h1)). Qed.
Lemma lem9319 {A : Type'} (P : A -> Prop) : (term6 A P) = ((term6 A P) = True).
Proof. exact (@lem7 (term6 A P)). Qed.
Lemma lem9320 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : (term6 A P) = True.
Proof. exact (EQ_MP (@lem9319 A P) (@lem9318 A P x h1)). Qed.
Lemma lem9325 {A : Type'} (x : A) (P : A -> Prop) : term7 A x P.
Proof. exact (fun h0 : P x => @lem9320 A P x h0). Qed.
Lemma lem9326 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (fun x : A => @lem9325 A x P). Qed.
Lemma lem9328 {_216 : Type'} (P : _216 -> Prop) (Q : Prop) : (term9 _216 P Q) = (term10 _216 P Q).
Proof. exact (@lem297 _216 P Q). Qed.
Lemma lem9329 {A : Type'} (P : A -> Prop) (Q : Prop) : (term9 A P Q) = (term10 A P Q).
Proof. exact (@lem9328 A P Q). Qed.
Lemma lem9330 {A : Type'} (P : A -> Prop) : (term8 A P) = (term11 A P).
Proof. exact (@lem9329 A P ((term6 A P) = True)). Qed.
Lemma lem9337 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term12 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem9338 (p : Prop) (q : Prop) (p' : Prop) : term13 p q p'.
Proof. exact (fun q' : Prop => @lem9337 p q p' q'). Qed.
Lemma lem9339 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (fun p' : Prop => @lem9338 p q p'). Qed.
Lemma lem9340 {A : Type'} (P : A -> Prop) : term15 A P.
Proof. exact (@lem9339 (ex P) (term6 A P)). Qed.
Lemma lem9341 {A : Type'} (P : A -> Prop) (p' : Prop) : term16 A P p'.
Proof. exact (@lem9340 A P p'). Qed.
Lemma lem9342 {A : Type'} (P : A -> Prop) (p' : Prop) : (term16 A P p') = (term17 A P p').
Proof. exact (eq_refl (term16 A P p')). Qed.
Lemma lem9343 {A : Type'} (P : A -> Prop) (p' : Prop) : term17 A P p'.
Proof. exact (EQ_MP (@lem9342 A P p') (@lem9341 A P p')). Qed.
Lemma lem9344 {A : Type'} (P : A -> Prop) (p' : Prop) (q' : Prop) : term18 A P p' q'.
Proof. exact (@lem9343 A P p' q'). Qed.
Lemma lem9345 {A : Type'} (P : A -> Prop) (p' : Prop) (q' : Prop) : (term18 A P p' q') = (term19 A P p' q').
Proof. exact (eq_refl (term18 A P p' q')). Qed.
Lemma lem9346 {A : Type'} (P : A -> Prop) (p' : Prop) (q' : Prop) : term19 A P p' q'.
Proof. exact (EQ_MP (@lem9345 A P p' q') (@lem9344 A P p' q')). Qed.
Lemma lem9353 {A : Type'} (P : A -> Prop) : (ex P) = (ex P).
Proof. exact (eq_refl (ex P)). Qed.
Lemma lem9354 {A : Type'} (P : A -> Prop) (q' : Prop) : term20 A P q'.
Proof. exact (@lem9346 A P (ex P) q'). Qed.
Lemma lem9355 {A : Type'} (P : A -> Prop) (q' : Prop) : term21 A P q'.
Proof. exact (@lem9354 A P q' (@lem9353 A P)). Qed.
Lemma lem9356 {A : Type'} (P : A -> Prop) (h1 : ex P) : ex P.
Proof. exact (h1). Qed.
Lemma lem9357 {A : Type'} (P : A -> Prop) : (ex P) = ((ex P) = True).
Proof. exact (@lem7 (ex P)). Qed.
Lemma lem9360 {A : Type'} (P : A -> Prop) : term11 A P.
Proof. exact (EQ_MP (@lem9330 A P) (@lem9326 A P)). Qed.
Lemma lem9361 {A : Type'} (P : A -> Prop) : term11 A P.
Proof. exact (@lem9360 A P). Qed.
Lemma lem9370 {A : Type'} (t : A -> Prop) : (term22 A t) = t.
Proof. exact (@lem9310 A Prop t). Qed.
Lemma lem9371 {A : Type'} (P : A -> Prop) : (term22 A P) = P.
Proof. exact (@lem9370 A P). Qed.
Lemma lem9374 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem9375 {A : Type'} (P : A -> Prop) : (term23 A P) = (ex P).
Proof. exact (MK_COMB (@lem9374 A) (@lem9371 A P)). Qed.
Lemma lem9377 {A : Type'} (P : A -> Prop) (h1 : ex P) : (ex P) = True.
Proof. exact (EQ_MP (@lem9357 A P) (@lem9356 A P h1)). Qed.
Lemma lem9380 {A : Type'} (P : A -> Prop) (h1 : ex P) : (term23 A P) = True.
Proof. exact (TRANS (@lem9375 A P) (@lem9377 A P h1)). Qed.
Lemma lem9381 {A : Type'} (P : A -> Prop) (h1 : ex P) : True = (term23 A P).
Proof. exact (SYM (@lem9380 A P h1)). Qed.
Lemma lem9382 {A : Type'} (P : A -> Prop) (h1 : ex P) : term23 A P.
Proof. exact (EQ_MP (@lem9381 A P h1) (@lem0)). Qed.
Lemma lem9383 {A : Type'} (P : A -> Prop) (h1 : ex P) : (term6 A P) = True.
Proof. exact (@lem9361 A P (@lem9382 A P h1)). Qed.
Lemma lem9386 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (fun h0 : ex P => @lem9383 A P h0). Qed.
Lemma lem9387 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (@lem9355 A P True). Qed.
Lemma lem9388 {A : Type'} (P : A -> Prop) : (term26 A P) = (term27 A P).
Proof. exact (@lem9387 A P (@lem9386 A P)). Qed.
Lemma lem9390 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem9391 {A : Type'} (P : A -> Prop) : (term27 A P) = True.
Proof. exact (@lem9390 (ex P)). Qed.
Lemma lem9394 {A : Type'} (P : A -> Prop) : (term26 A P) = True.
Proof. exact (TRANS (@lem9388 A P) (@lem9391 A P)). Qed.
Lemma lem9395 {A : Type'} (P : A -> Prop) : True = (term26 A P).
Proof. exact (SYM (@lem9394 A P)). Qed.
Lemma lem9396 {A : Type'} (P : A -> Prop) : term26 A P.
Proof. exact (EQ_MP (@lem9395 A P) (@lem0)). Qed.
