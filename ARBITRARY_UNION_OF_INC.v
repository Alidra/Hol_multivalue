Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_INC_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import UNION_OF_INC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4858330 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4858331 {A : Type'} (s : type686 A) : (term0 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4858333 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (@lem4842424 A P). Qed.
Lemma lem4858334 {A : Type'} (P : type180 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4858335 {A : Type'} (P : type180 A) : term2 A P.
Proof. exact (EQ_MP (@lem4858334 A P) (@lem4858333 A P)). Qed.
Lemma lem4858336 {A : Type'} (P : type180 A) (Q : type686 A) : term3 A P Q.
Proof. exact (@lem4858335 A P Q). Qed.
Lemma lem4858337 {A : Type'} (P : type180 A) (Q : type686 A) : (term3 A P Q) = (term4 A P Q).
Proof. exact (eq_refl (term3 A P Q)). Qed.
Lemma lem4858338 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (EQ_MP (@lem4858337 A P Q) (@lem4858336 A P Q)). Qed.
Lemma lem4858339 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term5 A P Q s.
Proof. exact (@lem4858338 A P Q s). Qed.
Lemma lem4858340 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term5 A P Q s) = (term6 A P Q s).
Proof. exact (eq_refl (term5 A P Q s)). Qed.
Lemma lem4858341 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term6 A P Q s.
Proof. exact (EQ_MP (@lem4858340 A P Q s) (@lem4858339 A P Q s)). Qed.
Lemma lem4858342 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term7 A P Q s) : term7 A P Q s.
Proof. exact (h1). Qed.
Lemma lem4858343 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term7 A P Q s) : @UNION_OF A P Q s.
Proof. exact (@lem4858341 A P Q s (@lem4858342 A P Q s h1)). Qed.
Lemma lem4858344 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@UNION_OF A P Q s) = ((@UNION_OF A P Q s) = True).
Proof. exact (@lem7 (@UNION_OF A P Q s)). Qed.
Lemma lem4858345 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term7 A P Q s) : (@UNION_OF A P Q s) = True.
Proof. exact (EQ_MP (@lem4858344 A P Q s) (@lem4858343 A P Q s h1)). Qed.
Lemma lem4858362 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4858363 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem4858362 p q p' q'). Qed.
Lemma lem4858364 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem4858363 p q p'). Qed.
Lemma lem4858365 {A : Type'} (P : type686 A) (s : A -> Prop) : term11 A P s.
Proof. exact (@lem4858364 (P s) (@UNION_OF A (@ARBITRARY A) P s)). Qed.
Lemma lem4858366 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term12 A P s p'.
Proof. exact (@lem4858365 A P s p'). Qed.
Lemma lem4858367 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : (term12 A P s p') = (term13 A P s p').
Proof. exact (eq_refl (term12 A P s p')). Qed.
Lemma lem4858368 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term13 A P s p'.
Proof. exact (EQ_MP (@lem4858367 A P s p') (@lem4858366 A P s p')). Qed.
Lemma lem4858369 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term14 A P s p' q'.
Proof. exact (@lem4858368 A P s p' q'). Qed.
Lemma lem4858370 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term14 A P s p' q') = (term15 A P s p' q').
Proof. exact (eq_refl (term14 A P s p' q')). Qed.
Lemma lem4858371 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term15 A P s p' q'.
Proof. exact (EQ_MP (@lem4858370 A P s p' q') (@lem4858369 A P s p' q')). Qed.
Lemma lem4858372 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4858373 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term16 A P s q'.
Proof. exact (@lem4858371 A P s (P s) q'). Qed.
Lemma lem4858374 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term17 A P s q'.
Proof. exact (@lem4858373 A P s q' (@lem4858372 A P s)). Qed.
Lemma lem4858375 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem4858376 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = ((P s) = True).
Proof. exact (@lem7 (P s)). Qed.
Lemma lem4858379 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term18 A P Q s.
Proof. exact (fun h0 : term7 A P Q s => @lem4858345 A P Q s h0). Qed.
Lemma lem4858380 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term18 A P Q s.
Proof. exact (@lem4858379 A P Q s). Qed.
Lemma lem4858381 {A : Type'} (P : type686 A) (s : A -> Prop) : term19 A P s.
Proof. exact (@lem4858380 A (@ARBITRARY A) P s). Qed.
Lemma lem4858385 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4858331 A s) (@lem4858330 A s)). Qed.
Lemma lem4858386 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4858385 A s). Qed.
Lemma lem4858387 {A : Type'} (s : A -> Prop) : (term20 A s) = True.
Proof. exact (@lem4858386 A (@INSERT (A -> Prop) s (@EMPTY (A -> Prop)))). Qed.
Lemma lem4858388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4858389 {A : Type'} (s : A -> Prop) : (term21 A s) = (and True).
Proof. exact (MK_COMB (@lem4858388) (@lem4858387 A s)). Qed.
Lemma lem4858391 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (P s) = True.
Proof. exact (EQ_MP (@lem4858376 A P s) (@lem4858375 A P s h1)). Qed.
Lemma lem4858392 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term22 A P s) = (True /\ True).
Proof. exact (MK_COMB (@lem4858389 A s) (@lem4858391 A P s h1)). Qed.
Lemma lem4858394 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4858395 : (True /\ True) = True.
Proof. exact (@lem4858394 True). Qed.
Lemma lem4858396 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term22 A P s) = True.
Proof. exact (TRANS (@lem4858392 A P s h1) (@lem4858395)). Qed.
Lemma lem4858397 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : True = (term22 A P s).
Proof. exact (SYM (@lem4858396 A P s h1)). Qed.
Lemma lem4858398 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : term22 A P s.
Proof. exact (EQ_MP (@lem4858397 A P s h1) (@lem0)). Qed.
Lemma lem4858399 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (@UNION_OF A (@ARBITRARY A) P s) = True.
Proof. exact (@lem4858381 A P s (@lem4858398 A P s h1)). Qed.
Lemma lem4858400 {A : Type'} (P : type686 A) (s : A -> Prop) : term23 A P s.
Proof. exact (fun h0 : P s => @lem4858399 A P s h0). Qed.
Lemma lem4858401 {A : Type'} (P : type686 A) (s : A -> Prop) : term24 A P s.
Proof. exact (@lem4858374 A P s True). Qed.
Lemma lem4858402 {A : Type'} (P : type686 A) (s : A -> Prop) : (term25 A P s) = (term26 A P s).
Proof. exact (@lem4858401 A P s (@lem4858400 A P s)). Qed.
Lemma lem4858404 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4858405 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = True.
Proof. exact (@lem4858404 (P s)). Qed.
Lemma lem4858406 {A : Type'} (P : type686 A) (s : A -> Prop) : (term25 A P s) = True.
Proof. exact (TRANS (@lem4858402 A P s) (@lem4858405 A P s)). Qed.
Lemma lem4858407 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4858406 A P s)). Qed.
Lemma lem4858408 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4858409 {A : Type'} (P : type686 A) : (term29 A P) = (term30 A).
Proof. exact (MK_COMB (@lem4858408 A) (@lem4858407 A P)). Qed.
Lemma lem4858411 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4858412 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem4858411 (A -> Prop) t). Qed.
Lemma lem4858413 {A : Type'} : (term30 A) = True.
Proof. exact (@lem4858412 A True). Qed.
Lemma lem4858414 {A : Type'} (P : type686 A) : (term29 A P) = True.
Proof. exact (TRANS (@lem4858409 A P) (@lem4858413 A)). Qed.
Lemma lem4858415 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4858414 A P)). Qed.
Lemma lem4858416 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4858417 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem4858416 A) (@lem4858415 A)). Qed.
Lemma lem4858419 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4858420 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (@lem4858419 (type686 A) t). Qed.
Lemma lem4858421 {A : Type'} : (term36 A) = True.
Proof. exact (@lem4858420 A True). Qed.
Lemma lem4858422 {A : Type'} : (term35 A) = True.
Proof. exact (TRANS (@lem4858417 A) (@lem4858421 A)). Qed.
Lemma lem4858423 {A : Type'} : True = (term35 A).
Proof. exact (SYM (@lem4858422 A)). Qed.
Lemma lem4858424 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem4858423 A) (@lem0)). Qed.
