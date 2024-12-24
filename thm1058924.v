Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1058924_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm7058_spec.
Require Import thm7129_spec.
Require Import thm7362_spec.
Require Import thm7400_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem1058350 {A : Type'} (a : type1597 A) (h1 : a = (@ZBOT A)) : a = (@ZBOT A).
Proof. exact (h1). Qed.
Lemma lem1058351 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' (@ZBOT A)) : ZRECSPACE' (@ZBOT A).
Proof. exact (h1). Qed.
Lemma lem1058352 {A : Type'} (ZRECSPACE' : type953 A) : ZRECSPACE' = ZRECSPACE'.
Proof. exact (eq_refl ZRECSPACE'). Qed.
Lemma lem1058353 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) : (ZRECSPACE' a) = (ZRECSPACE' (@ZBOT A)).
Proof. exact (MK_COMB (@lem1058352 A ZRECSPACE') (@lem1058350 A a h1)). Qed.
Lemma lem1058354 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) : (ZRECSPACE' (@ZBOT A)) = (ZRECSPACE' a).
Proof. exact (SYM (@lem1058353 A ZRECSPACE' a h1)). Qed.
Lemma lem1058355 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : ZRECSPACE' (@ZBOT A)) (h2 : a = (@ZBOT A)) : ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058354 A ZRECSPACE' a h2) (@lem1058351 A ZRECSPACE' h1)). Qed.
Lemma lem1058356 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' (@ZBOT A)) : term0 A ZRECSPACE' a.
Proof. exact (fun h0 : a = (@ZBOT A) => @lem1058355 A ZRECSPACE' a h1 h0). Qed.
Lemma lem1058357 {A : Type'} (a : type1597 A) (h1 : a = (@ZBOT A)) : a = (@ZBOT A).
Proof. exact (h1). Qed.
Lemma lem1058358 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : ZRECSPACE' (@ZBOT A)) (h2 : a = (@ZBOT A)) : ZRECSPACE' a.
Proof. exact (@lem1058356 A a ZRECSPACE' h1 (@lem1058357 A a h2)). Qed.
Lemma lem1058359 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' (@ZBOT A)) : term0 A ZRECSPACE' a.
Proof. exact (fun h0 : a = (@ZBOT A) => @lem1058358 A ZRECSPACE' a h1 h0). Qed.
Lemma lem1058360 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' (@ZBOT A)) : term1 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058359 A a ZRECSPACE' h1). Qed.
Lemma lem1058361 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term1 A ZRECSPACE') : term1 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058362 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term1 A ZRECSPACE') : term2 A ZRECSPACE'.
Proof. exact (@lem1058361 A ZRECSPACE' h1 (@ZBOT A)). Qed.
Lemma lem1058363 {A : Type'} (ZRECSPACE' : type953 A) : (term2 A ZRECSPACE') = (term3 A ZRECSPACE').
Proof. exact (eq_refl (term2 A ZRECSPACE')). Qed.
Lemma lem1058364 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term1 A ZRECSPACE') : term3 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058363 A ZRECSPACE') (@lem1058362 A ZRECSPACE' h1)). Qed.
Lemma lem1058365 {A : Type'} : (@ZBOT A) = (@ZBOT A).
Proof. exact (eq_refl (@ZBOT A)). Qed.
Lemma lem1058366 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term1 A ZRECSPACE') : ZRECSPACE' (@ZBOT A).
Proof. exact (@lem1058364 A ZRECSPACE' h1 (@lem1058365 A)). Qed.
Lemma lem1058367 {A : Type'} (ZRECSPACE' : type953 A) : term4 A ZRECSPACE'.
Proof. exact (fun h0 : term1 A ZRECSPACE' => @lem1058366 A ZRECSPACE' h0). Qed.
Lemma lem1058368 {A : Type'} (ZRECSPACE' : type953 A) : term5 A ZRECSPACE'.
Proof. exact (fun h0 : ZRECSPACE' (@ZBOT A) => @lem1058360 A ZRECSPACE' h0). Qed.
Lemma lem1058369 {A : Type'} (ZRECSPACE' : type953 A) : term6 A ZRECSPACE'.
Proof. exact (conj (@lem1058368 A ZRECSPACE') (@lem1058367 A ZRECSPACE')). Qed.
Lemma lem1058370 {A : Type'} (ZRECSPACE' : type953 A) : (term6 A ZRECSPACE') = ((ZRECSPACE' (@ZBOT A)) = (term1 A ZRECSPACE')).
Proof. exact (@lem32 (ZRECSPACE' (@ZBOT A)) (term1 A ZRECSPACE')). Qed.
Lemma lem1058371 {A : Type'} (ZRECSPACE' : type953 A) : (ZRECSPACE' (@ZBOT A)) = (term1 A ZRECSPACE').
Proof. exact (EQ_MP (@lem1058370 A ZRECSPACE') (@lem1058369 A ZRECSPACE')). Qed.
Lemma lem1058372 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term0 A ZRECSPACE' a) : term0 A ZRECSPACE' a.
Proof. exact (h1). Qed.
Lemma lem1058373 {A : Type'} (a : type1597 A) (h1 : a = (@ZBOT A)) : a = (@ZBOT A).
Proof. exact (h1). Qed.
Lemma lem1058374 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) (h2 : term0 A ZRECSPACE' a) : ZRECSPACE' a.
Proof. exact (@lem1058372 A ZRECSPACE' a h2 (@lem1058373 A a h1)). Qed.
Lemma lem1058375 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) : term7 A ZRECSPACE' a.
Proof. exact (fun h0 : term0 A ZRECSPACE' a => @lem1058374 A ZRECSPACE' a h1 h0). Qed.
Lemma lem1058376 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term0 A ZRECSPACE' a) : term0 A ZRECSPACE' a.
Proof. exact (h1). Qed.
Lemma lem1058377 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) (h2 : term0 A ZRECSPACE' a) : ZRECSPACE' a.
Proof. exact (@lem1058375 A ZRECSPACE' a h1 (@lem1058376 A ZRECSPACE' a h2)). Qed.
Lemma lem1058378 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term0 A ZRECSPACE' a) : term0 A ZRECSPACE' a.
Proof. exact (fun h0 : a = (@ZBOT A) => @lem1058377 A ZRECSPACE' a h0 h1). Qed.
Lemma lem1058379 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term0 A ZRECSPACE' a) : term0 A ZRECSPACE' a.
Proof. exact (h1). Qed.
Lemma lem1058380 {A : Type'} (a : type1597 A) (h1 : a = (@ZBOT A)) : a = (@ZBOT A).
Proof. exact (h1). Qed.
Lemma lem1058381 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) (h2 : term0 A ZRECSPACE' a) : ZRECSPACE' a.
Proof. exact (@lem1058379 A ZRECSPACE' a h2 (@lem1058380 A a h1)). Qed.
Lemma lem1058382 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term0 A ZRECSPACE' a) : term0 A ZRECSPACE' a.
Proof. exact (fun h0 : a = (@ZBOT A) => @lem1058381 A ZRECSPACE' a h0 h1). Qed.
Lemma lem1058383 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : term8 A ZRECSPACE' a.
Proof. exact (fun h0 : term0 A ZRECSPACE' a => @lem1058382 A ZRECSPACE' a h0). Qed.
Lemma lem1058384 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : term8 A ZRECSPACE' a.
Proof. exact (fun h0 : term0 A ZRECSPACE' a => @lem1058378 A ZRECSPACE' a h0). Qed.
Lemma lem1058385 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : term9 A ZRECSPACE' a.
Proof. exact (conj (@lem1058384 A ZRECSPACE' a) (@lem1058383 A ZRECSPACE' a)). Qed.
Lemma lem1058386 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term9 A ZRECSPACE' a) = ((term0 A ZRECSPACE' a) = (term0 A ZRECSPACE' a)).
Proof. exact (@lem32 (term0 A ZRECSPACE' a) (term0 A ZRECSPACE' a)). Qed.
Lemma lem1058387 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term0 A ZRECSPACE' a) = (term0 A ZRECSPACE' a).
Proof. exact (EQ_MP (@lem1058386 A ZRECSPACE' a) (@lem1058385 A ZRECSPACE' a)). Qed.
Lemma lem1058388 {A : Type'} (ZRECSPACE' : type953 A) : (term10 A ZRECSPACE') = (term10 A ZRECSPACE').
Proof. exact (fun_ext (fun a : type1597 A => @lem1058387 A ZRECSPACE' a)). Qed.
Lemma lem1058389 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem1058390 {A : Type'} (ZRECSPACE' : type953 A) : (term1 A ZRECSPACE') = (term1 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058389 A) (@lem1058388 A ZRECSPACE')). Qed.
Lemma lem1058391 {A : Type'} (ZRECSPACE' : type953 A) : (ZRECSPACE' (@ZBOT A)) = (term1 A ZRECSPACE').
Proof. exact (TRANS (@lem1058371 A ZRECSPACE') (@lem1058390 A ZRECSPACE')). Qed.
Lemma lem1058392 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term11 A a c i ZRECSPACE' r.
Proof. exact (h1). Qed.
Lemma lem1058393 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term12 A ZRECSPACE' r.
Proof. exact (proj2 (@lem1058392 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058394 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : a = (@ZCONSTR A c i r).
Proof. exact (proj1 (@lem1058392 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058395 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term13 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058396 {A : Type'} (c : nat) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term14 A ZRECSPACE' c.
Proof. exact (@lem1058395 A ZRECSPACE' h1 c). Qed.
Lemma lem1058397 {A : Type'} (ZRECSPACE' : type953 A) (c : nat) : (term14 A ZRECSPACE' c) = (term15 A ZRECSPACE' c).
Proof. exact (eq_refl (term14 A ZRECSPACE' c)). Qed.
Lemma lem1058398 {A : Type'} (c : nat) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term15 A ZRECSPACE' c.
Proof. exact (EQ_MP (@lem1058397 A ZRECSPACE' c) (@lem1058396 A c ZRECSPACE' h1)). Qed.
Lemma lem1058399 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term16 A ZRECSPACE' c i.
Proof. exact (@lem1058398 A c ZRECSPACE' h1 i). Qed.
Lemma lem1058400 {A : Type'} (ZRECSPACE' : type953 A) (c : nat) (i : A) : (term16 A ZRECSPACE' c i) = (term17 A ZRECSPACE' c i).
Proof. exact (eq_refl (term16 A ZRECSPACE' c i)). Qed.
Lemma lem1058401 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term17 A ZRECSPACE' c i.
Proof. exact (EQ_MP (@lem1058400 A ZRECSPACE' c i) (@lem1058399 A c i ZRECSPACE' h1)). Qed.
Lemma lem1058402 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term18 A ZRECSPACE' c i r.
Proof. exact (@lem1058401 A c i ZRECSPACE' h1 r). Qed.
Lemma lem1058403 {A : Type'} (ZRECSPACE' : type953 A) (c : nat) (i : A) (r : type1600 A) : (term18 A ZRECSPACE' c i r) = (term19 A ZRECSPACE' c i r).
Proof. exact (eq_refl (term18 A ZRECSPACE' c i r)). Qed.
Lemma lem1058404 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term19 A ZRECSPACE' c i r.
Proof. exact (EQ_MP (@lem1058403 A ZRECSPACE' c i r) (@lem1058402 A c i r ZRECSPACE' h1)). Qed.
Lemma lem1058405 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term13 A ZRECSPACE') (h2 : term11 A a c i ZRECSPACE' r) : term20 A ZRECSPACE' c i r.
Proof. exact (@lem1058404 A c i r ZRECSPACE' h1 (@lem1058393 A a c i ZRECSPACE' r h2)). Qed.
Lemma lem1058406 {A : Type'} (ZRECSPACE' : type953 A) : ZRECSPACE' = ZRECSPACE'.
Proof. exact (eq_refl ZRECSPACE'). Qed.
Lemma lem1058407 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : (ZRECSPACE' a) = (term20 A ZRECSPACE' c i r).
Proof. exact (MK_COMB (@lem1058406 A ZRECSPACE') (@lem1058394 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058408 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : (term20 A ZRECSPACE' c i r) = (ZRECSPACE' a).
Proof. exact (SYM (@lem1058407 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058409 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term13 A ZRECSPACE') (h2 : term11 A a c i ZRECSPACE' r) : ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058408 A a c i ZRECSPACE' r h2) (@lem1058405 A a c i ZRECSPACE' r h1 h2)). Qed.
Lemma lem1058410 {A : Type'} (c : nat) (i : A) (r : type1600 A) (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term21 A c i r ZRECSPACE' a.
Proof. exact (fun h0 : term11 A a c i ZRECSPACE' r => @lem1058409 A a c i ZRECSPACE' r h1 h0). Qed.
Lemma lem1058411 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term11 A a c i ZRECSPACE' r.
Proof. exact (h1). Qed.
Lemma lem1058412 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term13 A ZRECSPACE') (h2 : term11 A a c i ZRECSPACE' r) : ZRECSPACE' a.
Proof. exact (@lem1058410 A c i r a ZRECSPACE' h1 (@lem1058411 A a c i ZRECSPACE' r h2)). Qed.
Lemma lem1058413 {A : Type'} (c : nat) (i : A) (r : type1600 A) (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term21 A c i r ZRECSPACE' a.
Proof. exact (fun h0 : term11 A a c i ZRECSPACE' r => @lem1058412 A a c i ZRECSPACE' r h1 h0). Qed.
Lemma lem1058414 {A : Type'} (c : nat) (i : A) (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term22 A c i ZRECSPACE' a.
Proof. exact (fun r : type1600 A => @lem1058413 A c i r a ZRECSPACE' h1). Qed.
Lemma lem1058415 {A : Type'} (c : nat) (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term23 A c ZRECSPACE' a.
Proof. exact (fun i : A => @lem1058414 A c i a ZRECSPACE' h1). Qed.
Lemma lem1058416 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term24 A ZRECSPACE' a.
Proof. exact (fun c : nat => @lem1058415 A c a ZRECSPACE' h1). Qed.
Lemma lem1058417 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term13 A ZRECSPACE') : term25 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058416 A a ZRECSPACE' h1). Qed.
Lemma lem1058418 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term25 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058419 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term26 A ZRECSPACE' c i r.
Proof. exact (@lem1058418 A ZRECSPACE' h1 (@ZCONSTR A c i r)). Qed.
Lemma lem1058420 {A : Type'} (ZRECSPACE' : type953 A) (c : nat) (i : A) (r : type1600 A) : (term26 A ZRECSPACE' c i r) = (term27 A ZRECSPACE' c i r).
Proof. exact (eq_refl (term26 A ZRECSPACE' c i r)). Qed.
Lemma lem1058421 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term27 A ZRECSPACE' c i r.
Proof. exact (EQ_MP (@lem1058420 A ZRECSPACE' c i r) (@lem1058419 A c i r ZRECSPACE' h1)). Qed.
Lemma lem1058422 {A : Type'} (i : A) (r : type1600 A) (c : nat) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term28 A ZRECSPACE' i r c.
Proof. exact (@lem1058421 A c i r ZRECSPACE' h1 c). Qed.
Lemma lem1058423 {A : Type'} (ZRECSPACE' : type953 A) (c : nat) (i : A) (r : type1600 A) : (term28 A ZRECSPACE' i r c) = (term29 A ZRECSPACE' c i r).
Proof. exact (eq_refl (term28 A ZRECSPACE' i r c)). Qed.
Lemma lem1058424 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term29 A ZRECSPACE' c i r.
Proof. exact (EQ_MP (@lem1058423 A ZRECSPACE' c i r) (@lem1058422 A i r c ZRECSPACE' h1)). Qed.
Lemma lem1058425 {A : Type'} (c : nat) (r : type1600 A) (i : A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term30 A ZRECSPACE' c r i.
Proof. exact (@lem1058424 A c i r ZRECSPACE' h1 i). Qed.
Lemma lem1058426 {A : Type'} (ZRECSPACE' : type953 A) (c : nat) (i : A) (r : type1600 A) : (term30 A ZRECSPACE' c r i) = (term31 A ZRECSPACE' c i r).
Proof. exact (eq_refl (term30 A ZRECSPACE' c r i)). Qed.
Lemma lem1058427 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term31 A ZRECSPACE' c i r.
Proof. exact (EQ_MP (@lem1058426 A ZRECSPACE' c i r) (@lem1058425 A c r i ZRECSPACE' h1)). Qed.
Lemma lem1058428 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term32 A ZRECSPACE' c i r.
Proof. exact (@lem1058427 A c i r ZRECSPACE' h1 r). Qed.
Lemma lem1058429 {A : Type'} (ZRECSPACE' : type953 A) (c : nat) (i : A) (r : type1600 A) : (term32 A ZRECSPACE' c i r) = (term33 A ZRECSPACE' c i r).
Proof. exact (eq_refl (term32 A ZRECSPACE' c i r)). Qed.
Lemma lem1058430 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term33 A ZRECSPACE' c i r.
Proof. exact (EQ_MP (@lem1058429 A ZRECSPACE' c i r) (@lem1058428 A c i r ZRECSPACE' h1)). Qed.
Lemma lem1058431 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term12 A ZRECSPACE' r) : term12 A ZRECSPACE' r.
Proof. exact (h1). Qed.
Lemma lem1058432 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (@ZCONSTR A c i r).
Proof. exact (eq_refl (@ZCONSTR A c i r)). Qed.
Lemma lem1058433 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term12 A ZRECSPACE' r) : term34 A c i ZRECSPACE' r.
Proof. exact (conj (@lem1058432 A c i r) (@lem1058431 A ZRECSPACE' r h1)). Qed.
Lemma lem1058434 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term25 A ZRECSPACE') (h2 : term12 A ZRECSPACE' r) : term20 A ZRECSPACE' c i r.
Proof. exact (@lem1058430 A c i r ZRECSPACE' h1 (@lem1058433 A c i ZRECSPACE' r h2)). Qed.
Lemma lem1058435 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term19 A ZRECSPACE' c i r.
Proof. exact (fun h0 : term12 A ZRECSPACE' r => @lem1058434 A c i ZRECSPACE' r h1 h0). Qed.
Lemma lem1058436 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term17 A ZRECSPACE' c i.
Proof. exact (fun r : type1600 A => @lem1058435 A c i r ZRECSPACE' h1). Qed.
Lemma lem1058437 {A : Type'} (c : nat) (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term15 A ZRECSPACE' c.
Proof. exact (fun i : A => @lem1058436 A c i ZRECSPACE' h1). Qed.
Lemma lem1058438 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term25 A ZRECSPACE') : term13 A ZRECSPACE'.
Proof. exact (fun c : nat => @lem1058437 A c ZRECSPACE' h1). Qed.
Lemma lem1058439 {A : Type'} (ZRECSPACE' : type953 A) : term35 A ZRECSPACE'.
Proof. exact (fun h0 : term25 A ZRECSPACE' => @lem1058438 A ZRECSPACE' h0). Qed.
Lemma lem1058440 {A : Type'} (ZRECSPACE' : type953 A) : term36 A ZRECSPACE'.
Proof. exact (fun h0 : term13 A ZRECSPACE' => @lem1058417 A ZRECSPACE' h0). Qed.
Lemma lem1058441 {A : Type'} (ZRECSPACE' : type953 A) : term37 A ZRECSPACE'.
Proof. exact (conj (@lem1058440 A ZRECSPACE') (@lem1058439 A ZRECSPACE')). Qed.
Lemma lem1058442 {A : Type'} (ZRECSPACE' : type953 A) : (term37 A ZRECSPACE') = ((term13 A ZRECSPACE') = (term25 A ZRECSPACE')).
Proof. exact (@lem32 (term13 A ZRECSPACE') (term25 A ZRECSPACE')). Qed.
Lemma lem1058443 {A : Type'} (ZRECSPACE' : type953 A) : (term13 A ZRECSPACE') = (term25 A ZRECSPACE').
Proof. exact (EQ_MP (@lem1058442 A ZRECSPACE') (@lem1058441 A ZRECSPACE')). Qed.
Lemma lem1058444 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term24 A ZRECSPACE' a.
Proof. exact (h1). Qed.
Lemma lem1058445 {A : Type'} (c : nat) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term38 A ZRECSPACE' a c.
Proof. exact (@lem1058444 A ZRECSPACE' a h1 c). Qed.
Lemma lem1058446 {A : Type'} (c : nat) (ZRECSPACE' : type953 A) (a : type1597 A) : (term38 A ZRECSPACE' a c) = (term23 A c ZRECSPACE' a).
Proof. exact (eq_refl (term38 A ZRECSPACE' a c)). Qed.
Lemma lem1058447 {A : Type'} (c : nat) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term23 A c ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058446 A c ZRECSPACE' a) (@lem1058445 A c ZRECSPACE' a h1)). Qed.
Lemma lem1058448 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term39 A c ZRECSPACE' a i.
Proof. exact (@lem1058447 A c ZRECSPACE' a h1 i). Qed.
Lemma lem1058449 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (a : type1597 A) : (term39 A c ZRECSPACE' a i) = (term22 A c i ZRECSPACE' a).
Proof. exact (eq_refl (term39 A c ZRECSPACE' a i)). Qed.
Lemma lem1058450 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term22 A c i ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058449 A c i ZRECSPACE' a) (@lem1058448 A c i ZRECSPACE' a h1)). Qed.
Lemma lem1058451 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term40 A c i ZRECSPACE' a r.
Proof. exact (@lem1058450 A c i ZRECSPACE' a h1 r). Qed.
Lemma lem1058452 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (a : type1597 A) : (term40 A c i ZRECSPACE' a r) = (term21 A c i r ZRECSPACE' a).
Proof. exact (eq_refl (term40 A c i ZRECSPACE' a r)). Qed.
Lemma lem1058453 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term21 A c i r ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058452 A c i r ZRECSPACE' a) (@lem1058451 A c i r ZRECSPACE' a h1)). Qed.
Lemma lem1058454 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term11 A a c i ZRECSPACE' r.
Proof. exact (h1). Qed.
Lemma lem1058455 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term24 A ZRECSPACE' a) (h2 : term11 A a c i ZRECSPACE' r) : ZRECSPACE' a.
Proof. exact (@lem1058453 A c i r ZRECSPACE' a h1 (@lem1058454 A a c i ZRECSPACE' r h2)). Qed.
Lemma lem1058456 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term41 A ZRECSPACE' a.
Proof. exact (fun h0 : term24 A ZRECSPACE' a => @lem1058455 A a c i ZRECSPACE' r h0 h1). Qed.
Lemma lem1058457 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (h1 : term42 A a c i ZRECSPACE') : term42 A a c i ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058458 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (h1 : term42 A a c i ZRECSPACE') : term41 A ZRECSPACE' a.
Proof. exact (ex_elim (@lem1058457 A a c i ZRECSPACE' h1) (fun r : type1600 A => fun h0 : term43 A a c i ZRECSPACE' r => @lem1058456 A a c i ZRECSPACE' r h0)). Qed.
Lemma lem1058459 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) (h1 : term44 A a c ZRECSPACE') : term44 A a c ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058460 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) (h1 : term44 A a c ZRECSPACE') : term41 A ZRECSPACE' a.
Proof. exact (ex_elim (@lem1058459 A a c ZRECSPACE' h1) (fun i : A => fun h0 : term45 A a c ZRECSPACE' i => @lem1058458 A a c i ZRECSPACE' h0)). Qed.
Lemma lem1058461 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : term46 A a ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058462 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : term41 A ZRECSPACE' a.
Proof. exact (ex_elim (@lem1058461 A a ZRECSPACE' h1) (fun c : nat => fun h0 : term47 A a ZRECSPACE' c => @lem1058460 A a c ZRECSPACE' h0)). Qed.
Lemma lem1058463 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term24 A ZRECSPACE' a.
Proof. exact (h1). Qed.
Lemma lem1058464 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term24 A ZRECSPACE' a) (h2 : term46 A a ZRECSPACE') : ZRECSPACE' a.
Proof. exact (@lem1058462 A a ZRECSPACE' h2 (@lem1058463 A ZRECSPACE' a h1)). Qed.
Lemma lem1058465 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term24 A ZRECSPACE' a) : term48 A ZRECSPACE' a.
Proof. exact (fun h0 : term46 A a ZRECSPACE' => @lem1058464 A a ZRECSPACE' h1 h0). Qed.
Lemma lem1058466 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term48 A ZRECSPACE' a) : term48 A ZRECSPACE' a.
Proof. exact (h1). Qed.
Lemma lem1058467 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term11 A a c i ZRECSPACE' r.
Proof. exact (h1). Qed.
Lemma lem1058468 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term42 A a c i ZRECSPACE'.
Proof. exact (ex_intro (term43 A a c i ZRECSPACE') r (@lem1058467 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058469 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term44 A a c ZRECSPACE'.
Proof. exact (ex_intro (term45 A a c ZRECSPACE') i (@lem1058468 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058470 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) (h1 : term11 A a c i ZRECSPACE' r) : term46 A a ZRECSPACE'.
Proof. exact (ex_intro (term47 A a ZRECSPACE') c (@lem1058469 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058471 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term11 A a c i ZRECSPACE' r) (h2 : term48 A ZRECSPACE' a) : ZRECSPACE' a.
Proof. exact (@lem1058466 A ZRECSPACE' a h2 (@lem1058470 A a c i ZRECSPACE' r h1)). Qed.
Lemma lem1058472 {A : Type'} (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term48 A ZRECSPACE' a) : term21 A c i r ZRECSPACE' a.
Proof. exact (fun h0 : term11 A a c i ZRECSPACE' r => @lem1058471 A c i r ZRECSPACE' a h0 h1). Qed.
Lemma lem1058473 {A : Type'} (c : nat) (i : A) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term48 A ZRECSPACE' a) : term22 A c i ZRECSPACE' a.
Proof. exact (fun r : type1600 A => @lem1058472 A c i r ZRECSPACE' a h1). Qed.
Lemma lem1058474 {A : Type'} (c : nat) (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term48 A ZRECSPACE' a) : term23 A c ZRECSPACE' a.
Proof. exact (fun i : A => @lem1058473 A c i ZRECSPACE' a h1). Qed.
Lemma lem1058475 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term48 A ZRECSPACE' a) : term24 A ZRECSPACE' a.
Proof. exact (fun c : nat => @lem1058474 A c ZRECSPACE' a h1). Qed.
Lemma lem1058476 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : term49 A ZRECSPACE' a.
Proof. exact (fun h0 : term48 A ZRECSPACE' a => @lem1058475 A ZRECSPACE' a h0). Qed.
Lemma lem1058477 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : term50 A ZRECSPACE' a.
Proof. exact (fun h0 : term24 A ZRECSPACE' a => @lem1058465 A ZRECSPACE' a h0). Qed.
Lemma lem1058478 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : term51 A ZRECSPACE' a.
Proof. exact (conj (@lem1058477 A ZRECSPACE' a) (@lem1058476 A ZRECSPACE' a)). Qed.
Lemma lem1058479 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term51 A ZRECSPACE' a) = ((term24 A ZRECSPACE' a) = (term48 A ZRECSPACE' a)).
Proof. exact (@lem32 (term24 A ZRECSPACE' a) (term48 A ZRECSPACE' a)). Qed.
Lemma lem1058480 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term24 A ZRECSPACE' a) = (term48 A ZRECSPACE' a).
Proof. exact (EQ_MP (@lem1058479 A ZRECSPACE' a) (@lem1058478 A ZRECSPACE' a)). Qed.
Lemma lem1058481 {A : Type'} (ZRECSPACE' : type953 A) : (term52 A ZRECSPACE') = (term53 A ZRECSPACE').
Proof. exact (fun_ext (fun a : type1597 A => @lem1058480 A ZRECSPACE' a)). Qed.
Lemma lem1058482 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem1058483 {A : Type'} (ZRECSPACE' : type953 A) : (term25 A ZRECSPACE') = (term54 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058482 A) (@lem1058481 A ZRECSPACE')). Qed.
Lemma lem1058484 {A : Type'} (ZRECSPACE' : type953 A) : (term13 A ZRECSPACE') = (term54 A ZRECSPACE').
Proof. exact (TRANS (@lem1058443 A ZRECSPACE') (@lem1058483 A ZRECSPACE')). Qed.
Lemma lem1058486 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem1058487 (x : Prop) : (x = x) = True.
Proof. exact (@lem1058486 Prop x). Qed.
Lemma lem1058488 {A : Type'} (ZRECSPACE' : type953 A) : ((term55 A ZRECSPACE') = (term55 A ZRECSPACE')) = True.
Proof. exact (@lem1058487 (term55 A ZRECSPACE')). Qed.
Lemma lem1058489 {A : Type'} (ZRECSPACE' : type953 A) : True = ((term55 A ZRECSPACE') = (term55 A ZRECSPACE')).
Proof. exact (SYM (@lem1058488 A ZRECSPACE')). Qed.
Lemma lem1058490 {A : Type'} (ZRECSPACE' : type953 A) : (term55 A ZRECSPACE') = (term55 A ZRECSPACE').
Proof. exact (EQ_MP (@lem1058489 A ZRECSPACE') (@lem0)). Qed.
Lemma lem1058491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1058492 {A : Type'} (ZRECSPACE' : type953 A) : (term56 A ZRECSPACE') = (term57 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058491) (@lem1058391 A ZRECSPACE')). Qed.
Lemma lem1058493 {A : Type'} (ZRECSPACE' : type953 A) : (term58 A ZRECSPACE') = (term55 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058492 A ZRECSPACE') (@lem1058484 A ZRECSPACE')). Qed.
Lemma lem1058494 {A : Type'} (ZRECSPACE' : type953 A) : (term58 A ZRECSPACE') = (term55 A ZRECSPACE').
Proof. exact (TRANS (@lem1058493 A ZRECSPACE') (@lem1058490 A ZRECSPACE')). Qed.
Lemma lem1058495 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term55 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058496 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term54 A ZRECSPACE'.
Proof. exact (proj2 (@lem1058495 A ZRECSPACE' h1)). Qed.
Lemma lem1058497 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term1 A ZRECSPACE'.
Proof. exact (proj1 (@lem1058495 A ZRECSPACE' h1)). Qed.
Lemma lem1058498 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term59 A ZRECSPACE' a.
Proof. exact (@lem1058497 A ZRECSPACE' h1 a). Qed.
Lemma lem1058499 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term59 A ZRECSPACE' a) = (term0 A ZRECSPACE' a).
Proof. exact (eq_refl (term59 A ZRECSPACE' a)). Qed.
Lemma lem1058500 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term0 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058499 A ZRECSPACE' a) (@lem1058498 A a ZRECSPACE' h1)). Qed.
Lemma lem1058501 {A : Type'} (a : type1597 A) (h1 : a = (@ZBOT A)) : a = (@ZBOT A).
Proof. exact (h1). Qed.
Lemma lem1058502 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term55 A ZRECSPACE') (h2 : a = (@ZBOT A)) : ZRECSPACE' a.
Proof. exact (@lem1058500 A a ZRECSPACE' h1 (@lem1058501 A a h2)). Qed.
Lemma lem1058503 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) : term60 A ZRECSPACE' a.
Proof. exact (fun h0 : term55 A ZRECSPACE' => @lem1058502 A ZRECSPACE' a h0 h1). Qed.
Lemma lem1058504 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term61 A ZRECSPACE' a.
Proof. exact (@lem1058496 A ZRECSPACE' h1 a). Qed.
Lemma lem1058505 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term61 A ZRECSPACE' a) = (term48 A ZRECSPACE' a).
Proof. exact (eq_refl (term61 A ZRECSPACE' a)). Qed.
Lemma lem1058506 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term48 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058505 A ZRECSPACE' a) (@lem1058504 A a ZRECSPACE' h1)). Qed.
Lemma lem1058507 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : term46 A a ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058508 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') (h2 : term55 A ZRECSPACE') : ZRECSPACE' a.
Proof. exact (@lem1058506 A a ZRECSPACE' h2 (@lem1058507 A a ZRECSPACE' h1)). Qed.
Lemma lem1058509 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : term60 A ZRECSPACE' a.
Proof. exact (fun h0 : term55 A ZRECSPACE' => @lem1058508 A a ZRECSPACE' h1 h0). Qed.
Lemma lem1058510 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term62 A a ZRECSPACE') : term62 A a ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058511 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term62 A a ZRECSPACE') : term60 A ZRECSPACE' a.
Proof. exact (or_elim (@lem1058510 A a ZRECSPACE' h1) (fun h0 : a = (@ZBOT A) => @lem1058503 A ZRECSPACE' a h0) (fun h0 : term46 A a ZRECSPACE' => @lem1058509 A a ZRECSPACE' h0)). Qed.
Lemma lem1058512 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term55 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058513 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') (h2 : term62 A a ZRECSPACE') : ZRECSPACE' a.
Proof. exact (@lem1058511 A a ZRECSPACE' h2 (@lem1058512 A ZRECSPACE' h1)). Qed.
Lemma lem1058514 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term63 A ZRECSPACE' a.
Proof. exact (fun h0 : term62 A a ZRECSPACE' => @lem1058513 A a ZRECSPACE' h1 h0). Qed.
Lemma lem1058515 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term55 A ZRECSPACE') : term64 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058514 A a ZRECSPACE' h1). Qed.
Lemma lem1058516 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term64 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058517 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term65 A ZRECSPACE' a.
Proof. exact (@lem1058516 A ZRECSPACE' h1 a). Qed.
Lemma lem1058518 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term65 A ZRECSPACE' a) = (term63 A ZRECSPACE' a).
Proof. exact (eq_refl (term65 A ZRECSPACE' a)). Qed.
Lemma lem1058519 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term63 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058518 A ZRECSPACE' a) (@lem1058517 A a ZRECSPACE' h1)). Qed.
Lemma lem1058520 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term62 A a ZRECSPACE') : term62 A a ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058521 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') (h2 : term62 A a ZRECSPACE') : ZRECSPACE' a.
Proof. exact (@lem1058519 A a ZRECSPACE' h1 (@lem1058520 A a ZRECSPACE' h2)). Qed.
Lemma lem1058522 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term62 A a ZRECSPACE') : term66 A ZRECSPACE' a.
Proof. exact (fun h0 : term64 A ZRECSPACE' => @lem1058521 A a ZRECSPACE' h0 h1). Qed.
Lemma lem1058523 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : term46 A a ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058524 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : term62 A a ZRECSPACE'.
Proof. exact (or_intro2 (a = (@ZBOT A)) (@lem1058523 A a ZRECSPACE' h1)). Qed.
Lemma lem1058525 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : (term62 A a ZRECSPACE') = (term66 A ZRECSPACE' a).
Proof. exact (prop_ext (fun h2 : term62 A a ZRECSPACE' => @lem1058522 A a ZRECSPACE' h2) (fun h2 : term66 A ZRECSPACE' a => @lem1058524 A a ZRECSPACE' h1)). Qed.
Lemma lem1058526 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term46 A a ZRECSPACE') : term66 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058525 A a ZRECSPACE' h1) (@lem1058524 A a ZRECSPACE' h1)). Qed.
Lemma lem1058527 {A : Type'} (a : type1597 A) (h1 : a = (@ZBOT A)) : a = (@ZBOT A).
Proof. exact (h1). Qed.
Lemma lem1058528 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) : term62 A a ZRECSPACE'.
Proof. exact (or_intro1 (@lem1058527 A a h1) (term46 A a ZRECSPACE')). Qed.
Lemma lem1058529 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) : (term62 A a ZRECSPACE') = (term66 A ZRECSPACE' a).
Proof. exact (prop_ext (fun h2 : term62 A a ZRECSPACE' => @lem1058522 A a ZRECSPACE' h2) (fun h2 : term66 A ZRECSPACE' a => @lem1058528 A ZRECSPACE' a h1)). Qed.
Lemma lem1058530 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : a = (@ZBOT A)) : term66 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058529 A ZRECSPACE' a h1) (@lem1058528 A ZRECSPACE' a h1)). Qed.
Lemma lem1058531 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term64 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058532 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') (h2 : term46 A a ZRECSPACE') : ZRECSPACE' a.
Proof. exact (@lem1058526 A a ZRECSPACE' h2 (@lem1058531 A ZRECSPACE' h1)). Qed.
Lemma lem1058533 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term48 A ZRECSPACE' a.
Proof. exact (fun h0 : term46 A a ZRECSPACE' => @lem1058532 A a ZRECSPACE' h1 h0). Qed.
Lemma lem1058534 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term54 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058533 A a ZRECSPACE' h1). Qed.
Lemma lem1058535 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term64 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058536 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : term64 A ZRECSPACE') (h2 : a = (@ZBOT A)) : ZRECSPACE' a.
Proof. exact (@lem1058530 A ZRECSPACE' a h2 (@lem1058535 A ZRECSPACE' h1)). Qed.
Lemma lem1058537 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term0 A ZRECSPACE' a.
Proof. exact (fun h0 : a = (@ZBOT A) => @lem1058536 A ZRECSPACE' a h1 h0). Qed.
Lemma lem1058538 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term1 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058537 A a ZRECSPACE' h1). Qed.
Lemma lem1058539 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term55 A ZRECSPACE'.
Proof. exact (conj (@lem1058538 A ZRECSPACE' h1) (@lem1058534 A ZRECSPACE' h1)). Qed.
Lemma lem1058540 {A : Type'} (ZRECSPACE' : type953 A) : term67 A ZRECSPACE'.
Proof. exact (fun h0 : term64 A ZRECSPACE' => @lem1058539 A ZRECSPACE' h0). Qed.
Lemma lem1058541 {A : Type'} (ZRECSPACE' : type953 A) : term68 A ZRECSPACE'.
Proof. exact (fun h0 : term55 A ZRECSPACE' => @lem1058515 A ZRECSPACE' h0). Qed.
Lemma lem1058542 {A : Type'} (ZRECSPACE' : type953 A) : term69 A ZRECSPACE'.
Proof. exact (conj (@lem1058541 A ZRECSPACE') (@lem1058540 A ZRECSPACE')). Qed.
Lemma lem1058543 {A : Type'} (ZRECSPACE' : type953 A) : (term69 A ZRECSPACE') = ((term55 A ZRECSPACE') = (term64 A ZRECSPACE')).
Proof. exact (@lem32 (term55 A ZRECSPACE') (term64 A ZRECSPACE')). Qed.
Lemma lem1058544 {A : Type'} (ZRECSPACE' : type953 A) : (term55 A ZRECSPACE') = (term64 A ZRECSPACE').
Proof. exact (EQ_MP (@lem1058543 A ZRECSPACE') (@lem1058542 A ZRECSPACE')). Qed.
Lemma lem1058545 {A : Type'} (ZRECSPACE' : type953 A) : (term58 A ZRECSPACE') = (term64 A ZRECSPACE').
Proof. exact (TRANS (@lem1058494 A ZRECSPACE') (@lem1058544 A ZRECSPACE')). Qed.
Lemma lem1058546 {A : Type'} (ZRECSPACE' : type953 A) : (term64 A ZRECSPACE') = (term58 A ZRECSPACE').
Proof. exact (SYM (@lem1058545 A ZRECSPACE')). Qed.
Lemma lem1058547 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : ZRECSPACE' = (term70 A).
Proof. exact (h1). Qed.
Lemma lem1058548 {A : Type'} (a : type1597 A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1058549 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : (ZRECSPACE' a) = (term71 A a).
Proof. exact (MK_COMB (@lem1058547 A ZRECSPACE' h1) (@lem1058548 A a)). Qed.
Lemma lem1058550 {A : Type'} (a : type1597 A) : (term71 A a) = (term72 A a).
Proof. exact (eq_refl (term71 A a)). Qed.
Lemma lem1058551 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term73 A ZRECSPACE' a) = (term73 A ZRECSPACE' a).
Proof. exact (eq_refl (term73 A ZRECSPACE' a)). Qed.
Lemma lem1058552 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : ((ZRECSPACE' a) = (term71 A a)) = ((ZRECSPACE' a) = (term72 A a)).
Proof. exact (MK_COMB (@lem1058551 A ZRECSPACE' a) (@lem1058550 A a)). Qed.
Lemma lem1058553 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : (ZRECSPACE' a) = (term72 A a).
Proof. exact (EQ_MP (@lem1058552 A ZRECSPACE' a) (@lem1058549 A a ZRECSPACE' h1)). Qed.
Lemma lem1058554 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term74 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058553 A a ZRECSPACE' h1). Qed.
Lemma lem1058555 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term75 A ZRECSPACE' a.
Proof. exact (@lem1058554 A ZRECSPACE' h1 a). Qed.
Lemma lem1058556 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term75 A ZRECSPACE' a) = ((ZRECSPACE' a) = (term72 A a)).
Proof. exact (eq_refl (term75 A ZRECSPACE' a)). Qed.
Lemma lem1058557 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : (ZRECSPACE' a) = (term72 A a).
Proof. exact (EQ_MP (@lem1058556 A ZRECSPACE' a) (@lem1058555 A a ZRECSPACE' h1)). Qed.
Lemma lem1058560 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : term76 A ZRECSPACE' a.
Proof. exact (@lem37 (ZRECSPACE' a) (term72 A a)). Qed.
Lemma lem1058561 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term77 A ZRECSPACE' a.
Proof. exact (@lem1058560 A ZRECSPACE' a (@lem1058557 A a ZRECSPACE' h1)). Qed.
Lemma lem1058562 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (h1 : ZRECSPACE' a) : ZRECSPACE' a.
Proof. exact (h1). Qed.
Lemma lem1058563 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' a) (h2 : ZRECSPACE' = (term70 A)) : term72 A a.
Proof. exact (@lem1058561 A a ZRECSPACE' h2 (@lem1058562 A ZRECSPACE' a h1)). Qed.
Lemma lem1058564 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) (h1 : ZRECSPACE'' a) (h2 : ZRECSPACE'' = (term70 A)) : term78 A a ZRECSPACE'.
Proof. exact (@lem1058563 A a ZRECSPACE'' h1 h2 ZRECSPACE'). Qed.
Lemma lem1058565 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term78 A a ZRECSPACE') = (term66 A ZRECSPACE' a).
Proof. exact (eq_refl (term78 A a ZRECSPACE')). Qed.
Lemma lem1058566 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) (h1 : ZRECSPACE'' a) (h2 : ZRECSPACE'' = (term70 A)) : term66 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058565 A ZRECSPACE' a) (@lem1058564 A ZRECSPACE' a ZRECSPACE'' h1 h2)). Qed.
Lemma lem1058567 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term64 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058568 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) (h1 : term64 A ZRECSPACE') (h2 : ZRECSPACE'' a) (h3 : ZRECSPACE'' = (term70 A)) : ZRECSPACE' a.
Proof. exact (@lem1058566 A ZRECSPACE' a ZRECSPACE'' h2 h3 (@lem1058567 A ZRECSPACE' h1)). Qed.
Lemma lem1058569 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term64 A ZRECSPACE') (h2 : ZRECSPACE'' = (term70 A)) : term79 A ZRECSPACE'' ZRECSPACE' a.
Proof. exact (fun h0 : ZRECSPACE'' a => @lem1058568 A ZRECSPACE' a ZRECSPACE'' h1 h0 h2). Qed.
Lemma lem1058570 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term64 A ZRECSPACE') (h2 : ZRECSPACE'' = (term70 A)) : term80 A ZRECSPACE'' ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058569 A a ZRECSPACE' ZRECSPACE'' h1 h2). Qed.
Lemma lem1058571 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : ZRECSPACE'' = (term70 A)) : term81 A ZRECSPACE'' ZRECSPACE'.
Proof. exact (fun h0 : term64 A ZRECSPACE' => @lem1058570 A ZRECSPACE' ZRECSPACE'' h0 h1). Qed.
Lemma lem1058572 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term82 A ZRECSPACE'.
Proof. exact (fun ZRECSPACE'' : type953 A => @lem1058571 A ZRECSPACE'' ZRECSPACE' h1). Qed.
Lemma lem1058573 {A : Type'} (h1 : term83 A) : term83 A.
Proof. exact (h1). Qed.
Lemma lem1058574 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term64 A ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058575 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : ZRECSPACE'' = (term70 A)) : term84 A ZRECSPACE'' ZRECSPACE'.
Proof. exact (@lem1058572 A ZRECSPACE'' h1 ZRECSPACE'). Qed.
Lemma lem1058576 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) : (term84 A ZRECSPACE' ZRECSPACE'') = (term81 A ZRECSPACE' ZRECSPACE'').
Proof. exact (eq_refl (term84 A ZRECSPACE' ZRECSPACE'')). Qed.
Lemma lem1058577 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : ZRECSPACE'' = (term70 A)) : term81 A ZRECSPACE'' ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058576 A ZRECSPACE'' ZRECSPACE') (@lem1058575 A ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058578 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term64 A ZRECSPACE') (h2 : ZRECSPACE'' = (term70 A)) : term80 A ZRECSPACE'' ZRECSPACE'.
Proof. exact (@lem1058577 A ZRECSPACE' ZRECSPACE'' h2 (@lem1058574 A ZRECSPACE' h1)). Qed.
Lemma lem1058579 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) : term85 A ZRECSPACE'.
Proof. exact (@lem1058573 A h1 ZRECSPACE'). Qed.
Lemma lem1058580 {A : Type'} (ZRECSPACE' : type953 A) : (term85 A ZRECSPACE') = (term86 A ZRECSPACE').
Proof. exact (eq_refl (term85 A ZRECSPACE')). Qed.
Lemma lem1058581 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) : term86 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058580 A ZRECSPACE') (@lem1058579 A ZRECSPACE' h1)). Qed.
Lemma lem1058582 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) : term87 A ZRECSPACE' ZRECSPACE''.
Proof. exact (@lem1058581 A ZRECSPACE' h1 ZRECSPACE''). Qed.
Lemma lem1058583 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) : (term87 A ZRECSPACE' ZRECSPACE'') = (term88 A ZRECSPACE' ZRECSPACE'').
Proof. exact (eq_refl (term87 A ZRECSPACE' ZRECSPACE'')). Qed.
Lemma lem1058584 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) : term88 A ZRECSPACE' ZRECSPACE''.
Proof. exact (EQ_MP (@lem1058583 A ZRECSPACE' ZRECSPACE'') (@lem1058582 A ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058585 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) (h2 : term64 A ZRECSPACE') (h3 : ZRECSPACE'' = (term70 A)) : term89 A ZRECSPACE'' ZRECSPACE'.
Proof. exact (@lem1058584 A ZRECSPACE'' ZRECSPACE' h1 (@lem1058578 A ZRECSPACE' ZRECSPACE'' h2 h3)). Qed.
Lemma lem1058586 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term65 A ZRECSPACE' a.
Proof. exact (@lem1058574 A ZRECSPACE' h1 a). Qed.
Lemma lem1058587 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term65 A ZRECSPACE' a) = (term63 A ZRECSPACE' a).
Proof. exact (eq_refl (term65 A ZRECSPACE' a)). Qed.
Lemma lem1058588 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term64 A ZRECSPACE') : term63 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058587 A ZRECSPACE' a) (@lem1058586 A a ZRECSPACE' h1)). Qed.
Lemma lem1058589 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) (h2 : term64 A ZRECSPACE') (h3 : ZRECSPACE'' = (term70 A)) : term90 A ZRECSPACE'' ZRECSPACE' a.
Proof. exact (@lem1058585 A ZRECSPACE' ZRECSPACE'' h1 h2 h3 a). Qed.
Lemma lem1058590 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : (term90 A ZRECSPACE' ZRECSPACE'' a) = (term91 A ZRECSPACE' a ZRECSPACE'').
Proof. exact (eq_refl (term90 A ZRECSPACE' ZRECSPACE'' a)). Qed.
Lemma lem1058591 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) (h2 : term64 A ZRECSPACE') (h3 : ZRECSPACE'' = (term70 A)) : term91 A ZRECSPACE'' a ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058590 A ZRECSPACE'' a ZRECSPACE') (@lem1058589 A a ZRECSPACE' ZRECSPACE'' h1 h2 h3)). Qed.
Lemma lem1058592 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (a : type1597 A) : term92 A ZRECSPACE' ZRECSPACE'' a.
Proof. exact (@lem51 (term62 A a ZRECSPACE'') (term62 A a ZRECSPACE') (ZRECSPACE'' a)). Qed.
Lemma lem1058593 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) (h2 : term64 A ZRECSPACE') (h3 : ZRECSPACE'' = (term70 A)) : term93 A ZRECSPACE'' ZRECSPACE' a.
Proof. exact (@lem1058592 A ZRECSPACE'' ZRECSPACE' a (@lem1058591 A a ZRECSPACE' ZRECSPACE'' h1 h2 h3)). Qed.
Lemma lem1058594 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) (h2 : term64 A ZRECSPACE') (h3 : ZRECSPACE'' = (term70 A)) : term94 A ZRECSPACE'' ZRECSPACE' a.
Proof. exact (@lem1058593 A a ZRECSPACE' ZRECSPACE'' h1 h2 h3 (@lem1058588 A a ZRECSPACE' h2)). Qed.
Lemma lem1058595 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term62 A a ZRECSPACE') : term62 A a ZRECSPACE'.
Proof. exact (h1). Qed.
Lemma lem1058596 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) (h2 : term64 A ZRECSPACE') (h3 : ZRECSPACE'' = (term70 A)) (h4 : term62 A a ZRECSPACE'') : ZRECSPACE' a.
Proof. exact (@lem1058594 A a ZRECSPACE' ZRECSPACE'' h1 h2 h3 (@lem1058595 A a ZRECSPACE'' h4)). Qed.
Lemma lem1058597 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE'' = (term70 A)) (h3 : term62 A a ZRECSPACE'') : term66 A ZRECSPACE' a.
Proof. exact (fun h0 : term64 A ZRECSPACE' => @lem1058596 A ZRECSPACE' a ZRECSPACE'' h1 h0 h2 h3). Qed.
Lemma lem1058598 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) (h3 : term62 A a ZRECSPACE') : term72 A a.
Proof. exact (fun ZRECSPACE'' : type953 A => @lem1058597 A ZRECSPACE'' a ZRECSPACE' h1 h2 h3). Qed.
Lemma lem1058599 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term75 A ZRECSPACE' a.
Proof. exact (@lem1058554 A ZRECSPACE' h1 a). Qed.
Lemma lem1058600 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term75 A ZRECSPACE' a) = ((ZRECSPACE' a) = (term72 A a)).
Proof. exact (eq_refl (term75 A ZRECSPACE' a)). Qed.
Lemma lem1058601 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : (ZRECSPACE' a) = (term72 A a).
Proof. exact (EQ_MP (@lem1058600 A ZRECSPACE' a) (@lem1058599 A a ZRECSPACE' h1)). Qed.
Lemma lem1058602 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : (term72 A a) = (ZRECSPACE' a).
Proof. exact (SYM (@lem1058601 A a ZRECSPACE' h1)). Qed.
Lemma lem1058603 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) (h3 : term62 A a ZRECSPACE') : ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058602 A a ZRECSPACE' h2) (@lem1058598 A a ZRECSPACE' h1 h2 h3)). Qed.
Lemma lem1058604 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term63 A ZRECSPACE' a.
Proof. exact (fun h0 : term62 A a ZRECSPACE' => @lem1058603 A a ZRECSPACE' h1 h2 h0). Qed.
Lemma lem1058605 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term64 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058604 A a ZRECSPACE' h1 h2). Qed.
Lemma lem1058608 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term95 A ZRECSPACE' a) = (term95 A ZRECSPACE' a).
Proof. exact (eq_refl (term95 A ZRECSPACE' a)). Qed.
Lemma lem1058609 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term95 A ZRECSPACE' a) = (term62 A a ZRECSPACE').
Proof. exact (eq_refl (term95 A ZRECSPACE' a)). Qed.
Lemma lem1058610 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term96 A ZRECSPACE' a) = (term96 A ZRECSPACE' a).
Proof. exact (eq_refl (term96 A ZRECSPACE' a)). Qed.
Lemma lem1058611 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : ((term95 A ZRECSPACE' a) = (term95 A ZRECSPACE' a)) = ((term95 A ZRECSPACE' a) = (term62 A a ZRECSPACE')).
Proof. exact (MK_COMB (@lem1058610 A ZRECSPACE' a) (@lem1058609 A a ZRECSPACE')). Qed.
Lemma lem1058612 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term95 A ZRECSPACE' a) = (term62 A a ZRECSPACE').
Proof. exact (EQ_MP (@lem1058611 A a ZRECSPACE') (@lem1058608 A ZRECSPACE' a)). Qed.
Lemma lem1058613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058614 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term97 A ZRECSPACE' a) = (term98 A a ZRECSPACE').
Proof. exact (MK_COMB (@lem1058613) (@lem1058612 A a ZRECSPACE')). Qed.
Lemma lem1058615 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (ZRECSPACE' a) = (ZRECSPACE' a).
Proof. exact (eq_refl (ZRECSPACE' a)). Qed.
Lemma lem1058616 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term99 A ZRECSPACE' a) = (term63 A ZRECSPACE' a).
Proof. exact (MK_COMB (@lem1058614 A a ZRECSPACE') (@lem1058615 A ZRECSPACE' a)). Qed.
Lemma lem1058617 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term100 A a ZRECSPACE') = (term100 A a ZRECSPACE').
Proof. exact (eq_refl (term100 A a ZRECSPACE')). Qed.
Lemma lem1058618 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term101 A ZRECSPACE' a) = (term102 A a ZRECSPACE').
Proof. exact (MK_COMB (@lem1058617 A a ZRECSPACE') (@lem1058612 A a ZRECSPACE')). Qed.
Lemma lem1058619 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term103 A ZRECSPACE' a) = (term103 A ZRECSPACE' a).
Proof. exact (eq_refl (term103 A ZRECSPACE' a)). Qed.
Lemma lem1058620 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term104 A ZRECSPACE' a) = (term105 A a ZRECSPACE').
Proof. exact (MK_COMB (@lem1058619 A ZRECSPACE' a) (@lem1058612 A a ZRECSPACE')). Qed.
Lemma lem1058621 {A : Type'} (ZRECSPACE' : type953 A) : (term106 A ZRECSPACE') = (term107 A ZRECSPACE').
Proof. exact (fun_ext (fun a : type1597 A => @lem1058620 A a ZRECSPACE')). Qed.
Lemma lem1058622 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem1058623 {A : Type'} (ZRECSPACE' : type953 A) : (term108 A ZRECSPACE') = (term109 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058622 A) (@lem1058621 A ZRECSPACE')). Qed.
Lemma lem1058624 {A : Type'} (ZRECSPACE' : type953 A) : (term110 A ZRECSPACE') = (term111 A ZRECSPACE').
Proof. exact (fun_ext (fun a : type1597 A => @lem1058618 A a ZRECSPACE')). Qed.
Lemma lem1058625 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem1058626 {A : Type'} (ZRECSPACE' : type953 A) : (term112 A ZRECSPACE') = (term113 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058625 A) (@lem1058624 A ZRECSPACE')). Qed.
Lemma lem1058627 {A : Type'} (ZRECSPACE' : type953 A) : (term114 A ZRECSPACE') = (term115 A ZRECSPACE').
Proof. exact (fun_ext (fun a : type1597 A => @lem1058616 A ZRECSPACE' a)). Qed.
Lemma lem1058628 {A : Type'} : (@all (nat -> A -> Prop)) = (@all (nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> A -> Prop))). Qed.
Lemma lem1058629 {A : Type'} (ZRECSPACE' : type953 A) : (term116 A ZRECSPACE') = (term64 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058628 A) (@lem1058627 A ZRECSPACE')). Qed.
Lemma lem1058630 {A : Type'} (ZRECSPACE' : type953 A) : (term64 A ZRECSPACE') = (term116 A ZRECSPACE').
Proof. exact (SYM (@lem1058629 A ZRECSPACE')). Qed.
Lemma lem1058631 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term116 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058630 A ZRECSPACE') (@lem1058605 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058632 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) : term117 A ZRECSPACE'.
Proof. exact (@lem1058573 A h1 (term118 A ZRECSPACE')). Qed.
Lemma lem1058633 {A : Type'} (ZRECSPACE' : type953 A) : (term117 A ZRECSPACE') = (term119 A ZRECSPACE').
Proof. exact (eq_refl (term117 A ZRECSPACE')). Qed.
Lemma lem1058634 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) : term119 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058633 A ZRECSPACE') (@lem1058632 A ZRECSPACE' h1)). Qed.
Lemma lem1058635 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) : term120 A ZRECSPACE'.
Proof. exact (@lem1058634 A ZRECSPACE' h1 ZRECSPACE'). Qed.
Lemma lem1058636 {A : Type'} (ZRECSPACE' : type953 A) : (term120 A ZRECSPACE') = (term121 A ZRECSPACE').
Proof. exact (eq_refl (term120 A ZRECSPACE')). Qed.
Lemma lem1058637 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) : term121 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058636 A ZRECSPACE') (@lem1058635 A ZRECSPACE' h1)). Qed.
Lemma lem1058638 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term113 A ZRECSPACE'.
Proof. exact (@lem1058637 A ZRECSPACE' h1 (@lem1058631 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058639 {A : Type'} (ZRECSPACE' : type953 A) : (term113 A ZRECSPACE') = (term112 A ZRECSPACE').
Proof. exact (SYM (@lem1058626 A ZRECSPACE')). Qed.
Lemma lem1058640 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term112 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058639 A ZRECSPACE') (@lem1058638 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058641 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term122 A ZRECSPACE'.
Proof. exact (@lem1058572 A ZRECSPACE' h1 (term118 A ZRECSPACE')). Qed.
Lemma lem1058642 {A : Type'} (ZRECSPACE' : type953 A) : (term122 A ZRECSPACE') = (term123 A ZRECSPACE').
Proof. exact (eq_refl (term122 A ZRECSPACE')). Qed.
Lemma lem1058643 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term123 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058642 A ZRECSPACE') (@lem1058641 A ZRECSPACE' h1)). Qed.
Lemma lem1058644 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term108 A ZRECSPACE'.
Proof. exact (@lem1058643 A ZRECSPACE' h2 (@lem1058640 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058645 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term109 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058623 A ZRECSPACE') (@lem1058644 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058646 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term65 A ZRECSPACE' a.
Proof. exact (@lem1058605 A ZRECSPACE' h1 h2 a). Qed.
Lemma lem1058647 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) : (term65 A ZRECSPACE' a) = (term63 A ZRECSPACE' a).
Proof. exact (eq_refl (term65 A ZRECSPACE' a)). Qed.
Lemma lem1058648 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term63 A ZRECSPACE' a.
Proof. exact (EQ_MP (@lem1058647 A ZRECSPACE' a) (@lem1058646 A a ZRECSPACE' h1 h2)). Qed.
Lemma lem1058649 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term124 A ZRECSPACE' a.
Proof. exact (@lem1058645 A ZRECSPACE' h1 h2 a). Qed.
Lemma lem1058650 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term124 A ZRECSPACE' a) = (term105 A a ZRECSPACE').
Proof. exact (eq_refl (term124 A ZRECSPACE' a)). Qed.
Lemma lem1058651 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term105 A a ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058650 A a ZRECSPACE') (@lem1058649 A a ZRECSPACE' h1 h2)). Qed.
Lemma lem1058652 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term125 A ZRECSPACE' a.
Proof. exact (conj (@lem1058651 A a ZRECSPACE' h1 h2) (@lem1058648 A a ZRECSPACE' h1 h2)). Qed.
Lemma lem1058653 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term125 A ZRECSPACE' a) = ((ZRECSPACE' a) = (term62 A a ZRECSPACE')).
Proof. exact (@lem32 (ZRECSPACE' a) (term62 A a ZRECSPACE')). Qed.
Lemma lem1058654 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : (ZRECSPACE' a) = (term62 A a ZRECSPACE').
Proof. exact (EQ_MP (@lem1058653 A a ZRECSPACE') (@lem1058652 A a ZRECSPACE' h1 h2)). Qed.
Lemma lem1058659 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term64 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058604 A a ZRECSPACE' h1 h2). Qed.
Lemma lem1058660 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term126 A ZRECSPACE'.
Proof. exact (fun a : type1597 A => @lem1058654 A a ZRECSPACE' h1 h2). Qed.
Lemma lem1058661 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term82 A ZRECSPACE'.
Proof. exact (fun ZRECSPACE'' : type953 A => @lem1058571 A ZRECSPACE'' ZRECSPACE' h2). Qed.
Lemma lem1058662 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term58 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058546 A ZRECSPACE') (@lem1058659 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058676 {A : Type'} (ZRECSPACE' : type953 A) : (term64 A ZRECSPACE') = (term58 A ZRECSPACE').
Proof. exact (SYM (@lem1058545 A ZRECSPACE')). Qed.
Lemma lem1058677 {A : Type'} (ZRECSPACE' : type953 A) : (term64 A ZRECSPACE') = (term58 A ZRECSPACE').
Proof. exact (@lem1058676 A ZRECSPACE'). Qed.
Lemma lem1058678 {A : Type'} (ZRECSPACE' : type953 A) : (term64 A ZRECSPACE') = (term58 A ZRECSPACE').
Proof. exact (@lem1058677 A ZRECSPACE'). Qed.
Lemma lem1058679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058680 {A : Type'} (ZRECSPACE' : type953 A) : (term127 A ZRECSPACE') = (term128 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058679) (@lem1058678 A ZRECSPACE')). Qed.
Lemma lem1058705 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) : (term80 A ZRECSPACE' ZRECSPACE'') = (term80 A ZRECSPACE' ZRECSPACE'').
Proof. exact (eq_refl (term80 A ZRECSPACE' ZRECSPACE'')). Qed.
Lemma lem1058706 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) : (term81 A ZRECSPACE' ZRECSPACE'') = (term129 A ZRECSPACE' ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058680 A ZRECSPACE'') (@lem1058705 A ZRECSPACE' ZRECSPACE'')). Qed.
Lemma lem1058707 {A : Type'} (ZRECSPACE' : type953 A) : (term130 A ZRECSPACE') = (term131 A ZRECSPACE').
Proof. exact (fun_ext (fun ZRECSPACE'' : type953 A => @lem1058706 A ZRECSPACE' ZRECSPACE'')). Qed.
Lemma lem1058708 {A : Type'} : (@all ((nat -> A -> Prop) -> Prop)) = (@all ((nat -> A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((nat -> A -> Prop) -> Prop))). Qed.
Lemma lem1058709 {A : Type'} (ZRECSPACE' : type953 A) : (term82 A ZRECSPACE') = (term132 A ZRECSPACE').
Proof. exact (MK_COMB (@lem1058708 A) (@lem1058707 A ZRECSPACE')). Qed.
Lemma lem1058710 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term132 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058709 A ZRECSPACE') (@lem1058661 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058711 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term133 A ZRECSPACE'.
Proof. exact (conj (@lem1058710 A ZRECSPACE' h1 h2) (@lem1058660 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058712 {A : Type'} (ZRECSPACE' : type953 A) (h1 : term83 A) (h2 : ZRECSPACE' = (term70 A)) : term134 A ZRECSPACE'.
Proof. exact (conj (@lem1058662 A ZRECSPACE' h1 h2) (@lem1058711 A ZRECSPACE' h1 h2)). Qed.
Lemma lem1058713 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term80 A ZRECSPACE' ZRECSPACE''.
Proof. exact (h1). Qed.
Lemma lem1058715 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term135 A C B D.
Proof. exact (fun h0 : term136 A B C D => @lem7129 A B C D h0). Qed.
Lemma lem1058717 {A : Type'} (a : type1597 A) : term137 A a.
Proof. exact (@lem9120 (a = (@ZBOT A))). Qed.
Lemma lem1058718 {A : Type'} (a : type1597 A) : (term137 A a) = (term138 A a).
Proof. exact (eq_refl (term137 A a)). Qed.
Lemma lem1058719 {A : Type'} (a : type1597 A) : term138 A a.
Proof. exact (EQ_MP (@lem1058718 A a) (@lem1058717 A a)). Qed.
Lemma lem1058721 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term139 A P Q.
Proof. exact (fun h0 : term140 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1058722 (P : nat -> Prop) (Q : nat -> Prop) : term141 P Q.
Proof. exact (@lem1058721 nat P Q). Qed.
Lemma lem1058723 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : term142 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (@lem1058722 (term47 A a ZRECSPACE') (term47 A a ZRECSPACE'')). Qed.
Lemma lem1058724 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term143 A a ZRECSPACE' c) = (term44 A a c ZRECSPACE').
Proof. exact (eq_refl (term143 A a ZRECSPACE' c)). Qed.
Lemma lem1058725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058726 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term144 A a ZRECSPACE' c) = (term145 A a c ZRECSPACE').
Proof. exact (MK_COMB (@lem1058725) (@lem1058724 A a c ZRECSPACE')). Qed.
Lemma lem1058727 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term143 A a ZRECSPACE' c) = (term44 A a c ZRECSPACE').
Proof. exact (eq_refl (term143 A a ZRECSPACE' c)). Qed.
Lemma lem1058728 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : (term146 A ZRECSPACE' a ZRECSPACE'' c) = (term147 A ZRECSPACE' a c ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058726 A a c ZRECSPACE') (@lem1058727 A a c ZRECSPACE'')). Qed.
Lemma lem1058729 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : (term148 A ZRECSPACE' a ZRECSPACE'') = (term149 A ZRECSPACE' a ZRECSPACE'').
Proof. exact (fun_ext (fun c : nat => @lem1058728 A ZRECSPACE' a c ZRECSPACE'')). Qed.
Lemma lem1058730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1058731 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : (term150 A ZRECSPACE' a ZRECSPACE'') = (term151 A ZRECSPACE' a ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058730) (@lem1058729 A ZRECSPACE' a ZRECSPACE'')). Qed.
Lemma lem1058732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058733 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : (term152 A ZRECSPACE' a ZRECSPACE'') = (term153 A ZRECSPACE' a ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058732) (@lem1058731 A ZRECSPACE' a ZRECSPACE'')). Qed.
Lemma lem1058734 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term143 A a ZRECSPACE' c) = (term44 A a c ZRECSPACE').
Proof. exact (eq_refl (term143 A a ZRECSPACE' c)). Qed.
Lemma lem1058735 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term154 A a ZRECSPACE') = (term47 A a ZRECSPACE').
Proof. exact (fun_ext (fun c : nat => @lem1058734 A a c ZRECSPACE')). Qed.
Lemma lem1058736 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1058737 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term155 A a ZRECSPACE') = (term46 A a ZRECSPACE').
Proof. exact (MK_COMB (@lem1058736) (@lem1058735 A a ZRECSPACE')). Qed.
Lemma lem1058738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058739 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term156 A a ZRECSPACE') = (term157 A a ZRECSPACE').
Proof. exact (MK_COMB (@lem1058738) (@lem1058737 A a ZRECSPACE')). Qed.
Lemma lem1058740 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term143 A a ZRECSPACE' c) = (term44 A a c ZRECSPACE').
Proof. exact (eq_refl (term143 A a ZRECSPACE' c)). Qed.
Lemma lem1058741 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term154 A a ZRECSPACE') = (term47 A a ZRECSPACE').
Proof. exact (fun_ext (fun c : nat => @lem1058740 A a c ZRECSPACE')). Qed.
Lemma lem1058742 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1058743 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) : (term155 A a ZRECSPACE') = (term46 A a ZRECSPACE').
Proof. exact (MK_COMB (@lem1058742) (@lem1058741 A a ZRECSPACE')). Qed.
Lemma lem1058744 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : (term158 A ZRECSPACE' a ZRECSPACE'') = (term159 A ZRECSPACE' a ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058739 A a ZRECSPACE') (@lem1058743 A a ZRECSPACE'')). Qed.
Lemma lem1058745 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : (term142 A ZRECSPACE' a ZRECSPACE'') = (term160 A ZRECSPACE' a ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058733 A ZRECSPACE' a ZRECSPACE'') (@lem1058744 A ZRECSPACE' a ZRECSPACE'')). Qed.
Lemma lem1058748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term139 A P Q.
Proof. exact (fun h0 : term140 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1058749 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term139 A P Q.
Proof. exact (@lem1058748 A P Q). Qed.
Lemma lem1058750 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : term161 A ZRECSPACE' a c ZRECSPACE''.
Proof. exact (@lem1058749 A (term45 A a c ZRECSPACE') (term45 A a c ZRECSPACE'')). Qed.
Lemma lem1058751 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term162 A a c ZRECSPACE' i) = (term42 A a c i ZRECSPACE').
Proof. exact (eq_refl (term162 A a c ZRECSPACE' i)). Qed.
Lemma lem1058752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058753 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term163 A a c ZRECSPACE' i) = (term164 A a c i ZRECSPACE').
Proof. exact (MK_COMB (@lem1058752) (@lem1058751 A a c i ZRECSPACE')). Qed.
Lemma lem1058754 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term162 A a c ZRECSPACE' i) = (term42 A a c i ZRECSPACE').
Proof. exact (eq_refl (term162 A a c ZRECSPACE' i)). Qed.
Lemma lem1058755 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : (term165 A ZRECSPACE' a c ZRECSPACE'' i) = (term166 A ZRECSPACE' a c i ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058753 A a c i ZRECSPACE') (@lem1058754 A a c i ZRECSPACE'')). Qed.
Lemma lem1058756 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : (term167 A ZRECSPACE' a c ZRECSPACE'') = (term168 A ZRECSPACE' a c ZRECSPACE'').
Proof. exact (fun_ext (fun i : A => @lem1058755 A ZRECSPACE' a c i ZRECSPACE'')). Qed.
Lemma lem1058757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1058758 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : (term169 A ZRECSPACE' a c ZRECSPACE'') = (term170 A ZRECSPACE' a c ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058757 A) (@lem1058756 A ZRECSPACE' a c ZRECSPACE'')). Qed.
Lemma lem1058759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058760 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : (term171 A ZRECSPACE' a c ZRECSPACE'') = (term172 A ZRECSPACE' a c ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058759) (@lem1058758 A ZRECSPACE' a c ZRECSPACE'')). Qed.
Lemma lem1058761 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term162 A a c ZRECSPACE' i) = (term42 A a c i ZRECSPACE').
Proof. exact (eq_refl (term162 A a c ZRECSPACE' i)). Qed.
Lemma lem1058762 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term173 A a c ZRECSPACE') = (term45 A a c ZRECSPACE').
Proof. exact (fun_ext (fun i : A => @lem1058761 A a c i ZRECSPACE')). Qed.
Lemma lem1058763 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1058764 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term174 A a c ZRECSPACE') = (term44 A a c ZRECSPACE').
Proof. exact (MK_COMB (@lem1058763 A) (@lem1058762 A a c ZRECSPACE')). Qed.
Lemma lem1058765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058766 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term175 A a c ZRECSPACE') = (term145 A a c ZRECSPACE').
Proof. exact (MK_COMB (@lem1058765) (@lem1058764 A a c ZRECSPACE')). Qed.
Lemma lem1058767 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term162 A a c ZRECSPACE' i) = (term42 A a c i ZRECSPACE').
Proof. exact (eq_refl (term162 A a c ZRECSPACE' i)). Qed.
Lemma lem1058768 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term173 A a c ZRECSPACE') = (term45 A a c ZRECSPACE').
Proof. exact (fun_ext (fun i : A => @lem1058767 A a c i ZRECSPACE')). Qed.
Lemma lem1058769 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1058770 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) : (term174 A a c ZRECSPACE') = (term44 A a c ZRECSPACE').
Proof. exact (MK_COMB (@lem1058769 A) (@lem1058768 A a c ZRECSPACE')). Qed.
Lemma lem1058771 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : (term176 A ZRECSPACE' a c ZRECSPACE'') = (term147 A ZRECSPACE' a c ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058766 A a c ZRECSPACE') (@lem1058770 A a c ZRECSPACE'')). Qed.
Lemma lem1058772 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : (term161 A ZRECSPACE' a c ZRECSPACE'') = (term177 A ZRECSPACE' a c ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058760 A ZRECSPACE' a c ZRECSPACE'') (@lem1058771 A ZRECSPACE' a c ZRECSPACE'')). Qed.
Lemma lem1058775 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term139 A P Q.
Proof. exact (fun h0 : term140 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1058776 {A : Type'} (P : type955 A) (Q : type955 A) : term178 A P Q.
Proof. exact (@lem1058775 (type1600 A) P Q). Qed.
Lemma lem1058777 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : term179 A ZRECSPACE' a c i ZRECSPACE''.
Proof. exact (@lem1058776 A (term43 A a c i ZRECSPACE') (term43 A a c i ZRECSPACE'')). Qed.
Lemma lem1058778 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) : (term180 A a c i ZRECSPACE' r) = (term11 A a c i ZRECSPACE' r).
Proof. exact (eq_refl (term180 A a c i ZRECSPACE' r)). Qed.
Lemma lem1058779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058780 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) : (term181 A a c i ZRECSPACE' r) = (term182 A a c i ZRECSPACE' r).
Proof. exact (MK_COMB (@lem1058779) (@lem1058778 A a c i ZRECSPACE' r)). Qed.
Lemma lem1058781 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) : (term180 A a c i ZRECSPACE' r) = (term11 A a c i ZRECSPACE' r).
Proof. exact (eq_refl (term180 A a c i ZRECSPACE' r)). Qed.
Lemma lem1058782 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) (r : type1600 A) : (term183 A ZRECSPACE' a c i ZRECSPACE'' r) = (term184 A ZRECSPACE' a c i ZRECSPACE'' r).
Proof. exact (MK_COMB (@lem1058780 A a c i ZRECSPACE' r) (@lem1058781 A a c i ZRECSPACE'' r)). Qed.
Lemma lem1058783 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : (term185 A ZRECSPACE' a c i ZRECSPACE'') = (term186 A ZRECSPACE' a c i ZRECSPACE'').
Proof. exact (fun_ext (fun r : type1600 A => @lem1058782 A ZRECSPACE' a c i ZRECSPACE'' r)). Qed.
Lemma lem1058784 {A : Type'} : (@all (nat -> nat -> A -> Prop)) = (@all (nat -> nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> A -> Prop))). Qed.
Lemma lem1058785 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : (term187 A ZRECSPACE' a c i ZRECSPACE'') = (term188 A ZRECSPACE' a c i ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058784 A) (@lem1058783 A ZRECSPACE' a c i ZRECSPACE'')). Qed.
Lemma lem1058786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058787 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : (term189 A ZRECSPACE' a c i ZRECSPACE'') = (term190 A ZRECSPACE' a c i ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058786) (@lem1058785 A ZRECSPACE' a c i ZRECSPACE'')). Qed.
Lemma lem1058788 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) : (term180 A a c i ZRECSPACE' r) = (term11 A a c i ZRECSPACE' r).
Proof. exact (eq_refl (term180 A a c i ZRECSPACE' r)). Qed.
Lemma lem1058789 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term191 A a c i ZRECSPACE') = (term43 A a c i ZRECSPACE').
Proof. exact (fun_ext (fun r : type1600 A => @lem1058788 A a c i ZRECSPACE' r)). Qed.
Lemma lem1058790 {A : Type'} : (@ex (nat -> nat -> A -> Prop)) = (@ex (nat -> nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> A -> Prop))). Qed.
Lemma lem1058791 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term192 A a c i ZRECSPACE') = (term42 A a c i ZRECSPACE').
Proof. exact (MK_COMB (@lem1058790 A) (@lem1058789 A a c i ZRECSPACE')). Qed.
Lemma lem1058792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058793 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term193 A a c i ZRECSPACE') = (term164 A a c i ZRECSPACE').
Proof. exact (MK_COMB (@lem1058792) (@lem1058791 A a c i ZRECSPACE')). Qed.
Lemma lem1058794 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (r : type1600 A) : (term180 A a c i ZRECSPACE' r) = (term11 A a c i ZRECSPACE' r).
Proof. exact (eq_refl (term180 A a c i ZRECSPACE' r)). Qed.
Lemma lem1058795 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term191 A a c i ZRECSPACE') = (term43 A a c i ZRECSPACE').
Proof. exact (fun_ext (fun r : type1600 A => @lem1058794 A a c i ZRECSPACE' r)). Qed.
Lemma lem1058796 {A : Type'} : (@ex (nat -> nat -> A -> Prop)) = (@ex (nat -> nat -> A -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> A -> Prop))). Qed.
Lemma lem1058797 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) : (term192 A a c i ZRECSPACE') = (term42 A a c i ZRECSPACE').
Proof. exact (MK_COMB (@lem1058796 A) (@lem1058795 A a c i ZRECSPACE')). Qed.
Lemma lem1058798 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : (term194 A ZRECSPACE' a c i ZRECSPACE'') = (term166 A ZRECSPACE' a c i ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058793 A a c i ZRECSPACE') (@lem1058797 A a c i ZRECSPACE'')). Qed.
Lemma lem1058799 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : (term179 A ZRECSPACE' a c i ZRECSPACE'') = (term195 A ZRECSPACE' a c i ZRECSPACE'').
Proof. exact (MK_COMB (@lem1058787 A ZRECSPACE' a c i ZRECSPACE'') (@lem1058798 A ZRECSPACE' a c i ZRECSPACE'')). Qed.
Lemma lem1058802 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term196 A C B D.
Proof. exact (fun h0 : term136 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem1058804 {A : Type'} (a : type1597 A) (c : nat) (i : A) (r : type1600 A) : term197 A a c i r.
Proof. exact (@lem9120 (a = (@ZCONSTR A c i r))). Qed.
Lemma lem1058805 {A : Type'} (a : type1597 A) (c : nat) (i : A) (r : type1600 A) : (term197 A a c i r) = (term198 A a c i r).
Proof. exact (eq_refl (term197 A a c i r)). Qed.
Lemma lem1058806 {A : Type'} (a : type1597 A) (c : nat) (i : A) (r : type1600 A) : term198 A a c i r.
Proof. exact (EQ_MP (@lem1058805 A a c i r) (@lem1058804 A a c i r)). Qed.
Lemma lem1058808 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term199 A P Q.
Proof. exact (fun h0 : term140 A P Q => @lem7362 A P Q h0). Qed.
Lemma lem1058809 (P : nat -> Prop) (Q : nat -> Prop) : term200 P Q.
Proof. exact (@lem1058808 nat P Q). Qed.
Lemma lem1058810 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) : term201 A ZRECSPACE' ZRECSPACE'' r.
Proof. exact (@lem1058809 (term202 A ZRECSPACE' r) (term202 A ZRECSPACE'' r)). Qed.
Lemma lem1058811 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) (n : nat) : (term203 A ZRECSPACE' r n) = (term204 A ZRECSPACE' r n).
Proof. exact (eq_refl (term203 A ZRECSPACE' r n)). Qed.
Lemma lem1058812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058813 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) (n : nat) : (term205 A ZRECSPACE' r n) = (term206 A ZRECSPACE' r n).
Proof. exact (MK_COMB (@lem1058812) (@lem1058811 A ZRECSPACE' r n)). Qed.
Lemma lem1058814 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) (n : nat) : (term203 A ZRECSPACE' r n) = (term204 A ZRECSPACE' r n).
Proof. exact (eq_refl (term203 A ZRECSPACE' r n)). Qed.
Lemma lem1058815 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) (n : nat) : (term207 A ZRECSPACE' ZRECSPACE'' r n) = (term208 A ZRECSPACE' ZRECSPACE'' r n).
Proof. exact (MK_COMB (@lem1058813 A ZRECSPACE' r n) (@lem1058814 A ZRECSPACE'' r n)). Qed.
Lemma lem1058816 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) : (term209 A ZRECSPACE' ZRECSPACE'' r) = (term210 A ZRECSPACE' ZRECSPACE'' r).
Proof. exact (fun_ext (fun n : nat => @lem1058815 A ZRECSPACE' ZRECSPACE'' r n)). Qed.
Lemma lem1058817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1058818 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) : (term211 A ZRECSPACE' ZRECSPACE'' r) = (term212 A ZRECSPACE' ZRECSPACE'' r).
Proof. exact (MK_COMB (@lem1058817) (@lem1058816 A ZRECSPACE' ZRECSPACE'' r)). Qed.
Lemma lem1058819 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058820 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) : (term213 A ZRECSPACE' ZRECSPACE'' r) = (term214 A ZRECSPACE' ZRECSPACE'' r).
Proof. exact (MK_COMB (@lem1058819) (@lem1058818 A ZRECSPACE' ZRECSPACE'' r)). Qed.
Lemma lem1058821 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) (n : nat) : (term203 A ZRECSPACE' r n) = (term204 A ZRECSPACE' r n).
Proof. exact (eq_refl (term203 A ZRECSPACE' r n)). Qed.
Lemma lem1058822 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) : (term215 A ZRECSPACE' r) = (term202 A ZRECSPACE' r).
Proof. exact (fun_ext (fun n : nat => @lem1058821 A ZRECSPACE' r n)). Qed.
Lemma lem1058823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1058824 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) : (term216 A ZRECSPACE' r) = (term12 A ZRECSPACE' r).
Proof. exact (MK_COMB (@lem1058823) (@lem1058822 A ZRECSPACE' r)). Qed.
Lemma lem1058825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1058826 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) : (term217 A ZRECSPACE' r) = (term218 A ZRECSPACE' r).
Proof. exact (MK_COMB (@lem1058825) (@lem1058824 A ZRECSPACE' r)). Qed.
Lemma lem1058827 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) (n : nat) : (term203 A ZRECSPACE' r n) = (term204 A ZRECSPACE' r n).
Proof. exact (eq_refl (term203 A ZRECSPACE' r n)). Qed.
Lemma lem1058828 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) : (term215 A ZRECSPACE' r) = (term202 A ZRECSPACE' r).
Proof. exact (fun_ext (fun n : nat => @lem1058827 A ZRECSPACE' r n)). Qed.
Lemma lem1058829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1058830 {A : Type'} (ZRECSPACE' : type953 A) (r : type1600 A) : (term216 A ZRECSPACE' r) = (term12 A ZRECSPACE' r).
Proof. exact (MK_COMB (@lem1058829) (@lem1058828 A ZRECSPACE' r)). Qed.
Lemma lem1058831 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) : (term219 A ZRECSPACE' ZRECSPACE'' r) = (term220 A ZRECSPACE' ZRECSPACE'' r).
Proof. exact (MK_COMB (@lem1058826 A ZRECSPACE' r) (@lem1058830 A ZRECSPACE'' r)). Qed.
Lemma lem1058832 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) : (term201 A ZRECSPACE' ZRECSPACE'' r) = (term221 A ZRECSPACE' ZRECSPACE'' r).
Proof. exact (MK_COMB (@lem1058820 A ZRECSPACE' ZRECSPACE'' r) (@lem1058831 A ZRECSPACE' ZRECSPACE'' r)). Qed.
Lemma lem1058834 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term222 A ZRECSPACE' ZRECSPACE'' a.
Proof. exact (@lem1058713 A ZRECSPACE' ZRECSPACE'' h1 a). Qed.
Lemma lem1058835 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (a : type1597 A) : (term222 A ZRECSPACE' ZRECSPACE'' a) = (term79 A ZRECSPACE' ZRECSPACE'' a).
Proof. exact (eq_refl (term222 A ZRECSPACE' ZRECSPACE'' a)). Qed.
Lemma lem1058836 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term79 A ZRECSPACE' ZRECSPACE'' a.
Proof. exact (EQ_MP (@lem1058835 A ZRECSPACE' ZRECSPACE'' a) (@lem1058834 A a ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058837 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (a : type1597 A) : (term79 A ZRECSPACE' ZRECSPACE'' a) = ((term79 A ZRECSPACE' ZRECSPACE'' a) = True).
Proof. exact (@lem7 (term79 A ZRECSPACE' ZRECSPACE'' a)). Qed.
Lemma lem1058844 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : (term79 A ZRECSPACE' ZRECSPACE'' a) = True.
Proof. exact (EQ_MP (@lem1058837 A ZRECSPACE' ZRECSPACE'' a) (@lem1058836 A a ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058845 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : (term79 A ZRECSPACE' ZRECSPACE'' a) = True.
Proof. exact (@lem1058844 A a ZRECSPACE' ZRECSPACE'' h1). Qed.
Lemma lem1058846 {A : Type'} (r : type1600 A) (n : nat) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : (term208 A ZRECSPACE' ZRECSPACE'' r n) = True.
Proof. exact (@lem1058845 A (r n) ZRECSPACE' ZRECSPACE'' h1). Qed.
Lemma lem1058847 {A : Type'} (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : (term210 A ZRECSPACE' ZRECSPACE'' r) = term223.
Proof. exact (fun_ext (fun n : nat => @lem1058846 A r n ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1058849 {A : Type'} (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : (term212 A ZRECSPACE' ZRECSPACE'' r) = term224.
Proof. exact (MK_COMB (@lem1058848) (@lem1058847 A r ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058851 {A : Type'} (t : Prop) : (term225 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1058852 (t : Prop) : (term226 t) = t.
Proof. exact (@lem1058851 nat t). Qed.
Lemma lem1058853 : term224 = True.
Proof. exact (@lem1058852 True). Qed.
Lemma lem1058854 {A : Type'} (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : (term212 A ZRECSPACE' ZRECSPACE'' r) = True.
Proof. exact (TRANS (@lem1058849 A r ZRECSPACE' ZRECSPACE'' h1) (@lem1058853)). Qed.
Lemma lem1058855 {A : Type'} (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : True = (term212 A ZRECSPACE' ZRECSPACE'' r).
Proof. exact (SYM (@lem1058854 A r ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058856 {A : Type'} (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term212 A ZRECSPACE' ZRECSPACE'' r.
Proof. exact (EQ_MP (@lem1058855 A r ZRECSPACE' ZRECSPACE'' h1) (@lem0)). Qed.
Lemma lem1058858 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (r : type1600 A) : term221 A ZRECSPACE' ZRECSPACE'' r.
Proof. exact (EQ_MP (@lem1058832 A ZRECSPACE' ZRECSPACE'' r) (@lem1058810 A ZRECSPACE' ZRECSPACE'' r)). Qed.
Lemma lem1058859 {A : Type'} (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term220 A ZRECSPACE' ZRECSPACE'' r.
Proof. exact (@lem1058858 A ZRECSPACE' ZRECSPACE'' r (@lem1058856 A r ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058860 {A : Type'} (a : type1597 A) (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term227 A a c i ZRECSPACE' ZRECSPACE'' r.
Proof. exact (conj (@lem1058806 A a c i r) (@lem1058859 A r ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058862 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) (r : type1600 A) : term228 A ZRECSPACE' a c i ZRECSPACE'' r.
Proof. exact (@lem1058802 (a = (@ZCONSTR A c i r)) (term12 A ZRECSPACE' r) (a = (@ZCONSTR A c i r)) (term12 A ZRECSPACE'' r)). Qed.
Lemma lem1058863 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) (r : type1600 A) : term228 A ZRECSPACE' a c i ZRECSPACE'' r.
Proof. exact (@lem1058862 A ZRECSPACE' a c i ZRECSPACE'' r). Qed.
Lemma lem1058864 {A : Type'} (a : type1597 A) (c : nat) (i : A) (r : type1600 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term184 A ZRECSPACE' a c i ZRECSPACE'' r.
Proof. exact (@lem1058863 A ZRECSPACE' a c i ZRECSPACE'' r (@lem1058860 A a c i r ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058869 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term188 A ZRECSPACE' a c i ZRECSPACE''.
Proof. exact (fun r : type1600 A => @lem1058864 A a c i r ZRECSPACE' ZRECSPACE'' h1). Qed.
Lemma lem1058871 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : term195 A ZRECSPACE' a c i ZRECSPACE''.
Proof. exact (EQ_MP (@lem1058799 A ZRECSPACE' a c i ZRECSPACE'') (@lem1058777 A ZRECSPACE' a c i ZRECSPACE'')). Qed.
Lemma lem1058872 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (i : A) (ZRECSPACE'' : type953 A) : term195 A ZRECSPACE' a c i ZRECSPACE''.
Proof. exact (@lem1058871 A ZRECSPACE' a c i ZRECSPACE''). Qed.
Lemma lem1058873 {A : Type'} (a : type1597 A) (c : nat) (i : A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term166 A ZRECSPACE' a c i ZRECSPACE''.
Proof. exact (@lem1058872 A ZRECSPACE' a c i ZRECSPACE'' (@lem1058869 A a c i ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058878 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term170 A ZRECSPACE' a c ZRECSPACE''.
Proof. exact (fun i : A => @lem1058873 A a c i ZRECSPACE' ZRECSPACE'' h1). Qed.
Lemma lem1058880 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : term177 A ZRECSPACE' a c ZRECSPACE''.
Proof. exact (EQ_MP (@lem1058772 A ZRECSPACE' a c ZRECSPACE'') (@lem1058750 A ZRECSPACE' a c ZRECSPACE'')). Qed.
Lemma lem1058881 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (c : nat) (ZRECSPACE'' : type953 A) : term177 A ZRECSPACE' a c ZRECSPACE''.
Proof. exact (@lem1058880 A ZRECSPACE' a c ZRECSPACE''). Qed.
Lemma lem1058882 {A : Type'} (a : type1597 A) (c : nat) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term147 A ZRECSPACE' a c ZRECSPACE''.
Proof. exact (@lem1058881 A ZRECSPACE' a c ZRECSPACE'' (@lem1058878 A a c ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058887 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term151 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (fun c : nat => @lem1058882 A a c ZRECSPACE' ZRECSPACE'' h1). Qed.
Lemma lem1058889 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : term160 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (EQ_MP (@lem1058745 A ZRECSPACE' a ZRECSPACE'') (@lem1058723 A ZRECSPACE' a ZRECSPACE'')). Qed.
Lemma lem1058890 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : term160 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (@lem1058889 A ZRECSPACE' a ZRECSPACE''). Qed.
Lemma lem1058891 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term159 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (@lem1058890 A ZRECSPACE' a ZRECSPACE'' (@lem1058887 A a ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058892 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term229 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (conj (@lem1058719 A a) (@lem1058891 A a ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058894 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : term230 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (@lem1058715 (a = (@ZBOT A)) (term46 A a ZRECSPACE') (a = (@ZBOT A)) (term46 A a ZRECSPACE'')). Qed.
Lemma lem1058895 {A : Type'} (ZRECSPACE' : type953 A) (a : type1597 A) (ZRECSPACE'' : type953 A) : term230 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (@lem1058894 A ZRECSPACE' a ZRECSPACE''). Qed.
Lemma lem1058896 {A : Type'} (a : type1597 A) (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term91 A ZRECSPACE' a ZRECSPACE''.
Proof. exact (@lem1058895 A ZRECSPACE' a ZRECSPACE'' (@lem1058892 A a ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058901 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term89 A ZRECSPACE' ZRECSPACE''.
Proof. exact (fun a : type1597 A => @lem1058896 A a ZRECSPACE' ZRECSPACE'' h1). Qed.
Lemma lem1058902 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : (term80 A ZRECSPACE' ZRECSPACE'') = (term89 A ZRECSPACE' ZRECSPACE'').
Proof. exact (prop_ext (fun h2 : term80 A ZRECSPACE' ZRECSPACE'' => @lem1058901 A ZRECSPACE' ZRECSPACE'' h1) (fun h2 : term89 A ZRECSPACE' ZRECSPACE'' => @lem1058713 A ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058903 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) (h1 : term80 A ZRECSPACE' ZRECSPACE'') : term89 A ZRECSPACE' ZRECSPACE''.
Proof. exact (EQ_MP (@lem1058902 A ZRECSPACE' ZRECSPACE'' h1) (@lem1058713 A ZRECSPACE' ZRECSPACE'' h1)). Qed.
Lemma lem1058904 {A : Type'} (ZRECSPACE' : type953 A) (ZRECSPACE'' : type953 A) : term88 A ZRECSPACE' ZRECSPACE''.
Proof. exact (fun h0 : term80 A ZRECSPACE' ZRECSPACE'' => @lem1058903 A ZRECSPACE' ZRECSPACE'' h0). Qed.
Lemma lem1058909 {A : Type'} (ZRECSPACE' : type953 A) : term86 A ZRECSPACE'.
Proof. exact (fun ZRECSPACE'' : type953 A => @lem1058904 A ZRECSPACE' ZRECSPACE''). Qed.
Lemma lem1058914 {A : Type'} : term83 A.
Proof. exact (fun ZRECSPACE' : type953 A => @lem1058909 A ZRECSPACE'). Qed.
Lemma lem1058915 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : (term83 A) = (term134 A ZRECSPACE').
Proof. exact (prop_ext (fun h2 : term83 A => @lem1058712 A ZRECSPACE' h2 h1) (fun h2 : term134 A ZRECSPACE' => @lem1058914 A)). Qed.
Lemma lem1058916 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term134 A ZRECSPACE'.
Proof. exact (EQ_MP (@lem1058915 A ZRECSPACE' h1) (@lem1058914 A)). Qed.
Lemma lem1058917 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : ZRECSPACE' = (term70 A).
Proof. exact (h1). Qed.
Lemma lem1058918 {A : Type'} (ZRECSPACE' : type953 A) : term231 A ZRECSPACE'.
Proof. exact (fun h0 : ZRECSPACE' = (term70 A) => @lem1058916 A ZRECSPACE' h0). Qed.
Lemma lem1058919 {A : Type'} (ZRECSPACE' : type953 A) : term231 A ZRECSPACE'.
Proof. exact (@lem1058918 A ZRECSPACE'). Qed.
Lemma lem1058920 {A : Type'} (ZRECSPACE' : type953 A) (h1 : ZRECSPACE' = (term70 A)) : term134 A ZRECSPACE'.
Proof. exact (@lem1058919 A ZRECSPACE' (@lem1058917 A ZRECSPACE' h1)). Qed.
Lemma lem1058921 {A : Type'} : (@ZRECSPACE A) = (term70 A).
Proof. exact (@ZRECSPACE_def A). Qed.
Lemma lem1058922 {A : Type'} (ZRECSPACE' : type953 A) : term231 A ZRECSPACE'.
Proof. exact (fun h0 : ZRECSPACE' = (term70 A) => @lem1058920 A ZRECSPACE' h0). Qed.
Lemma lem1058923 {A : Type'} : term232 A.
Proof. exact (@lem1058922 A (@ZRECSPACE A)). Qed.
Lemma lem1058924 {A : Type'} : term233 A.
Proof. exact (@lem1058923 A (@lem1058921 A)). Qed.
