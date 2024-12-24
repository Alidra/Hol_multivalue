Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_GCD_term_abbrevs.
Require Import NUM_OF_INT_spec.
Require Import num_gcd_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm2801880_spec.
Require Import thm7_spec.
Lemma lem3070362 (x : int) (h1 : (term0 x) = ((term1 x) = x)) : (term0 x) = ((term1 x) = x).
Proof. exact (h1). Qed.
Lemma lem3070363 (x : int) (h1 : (term0 x) = ((term1 x) = x)) : ((term1 x) = x) = (term0 x).
Proof. exact (SYM (@lem3070362 x h1)). Qed.
Lemma lem3070364 (x : int) (h1 : ((term1 x) = x) = (term0 x)) : ((term1 x) = x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem3070365 (x : int) (h1 : ((term1 x) = x) = (term0 x)) : (term0 x) = ((term1 x) = x).
Proof. exact (SYM (@lem3070364 x h1)). Qed.
Lemma lem3070366 (x : int) : ((term0 x) = ((term1 x) = x)) = (((term1 x) = x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = ((term1 x) = x) => @lem3070363 x h1) (fun h1 : ((term1 x) = x) = (term0 x) => @lem3070365 x h1)). Qed.
Lemma lem3070367 : term2 = term3.
Proof. exact (fun_ext (fun x : int => @lem3070366 x)). Qed.
Lemma lem3070368 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3070369 : term4 = term5.
Proof. exact (MK_COMB (@lem3070368) (@lem3070367)). Qed.
Lemma lem3070370 : term5.
Proof. exact (EQ_MP (@lem3070369) (@lem2835223)). Qed.
Lemma lem3070371 (a : int) : term6 a.
Proof. exact (@lem2801880 a). Qed.
Lemma lem3070372 (a : int) : (term6 a) = (term7 a).
Proof. exact (eq_refl (term6 a)). Qed.
Lemma lem3070373 (a : int) : term7 a.
Proof. exact (EQ_MP (@lem3070372 a) (@lem3070371 a)). Qed.
Lemma lem3070374 (a : int) (b : int) : term8 a b.
Proof. exact (@lem3070373 a b). Qed.
Lemma lem3070375 (a : int) (b : int) : (term8 a b) = (term9 a b).
Proof. exact (eq_refl (term8 a b)). Qed.
Lemma lem3070376 (a : int) (b : int) : term9 a b.
Proof. exact (EQ_MP (@lem3070375 a b) (@lem3070374 a b)). Qed.
Lemma lem3070388 (a : int) (b : int) : term10 a b.
Proof. exact (proj1 (@lem3070376 a b)). Qed.
Lemma lem3070389 (a : int) (b : int) : (term10 a b) = ((term10 a b) = True).
Proof. exact (@lem7 (term10 a b)). Qed.
Lemma lem3070391 (x : int) : term11 x.
Proof. exact (@lem3070370 x). Qed.
Lemma lem3070392 (x : int) : (term11 x) = (((term1 x) = x) = (term0 x)).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem3070394 (a : nat) : term12 a.
Proof. exact (@lem2839311 a). Qed.
Lemma lem3070395 (a : nat) : (term12 a) = (term13 a).
Proof. exact (eq_refl (term12 a)). Qed.
Lemma lem3070396 (a : nat) : term13 a.
Proof. exact (EQ_MP (@lem3070395 a) (@lem3070394 a)). Qed.
Lemma lem3070397 (a : nat) (b : nat) : term14 a b.
Proof. exact (@lem3070396 a b). Qed.
Lemma lem3070398 (a : nat) (b : nat) : (term14 a b) = ((term15 a b) = (term16 a b)).
Proof. exact (eq_refl (term14 a b)). Qed.
Lemma lem3070411 (a : nat) (b : nat) : (term15 a b) = (term16 a b).
Proof. exact (EQ_MP (@lem3070398 a b) (@lem3070397 a b)). Qed.
Lemma lem3070412 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem3070413 (a : nat) (b : nat) : (term17 a b) = (term18 a b).
Proof. exact (MK_COMB (@lem3070412) (@lem3070411 a b)). Qed.
Lemma lem3070414 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3070415 (a : nat) (b : nat) : (term19 a b) = (term20 a b).
Proof. exact (MK_COMB (@lem3070414) (@lem3070413 a b)). Qed.
Lemma lem3070416 (a : nat) (b : nat) : (term21 a b) = (term21 a b).
Proof. exact (eq_refl (term21 a b)). Qed.
Lemma lem3070417 (a : nat) (b : nat) : ((term17 a b) = (term21 a b)) = ((term18 a b) = (term21 a b)).
Proof. exact (MK_COMB (@lem3070415 a b) (@lem3070416 a b)). Qed.
Lemma lem3070419 (x : int) : ((term1 x) = x) = (term0 x).
Proof. exact (EQ_MP (@lem3070392 x) (@lem3070391 x)). Qed.
Lemma lem3070420 (a : nat) (b : nat) : ((term18 a b) = (term21 a b)) = (term22 a b).
Proof. exact (@lem3070419 (term21 a b)). Qed.
Lemma lem3070422 (a : int) (b : int) : (term10 a b) = True.
Proof. exact (EQ_MP (@lem3070389 a b) (@lem3070388 a b)). Qed.
Lemma lem3070423 (a : nat) (b : nat) : (term22 a b) = True.
Proof. exact (@lem3070422 (int_of_num a) (int_of_num b)). Qed.
Lemma lem3070424 (a : nat) (b : nat) : ((term18 a b) = (term21 a b)) = True.
Proof. exact (TRANS (@lem3070420 a b) (@lem3070423 a b)). Qed.
Lemma lem3070425 (a : nat) (b : nat) : ((term17 a b) = (term21 a b)) = True.
Proof. exact (TRANS (@lem3070417 a b) (@lem3070424 a b)). Qed.
Lemma lem3070426 (a : nat) : (term23 a) = term24.
Proof. exact (fun_ext (fun b : nat => @lem3070425 a b)). Qed.
Lemma lem3070427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070428 (a : nat) : (term25 a) = term26.
Proof. exact (MK_COMB (@lem3070427) (@lem3070426 a)). Qed.
Lemma lem3070430 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070431 (t : Prop) : (term28 t) = t.
Proof. exact (@lem3070430 nat t). Qed.
Lemma lem3070432 : term26 = True.
Proof. exact (@lem3070431 True). Qed.
Lemma lem3070433 (a : nat) : (term25 a) = True.
Proof. exact (TRANS (@lem3070428 a) (@lem3070432)). Qed.
Lemma lem3070434 : term29 = term24.
Proof. exact (fun_ext (fun a : nat => @lem3070433 a)). Qed.
Lemma lem3070435 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070436 : term30 = term26.
Proof. exact (MK_COMB (@lem3070435) (@lem3070434)). Qed.
Lemma lem3070438 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070439 (t : Prop) : (term28 t) = t.
Proof. exact (@lem3070438 nat t). Qed.
Lemma lem3070440 : term26 = True.
Proof. exact (@lem3070439 True). Qed.
Lemma lem3070441 : term30 = True.
Proof. exact (TRANS (@lem3070436) (@lem3070440)). Qed.
Lemma lem3070442 : True = term30.
Proof. exact (SYM (@lem3070441)). Qed.
Lemma lem3070443 : term30.
Proof. exact (EQ_MP (@lem3070442) (@lem0)). Qed.
