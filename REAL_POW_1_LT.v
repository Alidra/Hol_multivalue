Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_1_LT_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_POW_LT2_spec.
Require Import REAL_POW_ONE_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1638436 (n : nat) : term0 n.
Proof. exact (@lem1638321 n). Qed.
Lemma lem1638437 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1638438 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1638437 n) (@lem1638436 n)). Qed.
Lemma lem1638439 (n : nat) (x : real) : term2 n x.
Proof. exact (@lem1638438 n x). Qed.
Lemma lem1638440 (x : real) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem1638441 (x : real) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem1638440 x n) (@lem1638439 n x)). Qed.
Lemma lem1638442 (x : real) (n : nat) : term4 x n.
Proof. exact (@lem1638441 x n term5). Qed.
Lemma lem1638443 (x : real) (n : nat) : (term4 x n) = (term6 x n).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem1638444 (x : real) (n : nat) : term6 x n.
Proof. exact (EQ_MP (@lem1638443 x n) (@lem1638442 x n)). Qed.
Lemma lem1638445 (n : nat) (x : real) (h1 : term7 n x) : term7 n x.
Proof. exact (h1). Qed.
Lemma lem1638446 (x : real) (h1 : term8 x) : term8 x.
Proof. exact (h1). Qed.
Lemma lem1638447 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem1638448 (x : real) (h1 : term10 x) : term10 x.
Proof. exact (h1). Qed.
Lemma lem1638449 (x : real) (h1 : term11 x) : term11 x.
Proof. exact (h1). Qed.
Lemma lem1638450 (n : nat) : term12 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem1638451 (n : nat) : (term12 n) = ((term13 n) = term5).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1638453 (n : nat) : term14 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1638466 (x : real) : (term11 x) = ((term11 x) = True).
Proof. exact (@lem7 (term11 x)). Qed.
Lemma lem1638468 (x : real) : (term10 x) = ((term10 x) = True).
Proof. exact (@lem7 (term10 x)). Qed.
Lemma lem1638477 (n : nat) (h1 : term9 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1638453 n (@lem1638447 n h1)). Qed.
Lemma lem1638478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1638479 (n : nat) (h1 : term9 n) : (term9 n) = (~ False).
Proof. exact (MK_COMB (@lem1638478) (@lem1638477 n h1)). Qed.
Lemma lem1638481 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1638482 (n : nat) (h1 : term9 n) : (term9 n) = True.
Proof. exact (TRANS (@lem1638479 n h1) (@lem1638481)). Qed.
Lemma lem1638483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638484 (n : nat) (h1 : term9 n) : (term15 n) = (and True).
Proof. exact (MK_COMB (@lem1638483) (@lem1638482 n h1)). Qed.
Lemma lem1638488 (x : real) (h1 : term11 x) : (term11 x) = True.
Proof. exact (EQ_MP (@lem1638466 x) (@lem1638449 x h1)). Qed.
Lemma lem1638489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1638490 (x : real) (h1 : term11 x) : (term16 x) = (and True).
Proof. exact (MK_COMB (@lem1638489) (@lem1638488 x h1)). Qed.
Lemma lem1638492 (x : real) (h1 : term10 x) : (term10 x) = True.
Proof. exact (EQ_MP (@lem1638468 x) (@lem1638448 x h1)). Qed.
Lemma lem1638493 (x : real) (h1 : term11 x) (h2 : term10 x) : (term8 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1638490 x h1) (@lem1638492 x h2)). Qed.
Lemma lem1638495 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638496 : (True /\ True) = True.
Proof. exact (@lem1638495 True). Qed.
Lemma lem1638497 (x : real) (h1 : term11 x) (h2 : term10 x) : (term8 x) = True.
Proof. exact (TRANS (@lem1638493 x h1 h2) (@lem1638496)). Qed.
Lemma lem1638498 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term7 n x) = (True /\ True).
Proof. exact (MK_COMB (@lem1638484 n h1) (@lem1638497 x h2 h3)). Qed.
Lemma lem1638500 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1638501 : (True /\ True) = True.
Proof. exact (@lem1638500 True). Qed.
Lemma lem1638502 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term7 n x) = True.
Proof. exact (TRANS (@lem1638498 n x h1 h2 h3) (@lem1638501)). Qed.
Lemma lem1638503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1638504 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term17 n x) = (imp True).
Proof. exact (MK_COMB (@lem1638503) (@lem1638502 n x h1 h2 h3)). Qed.
Lemma lem1638506 (n : nat) : (term13 n) = term5.
Proof. exact (EQ_MP (@lem1638451 n) (@lem1638450 n)). Qed.
Lemma lem1638507 (x : real) (n : nat) : (term18 x n) = (term18 x n).
Proof. exact (eq_refl (term18 x n)). Qed.
Lemma lem1638508 (x : real) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (MK_COMB (@lem1638507 x n) (@lem1638506 n)). Qed.
Lemma lem1638509 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term6 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem1638504 n x h1 h2 h3) (@lem1638508 x n)). Qed.
Lemma lem1638511 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1638512 (x : real) (n : nat) : (term21 x n) = (term20 x n).
Proof. exact (@lem1638511 (term20 x n)). Qed.
Lemma lem1638513 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term6 x n) = (term20 x n).
Proof. exact (TRANS (@lem1638509 n x h1 h2 h3) (@lem1638512 x n)). Qed.
Lemma lem1638514 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1638515 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term22 x n) = (term23 x n).
Proof. exact (MK_COMB (@lem1638514) (@lem1638513 n x h1 h2 h3)). Qed.
Lemma lem1638516 (x : real) (n : nat) : (term20 x n) = (term20 x n).
Proof. exact (eq_refl (term20 x n)). Qed.
Lemma lem1638517 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term24 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem1638515 n x h1 h2 h3) (@lem1638516 x n)). Qed.
Lemma lem1638519 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1638520 (x : real) (n : nat) : (term25 x n) = True.
Proof. exact (@lem1638519 (term20 x n)). Qed.
Lemma lem1638521 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term24 x n) = True.
Proof. exact (TRANS (@lem1638517 n x h1 h2 h3) (@lem1638520 x n)). Qed.
Lemma lem1638522 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : True = (term24 x n).
Proof. exact (SYM (@lem1638521 n x h1 h2 h3)). Qed.
Lemma lem1638523 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : term24 x n.
Proof. exact (EQ_MP (@lem1638522 n x h1 h2 h3) (@lem0)). Qed.
Lemma lem1638524 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : term20 x n.
Proof. exact (@lem1638523 n x h1 h2 h3 (@lem1638444 x n)). Qed.
Lemma lem1638525 (n : nat) (x : real) (h1 : term7 n x) : term8 x.
Proof. exact (proj2 (@lem1638445 n x h1)). Qed.
Lemma lem1638526 (n : nat) (x : real) (h1 : term7 n x) : term9 n.
Proof. exact (proj1 (@lem1638445 n x h1)). Qed.
Lemma lem1638527 (x : real) (h1 : term8 x) : term10 x.
Proof. exact (proj2 (@lem1638446 x h1)). Qed.
Lemma lem1638528 (x : real) (h1 : term8 x) : term11 x.
Proof. exact (proj1 (@lem1638446 x h1)). Qed.
Lemma lem1638529 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term10 x) = (term20 x n).
Proof. exact (prop_ext (fun h4 : term10 x => @lem1638524 n x h1 h2 h3) (fun h4 : term20 x n => @lem1638448 x h3)). Qed.
Lemma lem1638530 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : term20 x n.
Proof. exact (EQ_MP (@lem1638529 n x h1 h2 h3) (@lem1638448 x h3)). Qed.
Lemma lem1638531 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : (term11 x) = (term20 x n).
Proof. exact (prop_ext (fun h4 : term11 x => @lem1638530 n x h1 h2 h3) (fun h4 : term20 x n => @lem1638449 x h2)). Qed.
Lemma lem1638532 (n : nat) (x : real) (h1 : term9 n) (h2 : term11 x) (h3 : term10 x) : term20 x n.
Proof. exact (EQ_MP (@lem1638531 n x h1 h2 h3) (@lem1638449 x h2)). Qed.
Lemma lem1638533 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) (h3 : term11 x) : (term10 x) = (term20 x n).
Proof. exact (prop_ext (fun h4 : term10 x => @lem1638532 n x h1 h3 h4) (fun h4 : term20 x n => @lem1638527 x h2)). Qed.
Lemma lem1638534 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) (h3 : term11 x) : term20 x n.
Proof. exact (EQ_MP (@lem1638533 n x h1 h2 h3) (@lem1638527 x h2)). Qed.
Lemma lem1638535 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term11 x) = (term20 x n).
Proof. exact (prop_ext (fun h3 : term11 x => @lem1638534 n x h1 h2 h3) (fun h3 : term20 x n => @lem1638528 x h2)). Qed.
Lemma lem1638536 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : term20 x n.
Proof. exact (EQ_MP (@lem1638535 n x h1 h2) (@lem1638528 x h2)). Qed.
Lemma lem1638537 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : (term9 n) = (term20 x n).
Proof. exact (prop_ext (fun h3 : term9 n => @lem1638536 n x h1 h2) (fun h3 : term20 x n => @lem1638447 n h1)). Qed.
Lemma lem1638538 (n : nat) (x : real) (h1 : term9 n) (h2 : term8 x) : term20 x n.
Proof. exact (EQ_MP (@lem1638537 n x h1 h2) (@lem1638447 n h1)). Qed.
Lemma lem1638539 (n : nat) (x : real) (h1 : term9 n) (h2 : term7 n x) : (term8 x) = (term20 x n).
Proof. exact (prop_ext (fun h3 : term8 x => @lem1638538 n x h1 h3) (fun h3 : term20 x n => @lem1638525 n x h2)). Qed.
Lemma lem1638540 (n : nat) (x : real) (h1 : term9 n) (h2 : term7 n x) : term20 x n.
Proof. exact (EQ_MP (@lem1638539 n x h1 h2) (@lem1638525 n x h2)). Qed.
Lemma lem1638541 (n : nat) (x : real) (h1 : term7 n x) : (term9 n) = (term20 x n).
Proof. exact (prop_ext (fun h2 : term9 n => @lem1638540 n x h2 h1) (fun h2 : term20 x n => @lem1638526 n x h1)). Qed.
Lemma lem1638542 (n : nat) (x : real) (h1 : term7 n x) : term20 x n.
Proof. exact (EQ_MP (@lem1638541 n x h1) (@lem1638526 n x h1)). Qed.
Lemma lem1638543 (x : real) (n : nat) : term26 x n.
Proof. exact (fun h0 : term7 n x => @lem1638542 n x h0). Qed.
Lemma lem1638548 (n : nat) : term27 n.
Proof. exact (fun x : real => @lem1638543 x n). Qed.
Lemma lem1638553 : term28.
Proof. exact (fun n : nat => @lem1638548 n). Qed.
