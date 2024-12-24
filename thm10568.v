Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm10568_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem10460 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem10461 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem10462 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem10461 a) (@lem10460 a)). Qed.
Lemma lem10463 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem10464 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem10473 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem10474 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem10473 b) (@lem10463 a h1)). Qed.
Lemma lem10475 (b : Prop) : (term4 b) = ((True -> b) = (term5 b)).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem10476 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem10477 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = ((True -> b) = (term5 b))).
Proof. exact (MK_COMB (@lem10476 b a) (@lem10475 b)). Qed.
Lemma lem10478 (b : Prop) (a : Prop) : (term3 b a) = ((a -> b) = (term7 b a)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem10479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10480 (b : Prop) (a : Prop) : (term6 b a) = (term8 b a).
Proof. exact (MK_COMB (@lem10479) (@lem10478 b a)). Qed.
Lemma lem10481 (b : Prop) : ((True -> b) = (term5 b)) = ((True -> b) = (term5 b)).
Proof. exact (eq_refl ((True -> b) = (term5 b))). Qed.
Lemma lem10482 (a : Prop) (b : Prop) : ((term3 b a) = ((True -> b) = (term5 b))) = (((a -> b) = (term7 b a)) = ((True -> b) = (term5 b))).
Proof. exact (MK_COMB (@lem10480 b a) (@lem10481 b)). Qed.
Lemma lem10483 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = (((a -> b) = (term7 b a)) = ((True -> b) = (term5 b))).
Proof. exact (TRANS (@lem10477 a b) (@lem10482 a b)). Qed.
Lemma lem10484 (b : Prop) (a : Prop) (h1 : a = True) : ((a -> b) = (term7 b a)) = ((True -> b) = (term5 b)).
Proof. exact (EQ_MP (@lem10483 a b) (@lem10474 b a h1)). Qed.
Lemma lem10485 (b : Prop) (a : Prop) (h1 : a = True) : ((True -> b) = (term5 b)) = ((a -> b) = (term7 b a)).
Proof. exact (SYM (@lem10484 b a h1)). Qed.
Lemma lem10486 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem10487 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem10486 b) (@lem10464 a h1)). Qed.
Lemma lem10488 (b : Prop) : (term9 b) = ((False -> b) = (term10 b)).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem10489 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem10490 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = ((False -> b) = (term10 b))).
Proof. exact (MK_COMB (@lem10489 b a) (@lem10488 b)). Qed.
Lemma lem10491 (b : Prop) (a : Prop) : (term3 b a) = ((a -> b) = (term7 b a)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem10492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10493 (b : Prop) (a : Prop) : (term6 b a) = (term8 b a).
Proof. exact (MK_COMB (@lem10492) (@lem10491 b a)). Qed.
Lemma lem10494 (b : Prop) : ((False -> b) = (term10 b)) = ((False -> b) = (term10 b)).
Proof. exact (eq_refl ((False -> b) = (term10 b))). Qed.
Lemma lem10495 (a : Prop) (b : Prop) : ((term3 b a) = ((False -> b) = (term10 b))) = (((a -> b) = (term7 b a)) = ((False -> b) = (term10 b))).
Proof. exact (MK_COMB (@lem10493 b a) (@lem10494 b)). Qed.
Lemma lem10496 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = (((a -> b) = (term7 b a)) = ((False -> b) = (term10 b))).
Proof. exact (TRANS (@lem10490 a b) (@lem10495 a b)). Qed.
Lemma lem10497 (b : Prop) (a : Prop) (h1 : a = False) : ((a -> b) = (term7 b a)) = ((False -> b) = (term10 b)).
Proof. exact (EQ_MP (@lem10496 a b) (@lem10487 b a h1)). Qed.
Lemma lem10498 (b : Prop) (a : Prop) (h1 : a = False) : ((False -> b) = (term10 b)) = ((a -> b) = (term7 b a)).
Proof. exact (SYM (@lem10497 b a h1)). Qed.
Lemma lem10502 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem10503 (b : Prop) : (True -> b) = b.
Proof. exact (@lem10502 b). Qed.
Lemma lem10504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10505 (b : Prop) : (term11 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem10504) (@lem10503 b)). Qed.
Lemma lem10509 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10510 (b : Prop) : (term12 b) = (term12 b).
Proof. exact (eq_refl (term12 b)). Qed.
Lemma lem10511 (b : Prop) : (term5 b) = (term13 b).
Proof. exact (MK_COMB (@lem10510 b) (@lem10509)). Qed.
Lemma lem10513 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem10514 (b : Prop) : (term13 b) = (term14 b).
Proof. exact (@lem10513 (~ b)). Qed.
Lemma lem10515 (b : Prop) : (term5 b) = (term14 b).
Proof. exact (TRANS (@lem10511 b) (@lem10514 b)). Qed.
Lemma lem10516 (b : Prop) : ((True -> b) = (term5 b)) = (b = (term14 b)).
Proof. exact (MK_COMB (@lem10505 b) (@lem10515 b)). Qed.
Lemma lem10519 (b : Prop) : (b = (term14 b)) = ((True -> b) = (term5 b)).
Proof. exact (SYM (@lem10516 b)). Qed.
Lemma lem10528 (t : Prop) : (term14 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem10529 (b : Prop) : (term14 b) = b.
Proof. exact (@lem10528 b). Qed.
Lemma lem10530 (b : Prop) : (@eq Prop b) = (@eq Prop b).
Proof. exact (eq_refl (@eq Prop b)). Qed.
Lemma lem10531 (b : Prop) : (b = (term14 b)) = (b = b).
Proof. exact (MK_COMB (@lem10530 b) (@lem10529 b)). Qed.
Lemma lem10533 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10534 (x : Prop) : (x = x) = True.
Proof. exact (@lem10533 Prop x). Qed.
Lemma lem10535 (b : Prop) : (b = b) = True.
Proof. exact (@lem10534 b). Qed.
Lemma lem10536 (b : Prop) : (b = (term14 b)) = True.
Proof. exact (TRANS (@lem10531 b) (@lem10535 b)). Qed.
Lemma lem10537 (b : Prop) : True = (b = (term14 b)).
Proof. exact (SYM (@lem10536 b)). Qed.
Lemma lem10538 (b : Prop) : b = (term14 b).
Proof. exact (EQ_MP (@lem10537 b) (@lem0)). Qed.
Lemma lem10539 (b : Prop) : (True -> b) = (term5 b).
Proof. exact (EQ_MP (@lem10519 b) (@lem10538 b)). Qed.
Lemma lem10543 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem10544 (b : Prop) : (False -> b) = True.
Proof. exact (@lem10543 b). Qed.
Lemma lem10545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10546 (b : Prop) : (term15 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem10545) (@lem10544 b)). Qed.
Lemma lem10550 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10551 (b : Prop) : (term12 b) = (term12 b).
Proof. exact (eq_refl (term12 b)). Qed.
Lemma lem10552 (b : Prop) : (term10 b) = (term16 b).
Proof. exact (MK_COMB (@lem10551 b) (@lem10550)). Qed.
Lemma lem10554 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem10555 (b : Prop) : (term16 b) = True.
Proof. exact (@lem10554 (~ b)). Qed.
Lemma lem10556 (b : Prop) : (term10 b) = True.
Proof. exact (TRANS (@lem10552 b) (@lem10555 b)). Qed.
Lemma lem10557 (b : Prop) : ((False -> b) = (term10 b)) = (True = True).
Proof. exact (MK_COMB (@lem10546 b) (@lem10556 b)). Qed.
Lemma lem10559 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem10560 : (True = True) = True.
Proof. exact (@lem10559 True). Qed.
Lemma lem10561 (b : Prop) : ((False -> b) = (term10 b)) = True.
Proof. exact (TRANS (@lem10557 b) (@lem10560)). Qed.
Lemma lem10562 (b : Prop) : True = ((False -> b) = (term10 b)).
Proof. exact (SYM (@lem10561 b)). Qed.
Lemma lem10563 (b : Prop) : (False -> b) = (term10 b).
Proof. exact (EQ_MP (@lem10562 b) (@lem0)). Qed.
Lemma lem10564 (b : Prop) (a : Prop) (h1 : a = False) : (a -> b) = (term7 b a).
Proof. exact (EQ_MP (@lem10498 b a h1) (@lem10563 b)). Qed.
Lemma lem10565 (b : Prop) (a : Prop) (h1 : a = True) : (a -> b) = (term7 b a).
Proof. exact (EQ_MP (@lem10485 b a h1) (@lem10539 b)). Qed.
Lemma lem10568 (b : Prop) (a : Prop) : (a -> b) = (term7 b a).
Proof. exact (or_elim (@lem10462 a) (fun h0 : a = True => @lem10565 b a h0) (fun h0 : a = False => @lem10564 b a h0)). Qed.
