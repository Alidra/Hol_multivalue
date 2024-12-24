Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm22518_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem22412 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem22413 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem22414 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem22413 a) (@lem22412 a)). Qed.
Lemma lem22415 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem22416 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem22425 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem22426 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem22425 b) (@lem22415 a h1)). Qed.
Lemma lem22427 (b : Prop) : (term4 b) = ((True -> b) = (term5 b)).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem22428 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem22429 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = ((True -> b) = (term5 b))).
Proof. exact (MK_COMB (@lem22428 b a) (@lem22427 b)). Qed.
Lemma lem22430 (a : Prop) (b : Prop) : (term3 b a) = ((a -> b) = (term7 a b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem22431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22432 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem22431) (@lem22430 a b)). Qed.
Lemma lem22433 (b : Prop) : ((True -> b) = (term5 b)) = ((True -> b) = (term5 b)).
Proof. exact (eq_refl ((True -> b) = (term5 b))). Qed.
Lemma lem22434 (a : Prop) (b : Prop) : ((term3 b a) = ((True -> b) = (term5 b))) = (((a -> b) = (term7 a b)) = ((True -> b) = (term5 b))).
Proof. exact (MK_COMB (@lem22432 a b) (@lem22433 b)). Qed.
Lemma lem22435 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = (((a -> b) = (term7 a b)) = ((True -> b) = (term5 b))).
Proof. exact (TRANS (@lem22429 a b) (@lem22434 a b)). Qed.
Lemma lem22436 (b : Prop) (a : Prop) (h1 : a = True) : ((a -> b) = (term7 a b)) = ((True -> b) = (term5 b)).
Proof. exact (EQ_MP (@lem22435 a b) (@lem22426 b a h1)). Qed.
Lemma lem22437 (b : Prop) (a : Prop) (h1 : a = True) : ((True -> b) = (term5 b)) = ((a -> b) = (term7 a b)).
Proof. exact (SYM (@lem22436 b a h1)). Qed.
Lemma lem22438 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem22439 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem22438 b) (@lem22416 a h1)). Qed.
Lemma lem22440 (b : Prop) : (term9 b) = ((False -> b) = (term10 b)).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem22441 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem22442 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = ((False -> b) = (term10 b))).
Proof. exact (MK_COMB (@lem22441 b a) (@lem22440 b)). Qed.
Lemma lem22443 (a : Prop) (b : Prop) : (term3 b a) = ((a -> b) = (term7 a b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem22444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22445 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem22444) (@lem22443 a b)). Qed.
Lemma lem22446 (b : Prop) : ((False -> b) = (term10 b)) = ((False -> b) = (term10 b)).
Proof. exact (eq_refl ((False -> b) = (term10 b))). Qed.
Lemma lem22447 (a : Prop) (b : Prop) : ((term3 b a) = ((False -> b) = (term10 b))) = (((a -> b) = (term7 a b)) = ((False -> b) = (term10 b))).
Proof. exact (MK_COMB (@lem22445 a b) (@lem22446 b)). Qed.
Lemma lem22448 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = (((a -> b) = (term7 a b)) = ((False -> b) = (term10 b))).
Proof. exact (TRANS (@lem22442 a b) (@lem22447 a b)). Qed.
Lemma lem22449 (b : Prop) (a : Prop) (h1 : a = False) : ((a -> b) = (term7 a b)) = ((False -> b) = (term10 b)).
Proof. exact (EQ_MP (@lem22448 a b) (@lem22439 b a h1)). Qed.
Lemma lem22450 (b : Prop) (a : Prop) (h1 : a = False) : ((False -> b) = (term10 b)) = ((a -> b) = (term7 a b)).
Proof. exact (SYM (@lem22449 b a h1)). Qed.
Lemma lem22454 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem22455 (b : Prop) : (True -> b) = b.
Proof. exact (@lem22454 b). Qed.
Lemma lem22456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22457 (b : Prop) : (term11 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem22456) (@lem22455 b)). Qed.
Lemma lem22461 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem22462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem22463 : term12 = (or False).
Proof. exact (MK_COMB (@lem22462) (@lem22461)). Qed.
Lemma lem22464 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem22465 (b : Prop) : (term5 b) = (False \/ b).
Proof. exact (MK_COMB (@lem22463) (@lem22464 b)). Qed.
Lemma lem22467 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem22468 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem22467 b). Qed.
Lemma lem22469 (b : Prop) : (term5 b) = b.
Proof. exact (TRANS (@lem22465 b) (@lem22468 b)). Qed.
Lemma lem22470 (b : Prop) : ((True -> b) = (term5 b)) = (b = b).
Proof. exact (MK_COMB (@lem22457 b) (@lem22469 b)). Qed.
Lemma lem22472 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem22473 (x : Prop) : (x = x) = True.
Proof. exact (@lem22472 Prop x). Qed.
Lemma lem22474 (b : Prop) : (b = b) = True.
Proof. exact (@lem22473 b). Qed.
Lemma lem22475 (b : Prop) : ((True -> b) = (term5 b)) = True.
Proof. exact (TRANS (@lem22470 b) (@lem22474 b)). Qed.
Lemma lem22476 (b : Prop) : True = ((True -> b) = (term5 b)).
Proof. exact (SYM (@lem22475 b)). Qed.
Lemma lem22477 (b : Prop) : (True -> b) = (term5 b).
Proof. exact (EQ_MP (@lem22476 b) (@lem0)). Qed.
Lemma lem22481 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem22482 (b : Prop) : (False -> b) = True.
Proof. exact (@lem22481 b). Qed.
Lemma lem22483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22484 (b : Prop) : (term13 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem22483) (@lem22482 b)). Qed.
Lemma lem22488 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem22489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem22490 : term14 = (or True).
Proof. exact (MK_COMB (@lem22489) (@lem22488)). Qed.
Lemma lem22491 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem22492 (b : Prop) : (term10 b) = (True \/ b).
Proof. exact (MK_COMB (@lem22490) (@lem22491 b)). Qed.
Lemma lem22494 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem22495 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem22494 b). Qed.
Lemma lem22496 (b : Prop) : (term10 b) = True.
Proof. exact (TRANS (@lem22492 b) (@lem22495 b)). Qed.
Lemma lem22497 (b : Prop) : ((False -> b) = (term10 b)) = (True = True).
Proof. exact (MK_COMB (@lem22484 b) (@lem22496 b)). Qed.
Lemma lem22499 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem22500 : (True = True) = True.
Proof. exact (@lem22499 True). Qed.
Lemma lem22501 (b : Prop) : ((False -> b) = (term10 b)) = True.
Proof. exact (TRANS (@lem22497 b) (@lem22500)). Qed.
Lemma lem22502 (b : Prop) : True = ((False -> b) = (term10 b)).
Proof. exact (SYM (@lem22501 b)). Qed.
Lemma lem22503 (b : Prop) : (False -> b) = (term10 b).
Proof. exact (EQ_MP (@lem22502 b) (@lem0)). Qed.
Lemma lem22504 (b : Prop) (a : Prop) (h1 : a = False) : (a -> b) = (term7 a b).
Proof. exact (EQ_MP (@lem22450 b a h1) (@lem22503 b)). Qed.
Lemma lem22505 (b : Prop) (a : Prop) (h1 : a = True) : (a -> b) = (term7 a b).
Proof. exact (EQ_MP (@lem22437 b a h1) (@lem22477 b)). Qed.
Lemma lem22508 (a : Prop) (b : Prop) : (a -> b) = (term7 a b).
Proof. exact (or_elim (@lem22414 a) (fun h0 : a = True => @lem22505 b a h0) (fun h0 : a = False => @lem22504 b a h0)). Qed.
Lemma lem22513 (a : Prop) : term15 a.
Proof. exact (fun b : Prop => @lem22508 a b). Qed.
Lemma lem22518 : term16.
Proof. exact (fun a : Prop => @lem22513 a). Qed.
