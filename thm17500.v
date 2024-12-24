Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17500_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem17375 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem17376 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem17377 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem17376 p) (@lem17375 p)). Qed.
Lemma lem17378 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem17379 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem17392 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17393 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem17392 q) (@lem17378 p h1)). Qed.
Lemma lem17394 (q : Prop) : (term4 q) = ((True = q) = (term5 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem17395 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem17396 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((True = q) = (term5 q))).
Proof. exact (MK_COMB (@lem17395 q p) (@lem17394 q)). Qed.
Lemma lem17397 (p : Prop) (q : Prop) : (term3 q p) = ((p = q) = (term7 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17399 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem17398) (@lem17397 p q)). Qed.
Lemma lem17400 (q : Prop) : ((True = q) = (term5 q)) = ((True = q) = (term5 q)).
Proof. exact (eq_refl ((True = q) = (term5 q))). Qed.
Lemma lem17401 (p : Prop) (q : Prop) : ((term3 q p) = ((True = q) = (term5 q))) = (((p = q) = (term7 p q)) = ((True = q) = (term5 q))).
Proof. exact (MK_COMB (@lem17399 p q) (@lem17400 q)). Qed.
Lemma lem17402 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((p = q) = (term7 p q)) = ((True = q) = (term5 q))).
Proof. exact (TRANS (@lem17396 p q) (@lem17401 p q)). Qed.
Lemma lem17403 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = (term7 p q)) = ((True = q) = (term5 q)).
Proof. exact (EQ_MP (@lem17402 p q) (@lem17393 q p h1)). Qed.
Lemma lem17404 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = (term5 q)) = ((p = q) = (term7 p q)).
Proof. exact (SYM (@lem17403 q p h1)). Qed.
Lemma lem17405 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17406 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term9 q).
Proof. exact (MK_COMB (@lem17405 q) (@lem17379 p h1)). Qed.
Lemma lem17407 (q : Prop) : (term9 q) = ((False = q) = (term10 q)).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem17408 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem17409 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = ((term3 q p) = ((False = q) = (term10 q))).
Proof. exact (MK_COMB (@lem17408 q p) (@lem17407 q)). Qed.
Lemma lem17410 (p : Prop) (q : Prop) : (term3 q p) = ((p = q) = (term7 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17412 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem17411) (@lem17410 p q)). Qed.
Lemma lem17413 (q : Prop) : ((False = q) = (term10 q)) = ((False = q) = (term10 q)).
Proof. exact (eq_refl ((False = q) = (term10 q))). Qed.
Lemma lem17414 (p : Prop) (q : Prop) : ((term3 q p) = ((False = q) = (term10 q))) = (((p = q) = (term7 p q)) = ((False = q) = (term10 q))).
Proof. exact (MK_COMB (@lem17412 p q) (@lem17413 q)). Qed.
Lemma lem17415 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = (((p = q) = (term7 p q)) = ((False = q) = (term10 q))).
Proof. exact (TRANS (@lem17409 p q) (@lem17414 p q)). Qed.
Lemma lem17416 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = (term7 p q)) = ((False = q) = (term10 q)).
Proof. exact (EQ_MP (@lem17415 p q) (@lem17406 q p h1)). Qed.
Lemma lem17417 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = (term10 q)) = ((p = q) = (term7 p q)).
Proof. exact (SYM (@lem17416 q p h1)). Qed.
Lemma lem17421 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem17422 (q : Prop) : (True = q) = q.
Proof. exact (@lem17421 q). Qed.
Lemma lem17423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17424 (q : Prop) : (term11 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem17423) (@lem17422 q)). Qed.
Lemma lem17428 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17429 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem17428 q). Qed.
Lemma lem17430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17431 (q : Prop) : (term12 q) = (or q).
Proof. exact (MK_COMB (@lem17430) (@lem17429 q)). Qed.
Lemma lem17435 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17437 : term13 = (and False).
Proof. exact (MK_COMB (@lem17436) (@lem17435)). Qed.
Lemma lem17438 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem17439 (q : Prop) : (term14 q) = (term15 q).
Proof. exact (MK_COMB (@lem17437) (@lem17438 q)). Qed.
Lemma lem17441 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem17442 (q : Prop) : (term15 q) = False.
Proof. exact (@lem17441 (~ q)). Qed.
Lemma lem17443 (q : Prop) : (term14 q) = False.
Proof. exact (TRANS (@lem17439 q) (@lem17442 q)). Qed.
Lemma lem17444 (q : Prop) : (term5 q) = (q \/ False).
Proof. exact (MK_COMB (@lem17431 q) (@lem17443 q)). Qed.
Lemma lem17446 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem17447 (q : Prop) : (q \/ False) = q.
Proof. exact (@lem17446 q). Qed.
Lemma lem17448 (q : Prop) : (term5 q) = q.
Proof. exact (TRANS (@lem17444 q) (@lem17447 q)). Qed.
Lemma lem17449 (q : Prop) : ((True = q) = (term5 q)) = (q = q).
Proof. exact (MK_COMB (@lem17424 q) (@lem17448 q)). Qed.
Lemma lem17451 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17452 (x : Prop) : (x = x) = True.
Proof. exact (@lem17451 Prop x). Qed.
Lemma lem17453 (q : Prop) : (q = q) = True.
Proof. exact (@lem17452 q). Qed.
Lemma lem17454 (q : Prop) : ((True = q) = (term5 q)) = True.
Proof. exact (TRANS (@lem17449 q) (@lem17453 q)). Qed.
Lemma lem17455 (q : Prop) : True = ((True = q) = (term5 q)).
Proof. exact (SYM (@lem17454 q)). Qed.
Lemma lem17456 (q : Prop) : (True = q) = (term5 q).
Proof. exact (EQ_MP (@lem17455 q) (@lem0)). Qed.
Lemma lem17460 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem17461 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem17460 q). Qed.
Lemma lem17462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17463 (q : Prop) : (term16 q) = (term17 q).
Proof. exact (MK_COMB (@lem17462) (@lem17461 q)). Qed.
Lemma lem17467 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem17468 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem17467 q). Qed.
Lemma lem17469 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17470 (q : Prop) : (term18 q) = (or False).
Proof. exact (MK_COMB (@lem17469) (@lem17468 q)). Qed.
Lemma lem17474 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17476 : term19 = (and True).
Proof. exact (MK_COMB (@lem17475) (@lem17474)). Qed.
Lemma lem17477 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem17478 (q : Prop) : (term20 q) = (term21 q).
Proof. exact (MK_COMB (@lem17476) (@lem17477 q)). Qed.
Lemma lem17480 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17481 (q : Prop) : (term21 q) = (~ q).
Proof. exact (@lem17480 (~ q)). Qed.
Lemma lem17482 (q : Prop) : (term20 q) = (~ q).
Proof. exact (TRANS (@lem17478 q) (@lem17481 q)). Qed.
Lemma lem17483 (q : Prop) : (term10 q) = (term22 q).
Proof. exact (MK_COMB (@lem17470 q) (@lem17482 q)). Qed.
Lemma lem17485 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17486 (q : Prop) : (term22 q) = (~ q).
Proof. exact (@lem17485 (~ q)). Qed.
Lemma lem17487 (q : Prop) : (term10 q) = (~ q).
Proof. exact (TRANS (@lem17483 q) (@lem17486 q)). Qed.
Lemma lem17488 (q : Prop) : ((False = q) = (term10 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem17463 q) (@lem17487 q)). Qed.
Lemma lem17490 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17491 (x : Prop) : (x = x) = True.
Proof. exact (@lem17490 Prop x). Qed.
Lemma lem17492 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem17491 (~ q)). Qed.
Lemma lem17493 (q : Prop) : ((False = q) = (term10 q)) = True.
Proof. exact (TRANS (@lem17488 q) (@lem17492 q)). Qed.
Lemma lem17494 (q : Prop) : True = ((False = q) = (term10 q)).
Proof. exact (SYM (@lem17493 q)). Qed.
Lemma lem17495 (q : Prop) : (False = q) = (term10 q).
Proof. exact (EQ_MP (@lem17494 q) (@lem0)). Qed.
Lemma lem17496 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = (term7 p q).
Proof. exact (EQ_MP (@lem17417 q p h1) (@lem17495 q)). Qed.
Lemma lem17497 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = (term7 p q).
Proof. exact (EQ_MP (@lem17404 q p h1) (@lem17456 q)). Qed.
Lemma lem17500 (p : Prop) (q : Prop) : (p = q) = (term7 p q).
Proof. exact (or_elim (@lem17377 p) (fun h0 : p = True => @lem17497 q p h0) (fun h0 : p = False => @lem17496 q p h0)). Qed.
