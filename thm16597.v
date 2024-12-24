Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16597_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Lemma lem16515 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem16516 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem16517 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem16516 a) (@lem16515 a)). Qed.
Lemma lem16518 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem16519 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem16526 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16527 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem16526 b) (@lem16518 a h1)). Qed.
Lemma lem16528 (b : Prop) : (term4 b) = (term5 b).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem16529 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16530 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = (term5 b)).
Proof. exact (MK_COMB (@lem16529 b a) (@lem16528 b)). Qed.
Lemma lem16531 (b : Prop) (a : Prop) : (term3 b a) = (term7 b a).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16533 (b : Prop) (a : Prop) : (term6 b a) = (term8 b a).
Proof. exact (MK_COMB (@lem16532) (@lem16531 b a)). Qed.
Lemma lem16534 (b : Prop) : (term5 b) = (term5 b).
Proof. exact (eq_refl (term5 b)). Qed.
Lemma lem16535 (a : Prop) (b : Prop) : ((term3 b a) = (term5 b)) = ((term7 b a) = (term5 b)).
Proof. exact (MK_COMB (@lem16533 b a) (@lem16534 b)). Qed.
Lemma lem16536 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term7 b a) = (term5 b)).
Proof. exact (TRANS (@lem16530 a b) (@lem16535 a b)). Qed.
Lemma lem16537 (b : Prop) (a : Prop) (h1 : a = True) : (term7 b a) = (term5 b).
Proof. exact (EQ_MP (@lem16536 a b) (@lem16527 b a h1)). Qed.
Lemma lem16538 (b : Prop) (a : Prop) (h1 : a = True) : (term5 b) = (term7 b a).
Proof. exact (SYM (@lem16537 b a h1)). Qed.
Lemma lem16539 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16540 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem16539 b) (@lem16519 a h1)). Qed.
Lemma lem16541 (b : Prop) : (term9 b) = (term10 b).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem16542 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16543 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = (term10 b)).
Proof. exact (MK_COMB (@lem16542 b a) (@lem16541 b)). Qed.
Lemma lem16544 (b : Prop) (a : Prop) : (term3 b a) = (term7 b a).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16546 (b : Prop) (a : Prop) : (term6 b a) = (term8 b a).
Proof. exact (MK_COMB (@lem16545) (@lem16544 b a)). Qed.
Lemma lem16547 (b : Prop) : (term10 b) = (term10 b).
Proof. exact (eq_refl (term10 b)). Qed.
Lemma lem16548 (a : Prop) (b : Prop) : ((term3 b a) = (term10 b)) = ((term7 b a) = (term10 b)).
Proof. exact (MK_COMB (@lem16546 b a) (@lem16547 b)). Qed.
Lemma lem16549 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term7 b a) = (term10 b)).
Proof. exact (TRANS (@lem16543 a b) (@lem16548 a b)). Qed.
Lemma lem16550 (b : Prop) (a : Prop) (h1 : a = False) : (term7 b a) = (term10 b).
Proof. exact (EQ_MP (@lem16549 a b) (@lem16540 b a h1)). Qed.
Lemma lem16551 (b : Prop) (a : Prop) (h1 : a = False) : (term10 b) = (term7 b a).
Proof. exact (SYM (@lem16550 b a h1)). Qed.
Lemma lem16555 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem16556 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem16555 b). Qed.
Lemma lem16557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem16558 (b : Prop) : (term11 b) = (~ True).
Proof. exact (MK_COMB (@lem16557) (@lem16556 b)). Qed.
Lemma lem16560 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16561 (b : Prop) : (term11 b) = False.
Proof. exact (TRANS (@lem16558 b) (@lem16560)). Qed.
Lemma lem16562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16563 (b : Prop) : (term12 b) = (imp False).
Proof. exact (MK_COMB (@lem16562) (@lem16561 b)). Qed.
Lemma lem16565 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16566 (b : Prop) : (term5 b) = (False -> False).
Proof. exact (MK_COMB (@lem16563 b) (@lem16565)). Qed.
Lemma lem16568 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem16569 : (False -> False) = True.
Proof. exact (@lem16568 False). Qed.
Lemma lem16570 (b : Prop) : (term5 b) = True.
Proof. exact (TRANS (@lem16566 b) (@lem16569)). Qed.
Lemma lem16571 (b : Prop) : True = (term5 b).
Proof. exact (SYM (@lem16570 b)). Qed.
Lemma lem16572 (b : Prop) : term5 b.
Proof. exact (EQ_MP (@lem16571 b) (@lem0)). Qed.
Lemma lem16576 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem16577 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem16576 b). Qed.
Lemma lem16578 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem16579 (b : Prop) : (term13 b) = (~ b).
Proof. exact (MK_COMB (@lem16578) (@lem16577 b)). Qed.
Lemma lem16580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16581 (b : Prop) : (term14 b) = (term15 b).
Proof. exact (MK_COMB (@lem16580) (@lem16579 b)). Qed.
Lemma lem16583 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem16584 (b : Prop) : (term10 b) = (term16 b).
Proof. exact (MK_COMB (@lem16581 b) (@lem16583)). Qed.
Lemma lem16586 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem16587 (b : Prop) : (term16 b) = True.
Proof. exact (@lem16586 (~ b)). Qed.
Lemma lem16588 (b : Prop) : (term10 b) = True.
Proof. exact (TRANS (@lem16584 b) (@lem16587 b)). Qed.
Lemma lem16589 (b : Prop) : True = (term10 b).
Proof. exact (SYM (@lem16588 b)). Qed.
Lemma lem16590 (b : Prop) : term10 b.
Proof. exact (EQ_MP (@lem16589 b) (@lem0)). Qed.
Lemma lem16591 (b : Prop) (a : Prop) (h1 : a = False) : term7 b a.
Proof. exact (EQ_MP (@lem16551 b a h1) (@lem16590 b)). Qed.
Lemma lem16592 (b : Prop) (a : Prop) (h1 : a = True) : term7 b a.
Proof. exact (EQ_MP (@lem16538 b a h1) (@lem16572 b)). Qed.
Lemma lem16595 (b : Prop) (a : Prop) : term7 b a.
Proof. exact (or_elim (@lem16517 a) (fun h0 : a = True => @lem16592 b a h0) (fun h0 : a = False => @lem16591 b a h0)). Qed.
Lemma lem16596 (a : Prop) (b : Prop) (h1 : term17 a b) : term17 a b.
Proof. exact (h1). Qed.
Lemma lem16597 (a : Prop) (b : Prop) (h1 : term17 a b) : ~ a.
Proof. exact (@lem16595 b a (@lem16596 a b h1)). Qed.
