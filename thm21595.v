Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21595_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1857_spec.
Require Import thm21542_spec.
Lemma lem21574 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem21575 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem21574 b). Qed.
Lemma lem21576 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem21577 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (MK_COMB (@lem21576) (@lem21575 b)). Qed.
Lemma lem21581 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21582 (b : Prop) : (or b) = (or b).
Proof. exact (eq_refl (or b)). Qed.
Lemma lem21583 (b : Prop) : (term2 b) = (b \/ True).
Proof. exact (MK_COMB (@lem21582 b) (@lem21581)). Qed.
Lemma lem21585 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem21586 (b : Prop) : (b \/ True) = True.
Proof. exact (@lem21585 b). Qed.
Lemma lem21587 (b : Prop) : (term2 b) = True.
Proof. exact (TRANS (@lem21583 b) (@lem21586 b)). Qed.
Lemma lem21588 (b : Prop) : (term3 b) = (term4 b).
Proof. exact (MK_COMB (@lem21577 b) (@lem21587 b)). Qed.
Lemma lem21590 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem21591 (b : Prop) : (term4 b) = True.
Proof. exact (@lem21590 (~ b)). Qed.
Lemma lem21592 (b : Prop) : (term3 b) = True.
Proof. exact (TRANS (@lem21588 b) (@lem21591 b)). Qed.
Lemma lem21593 (b : Prop) : True = (term3 b).
Proof. exact (SYM (@lem21592 b)). Qed.
Lemma lem21594 (b : Prop) : term3 b.
Proof. exact (EQ_MP (@lem21593 b) (@lem0)). Qed.
Lemma lem21595 (b : Prop) (a : Prop) (h1 : a = False) : term5 b a.
Proof. exact (EQ_MP (@lem21542 b a h1) (@lem21594 b)). Qed.
