Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21487_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1855_spec.
Require Import thm21433_spec.
Lemma lem21464 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem21465 (b : Prop) : (False -> b) = True.
Proof. exact (@lem21464 b). Qed.
Lemma lem21466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21467 (b : Prop) : (term0 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem21466) (@lem21465 b)). Qed.
Lemma lem21471 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem21473 : term1 = (or True).
Proof. exact (MK_COMB (@lem21472) (@lem21471)). Qed.
Lemma lem21474 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem21475 (b : Prop) : (term2 b) = (True \/ b).
Proof. exact (MK_COMB (@lem21473) (@lem21474 b)). Qed.
Lemma lem21477 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem21478 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem21477 b). Qed.
Lemma lem21479 (b : Prop) : (term2 b) = True.
Proof. exact (TRANS (@lem21475 b) (@lem21478 b)). Qed.
Lemma lem21480 (b : Prop) : ((False -> b) = (term2 b)) = (True = True).
Proof. exact (MK_COMB (@lem21467 b) (@lem21479 b)). Qed.
Lemma lem21482 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem21483 : (True = True) = True.
Proof. exact (@lem21482 True). Qed.
Lemma lem21484 (b : Prop) : ((False -> b) = (term2 b)) = True.
Proof. exact (TRANS (@lem21480 b) (@lem21483)). Qed.
Lemma lem21485 (b : Prop) : True = ((False -> b) = (term2 b)).
Proof. exact (SYM (@lem21484 b)). Qed.
Lemma lem21486 (b : Prop) : (False -> b) = (term2 b).
Proof. exact (EQ_MP (@lem21485 b) (@lem0)). Qed.
Lemma lem21487 (b : Prop) (a : Prop) (h1 : a = False) : (a -> b) = (term3 a b).
Proof. exact (EQ_MP (@lem21433 b a h1) (@lem21486 b)). Qed.
