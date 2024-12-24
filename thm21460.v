Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21460_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem21437 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem21438 (b : Prop) : (True -> b) = b.
Proof. exact (@lem21437 b). Qed.
Lemma lem21439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21440 (b : Prop) : (term0 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem21439) (@lem21438 b)). Qed.
Lemma lem21444 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem21445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem21446 : term1 = (or False).
Proof. exact (MK_COMB (@lem21445) (@lem21444)). Qed.
Lemma lem21447 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem21448 (b : Prop) : (term2 b) = (False \/ b).
Proof. exact (MK_COMB (@lem21446) (@lem21447 b)). Qed.
Lemma lem21450 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem21451 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem21450 b). Qed.
Lemma lem21452 (b : Prop) : (term2 b) = b.
Proof. exact (TRANS (@lem21448 b) (@lem21451 b)). Qed.
Lemma lem21453 (b : Prop) : ((True -> b) = (term2 b)) = (b = b).
Proof. exact (MK_COMB (@lem21440 b) (@lem21452 b)). Qed.
Lemma lem21455 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem21456 (x : Prop) : (x = x) = True.
Proof. exact (@lem21455 Prop x). Qed.
Lemma lem21457 (b : Prop) : (b = b) = True.
Proof. exact (@lem21456 b). Qed.
Lemma lem21458 (b : Prop) : ((True -> b) = (term2 b)) = True.
Proof. exact (TRANS (@lem21453 b) (@lem21457 b)). Qed.
Lemma lem21459 (b : Prop) : True = ((True -> b) = (term2 b)).
Proof. exact (SYM (@lem21458 b)). Qed.
Lemma lem21460 (b : Prop) : (True -> b) = (term2 b).
Proof. exact (EQ_MP (@lem21459 b) (@lem0)). Qed.
