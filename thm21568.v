Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21568_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1834_spec.
Require Import thm1855_spec.
Lemma lem21548 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem21549 (b : Prop) : (True = b) = b.
Proof. exact (@lem21548 b). Qed.
Lemma lem21550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem21551 (b : Prop) : (term0 b) = (imp b).
Proof. exact (MK_COMB (@lem21550) (@lem21549 b)). Qed.
Lemma lem21555 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem21556 (b : Prop) : (or b) = (or b).
Proof. exact (eq_refl (or b)). Qed.
Lemma lem21557 (b : Prop) : (term1 b) = (b \/ False).
Proof. exact (MK_COMB (@lem21556 b) (@lem21555)). Qed.
Lemma lem21559 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem21560 (b : Prop) : (b \/ False) = b.
Proof. exact (@lem21559 b). Qed.
Lemma lem21561 (b : Prop) : (term1 b) = b.
Proof. exact (TRANS (@lem21557 b) (@lem21560 b)). Qed.
Lemma lem21562 (b : Prop) : (term2 b) = (b -> b).
Proof. exact (MK_COMB (@lem21551 b) (@lem21561 b)). Qed.
Lemma lem21564 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem21565 (b : Prop) : (b -> b) = True.
Proof. exact (@lem21564 b). Qed.
Lemma lem21566 (b : Prop) : (term2 b) = True.
Proof. exact (TRANS (@lem21562 b) (@lem21565 b)). Qed.
Lemma lem21567 (b : Prop) : True = (term2 b).
Proof. exact (SYM (@lem21566 b)). Qed.
Lemma lem21568 (b : Prop) : term2 b.
Proof. exact (EQ_MP (@lem21567 b) (@lem0)). Qed.
