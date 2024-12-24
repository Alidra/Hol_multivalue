Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2954598_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2954586 (t : Prop) : (term0 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2954587 (p : Prop) : (term0 p) = p.
Proof. exact (@lem2954586 p). Qed.
Lemma lem2954588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2954589 (p : Prop) : (term1 p) = (@eq Prop p).
Proof. exact (MK_COMB (@lem2954588) (@lem2954587 p)). Qed.
Lemma lem2954590 (p : Prop) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2954591 (p : Prop) : ((term0 p) = p) = (p = p).
Proof. exact (MK_COMB (@lem2954589 p) (@lem2954590 p)). Qed.
Lemma lem2954593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2954594 (x : Prop) : (x = x) = True.
Proof. exact (@lem2954593 Prop x). Qed.
Lemma lem2954595 (p : Prop) : (p = p) = True.
Proof. exact (@lem2954594 p). Qed.
Lemma lem2954596 (p : Prop) : ((term0 p) = p) = True.
Proof. exact (TRANS (@lem2954591 p) (@lem2954595 p)). Qed.
Lemma lem2954597 (p : Prop) : True = ((term0 p) = p).
Proof. exact (SYM (@lem2954596 p)). Qed.
Lemma lem2954598 (p : Prop) : (term0 p) = p.
Proof. exact (EQ_MP (@lem2954597 p) (@lem0)). Qed.
