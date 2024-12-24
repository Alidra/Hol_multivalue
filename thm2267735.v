Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267735_term_abbrevs.
Lemma lem2267727 (r : real) : (term0 r) = ((term1 r) = r).
Proof. exact (@axiom_26 r). Qed.
Lemma lem2267730 (r : real) : (term0 r) = (integer r).
Proof. exact (eq_refl (term0 r)). Qed.
Lemma lem2267731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2267732 (r : real) : (term2 r) = (term3 r).
Proof. exact (MK_COMB (@lem2267731) (@lem2267730 r)). Qed.
Lemma lem2267733 (r : real) : ((term1 r) = r) = ((term1 r) = r).
Proof. exact (eq_refl ((term1 r) = r)). Qed.
Lemma lem2267734 (r : real) : ((term0 r) = ((term1 r) = r)) = ((integer r) = ((term1 r) = r)).
Proof. exact (MK_COMB (@lem2267732 r) (@lem2267733 r)). Qed.
Lemma lem2267735 (r : real) : (integer r) = ((term1 r) = r).
Proof. exact (EQ_MP (@lem2267734 r) (@lem2267727 r)). Qed.
