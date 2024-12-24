Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3070937_term_abbrevs.
Require Import INT_OF_NUM_OF_INT_spec.
Lemma lem3070933 (x : int) : term0 x.
Proof. exact (@lem2834258 x). Qed.
Lemma lem3070934 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3070935 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem3070934 x) (@lem3070933 x)). Qed.
Lemma lem3070936 (x : int) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem3070937 (x : int) (h1 : term2 x) : (term3 x) = x.
Proof. exact (@lem3070935 x (@lem3070936 x h1)). Qed.
