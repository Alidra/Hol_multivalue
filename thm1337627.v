Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337627_term_abbrevs.
Lemma lem1337623 (x1 : prod hreal hreal) (h1 : (term0 x1) = (term1 x1)) : (term0 x1) = (term1 x1).
Proof. exact (h1). Qed.
Lemma lem1337624 (x1 : prod hreal hreal) (h1 : (term0 x1) = (term1 x1)) : (term1 x1) = (term0 x1).
Proof. exact (SYM (@lem1337623 x1 h1)). Qed.
Lemma lem1337625 (x1 : prod hreal hreal) (h1 : (term1 x1) = (term0 x1)) : (term1 x1) = (term0 x1).
Proof. exact (h1). Qed.
Lemma lem1337626 (x1 : prod hreal hreal) (h1 : (term1 x1) = (term0 x1)) : (term0 x1) = (term1 x1).
Proof. exact (SYM (@lem1337625 x1 h1)). Qed.
Lemma lem1337627 (x1 : prod hreal hreal) : ((term0 x1) = (term1 x1)) = ((term1 x1) = (term0 x1)).
Proof. exact (prop_ext (fun h1 : (term0 x1) = (term1 x1) => @lem1337624 x1 h1) (fun h1 : (term1 x1) = (term0 x1) => @lem1337626 x1 h1)). Qed.
