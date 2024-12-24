Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338081_term_abbrevs.
Lemma lem1338077 (x : prod hreal hreal) (h1 : (term0 x) = (term1 x)) : (term0 x) = (term1 x).
Proof. exact (h1). Qed.
Lemma lem1338078 (x : prod hreal hreal) (h1 : (term0 x) = (term1 x)) : (term1 x) = (term0 x).
Proof. exact (SYM (@lem1338077 x h1)). Qed.
Lemma lem1338079 (x : prod hreal hreal) (h1 : (term1 x) = (term0 x)) : (term1 x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1338080 (x : prod hreal hreal) (h1 : (term1 x) = (term0 x)) : (term0 x) = (term1 x).
Proof. exact (SYM (@lem1338079 x h1)). Qed.
Lemma lem1338081 (x : prod hreal hreal) : ((term0 x) = (term1 x)) = ((term1 x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (term1 x) => @lem1338078 x h1) (fun h1 : (term1 x) = (term0 x) => @lem1338080 x h1)). Qed.
