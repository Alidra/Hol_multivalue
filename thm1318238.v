Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318238_term_abbrevs.
Lemma lem1318234 (x : nadd) (h1 : (term0 x) = (term1 x)) : (term0 x) = (term1 x).
Proof. exact (h1). Qed.
Lemma lem1318235 (x : nadd) (h1 : (term0 x) = (term1 x)) : (term1 x) = (term0 x).
Proof. exact (SYM (@lem1318234 x h1)). Qed.
Lemma lem1318236 (x : nadd) (h1 : (term1 x) = (term0 x)) : (term1 x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1318237 (x : nadd) (h1 : (term1 x) = (term0 x)) : (term0 x) = (term1 x).
Proof. exact (SYM (@lem1318236 x h1)). Qed.
Lemma lem1318238 (x : nadd) : ((term0 x) = (term1 x)) = ((term1 x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (term1 x) => @lem1318235 x h1) (fun h1 : (term1 x) = (term0 x) => @lem1318237 x h1)). Qed.
