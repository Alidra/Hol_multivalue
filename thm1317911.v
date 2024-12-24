Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1317911_term_abbrevs.
Lemma lem1317907 (x : nadd) (y : nadd) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem1317908 (x : nadd) (y : nadd) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem1317907 x y h1)). Qed.
Lemma lem1317909 (x : nadd) (y : nadd) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1317910 (x : nadd) (y : nadd) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem1317909 x y h1)). Qed.
Lemma lem1317911 (x : nadd) (y : nadd) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem1317908 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem1317910 x y h1)). Qed.
