Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318035_term_abbrevs.
Lemma lem1318031 (x : nadd) (y : nadd) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem1318032 (x : nadd) (y : nadd) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem1318031 x y h1)). Qed.
Lemma lem1318033 (x : nadd) (y : nadd) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1318034 (x : nadd) (y : nadd) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem1318033 x y h1)). Qed.
Lemma lem1318035 (x : nadd) (y : nadd) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem1318032 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem1318034 x y h1)). Qed.
