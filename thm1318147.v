Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318147_term_abbrevs.
Lemma lem1318143 (x : nadd) (y : nadd) (h1 : (term0 x y) = (nadd_le x y)) : (term0 x y) = (nadd_le x y).
Proof. exact (h1). Qed.
Lemma lem1318144 (x : nadd) (y : nadd) (h1 : (term0 x y) = (nadd_le x y)) : (nadd_le x y) = (term0 x y).
Proof. exact (SYM (@lem1318143 x y h1)). Qed.
Lemma lem1318145 (x : nadd) (y : nadd) (h1 : (nadd_le x y) = (term0 x y)) : (nadd_le x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1318146 (x : nadd) (y : nadd) (h1 : (nadd_le x y) = (term0 x y)) : (term0 x y) = (nadd_le x y).
Proof. exact (SYM (@lem1318145 x y h1)). Qed.
Lemma lem1318147 (x : nadd) (y : nadd) : ((term0 x y) = (nadd_le x y)) = ((nadd_le x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (nadd_le x y) => @lem1318144 x y h1) (fun h1 : (nadd_le x y) = (term0 x y) => @lem1318146 x y h1)). Qed.
