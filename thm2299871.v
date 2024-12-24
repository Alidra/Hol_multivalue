Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299871_term_abbrevs.
Lemma lem2299867 (b : Prop) (x : int) (y : int) (h1 : (term0 b x y) = (term1 b x y)) : (term0 b x y) = (term1 b x y).
Proof. exact (h1). Qed.
Lemma lem2299868 (b : Prop) (x : int) (y : int) (h1 : (term0 b x y) = (term1 b x y)) : (term1 b x y) = (term0 b x y).
Proof. exact (SYM (@lem2299867 b x y h1)). Qed.
Lemma lem2299869 (b : Prop) (x : int) (y : int) (h1 : (term1 b x y) = (term0 b x y)) : (term1 b x y) = (term0 b x y).
Proof. exact (h1). Qed.
Lemma lem2299870 (b : Prop) (x : int) (y : int) (h1 : (term1 b x y) = (term0 b x y)) : (term0 b x y) = (term1 b x y).
Proof. exact (SYM (@lem2299869 b x y h1)). Qed.
Lemma lem2299871 (b : Prop) (x : int) (y : int) : ((term0 b x y) = (term1 b x y)) = ((term1 b x y) = (term0 b x y)).
Proof. exact (prop_ext (fun h1 : (term0 b x y) = (term1 b x y) => @lem2299868 b x y h1) (fun h1 : (term1 b x y) = (term0 b x y) => @lem2299870 b x y h1)). Qed.
