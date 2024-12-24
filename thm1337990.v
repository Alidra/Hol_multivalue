Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337990_term_abbrevs.
Lemma lem1337986 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term0 x1 y1) = (treal_le x1 y1)) : (term0 x1 y1) = (treal_le x1 y1).
Proof. exact (h1). Qed.
Lemma lem1337987 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term0 x1 y1) = (treal_le x1 y1)) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (SYM (@lem1337986 x1 y1 h1)). Qed.
Lemma lem1337988 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term0 x1 y1)) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1337989 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (treal_le x1 y1) = (term0 x1 y1)) : (term0 x1 y1) = (treal_le x1 y1).
Proof. exact (SYM (@lem1337988 x1 y1 h1)). Qed.
Lemma lem1337990 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term0 x1 y1) = (treal_le x1 y1)) = ((treal_le x1 y1) = (term0 x1 y1)).
Proof. exact (prop_ext (fun h1 : (term0 x1 y1) = (treal_le x1 y1) => @lem1337987 x1 y1 h1) (fun h1 : (treal_le x1 y1) = (term0 x1 y1) => @lem1337989 x1 y1 h1)). Qed.
