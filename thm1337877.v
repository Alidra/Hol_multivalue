Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337877_term_abbrevs.
Lemma lem1337873 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term0 x1 y1) = (term1 x1 y1)) : (term0 x1 y1) = (term1 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1337874 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term0 x1 y1) = (term1 x1 y1)) : (term1 x1 y1) = (term0 x1 y1).
Proof. exact (SYM (@lem1337873 x1 y1 h1)). Qed.
Lemma lem1337875 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term1 x1 y1) = (term0 x1 y1)) : (term1 x1 y1) = (term0 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1337876 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term1 x1 y1) = (term0 x1 y1)) : (term0 x1 y1) = (term1 x1 y1).
Proof. exact (SYM (@lem1337875 x1 y1 h1)). Qed.
Lemma lem1337877 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term0 x1 y1) = (term1 x1 y1)) = ((term1 x1 y1) = (term0 x1 y1)).
Proof. exact (prop_ext (fun h1 : (term0 x1 y1) = (term1 x1 y1) => @lem1337874 x1 y1 h1) (fun h1 : (term1 x1 y1) = (term0 x1 y1) => @lem1337876 x1 y1 h1)). Qed.
