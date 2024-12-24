Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337752_term_abbrevs.
Lemma lem1337748 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term0 x1 y1) = (term1 x1 y1)) : (term0 x1 y1) = (term1 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1337749 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term0 x1 y1) = (term1 x1 y1)) : (term1 x1 y1) = (term0 x1 y1).
Proof. exact (SYM (@lem1337748 x1 y1 h1)). Qed.
Lemma lem1337750 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term1 x1 y1) = (term0 x1 y1)) : (term1 x1 y1) = (term0 x1 y1).
Proof. exact (h1). Qed.
Lemma lem1337751 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : (term1 x1 y1) = (term0 x1 y1)) : (term0 x1 y1) = (term1 x1 y1).
Proof. exact (SYM (@lem1337750 x1 y1 h1)). Qed.
Lemma lem1337752 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term0 x1 y1) = (term1 x1 y1)) = ((term1 x1 y1) = (term0 x1 y1)).
Proof. exact (prop_ext (fun h1 : (term0 x1 y1) = (term1 x1 y1) => @lem1337749 x1 y1 h1) (fun h1 : (term1 x1 y1) = (term0 x1 y1) => @lem1337751 x1 y1 h1)). Qed.
