Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21138_term_abbrevs.
Require Import thm21118_spec.
Lemma lem21126 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem21127 (p : Prop) (h1 : p = True) : (term1 p) = term2.
Proof. exact (MK_COMB (@lem21126) (@lem21118 p h1)). Qed.
Lemma lem21128 : term2 = (term3 = True).
Proof. exact (eq_refl term2). Qed.
Lemma lem21129 (p : Prop) : (term4 p) = (term4 p).
Proof. exact (eq_refl (term4 p)). Qed.
Lemma lem21130 (p : Prop) : ((term1 p) = term2) = ((term1 p) = (term3 = True)).
Proof. exact (MK_COMB (@lem21129 p) (@lem21128)). Qed.
Lemma lem21131 (p : Prop) : (term1 p) = ((term5 p) = p).
Proof. exact (eq_refl (term1 p)). Qed.
Lemma lem21132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21133 (p : Prop) : (term4 p) = (term6 p).
Proof. exact (MK_COMB (@lem21132) (@lem21131 p)). Qed.
Lemma lem21134 : (term3 = True) = (term3 = True).
Proof. exact (eq_refl (term3 = True)). Qed.
Lemma lem21135 (p : Prop) : ((term1 p) = (term3 = True)) = (((term5 p) = p) = (term3 = True)).
Proof. exact (MK_COMB (@lem21133 p) (@lem21134)). Qed.
Lemma lem21136 (p : Prop) : ((term1 p) = term2) = (((term5 p) = p) = (term3 = True)).
Proof. exact (TRANS (@lem21130 p) (@lem21135 p)). Qed.
Lemma lem21137 (p : Prop) (h1 : p = True) : ((term5 p) = p) = (term3 = True).
Proof. exact (EQ_MP (@lem21136 p) (@lem21127 p h1)). Qed.
Lemma lem21138 (p : Prop) (h1 : p = True) : (term3 = True) = ((term5 p) = p).
Proof. exact (SYM (@lem21137 p h1)). Qed.
