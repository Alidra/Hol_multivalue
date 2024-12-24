Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21151_term_abbrevs.
Require Import thm21119_spec.
Lemma lem21139 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem21140 (p : Prop) (h1 : p = False) : (term1 p) = term2.
Proof. exact (MK_COMB (@lem21139) (@lem21119 p h1)). Qed.
Lemma lem21141 : term2 = (term3 = False).
Proof. exact (eq_refl term2). Qed.
Lemma lem21142 (p : Prop) : (term4 p) = (term4 p).
Proof. exact (eq_refl (term4 p)). Qed.
Lemma lem21143 (p : Prop) : ((term1 p) = term2) = ((term1 p) = (term3 = False)).
Proof. exact (MK_COMB (@lem21142 p) (@lem21141)). Qed.
Lemma lem21144 (p : Prop) : (term1 p) = ((term5 p) = p).
Proof. exact (eq_refl (term1 p)). Qed.
Lemma lem21145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21146 (p : Prop) : (term4 p) = (term6 p).
Proof. exact (MK_COMB (@lem21145) (@lem21144 p)). Qed.
Lemma lem21147 : (term3 = False) = (term3 = False).
Proof. exact (eq_refl (term3 = False)). Qed.
Lemma lem21148 (p : Prop) : ((term1 p) = (term3 = False)) = (((term5 p) = p) = (term3 = False)).
Proof. exact (MK_COMB (@lem21146 p) (@lem21147)). Qed.
Lemma lem21149 (p : Prop) : ((term1 p) = term2) = (((term5 p) = p) = (term3 = False)).
Proof. exact (TRANS (@lem21143 p) (@lem21148 p)). Qed.
Lemma lem21150 (p : Prop) (h1 : p = False) : ((term5 p) = p) = (term3 = False).
Proof. exact (EQ_MP (@lem21149 p) (@lem21140 p h1)). Qed.
Lemma lem21151 (p : Prop) (h1 : p = False) : (term3 = False) = ((term5 p) = p).
Proof. exact (SYM (@lem21150 p h1)). Qed.
