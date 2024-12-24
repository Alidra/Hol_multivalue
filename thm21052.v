Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21052_term_abbrevs.
Require Import thm21032_spec.
Lemma lem21040 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem21041 (p : Prop) (h1 : p = True) : (term1 p) = term2.
Proof. exact (MK_COMB (@lem21040) (@lem21032 p h1)). Qed.
Lemma lem21042 : term2 = (term3 = (~ True)).
Proof. exact (eq_refl term2). Qed.
Lemma lem21043 (p : Prop) : (term4 p) = (term4 p).
Proof. exact (eq_refl (term4 p)). Qed.
Lemma lem21044 (p : Prop) : ((term1 p) = term2) = ((term1 p) = (term3 = (~ True))).
Proof. exact (MK_COMB (@lem21043 p) (@lem21042)). Qed.
Lemma lem21045 (p : Prop) : (term1 p) = ((term5 p) = (~ p)).
Proof. exact (eq_refl (term1 p)). Qed.
Lemma lem21046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21047 (p : Prop) : (term4 p) = (term6 p).
Proof. exact (MK_COMB (@lem21046) (@lem21045 p)). Qed.
Lemma lem21048 : (term3 = (~ True)) = (term3 = (~ True)).
Proof. exact (eq_refl (term3 = (~ True))). Qed.
Lemma lem21049 (p : Prop) : ((term1 p) = (term3 = (~ True))) = (((term5 p) = (~ p)) = (term3 = (~ True))).
Proof. exact (MK_COMB (@lem21047 p) (@lem21048)). Qed.
Lemma lem21050 (p : Prop) : ((term1 p) = term2) = (((term5 p) = (~ p)) = (term3 = (~ True))).
Proof. exact (TRANS (@lem21044 p) (@lem21049 p)). Qed.
Lemma lem21051 (p : Prop) (h1 : p = True) : ((term5 p) = (~ p)) = (term3 = (~ True)).
Proof. exact (EQ_MP (@lem21050 p) (@lem21041 p h1)). Qed.
Lemma lem21052 (p : Prop) (h1 : p = True) : (term3 = (~ True)) = ((term5 p) = (~ p)).
Proof. exact (SYM (@lem21051 p h1)). Qed.
