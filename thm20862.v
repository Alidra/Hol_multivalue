Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20862_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Lemma lem20832 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem20833 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem20832 b). Qed.
Lemma lem20834 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem20835 (b : Prop) : (term0 b) = (~ True).
Proof. exact (MK_COMB (@lem20834) (@lem20833 b)). Qed.
Lemma lem20837 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem20838 (b : Prop) : (term0 b) = False.
Proof. exact (TRANS (@lem20835 b) (@lem20837)). Qed.
Lemma lem20839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20840 (b : Prop) : (term1 b) = (@eq Prop False).
Proof. exact (MK_COMB (@lem20839) (@lem20838 b)). Qed.
Lemma lem20844 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem20845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem20846 : term2 = (and False).
Proof. exact (MK_COMB (@lem20845) (@lem20844)). Qed.
Lemma lem20847 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem20848 (b : Prop) : (term3 b) = (term4 b).
Proof. exact (MK_COMB (@lem20846) (@lem20847 b)). Qed.
Lemma lem20850 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem20851 (b : Prop) : (term4 b) = False.
Proof. exact (@lem20850 (~ b)). Qed.
Lemma lem20852 (b : Prop) : (term3 b) = False.
Proof. exact (TRANS (@lem20848 b) (@lem20851 b)). Qed.
Lemma lem20853 (b : Prop) : ((term0 b) = (term3 b)) = (False = False).
Proof. exact (MK_COMB (@lem20840 b) (@lem20852 b)). Qed.
Lemma lem20855 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem20856 : (False = False) = (~ False).
Proof. exact (@lem20855 False). Qed.
Lemma lem20858 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem20859 : (False = False) = True.
Proof. exact (TRANS (@lem20856) (@lem20858)). Qed.
Lemma lem20860 (b : Prop) : ((term0 b) = (term3 b)) = True.
Proof. exact (TRANS (@lem20853 b) (@lem20859)). Qed.
Lemma lem20861 (b : Prop) : True = ((term0 b) = (term3 b)).
Proof. exact (SYM (@lem20860 b)). Qed.
Lemma lem20862 (b : Prop) : (term0 b) = (term3 b).
Proof. exact (EQ_MP (@lem20861 b) (@lem0)). Qed.
