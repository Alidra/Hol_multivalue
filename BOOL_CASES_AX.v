Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BOOL_CASES_AX_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem9785 (t : Prop) : term0 t.
Proof. exact (@lem9784 t). Qed.
Lemma lem9786 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem9787 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem9786 t) (@lem9785 t)). Qed.
Lemma lem9788 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem9789 (t : Prop) (h1 : ~ t) : ~ t.
Proof. exact (h1). Qed.
Lemma lem9790 (t : Prop) : t = (t = True).
Proof. exact (@lem7 t). Qed.
Lemma lem9795 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem9797 (t : Prop) (h1 : t) : t = True.
Proof. exact (EQ_MP (@lem9790 t) (@lem9788 t h1)). Qed.
Lemma lem9798 (t : Prop) (h1 : t) : (t = True) = True.
Proof. exact (TRANS (@lem9795 t) (@lem9797 t h1)). Qed.
Lemma lem9799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9800 (t : Prop) (h1 : t) : (term2 t) = (or True).
Proof. exact (MK_COMB (@lem9799) (@lem9798 t h1)). Qed.
Lemma lem9802 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem9804 (t : Prop) (h1 : t) : t = True.
Proof. exact (EQ_MP (@lem9790 t) (@lem9788 t h1)). Qed.
Lemma lem9805 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem9806 (t : Prop) (h1 : t) : (~ t) = (~ True).
Proof. exact (MK_COMB (@lem9805) (@lem9804 t h1)). Qed.
Lemma lem9808 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem9809 (t : Prop) (h1 : t) : (~ t) = False.
Proof. exact (TRANS (@lem9806 t h1) (@lem9808)). Qed.
Lemma lem9810 (t : Prop) (h1 : t) : (t = False) = False.
Proof. exact (TRANS (@lem9802 t) (@lem9809 t h1)). Qed.
Lemma lem9811 (t : Prop) (h1 : t) : (term3 t) = (True \/ False).
Proof. exact (MK_COMB (@lem9800 t h1) (@lem9810 t h1)). Qed.
Lemma lem9813 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem9814 : (True \/ False) = True.
Proof. exact (@lem9813 False). Qed.
Lemma lem9815 (t : Prop) (h1 : t) : (term3 t) = True.
Proof. exact (TRANS (@lem9811 t h1) (@lem9814)). Qed.
Lemma lem9816 (t : Prop) (h1 : t) : True = (term3 t).
Proof. exact (SYM (@lem9815 t h1)). Qed.
Lemma lem9817 (t : Prop) (h1 : t) : term3 t.
Proof. exact (EQ_MP (@lem9816 t h1) (@lem0)). Qed.
Lemma lem9818 (t : Prop) : term4 t.
Proof. exact (@lem82 t). Qed.
Lemma lem9823 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem9825 (t : Prop) (h1 : ~ t) : t = False.
Proof. exact (@lem9818 t (@lem9789 t h1)). Qed.
Lemma lem9826 (t : Prop) (h1 : ~ t) : (t = True) = False.
Proof. exact (TRANS (@lem9823 t) (@lem9825 t h1)). Qed.
Lemma lem9827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9828 (t : Prop) (h1 : ~ t) : (term2 t) = (or False).
Proof. exact (MK_COMB (@lem9827) (@lem9826 t h1)). Qed.
Lemma lem9830 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem9832 (t : Prop) (h1 : ~ t) : t = False.
Proof. exact (@lem9818 t (@lem9789 t h1)). Qed.
Lemma lem9833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem9834 (t : Prop) (h1 : ~ t) : (~ t) = (~ False).
Proof. exact (MK_COMB (@lem9833) (@lem9832 t h1)). Qed.
Lemma lem9836 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem9837 (t : Prop) (h1 : ~ t) : (~ t) = True.
Proof. exact (TRANS (@lem9834 t h1) (@lem9836)). Qed.
Lemma lem9838 (t : Prop) (h1 : ~ t) : (t = False) = True.
Proof. exact (TRANS (@lem9830 t) (@lem9837 t h1)). Qed.
Lemma lem9839 (t : Prop) (h1 : ~ t) : (term3 t) = (False \/ True).
Proof. exact (MK_COMB (@lem9828 t h1) (@lem9838 t h1)). Qed.
Lemma lem9841 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem9842 : (False \/ True) = True.
Proof. exact (@lem9841 True). Qed.
Lemma lem9843 (t : Prop) (h1 : ~ t) : (term3 t) = True.
Proof. exact (TRANS (@lem9839 t h1) (@lem9842)). Qed.
Lemma lem9844 (t : Prop) (h1 : ~ t) : True = (term3 t).
Proof. exact (SYM (@lem9843 t h1)). Qed.
Lemma lem9845 (t : Prop) (h1 : ~ t) : term3 t.
Proof. exact (EQ_MP (@lem9844 t h1) (@lem0)). Qed.
Lemma lem9846 (t : Prop) : term3 t.
Proof. exact (or_elim (@lem9787 t) (fun h0 : t => @lem9817 t h0) (fun h0 : ~ t => @lem9845 t h0)). Qed.
Lemma lem9851 : term5.
Proof. exact (fun t : Prop => @lem9846 t). Qed.
