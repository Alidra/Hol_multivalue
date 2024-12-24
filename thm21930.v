Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21930_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Lemma lem21825 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem21826 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem21827 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem21826 a) (@lem21825 a)). Qed.
Lemma lem21828 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem21829 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem21838 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem21839 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem21838 b) (@lem21828 a h1)). Qed.
Lemma lem21840 (b : Prop) : (term4 b) = (term5 b).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem21841 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem21842 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = (term5 b)).
Proof. exact (MK_COMB (@lem21841 b a) (@lem21840 b)). Qed.
Lemma lem21843 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem21844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21845 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem21844) (@lem21843 a b)). Qed.
Lemma lem21846 (b : Prop) : (term5 b) = (term5 b).
Proof. exact (eq_refl (term5 b)). Qed.
Lemma lem21847 (a : Prop) (b : Prop) : ((term3 b a) = (term5 b)) = ((term7 a b) = (term5 b)).
Proof. exact (MK_COMB (@lem21845 a b) (@lem21846 b)). Qed.
Lemma lem21848 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term7 a b) = (term5 b)).
Proof. exact (TRANS (@lem21842 a b) (@lem21847 a b)). Qed.
Lemma lem21849 (b : Prop) (a : Prop) (h1 : a = True) : (term7 a b) = (term5 b).
Proof. exact (EQ_MP (@lem21848 a b) (@lem21839 b a h1)). Qed.
Lemma lem21850 (b : Prop) (a : Prop) (h1 : a = True) : (term5 b) = (term7 a b).
Proof. exact (SYM (@lem21849 b a h1)). Qed.
Lemma lem21851 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem21852 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem21851 b) (@lem21829 a h1)). Qed.
Lemma lem21853 (b : Prop) : (term9 b) = (term10 b).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem21854 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem21855 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = (term10 b)).
Proof. exact (MK_COMB (@lem21854 b a) (@lem21853 b)). Qed.
Lemma lem21856 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem21857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21858 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem21857) (@lem21856 a b)). Qed.
Lemma lem21859 (b : Prop) : (term10 b) = (term10 b).
Proof. exact (eq_refl (term10 b)). Qed.
Lemma lem21860 (a : Prop) (b : Prop) : ((term3 b a) = (term10 b)) = ((term7 a b) = (term10 b)).
Proof. exact (MK_COMB (@lem21858 a b) (@lem21859 b)). Qed.
Lemma lem21861 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term7 a b) = (term10 b)).
Proof. exact (TRANS (@lem21855 a b) (@lem21860 a b)). Qed.
Lemma lem21862 (b : Prop) (a : Prop) (h1 : a = False) : (term7 a b) = (term10 b).
Proof. exact (EQ_MP (@lem21861 a b) (@lem21852 b a h1)). Qed.
Lemma lem21863 (b : Prop) (a : Prop) (h1 : a = False) : (term10 b) = (term7 a b).
Proof. exact (SYM (@lem21862 b a h1)). Qed.
Lemma lem21867 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem21868 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem21867 b). Qed.
Lemma lem21869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem21870 (b : Prop) : (term11 b) = (imp True).
Proof. exact (MK_COMB (@lem21869) (@lem21868 b)). Qed.
Lemma lem21874 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem21875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem21876 : term12 = (imp False).
Proof. exact (MK_COMB (@lem21875) (@lem21874)). Qed.
Lemma lem21877 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem21878 (b : Prop) : (term13 b) = (False -> b).
Proof. exact (MK_COMB (@lem21876) (@lem21877 b)). Qed.
Lemma lem21880 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem21881 (b : Prop) : (False -> b) = True.
Proof. exact (@lem21880 b). Qed.
Lemma lem21882 (b : Prop) : (term13 b) = True.
Proof. exact (TRANS (@lem21878 b) (@lem21881 b)). Qed.
Lemma lem21883 (b : Prop) : (term5 b) = (True -> True).
Proof. exact (MK_COMB (@lem21870 b) (@lem21882 b)). Qed.
Lemma lem21885 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem21886 : (True -> True) = True.
Proof. exact (@lem21885 True). Qed.
Lemma lem21887 (b : Prop) : (term5 b) = True.
Proof. exact (TRANS (@lem21883 b) (@lem21886)). Qed.
Lemma lem21888 (b : Prop) : True = (term5 b).
Proof. exact (SYM (@lem21887 b)). Qed.
Lemma lem21889 (b : Prop) : term5 b.
Proof. exact (EQ_MP (@lem21888 b) (@lem0)). Qed.
Lemma lem21893 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem21894 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem21893 b). Qed.
Lemma lem21895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem21896 (b : Prop) : (term14 b) = (imp b).
Proof. exact (MK_COMB (@lem21895) (@lem21894 b)). Qed.
Lemma lem21900 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem21902 : term15 = (imp True).
Proof. exact (MK_COMB (@lem21901) (@lem21900)). Qed.
Lemma lem21903 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem21904 (b : Prop) : (term16 b) = (True -> b).
Proof. exact (MK_COMB (@lem21902) (@lem21903 b)). Qed.
Lemma lem21906 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem21907 (b : Prop) : (True -> b) = b.
Proof. exact (@lem21906 b). Qed.
Lemma lem21908 (b : Prop) : (term16 b) = b.
Proof. exact (TRANS (@lem21904 b) (@lem21907 b)). Qed.
Lemma lem21909 (b : Prop) : (term10 b) = (b -> b).
Proof. exact (MK_COMB (@lem21896 b) (@lem21908 b)). Qed.
Lemma lem21911 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem21912 (b : Prop) : (b -> b) = True.
Proof. exact (@lem21911 b). Qed.
Lemma lem21913 (b : Prop) : (term10 b) = True.
Proof. exact (TRANS (@lem21909 b) (@lem21912 b)). Qed.
Lemma lem21914 (b : Prop) : True = (term10 b).
Proof. exact (SYM (@lem21913 b)). Qed.
Lemma lem21915 (b : Prop) : term10 b.
Proof. exact (EQ_MP (@lem21914 b) (@lem0)). Qed.
Lemma lem21916 (b : Prop) (a : Prop) (h1 : a = False) : term7 a b.
Proof. exact (EQ_MP (@lem21863 b a h1) (@lem21915 b)). Qed.
Lemma lem21917 (b : Prop) (a : Prop) (h1 : a = True) : term7 a b.
Proof. exact (EQ_MP (@lem21850 b a h1) (@lem21889 b)). Qed.
Lemma lem21920 (a : Prop) (b : Prop) : term7 a b.
Proof. exact (or_elim (@lem21827 a) (fun h0 : a = True => @lem21917 b a h0) (fun h0 : a = False => @lem21916 b a h0)). Qed.
Lemma lem21925 (a : Prop) : term17 a.
Proof. exact (fun b : Prop => @lem21920 a b). Qed.
Lemma lem21930 : term18.
Proof. exact (fun a : Prop => @lem21925 a). Qed.
