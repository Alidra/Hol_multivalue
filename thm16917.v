Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16917_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Lemma lem16810 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem16811 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem16812 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem16811 a) (@lem16810 a)). Qed.
Lemma lem16813 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem16814 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem16825 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16826 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem16825 b) (@lem16813 a h1)). Qed.
Lemma lem16827 (b : Prop) : (term4 b) = (term5 b).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem16828 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16829 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = (term5 b)).
Proof. exact (MK_COMB (@lem16828 b a) (@lem16827 b)). Qed.
Lemma lem16830 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16832 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem16831) (@lem16830 a b)). Qed.
Lemma lem16833 (b : Prop) : (term5 b) = (term5 b).
Proof. exact (eq_refl (term5 b)). Qed.
Lemma lem16834 (a : Prop) (b : Prop) : ((term3 b a) = (term5 b)) = ((term7 a b) = (term5 b)).
Proof. exact (MK_COMB (@lem16832 a b) (@lem16833 b)). Qed.
Lemma lem16835 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term7 a b) = (term5 b)).
Proof. exact (TRANS (@lem16829 a b) (@lem16834 a b)). Qed.
Lemma lem16836 (b : Prop) (a : Prop) (h1 : a = True) : (term7 a b) = (term5 b).
Proof. exact (EQ_MP (@lem16835 a b) (@lem16826 b a h1)). Qed.
Lemma lem16837 (b : Prop) (a : Prop) (h1 : a = True) : (term5 b) = (term7 a b).
Proof. exact (SYM (@lem16836 b a h1)). Qed.
Lemma lem16838 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem16839 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem16838 b) (@lem16814 a h1)). Qed.
Lemma lem16840 (b : Prop) : (term9 b) = (term10 b).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem16841 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem16842 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = (term10 b)).
Proof. exact (MK_COMB (@lem16841 b a) (@lem16840 b)). Qed.
Lemma lem16843 (a : Prop) (b : Prop) : (term3 b a) = (term7 a b).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem16844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16845 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem16844) (@lem16843 a b)). Qed.
Lemma lem16846 (b : Prop) : (term10 b) = (term10 b).
Proof. exact (eq_refl (term10 b)). Qed.
Lemma lem16847 (a : Prop) (b : Prop) : ((term3 b a) = (term10 b)) = ((term7 a b) = (term10 b)).
Proof. exact (MK_COMB (@lem16845 a b) (@lem16846 b)). Qed.
Lemma lem16848 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term7 a b) = (term10 b)).
Proof. exact (TRANS (@lem16842 a b) (@lem16847 a b)). Qed.
Lemma lem16849 (b : Prop) (a : Prop) (h1 : a = False) : (term7 a b) = (term10 b).
Proof. exact (EQ_MP (@lem16848 a b) (@lem16839 b a h1)). Qed.
Lemma lem16850 (b : Prop) (a : Prop) (h1 : a = False) : (term10 b) = (term7 a b).
Proof. exact (SYM (@lem16849 b a h1)). Qed.
Lemma lem16858 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16860 : term11 = (@eq Prop False).
Proof. exact (MK_COMB (@lem16859) (@lem16858)). Qed.
Lemma lem16861 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem16862 (b : Prop) : ((~ True) = (~ b)) = (False = (~ b)).
Proof. exact (MK_COMB (@lem16860) (@lem16861 b)). Qed.
Lemma lem16864 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem16865 (b : Prop) : (False = (~ b)) = (term12 b).
Proof. exact (@lem16864 (~ b)). Qed.
Lemma lem16867 (t : Prop) : (term12 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem16868 (b : Prop) : (term12 b) = b.
Proof. exact (@lem16867 b). Qed.
Lemma lem16869 (b : Prop) : (False = (~ b)) = b.
Proof. exact (TRANS (@lem16865 b) (@lem16868 b)). Qed.
Lemma lem16870 (b : Prop) : ((~ True) = (~ b)) = b.
Proof. exact (TRANS (@lem16862 b) (@lem16869 b)). Qed.
Lemma lem16871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16872 (b : Prop) : (term13 b) = (imp b).
Proof. exact (MK_COMB (@lem16871) (@lem16870 b)). Qed.
Lemma lem16874 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem16875 (b : Prop) : (True = b) = b.
Proof. exact (@lem16874 b). Qed.
Lemma lem16876 (b : Prop) : (term5 b) = (b -> b).
Proof. exact (MK_COMB (@lem16872 b) (@lem16875 b)). Qed.
Lemma lem16878 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem16879 (b : Prop) : (b -> b) = True.
Proof. exact (@lem16878 b). Qed.
Lemma lem16880 (b : Prop) : (term5 b) = True.
Proof. exact (TRANS (@lem16876 b) (@lem16879 b)). Qed.
Lemma lem16881 (b : Prop) : True = (term5 b).
Proof. exact (SYM (@lem16880 b)). Qed.
Lemma lem16882 (b : Prop) : term5 b.
Proof. exact (EQ_MP (@lem16881 b) (@lem0)). Qed.
Lemma lem16890 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem16891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16892 : term14 = (@eq Prop True).
Proof. exact (MK_COMB (@lem16891) (@lem16890)). Qed.
Lemma lem16893 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem16894 (b : Prop) : ((~ False) = (~ b)) = (True = (~ b)).
Proof. exact (MK_COMB (@lem16892) (@lem16893 b)). Qed.
Lemma lem16896 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem16897 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem16896 (~ b)). Qed.
Lemma lem16898 (b : Prop) : ((~ False) = (~ b)) = (~ b).
Proof. exact (TRANS (@lem16894 b) (@lem16897 b)). Qed.
Lemma lem16899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16900 (b : Prop) : (term15 b) = (term16 b).
Proof. exact (MK_COMB (@lem16899) (@lem16898 b)). Qed.
Lemma lem16902 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem16903 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem16902 b). Qed.
Lemma lem16904 (b : Prop) : (term10 b) = (term17 b).
Proof. exact (MK_COMB (@lem16900 b) (@lem16903 b)). Qed.
Lemma lem16906 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem16907 (b : Prop) : (term17 b) = True.
Proof. exact (@lem16906 (~ b)). Qed.
Lemma lem16908 (b : Prop) : (term10 b) = True.
Proof. exact (TRANS (@lem16904 b) (@lem16907 b)). Qed.
Lemma lem16909 (b : Prop) : True = (term10 b).
Proof. exact (SYM (@lem16908 b)). Qed.
Lemma lem16910 (b : Prop) : term10 b.
Proof. exact (EQ_MP (@lem16909 b) (@lem0)). Qed.
Lemma lem16911 (b : Prop) (a : Prop) (h1 : a = False) : term7 a b.
Proof. exact (EQ_MP (@lem16850 b a h1) (@lem16910 b)). Qed.
Lemma lem16912 (b : Prop) (a : Prop) (h1 : a = True) : term7 a b.
Proof. exact (EQ_MP (@lem16837 b a h1) (@lem16882 b)). Qed.
Lemma lem16915 (a : Prop) (b : Prop) : term7 a b.
Proof. exact (or_elim (@lem16812 a) (fun h0 : a = True => @lem16912 b a h0) (fun h0 : a = False => @lem16911 b a h0)). Qed.
Lemma lem16916 (a : Prop) (b : Prop) (h1 : (~ a) = (~ b)) : (~ a) = (~ b).
Proof. exact (h1). Qed.
Lemma lem16917 (a : Prop) (b : Prop) (h1 : (~ a) = (~ b)) : a = b.
Proof. exact (@lem16915 a b (@lem16916 a b h1)). Qed.
