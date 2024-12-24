Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925098_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem7924818 {A : Type'} (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : a = (_103783' a').
Proof. exact (h1). Qed.
Lemma lem7924819 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term0 A tybit0' _103783') : term0 A tybit0' _103783'.
Proof. exact (h1). Qed.
Lemma lem7924820 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term0 A tybit0' _103783') : term1 A tybit0' _103783' a.
Proof. exact (@lem7924819 A tybit0' _103783' h1 a). Qed.
Lemma lem7924821 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) : (term1 A tybit0' _103783' a) = (term2 A tybit0' _103783' a).
Proof. exact (eq_refl (term1 A tybit0' _103783' a)). Qed.
Lemma lem7924822 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term0 A tybit0' _103783') : term2 A tybit0' _103783' a.
Proof. exact (EQ_MP (@lem7924821 A tybit0' _103783' a) (@lem7924820 A a tybit0' _103783' h1)). Qed.
Lemma lem7924823 {A : Type'} (tybit0' : type1331 A) : tybit0' = tybit0'.
Proof. exact (eq_refl tybit0'). Qed.
Lemma lem7924824 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : (tybit0' a) = (term2 A tybit0' _103783' a').
Proof. exact (MK_COMB (@lem7924823 A tybit0') (@lem7924818 A a _103783' a' h1)). Qed.
Lemma lem7924825 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : (term2 A tybit0' _103783' a') = (tybit0' a).
Proof. exact (SYM (@lem7924824 A tybit0' a _103783' a' h1)). Qed.
Lemma lem7924826 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : term0 A tybit0' _103783') (h2 : a = (_103783' a')) : tybit0' a.
Proof. exact (EQ_MP (@lem7924825 A tybit0' a _103783' a' h2) (@lem7924822 A a' tybit0' _103783' h1)). Qed.
Lemma lem7924827 {A : Type'} (a : finite_sum A A) (a' : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term0 A tybit0' _103783') : term3 A _103783' a tybit0' a'.
Proof. exact (fun h0 : a' = (_103783' a) => @lem7924826 A tybit0' a' _103783' a h1 h0). Qed.
Lemma lem7924828 {A : Type'} (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : a = (_103783' a').
Proof. exact (h1). Qed.
Lemma lem7924829 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : term0 A tybit0' _103783') (h2 : a = (_103783' a')) : tybit0' a.
Proof. exact (@lem7924827 A a' a tybit0' _103783' h1 (@lem7924828 A a _103783' a' h2)). Qed.
Lemma lem7924830 {A : Type'} (a : finite_sum A A) (a' : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term0 A tybit0' _103783') : term3 A _103783' a tybit0' a'.
Proof. exact (fun h0 : a' = (_103783' a) => @lem7924829 A tybit0' a' _103783' a h1 h0). Qed.
Lemma lem7924831 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term0 A tybit0' _103783') : term4 A _103783' tybit0' a.
Proof. exact (fun a' : finite_sum A A => @lem7924830 A a' a tybit0' _103783' h1). Qed.
Lemma lem7924832 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term0 A tybit0' _103783') : term5 A _103783' tybit0'.
Proof. exact (fun a : type1676 A => @lem7924831 A a tybit0' _103783' h1). Qed.
Lemma lem7924833 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term5 A _103783' tybit0') : term5 A _103783' tybit0'.
Proof. exact (h1). Qed.
Lemma lem7924834 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term5 A _103783' tybit0') : term6 A tybit0' _103783' a.
Proof. exact (@lem7924833 A _103783' tybit0' h1 (_103783' a)). Qed.
Lemma lem7924835 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) : (term6 A tybit0' _103783' a) = (term7 A tybit0' _103783' a).
Proof. exact (eq_refl (term6 A tybit0' _103783' a)). Qed.
Lemma lem7924836 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term5 A _103783' tybit0') : term7 A tybit0' _103783' a.
Proof. exact (EQ_MP (@lem7924835 A tybit0' _103783' a) (@lem7924834 A a _103783' tybit0' h1)). Qed.
Lemma lem7924837 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term5 A _103783' tybit0') : term8 A tybit0' _103783' a.
Proof. exact (@lem7924836 A a _103783' tybit0' h1 a). Qed.
Lemma lem7924838 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) : (term8 A tybit0' _103783' a) = (term9 A tybit0' _103783' a).
Proof. exact (eq_refl (term8 A tybit0' _103783' a)). Qed.
Lemma lem7924839 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term5 A _103783' tybit0') : term9 A tybit0' _103783' a.
Proof. exact (EQ_MP (@lem7924838 A tybit0' _103783' a) (@lem7924837 A a _103783' tybit0' h1)). Qed.
Lemma lem7924840 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) : (_103783' a) = (_103783' a).
Proof. exact (eq_refl (_103783' a)). Qed.
Lemma lem7924841 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term5 A _103783' tybit0') : term2 A tybit0' _103783' a.
Proof. exact (@lem7924839 A a _103783' tybit0' h1 (@lem7924840 A _103783' a)). Qed.
Lemma lem7924842 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term5 A _103783' tybit0') : term0 A tybit0' _103783'.
Proof. exact (fun a : finite_sum A A => @lem7924841 A a _103783' tybit0' h1). Qed.
Lemma lem7924843 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : term10 A tybit0' _103783'.
Proof. exact (fun h0 : term5 A _103783' tybit0' => @lem7924842 A _103783' tybit0' h0). Qed.
Lemma lem7924844 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : term11 A _103783' tybit0'.
Proof. exact (fun h0 : term0 A tybit0' _103783' => @lem7924832 A tybit0' _103783' h0). Qed.
Lemma lem7924845 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : term12 A tybit0' _103783'.
Proof. exact (conj (@lem7924844 A _103783' tybit0') (@lem7924843 A tybit0' _103783')). Qed.
Lemma lem7924846 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term12 A tybit0' _103783') = ((term0 A tybit0' _103783') = (term5 A _103783' tybit0')).
Proof. exact (@lem32 (term0 A tybit0' _103783') (term5 A _103783' tybit0')). Qed.
Lemma lem7924847 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term0 A tybit0' _103783') = (term5 A _103783' tybit0').
Proof. exact (EQ_MP (@lem7924846 A _103783' tybit0') (@lem7924845 A tybit0' _103783')). Qed.
Lemma lem7924848 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) (h1 : term4 A _103783' tybit0' a) : term4 A _103783' tybit0' a.
Proof. exact (h1). Qed.
Lemma lem7924849 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (a' : type1676 A) (h1 : term4 A _103783' tybit0' a') : term13 A _103783' tybit0' a' a.
Proof. exact (@lem7924848 A _103783' tybit0' a' h1 a). Qed.
Lemma lem7924850 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) (tybit0' : type1331 A) (a' : type1676 A) : (term13 A _103783' tybit0' a' a) = (term3 A _103783' a tybit0' a').
Proof. exact (eq_refl (term13 A _103783' tybit0' a' a)). Qed.
Lemma lem7924851 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (a' : type1676 A) (h1 : term4 A _103783' tybit0' a') : term3 A _103783' a tybit0' a'.
Proof. exact (EQ_MP (@lem7924850 A _103783' a tybit0' a') (@lem7924849 A a _103783' tybit0' a' h1)). Qed.
Lemma lem7924852 {A : Type'} (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : a = (_103783' a').
Proof. exact (h1). Qed.
Lemma lem7924853 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : term4 A _103783' tybit0' a) (h2 : a = (_103783' a')) : tybit0' a.
Proof. exact (@lem7924851 A a' _103783' tybit0' a h1 (@lem7924852 A a _103783' a' h2)). Qed.
Lemma lem7924854 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : term14 A _103783' tybit0' a.
Proof. exact (fun h0 : term4 A _103783' tybit0' a => @lem7924853 A tybit0' a _103783' a' h0 h1). Qed.
Lemma lem7924855 {A : Type'} (a : type1676 A) (_103783' : type45 A) (h1 : term15 A a _103783') : term15 A a _103783'.
Proof. exact (h1). Qed.
Lemma lem7924856 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term15 A a _103783') : term14 A _103783' tybit0' a.
Proof. exact (ex_elim (@lem7924855 A a _103783' h1) (fun a' : finite_sum A A => fun h0 : term16 A a _103783' a' => @lem7924854 A tybit0' a _103783' a' h0)). Qed.
Lemma lem7924857 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) (h1 : term4 A _103783' tybit0' a) : term4 A _103783' tybit0' a.
Proof. exact (h1). Qed.
Lemma lem7924858 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term4 A _103783' tybit0' a) (h2 : term15 A a _103783') : tybit0' a.
Proof. exact (@lem7924856 A tybit0' a _103783' h2 (@lem7924857 A _103783' tybit0' a h1)). Qed.
Lemma lem7924859 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) (h1 : term4 A _103783' tybit0' a) : term17 A _103783' tybit0' a.
Proof. exact (fun h0 : term15 A a _103783' => @lem7924858 A tybit0' a _103783' h1 h0). Qed.
Lemma lem7924860 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) (h1 : term17 A _103783' tybit0' a) : term17 A _103783' tybit0' a.
Proof. exact (h1). Qed.
Lemma lem7924861 {A : Type'} (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : a = (_103783' a').
Proof. exact (h1). Qed.
Lemma lem7924862 {A : Type'} (a : type1676 A) (_103783' : type45 A) (a' : finite_sum A A) (h1 : a = (_103783' a')) : term15 A a _103783'.
Proof. exact (ex_intro (term16 A a _103783') a' (@lem7924861 A a _103783' a' h1)). Qed.
Lemma lem7924863 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (a' : type1676 A) (h1 : a' = (_103783' a)) (h2 : term17 A _103783' tybit0' a') : tybit0' a'.
Proof. exact (@lem7924860 A _103783' tybit0' a' h2 (@lem7924862 A a' _103783' a h1)). Qed.
Lemma lem7924864 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (tybit0' : type1331 A) (a' : type1676 A) (h1 : term17 A _103783' tybit0' a') : term3 A _103783' a tybit0' a'.
Proof. exact (fun h0 : a' = (_103783' a) => @lem7924863 A a _103783' tybit0' a' h0 h1). Qed.
Lemma lem7924865 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) (h1 : term17 A _103783' tybit0' a) : term4 A _103783' tybit0' a.
Proof. exact (fun a' : finite_sum A A => @lem7924864 A a' _103783' tybit0' a h1). Qed.
Lemma lem7924866 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : term18 A _103783' tybit0' a.
Proof. exact (fun h0 : term17 A _103783' tybit0' a => @lem7924865 A _103783' tybit0' a h0). Qed.
Lemma lem7924867 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : term19 A _103783' tybit0' a.
Proof. exact (fun h0 : term4 A _103783' tybit0' a => @lem7924859 A _103783' tybit0' a h0). Qed.
Lemma lem7924868 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : term20 A _103783' tybit0' a.
Proof. exact (conj (@lem7924867 A _103783' tybit0' a) (@lem7924866 A _103783' tybit0' a)). Qed.
Lemma lem7924869 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term20 A _103783' tybit0' a) = ((term4 A _103783' tybit0' a) = (term17 A _103783' tybit0' a)).
Proof. exact (@lem32 (term4 A _103783' tybit0' a) (term17 A _103783' tybit0' a)). Qed.
Lemma lem7924870 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term4 A _103783' tybit0' a) = (term17 A _103783' tybit0' a).
Proof. exact (EQ_MP (@lem7924869 A _103783' tybit0' a) (@lem7924868 A _103783' tybit0' a)). Qed.
Lemma lem7924871 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term21 A _103783' tybit0') = (term22 A _103783' tybit0').
Proof. exact (fun_ext (fun a : type1676 A => @lem7924870 A _103783' tybit0' a)). Qed.
Lemma lem7924872 {A : Type'} : (@all (recspace (finite_sum A A))) = (@all (recspace (finite_sum A A))).
Proof. exact (eq_refl (@all (recspace (finite_sum A A)))). Qed.
Lemma lem7924873 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term5 A _103783' tybit0') = (term23 A _103783' tybit0').
Proof. exact (MK_COMB (@lem7924872 A) (@lem7924871 A _103783' tybit0')). Qed.
Lemma lem7924874 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term0 A tybit0' _103783') = (term23 A _103783' tybit0').
Proof. exact (TRANS (@lem7924847 A _103783' tybit0') (@lem7924873 A _103783' tybit0')). Qed.
Lemma lem7924876 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem7924877 (x : Prop) : (x = x) = True.
Proof. exact (@lem7924876 Prop x). Qed.
Lemma lem7924878 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : ((term23 A _103783' tybit0') = (term23 A _103783' tybit0')) = True.
Proof. exact (@lem7924877 (term23 A _103783' tybit0')). Qed.
Lemma lem7924879 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : True = ((term23 A _103783' tybit0') = (term23 A _103783' tybit0')).
Proof. exact (SYM (@lem7924878 A _103783' tybit0')). Qed.
Lemma lem7924880 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term23 A _103783' tybit0') = (term23 A _103783' tybit0').
Proof. exact (EQ_MP (@lem7924879 A _103783' tybit0') (@lem0)). Qed.
Lemma lem7924881 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term0 A tybit0' _103783') = (term23 A _103783' tybit0').
Proof. exact (TRANS (@lem7924874 A _103783' tybit0') (@lem7924880 A _103783' tybit0')). Qed.
Lemma lem7924882 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (h1). Qed.
Lemma lem7924883 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term24 A _103783' tybit0' a.
Proof. exact (@lem7924882 A _103783' tybit0' h1 a). Qed.
Lemma lem7924884 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term24 A _103783' tybit0' a) = (term17 A _103783' tybit0' a).
Proof. exact (eq_refl (term24 A _103783' tybit0' a)). Qed.
Lemma lem7924885 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term17 A _103783' tybit0' a.
Proof. exact (EQ_MP (@lem7924884 A _103783' tybit0' a) (@lem7924883 A a _103783' tybit0' h1)). Qed.
Lemma lem7924886 {A : Type'} (a : type1676 A) (_103783' : type45 A) (h1 : term15 A a _103783') : term15 A a _103783'.
Proof. exact (h1). Qed.
Lemma lem7924887 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : term15 A a _103783') : tybit0' a.
Proof. exact (@lem7924885 A a _103783' tybit0' h1 (@lem7924886 A a _103783' h2)). Qed.
Lemma lem7924888 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term15 A a _103783') : term25 A _103783' tybit0' a.
Proof. exact (fun h0 : term23 A _103783' tybit0' => @lem7924887 A tybit0' a _103783' h0 h1). Qed.
Lemma lem7924889 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (h1). Qed.
Lemma lem7924890 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : term15 A a _103783') : tybit0' a.
Proof. exact (@lem7924888 A tybit0' a _103783' h2 (@lem7924889 A _103783' tybit0' h1)). Qed.
Lemma lem7924891 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term17 A _103783' tybit0' a.
Proof. exact (fun h0 : term15 A a _103783' => @lem7924890 A tybit0' a _103783' h1 h0). Qed.
Lemma lem7924892 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (fun a : type1676 A => @lem7924891 A a _103783' tybit0' h1). Qed.
Lemma lem7924893 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (h1). Qed.
Lemma lem7924894 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term24 A _103783' tybit0' a.
Proof. exact (@lem7924893 A _103783' tybit0' h1 a). Qed.
Lemma lem7924895 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term24 A _103783' tybit0' a) = (term17 A _103783' tybit0' a).
Proof. exact (eq_refl (term24 A _103783' tybit0' a)). Qed.
Lemma lem7924896 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term17 A _103783' tybit0' a.
Proof. exact (EQ_MP (@lem7924895 A _103783' tybit0' a) (@lem7924894 A a _103783' tybit0' h1)). Qed.
Lemma lem7924897 {A : Type'} (a : type1676 A) (_103783' : type45 A) (h1 : term15 A a _103783') : term15 A a _103783'.
Proof. exact (h1). Qed.
Lemma lem7924898 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : term15 A a _103783') : tybit0' a.
Proof. exact (@lem7924896 A a _103783' tybit0' h1 (@lem7924897 A a _103783' h2)). Qed.
Lemma lem7924899 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term15 A a _103783') : term25 A _103783' tybit0' a.
Proof. exact (fun h0 : term23 A _103783' tybit0' => @lem7924898 A tybit0' a _103783' h0 h1). Qed.
Lemma lem7924900 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (h1). Qed.
Lemma lem7924901 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : term15 A a _103783') : tybit0' a.
Proof. exact (@lem7924899 A tybit0' a _103783' h2 (@lem7924900 A _103783' tybit0' h1)). Qed.
Lemma lem7924902 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term17 A _103783' tybit0' a.
Proof. exact (fun h0 : term15 A a _103783' => @lem7924901 A tybit0' a _103783' h1 h0). Qed.
Lemma lem7924903 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (fun a : type1676 A => @lem7924902 A a _103783' tybit0' h1). Qed.
Lemma lem7924904 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : term26 A _103783' tybit0'.
Proof. exact (fun h0 : term23 A _103783' tybit0' => @lem7924903 A _103783' tybit0' h0). Qed.
Lemma lem7924905 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : term26 A _103783' tybit0'.
Proof. exact (fun h0 : term23 A _103783' tybit0' => @lem7924892 A _103783' tybit0' h0). Qed.
Lemma lem7924906 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : term27 A _103783' tybit0'.
Proof. exact (conj (@lem7924905 A _103783' tybit0') (@lem7924904 A _103783' tybit0')). Qed.
Lemma lem7924907 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term27 A _103783' tybit0') = ((term23 A _103783' tybit0') = (term23 A _103783' tybit0')).
Proof. exact (@lem32 (term23 A _103783' tybit0') (term23 A _103783' tybit0')). Qed.
Lemma lem7924908 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term23 A _103783' tybit0') = (term23 A _103783' tybit0').
Proof. exact (EQ_MP (@lem7924907 A _103783' tybit0') (@lem7924906 A _103783' tybit0')). Qed.
Lemma lem7924909 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term0 A tybit0' _103783') = (term23 A _103783' tybit0').
Proof. exact (TRANS (@lem7924881 A _103783' tybit0') (@lem7924908 A _103783' tybit0')). Qed.
Lemma lem7924910 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term23 A _103783' tybit0') = (term0 A tybit0' _103783').
Proof. exact (SYM (@lem7924909 A _103783' tybit0')). Qed.
Lemma lem7924911 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : tybit0' = (term28 A _103783').
Proof. exact (h1). Qed.
Lemma lem7924912 {A : Type'} (a : type1676 A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7924913 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : (tybit0' a) = (term29 A _103783' a).
Proof. exact (MK_COMB (@lem7924911 A tybit0' _103783' h1) (@lem7924912 A a)). Qed.
Lemma lem7924914 {A : Type'} (_103783' : type45 A) (a : type1676 A) : (term29 A _103783' a) = (term30 A _103783' a).
Proof. exact (eq_refl (term29 A _103783' a)). Qed.
Lemma lem7924915 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) : (term31 A tybit0' a) = (term31 A tybit0' a).
Proof. exact (eq_refl (term31 A tybit0' a)). Qed.
Lemma lem7924916 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : type1676 A) : ((tybit0' a) = (term29 A _103783' a)) = ((tybit0' a) = (term30 A _103783' a)).
Proof. exact (MK_COMB (@lem7924915 A tybit0' a) (@lem7924914 A _103783' a)). Qed.
Lemma lem7924917 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : (tybit0' a) = (term30 A _103783' a).
Proof. exact (EQ_MP (@lem7924916 A tybit0' _103783' a) (@lem7924913 A a tybit0' _103783' h1)). Qed.
Lemma lem7924918 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term32 A tybit0' _103783'.
Proof. exact (fun a : type1676 A => @lem7924917 A a tybit0' _103783' h1). Qed.
Lemma lem7924919 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term33 A tybit0' _103783' a.
Proof. exact (@lem7924918 A tybit0' _103783' h1 a). Qed.
Lemma lem7924920 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : type1676 A) : (term33 A tybit0' _103783' a) = ((tybit0' a) = (term30 A _103783' a)).
Proof. exact (eq_refl (term33 A tybit0' _103783' a)). Qed.
Lemma lem7924921 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : (tybit0' a) = (term30 A _103783' a).
Proof. exact (EQ_MP (@lem7924920 A tybit0' _103783' a) (@lem7924919 A a tybit0' _103783' h1)). Qed.
Lemma lem7924924 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : type1676 A) : term34 A tybit0' _103783' a.
Proof. exact (@lem37 (tybit0' a) (term30 A _103783' a)). Qed.
Lemma lem7924925 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term35 A tybit0' _103783' a.
Proof. exact (@lem7924924 A tybit0' _103783' a (@lem7924921 A a tybit0' _103783' h1)). Qed.
Lemma lem7924926 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (h1 : tybit0' a) : tybit0' a.
Proof. exact (h1). Qed.
Lemma lem7924927 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' a) (h2 : tybit0' = (term28 A _103783')) : term30 A _103783' a.
Proof. exact (@lem7924925 A a tybit0' _103783' h2 (@lem7924926 A tybit0' a h1)). Qed.
Lemma lem7924928 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : tybit0'' a) (h2 : tybit0'' = (term28 A _103783')) : term36 A _103783' a tybit0'.
Proof. exact (@lem7924927 A a tybit0'' _103783' h1 h2 tybit0'). Qed.
Lemma lem7924929 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term36 A _103783' a tybit0') = (term25 A _103783' tybit0' a).
Proof. exact (eq_refl (term36 A _103783' a tybit0')). Qed.
Lemma lem7924930 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : tybit0'' a) (h2 : tybit0'' = (term28 A _103783')) : term25 A _103783' tybit0' a.
Proof. exact (EQ_MP (@lem7924929 A _103783' tybit0' a) (@lem7924928 A tybit0' a tybit0'' _103783' h1 h2)). Qed.
Lemma lem7924931 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (h1). Qed.
Lemma lem7924932 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : tybit0'' a) (h3 : tybit0'' = (term28 A _103783')) : tybit0' a.
Proof. exact (@lem7924930 A tybit0' a tybit0'' _103783' h2 h3 (@lem7924931 A _103783' tybit0' h1)). Qed.
Lemma lem7924933 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : tybit0'' = (term28 A _103783')) : term37 A tybit0'' tybit0' a.
Proof. exact (fun h0 : tybit0'' a => @lem7924932 A tybit0' a tybit0'' _103783' h1 h0 h2). Qed.
Lemma lem7924934 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : tybit0'' = (term28 A _103783')) : term38 A tybit0'' tybit0'.
Proof. exact (fun a : type1676 A => @lem7924933 A a tybit0' tybit0'' _103783' h1 h2). Qed.
Lemma lem7924935 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : tybit0'' = (term28 A _103783')) : term39 A _103783' tybit0'' tybit0'.
Proof. exact (fun h0 : term23 A _103783' tybit0' => @lem7924934 A tybit0' tybit0'' _103783' h0 h1). Qed.
Lemma lem7924936 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term40 A _103783' tybit0'.
Proof. exact (fun tybit0'' : type1331 A => @lem7924935 A tybit0'' tybit0' _103783' h1). Qed.
Lemma lem7924937 {A : Type'} (_103783' : type45 A) (h1 : term41 A _103783') : term41 A _103783'.
Proof. exact (h1). Qed.
Lemma lem7924938 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term23 A _103783' tybit0'.
Proof. exact (h1). Qed.
Lemma lem7924939 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : tybit0'' = (term28 A _103783')) : term42 A _103783' tybit0'' tybit0'.
Proof. exact (@lem7924936 A tybit0'' _103783' h1 tybit0'). Qed.
Lemma lem7924940 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (tybit0'' : type1331 A) : (term42 A _103783' tybit0' tybit0'') = (term39 A _103783' tybit0' tybit0'').
Proof. exact (eq_refl (term42 A _103783' tybit0' tybit0'')). Qed.
Lemma lem7924941 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : tybit0'' = (term28 A _103783')) : term39 A _103783' tybit0'' tybit0'.
Proof. exact (EQ_MP (@lem7924940 A _103783' tybit0'' tybit0') (@lem7924939 A tybit0' tybit0'' _103783' h1)). Qed.
Lemma lem7924942 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term23 A _103783' tybit0') (h2 : tybit0'' = (term28 A _103783')) : term38 A tybit0'' tybit0'.
Proof. exact (@lem7924941 A tybit0' tybit0'' _103783' h2 (@lem7924938 A _103783' tybit0' h1)). Qed.
Lemma lem7924943 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') : term43 A _103783' tybit0'.
Proof. exact (@lem7924937 A _103783' h1 tybit0'). Qed.
Lemma lem7924944 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term43 A _103783' tybit0') = (term44 A tybit0' _103783').
Proof. exact (eq_refl (term43 A _103783' tybit0')). Qed.
Lemma lem7924945 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') : term44 A tybit0' _103783'.
Proof. exact (EQ_MP (@lem7924944 A tybit0' _103783') (@lem7924943 A tybit0' _103783' h1)). Qed.
Lemma lem7924946 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') : term45 A tybit0' _103783' tybit0''.
Proof. exact (@lem7924945 A tybit0' _103783' h1 tybit0''). Qed.
Lemma lem7924947 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) : (term45 A tybit0' _103783' tybit0'') = (term46 A tybit0' tybit0'' _103783').
Proof. exact (eq_refl (term45 A tybit0' _103783' tybit0'')). Qed.
Lemma lem7924948 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') : term46 A tybit0' tybit0'' _103783'.
Proof. exact (EQ_MP (@lem7924947 A tybit0' tybit0'' _103783') (@lem7924946 A tybit0' tybit0'' _103783' h1)). Qed.
Lemma lem7924949 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term23 A _103783' tybit0') (h3 : tybit0'' = (term28 A _103783')) : term47 A _103783'.
Proof. exact (@lem7924948 A tybit0'' tybit0' _103783' h1 (@lem7924942 A tybit0' tybit0'' _103783' h2 h3)). Qed.
Lemma lem7924950 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term24 A _103783' tybit0' a.
Proof. exact (@lem7924938 A _103783' tybit0' h1 a). Qed.
Lemma lem7924951 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term24 A _103783' tybit0' a) = (term17 A _103783' tybit0' a).
Proof. exact (eq_refl (term24 A _103783' tybit0' a)). Qed.
Lemma lem7924952 {A : Type'} (a : type1676 A) (_103783' : type45 A) (tybit0' : type1331 A) (h1 : term23 A _103783' tybit0') : term17 A _103783' tybit0' a.
Proof. exact (EQ_MP (@lem7924951 A _103783' tybit0' a) (@lem7924950 A a _103783' tybit0' h1)). Qed.
Lemma lem7924953 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term23 A _103783' tybit0') (h3 : tybit0'' = (term28 A _103783')) : term48 A _103783' a.
Proof. exact (@lem7924949 A tybit0' tybit0'' _103783' h1 h2 h3 a). Qed.
Lemma lem7924954 {A : Type'} (a : type1676 A) (_103783' : type45 A) : (term48 A _103783' a) = (term49 A a _103783').
Proof. exact (eq_refl (term48 A _103783' a)). Qed.
Lemma lem7924955 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term23 A _103783' tybit0') (h3 : tybit0'' = (term28 A _103783')) : term49 A a _103783'.
Proof. exact (EQ_MP (@lem7924954 A a _103783') (@lem7924953 A a tybit0' tybit0'' _103783' h1 h2 h3)). Qed.
Lemma lem7924956 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : term50 A _103783' tybit0' a.
Proof. exact (@lem51 (term15 A a _103783') (term15 A a _103783') (tybit0' a)). Qed.
Lemma lem7924957 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term23 A _103783' tybit0') (h3 : tybit0'' = (term28 A _103783')) : term51 A _103783' tybit0' a.
Proof. exact (@lem7924956 A _103783' tybit0' a (@lem7924955 A a tybit0' tybit0'' _103783' h1 h2 h3)). Qed.
Lemma lem7924958 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term23 A _103783' tybit0') (h3 : tybit0'' = (term28 A _103783')) : term17 A _103783' tybit0' a.
Proof. exact (@lem7924957 A a tybit0' tybit0'' _103783' h1 h2 h3 (@lem7924952 A a _103783' tybit0' h2)). Qed.
Lemma lem7924959 {A : Type'} (a : type1676 A) (_103783' : type45 A) (h1 : term15 A a _103783') : term15 A a _103783'.
Proof. exact (h1). Qed.
Lemma lem7924960 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term23 A _103783' tybit0') (h3 : term15 A a _103783') (h4 : tybit0'' = (term28 A _103783')) : tybit0' a.
Proof. exact (@lem7924958 A a tybit0' tybit0'' _103783' h1 h2 h4 (@lem7924959 A a _103783' h3)). Qed.
Lemma lem7924961 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (tybit0'' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term15 A a _103783') (h3 : tybit0'' = (term28 A _103783')) : term25 A _103783' tybit0' a.
Proof. exact (fun h0 : term23 A _103783' tybit0' => @lem7924960 A tybit0' a tybit0'' _103783' h1 h0 h2 h3). Qed.
Lemma lem7924962 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term15 A a _103783') (h3 : tybit0' = (term28 A _103783')) : term30 A _103783' a.
Proof. exact (fun tybit0'' : type1331 A => @lem7924961 A tybit0'' a tybit0' _103783' h1 h2 h3). Qed.
Lemma lem7924963 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term33 A tybit0' _103783' a.
Proof. exact (@lem7924918 A tybit0' _103783' h1 a). Qed.
Lemma lem7924964 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : type1676 A) : (term33 A tybit0' _103783' a) = ((tybit0' a) = (term30 A _103783' a)).
Proof. exact (eq_refl (term33 A tybit0' _103783' a)). Qed.
Lemma lem7924965 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : (tybit0' a) = (term30 A _103783' a).
Proof. exact (EQ_MP (@lem7924964 A tybit0' _103783' a) (@lem7924963 A a tybit0' _103783' h1)). Qed.
Lemma lem7924966 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : (term30 A _103783' a) = (tybit0' a).
Proof. exact (SYM (@lem7924965 A a tybit0' _103783' h1)). Qed.
Lemma lem7924967 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : term15 A a _103783') (h3 : tybit0' = (term28 A _103783')) : tybit0' a.
Proof. exact (EQ_MP (@lem7924966 A a tybit0' _103783' h3) (@lem7924962 A a tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7924968 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term17 A _103783' tybit0' a.
Proof. exact (fun h0 : term15 A a _103783' => @lem7924967 A a tybit0' _103783' h1 h0 h2). Qed.
Lemma lem7924969 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term23 A _103783' tybit0'.
Proof. exact (fun a : type1676 A => @lem7924968 A a tybit0' _103783' h1 h2). Qed.
Lemma lem7924972 {A : Type'} (_103783' : type45 A) (a : type1676 A) : (term52 A _103783' a) = (term52 A _103783' a).
Proof. exact (eq_refl (term52 A _103783' a)). Qed.
Lemma lem7924973 {A : Type'} (a : type1676 A) (_103783' : type45 A) : (term52 A _103783' a) = (term15 A a _103783').
Proof. exact (eq_refl (term52 A _103783' a)). Qed.
Lemma lem7924974 {A : Type'} (_103783' : type45 A) (a : type1676 A) : (term53 A _103783' a) = (term53 A _103783' a).
Proof. exact (eq_refl (term53 A _103783' a)). Qed.
Lemma lem7924975 {A : Type'} (a : type1676 A) (_103783' : type45 A) : ((term52 A _103783' a) = (term52 A _103783' a)) = ((term52 A _103783' a) = (term15 A a _103783')).
Proof. exact (MK_COMB (@lem7924974 A _103783' a) (@lem7924973 A a _103783')). Qed.
Lemma lem7924976 {A : Type'} (a : type1676 A) (_103783' : type45 A) : (term52 A _103783' a) = (term15 A a _103783').
Proof. exact (EQ_MP (@lem7924975 A a _103783') (@lem7924972 A _103783' a)). Qed.
Lemma lem7924977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7924978 {A : Type'} (a : type1676 A) (_103783' : type45 A) : (term54 A _103783' a) = (term55 A a _103783').
Proof. exact (MK_COMB (@lem7924977) (@lem7924976 A a _103783')). Qed.
Lemma lem7924979 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) : (tybit0' a) = (tybit0' a).
Proof. exact (eq_refl (tybit0' a)). Qed.
Lemma lem7924980 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term56 A _103783' tybit0' a) = (term17 A _103783' tybit0' a).
Proof. exact (MK_COMB (@lem7924978 A a _103783') (@lem7924979 A tybit0' a)). Qed.
Lemma lem7924981 {A : Type'} (a : type1676 A) (_103783' : type45 A) : (term55 A a _103783') = (term55 A a _103783').
Proof. exact (eq_refl (term55 A a _103783')). Qed.
Lemma lem7924982 {A : Type'} (a : type1676 A) (_103783' : type45 A) : (term57 A _103783' a) = (term49 A a _103783').
Proof. exact (MK_COMB (@lem7924981 A a _103783') (@lem7924976 A a _103783')). Qed.
Lemma lem7924983 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) : (term58 A tybit0' a) = (term58 A tybit0' a).
Proof. exact (eq_refl (term58 A tybit0' a)). Qed.
Lemma lem7924984 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) : (term59 A tybit0' _103783' a) = (term60 A tybit0' a _103783').
Proof. exact (MK_COMB (@lem7924983 A tybit0' a) (@lem7924976 A a _103783')). Qed.
Lemma lem7924985 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term61 A tybit0' _103783') = (term62 A tybit0' _103783').
Proof. exact (fun_ext (fun a : type1676 A => @lem7924984 A tybit0' a _103783')). Qed.
Lemma lem7924986 {A : Type'} : (@all (recspace (finite_sum A A))) = (@all (recspace (finite_sum A A))).
Proof. exact (eq_refl (@all (recspace (finite_sum A A)))). Qed.
Lemma lem7924987 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term63 A tybit0' _103783') = (term64 A tybit0' _103783').
Proof. exact (MK_COMB (@lem7924986 A) (@lem7924985 A tybit0' _103783')). Qed.
Lemma lem7924988 {A : Type'} (_103783' : type45 A) : (term65 A _103783') = (term66 A _103783').
Proof. exact (fun_ext (fun a : type1676 A => @lem7924982 A a _103783')). Qed.
Lemma lem7924989 {A : Type'} : (@all (recspace (finite_sum A A))) = (@all (recspace (finite_sum A A))).
Proof. exact (eq_refl (@all (recspace (finite_sum A A)))). Qed.
Lemma lem7924990 {A : Type'} (_103783' : type45 A) : (term67 A _103783') = (term47 A _103783').
Proof. exact (MK_COMB (@lem7924989 A) (@lem7924988 A _103783')). Qed.
Lemma lem7924991 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term68 A _103783' tybit0') = (term22 A _103783' tybit0').
Proof. exact (fun_ext (fun a : type1676 A => @lem7924980 A _103783' tybit0' a)). Qed.
Lemma lem7924992 {A : Type'} : (@all (recspace (finite_sum A A))) = (@all (recspace (finite_sum A A))).
Proof. exact (eq_refl (@all (recspace (finite_sum A A)))). Qed.
Lemma lem7924993 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term69 A _103783' tybit0') = (term23 A _103783' tybit0').
Proof. exact (MK_COMB (@lem7924992 A) (@lem7924991 A _103783' tybit0')). Qed.
Lemma lem7924994 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term23 A _103783' tybit0') = (term69 A _103783' tybit0').
Proof. exact (SYM (@lem7924993 A _103783' tybit0')). Qed.
Lemma lem7924995 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term69 A _103783' tybit0'.
Proof. exact (EQ_MP (@lem7924994 A _103783' tybit0') (@lem7924969 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7924996 {A : Type'} (_103783' : type45 A) (h1 : term41 A _103783') : term70 A _103783'.
Proof. exact (@lem7924937 A _103783' h1 (term71 A _103783')). Qed.
Lemma lem7924997 {A : Type'} (_103783' : type45 A) : (term70 A _103783') = (term72 A _103783').
Proof. exact (eq_refl (term70 A _103783')). Qed.
Lemma lem7924998 {A : Type'} (_103783' : type45 A) (h1 : term41 A _103783') : term72 A _103783'.
Proof. exact (EQ_MP (@lem7924997 A _103783') (@lem7924996 A _103783' h1)). Qed.
Lemma lem7924999 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') : term73 A _103783' tybit0'.
Proof. exact (@lem7924998 A _103783' h1 tybit0'). Qed.
Lemma lem7925000 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term73 A _103783' tybit0') = (term74 A tybit0' _103783').
Proof. exact (eq_refl (term73 A _103783' tybit0')). Qed.
Lemma lem7925001 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') : term74 A tybit0' _103783'.
Proof. exact (EQ_MP (@lem7925000 A tybit0' _103783') (@lem7924999 A tybit0' _103783' h1)). Qed.
Lemma lem7925002 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term47 A _103783'.
Proof. exact (@lem7925001 A tybit0' _103783' h1 (@lem7924995 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925003 {A : Type'} (_103783' : type45 A) : (term47 A _103783') = (term67 A _103783').
Proof. exact (SYM (@lem7924990 A _103783')). Qed.
Lemma lem7925004 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term67 A _103783'.
Proof. exact (EQ_MP (@lem7925003 A _103783') (@lem7925002 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925005 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term75 A tybit0' _103783'.
Proof. exact (@lem7924936 A tybit0' _103783' h1 (term71 A _103783')). Qed.
Lemma lem7925006 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term75 A tybit0' _103783') = (term76 A tybit0' _103783').
Proof. exact (eq_refl (term75 A tybit0' _103783')). Qed.
Lemma lem7925007 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term76 A tybit0' _103783'.
Proof. exact (EQ_MP (@lem7925006 A tybit0' _103783') (@lem7925005 A tybit0' _103783' h1)). Qed.
Lemma lem7925008 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term63 A tybit0' _103783'.
Proof. exact (@lem7925007 A tybit0' _103783' h2 (@lem7925004 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925009 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term64 A tybit0' _103783'.
Proof. exact (EQ_MP (@lem7924987 A tybit0' _103783') (@lem7925008 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925010 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term24 A _103783' tybit0' a.
Proof. exact (@lem7924969 A tybit0' _103783' h1 h2 a). Qed.
Lemma lem7925011 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (a : type1676 A) : (term24 A _103783' tybit0' a) = (term17 A _103783' tybit0' a).
Proof. exact (eq_refl (term24 A _103783' tybit0' a)). Qed.
Lemma lem7925012 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term17 A _103783' tybit0' a.
Proof. exact (EQ_MP (@lem7925011 A _103783' tybit0' a) (@lem7925010 A a tybit0' _103783' h1 h2)). Qed.
Lemma lem7925013 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term77 A tybit0' _103783' a.
Proof. exact (@lem7925009 A tybit0' _103783' h1 h2 a). Qed.
Lemma lem7925014 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) : (term77 A tybit0' _103783' a) = (term60 A tybit0' a _103783').
Proof. exact (eq_refl (term77 A tybit0' _103783' a)). Qed.
Lemma lem7925015 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term60 A tybit0' a _103783'.
Proof. exact (EQ_MP (@lem7925014 A tybit0' a _103783') (@lem7925013 A a tybit0' _103783' h1 h2)). Qed.
Lemma lem7925016 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term78 A _103783' tybit0' a.
Proof. exact (conj (@lem7925015 A a tybit0' _103783' h1 h2) (@lem7925012 A a tybit0' _103783' h1 h2)). Qed.
Lemma lem7925017 {A : Type'} (tybit0' : type1331 A) (a : type1676 A) (_103783' : type45 A) : (term78 A _103783' tybit0' a) = ((tybit0' a) = (term15 A a _103783')).
Proof. exact (@lem32 (tybit0' a) (term15 A a _103783')). Qed.
Lemma lem7925018 {A : Type'} (a : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : (tybit0' a) = (term15 A a _103783').
Proof. exact (EQ_MP (@lem7925017 A tybit0' a _103783') (@lem7925016 A a tybit0' _103783' h1 h2)). Qed.
Lemma lem7925023 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term23 A _103783' tybit0'.
Proof. exact (fun a : type1676 A => @lem7924968 A a tybit0' _103783' h1 h2). Qed.
Lemma lem7925024 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term79 A tybit0' _103783'.
Proof. exact (fun a : type1676 A => @lem7925018 A a tybit0' _103783' h1 h2). Qed.
Lemma lem7925025 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term40 A _103783' tybit0'.
Proof. exact (fun tybit0'' : type1331 A => @lem7924935 A tybit0'' tybit0' _103783' h2). Qed.
Lemma lem7925026 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term0 A tybit0' _103783'.
Proof. exact (EQ_MP (@lem7924910 A tybit0' _103783') (@lem7925023 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925040 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term23 A _103783' tybit0') = (term0 A tybit0' _103783').
Proof. exact (SYM (@lem7924909 A _103783' tybit0')). Qed.
Lemma lem7925041 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term23 A _103783' tybit0') = (term0 A tybit0' _103783').
Proof. exact (@lem7925040 A tybit0' _103783'). Qed.
Lemma lem7925042 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term23 A _103783' tybit0') = (term0 A tybit0' _103783').
Proof. exact (@lem7925041 A tybit0' _103783'). Qed.
Lemma lem7925043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7925044 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : (term80 A _103783' tybit0') = (term81 A tybit0' _103783').
Proof. exact (MK_COMB (@lem7925043) (@lem7925042 A tybit0' _103783')). Qed.
Lemma lem7925069 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) : (term38 A tybit0' tybit0'') = (term38 A tybit0' tybit0'').
Proof. exact (eq_refl (term38 A tybit0' tybit0'')). Qed.
Lemma lem7925070 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (tybit0'' : type1331 A) : (term39 A _103783' tybit0' tybit0'') = (term82 A _103783' tybit0' tybit0'').
Proof. exact (MK_COMB (@lem7925044 A tybit0'' _103783') (@lem7925069 A tybit0' tybit0'')). Qed.
Lemma lem7925071 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term83 A _103783' tybit0') = (term84 A _103783' tybit0').
Proof. exact (fun_ext (fun tybit0'' : type1331 A => @lem7925070 A _103783' tybit0' tybit0'')). Qed.
Lemma lem7925072 {A : Type'} : (@all ((recspace (finite_sum A A)) -> Prop)) = (@all ((recspace (finite_sum A A)) -> Prop)).
Proof. exact (eq_refl (@all ((recspace (finite_sum A A)) -> Prop))). Qed.
Lemma lem7925073 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) : (term40 A _103783' tybit0') = (term85 A _103783' tybit0').
Proof. exact (MK_COMB (@lem7925072 A) (@lem7925071 A _103783' tybit0')). Qed.
Lemma lem7925074 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term85 A _103783' tybit0'.
Proof. exact (EQ_MP (@lem7925073 A _103783' tybit0') (@lem7925025 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925075 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term86 A tybit0' _103783'.
Proof. exact (conj (@lem7925074 A tybit0' _103783' h1 h2) (@lem7925024 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925076 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term41 A _103783') (h2 : tybit0' = (term28 A _103783')) : term87 A tybit0' _103783'.
Proof. exact (conj (@lem7925026 A tybit0' _103783' h1 h2) (@lem7925075 A tybit0' _103783' h1 h2)). Qed.
Lemma lem7925078 {A : Type'} (a : type1676 A) (_103783' : type45 A) : term88 A a _103783'.
Proof. exact (@lem9120 (term15 A a _103783')). Qed.
Lemma lem7925079 {A : Type'} (a : type1676 A) (_103783' : type45 A) : (term88 A a _103783') = (term49 A a _103783').
Proof. exact (eq_refl (term88 A a _103783')). Qed.
Lemma lem7925080 {A : Type'} (a : type1676 A) (_103783' : type45 A) : term49 A a _103783'.
Proof. exact (EQ_MP (@lem7925079 A a _103783') (@lem7925078 A a _103783')). Qed.
Lemma lem7925085 {A : Type'} (_103783' : type45 A) : term47 A _103783'.
Proof. exact (fun a : type1676 A => @lem7925080 A a _103783'). Qed.
Lemma lem7925086 {A : Type'} (tybit0' : type1331 A) (tybit0'' : type1331 A) (_103783' : type45 A) : term46 A tybit0' tybit0'' _103783'.
Proof. exact (fun h0 : term38 A tybit0' tybit0'' => @lem7925085 A _103783'). Qed.
Lemma lem7925091 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : term44 A tybit0' _103783'.
Proof. exact (fun tybit0'' : type1331 A => @lem7925086 A tybit0' tybit0'' _103783'). Qed.
Lemma lem7925096 {A : Type'} (_103783' : type45 A) : term41 A _103783'.
Proof. exact (fun tybit0' : type1331 A => @lem7925091 A tybit0' _103783'). Qed.
Lemma lem7925097 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : (term41 A _103783') = (term87 A tybit0' _103783').
Proof. exact (prop_ext (fun h2 : term41 A _103783' => @lem7925076 A tybit0' _103783' h2 h1) (fun h2 : term87 A tybit0' _103783' => @lem7925096 A _103783')). Qed.
Lemma lem7925098 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term28 A _103783')) : term87 A tybit0' _103783'.
Proof. exact (EQ_MP (@lem7925097 A tybit0' _103783' h1) (@lem7925096 A _103783')). Qed.
