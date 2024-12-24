Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm14995_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Lemma lem14840 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem14841 (g' : Prop) : (True = g') = g'.
Proof. exact (@lem14840 g'). Qed.
Lemma lem14842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem14843 (g' : Prop) : (term0 g') = (imp g').
Proof. exact (MK_COMB (@lem14842) (@lem14841 g')). Qed.
Lemma lem14859 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem14860 {_2963 : Type'} (t2 : _2963) (t1 : _2963) : (@COND _2963 True t1 t2) = t1.
Proof. exact (@lem14859 _2963 t2 t1). Qed.
Lemma lem14861 {_2963 : Type'} (e : _2963) (t : _2963) : (@COND _2963 True t e) = t.
Proof. exact (@lem14860 _2963 e t). Qed.
Lemma lem14862 {_2963 : Type'} : (@eq _2963) = (@eq _2963).
Proof. exact (eq_refl (@eq _2963)). Qed.
Lemma lem14863 {_2963 : Type'} (e : _2963) (t : _2963) : (term1 _2963 t e) = (@eq _2963 t).
Proof. exact (MK_COMB (@lem14862 _2963) (@lem14861 _2963 e t)). Qed.
Lemma lem14864 {_2963 : Type'} (g' : Prop) (t' : _2963) (e' : _2963) : (@COND _2963 g' t' e') = (@COND _2963 g' t' e').
Proof. exact (eq_refl (@COND _2963 g' t' e')). Qed.
Lemma lem14865 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((@COND _2963 True t e) = (@COND _2963 g' t' e')) = (t = (@COND _2963 g' t' e')).
Proof. exact (MK_COMB (@lem14863 _2963 e t) (@lem14864 _2963 g' t' e')). Qed.
Lemma lem14868 {_2963 : Type'} (g' : Prop) (e : _2963) (e' : _2963) : (term2 _2963 g' e e') = (term2 _2963 g' e e').
Proof. exact (eq_refl (term2 _2963 g' e e')). Qed.
Lemma lem14869 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term3 _2963 t e g' t' e') = (term4 _2963 e t g' t' e').
Proof. exact (MK_COMB (@lem14868 _2963 g' e e') (@lem14865 _2963 e t g' t' e')). Qed.
Lemma lem14872 {_2963 : Type'} (g' : Prop) (t : _2963) (t' : _2963) : (term5 _2963 g' t t') = (term5 _2963 g' t t').
Proof. exact (eq_refl (term5 _2963 g' t t')). Qed.
Lemma lem14873 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term6 _2963 t e g' t' e') = (term7 _2963 e t g' t' e').
Proof. exact (MK_COMB (@lem14872 _2963 g' t t') (@lem14869 _2963 e t g' t' e')). Qed.
Lemma lem14876 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term8 _2963 t e g' t' e') = (term9 _2963 e t g' t' e').
Proof. exact (MK_COMB (@lem14843 g') (@lem14873 _2963 e t g' t' e')). Qed.
Lemma lem14879 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term9 _2963 e t g' t' e') = (term8 _2963 t e g' t' e').
Proof. exact (SYM (@lem14876 _2963 e t g' t' e')). Qed.
Lemma lem14880 (g' : Prop) : term10 g'.
Proof. exact (@lem9851 g'). Qed.
Lemma lem14881 (g' : Prop) : (term10 g') = (term11 g').
Proof. exact (eq_refl (term10 g')). Qed.
Lemma lem14882 (g' : Prop) : term11 g'.
Proof. exact (EQ_MP (@lem14881 g') (@lem14880 g')). Qed.
Lemma lem14883 (g' : Prop) (h1 : g' = True) : g' = True.
Proof. exact (h1). Qed.
Lemma lem14884 (g' : Prop) (h1 : g' = False) : g' = False.
Proof. exact (h1). Qed.
Lemma lem14903 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term12 _2963 e t t' e') = (term12 _2963 e t t' e').
Proof. exact (eq_refl (term12 _2963 e t t' e')). Qed.
Lemma lem14904 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : (term13 _2963 e t t' e' g') = (term14 _2963 e t t' e').
Proof. exact (MK_COMB (@lem14903 _2963 e t t' e') (@lem14883 g' h1)). Qed.
Lemma lem14905 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term14 _2963 e t t' e') = (term15 _2963 e t t' e').
Proof. exact (eq_refl (term14 _2963 e t t' e')). Qed.
Lemma lem14906 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) : (term16 _2963 e t t' e' g') = (term16 _2963 e t t' e' g').
Proof. exact (eq_refl (term16 _2963 e t t' e' g')). Qed.
Lemma lem14907 {_2963 : Type'} (g' : Prop) (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : ((term13 _2963 e t t' e' g') = (term14 _2963 e t t' e')) = ((term13 _2963 e t t' e' g') = (term15 _2963 e t t' e')).
Proof. exact (MK_COMB (@lem14906 _2963 e t t' e' g') (@lem14905 _2963 e t t' e')). Qed.
Lemma lem14908 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term13 _2963 e t t' e' g') = (term9 _2963 e t g' t' e').
Proof. exact (eq_refl (term13 _2963 e t t' e' g')). Qed.
Lemma lem14909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem14910 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term16 _2963 e t t' e' g') = (term17 _2963 e t g' t' e').
Proof. exact (MK_COMB (@lem14909) (@lem14908 _2963 e t g' t' e')). Qed.
Lemma lem14911 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term15 _2963 e t t' e') = (term15 _2963 e t t' e').
Proof. exact (eq_refl (term15 _2963 e t t' e')). Qed.
Lemma lem14912 {_2963 : Type'} (g' : Prop) (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : ((term13 _2963 e t t' e' g') = (term15 _2963 e t t' e')) = ((term9 _2963 e t g' t' e') = (term15 _2963 e t t' e')).
Proof. exact (MK_COMB (@lem14910 _2963 e t g' t' e') (@lem14911 _2963 e t t' e')). Qed.
Lemma lem14913 {_2963 : Type'} (g' : Prop) (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : ((term13 _2963 e t t' e' g') = (term14 _2963 e t t' e')) = ((term9 _2963 e t g' t' e') = (term15 _2963 e t t' e')).
Proof. exact (TRANS (@lem14907 _2963 g' e t t' e') (@lem14912 _2963 g' e t t' e')). Qed.
Lemma lem14914 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : (term9 _2963 e t g' t' e') = (term15 _2963 e t t' e').
Proof. exact (EQ_MP (@lem14913 _2963 g' e t t' e') (@lem14904 _2963 e t t' e' g' h1)). Qed.
Lemma lem14915 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : (term15 _2963 e t t' e') = (term9 _2963 e t g' t' e').
Proof. exact (SYM (@lem14914 _2963 e t t' e' g' h1)). Qed.
Lemma lem14916 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term12 _2963 e t t' e') = (term12 _2963 e t t' e').
Proof. exact (eq_refl (term12 _2963 e t t' e')). Qed.
Lemma lem14917 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : (term13 _2963 e t t' e' g') = (term18 _2963 e t t' e').
Proof. exact (MK_COMB (@lem14916 _2963 e t t' e') (@lem14884 g' h1)). Qed.
Lemma lem14918 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term18 _2963 e t t' e') = (term19 _2963 e t t' e').
Proof. exact (eq_refl (term18 _2963 e t t' e')). Qed.
Lemma lem14919 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) : (term16 _2963 e t t' e' g') = (term16 _2963 e t t' e' g').
Proof. exact (eq_refl (term16 _2963 e t t' e' g')). Qed.
Lemma lem14920 {_2963 : Type'} (g' : Prop) (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : ((term13 _2963 e t t' e' g') = (term18 _2963 e t t' e')) = ((term13 _2963 e t t' e' g') = (term19 _2963 e t t' e')).
Proof. exact (MK_COMB (@lem14919 _2963 e t t' e' g') (@lem14918 _2963 e t t' e')). Qed.
Lemma lem14921 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term13 _2963 e t t' e' g') = (term9 _2963 e t g' t' e').
Proof. exact (eq_refl (term13 _2963 e t t' e' g')). Qed.
Lemma lem14922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem14923 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term16 _2963 e t t' e' g') = (term17 _2963 e t g' t' e').
Proof. exact (MK_COMB (@lem14922) (@lem14921 _2963 e t g' t' e')). Qed.
Lemma lem14924 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term19 _2963 e t t' e') = (term19 _2963 e t t' e').
Proof. exact (eq_refl (term19 _2963 e t t' e')). Qed.
Lemma lem14925 {_2963 : Type'} (g' : Prop) (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : ((term13 _2963 e t t' e' g') = (term19 _2963 e t t' e')) = ((term9 _2963 e t g' t' e') = (term19 _2963 e t t' e')).
Proof. exact (MK_COMB (@lem14923 _2963 e t g' t' e') (@lem14924 _2963 e t t' e')). Qed.
Lemma lem14926 {_2963 : Type'} (g' : Prop) (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : ((term13 _2963 e t t' e' g') = (term18 _2963 e t t' e')) = ((term9 _2963 e t g' t' e') = (term19 _2963 e t t' e')).
Proof. exact (TRANS (@lem14920 _2963 g' e t t' e') (@lem14925 _2963 g' e t t' e')). Qed.
Lemma lem14927 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : (term9 _2963 e t g' t' e') = (term19 _2963 e t t' e').
Proof. exact (EQ_MP (@lem14926 _2963 g' e t t' e') (@lem14917 _2963 e t t' e' g' h1)). Qed.
Lemma lem14928 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : (term19 _2963 e t t' e') = (term9 _2963 e t g' t' e').
Proof. exact (SYM (@lem14927 _2963 e t t' e' g' h1)). Qed.
Lemma lem14930 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem14931 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term15 _2963 e t t' e') = (term20 _2963 e t t' e').
Proof. exact (@lem14930 (term20 _2963 e t t' e')). Qed.
Lemma lem14935 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem14936 {_2963 : Type'} (t : _2963) (t' : _2963) : (term21 _2963 t t') = (t = t').
Proof. exact (@lem14935 (t = t')). Qed.
Lemma lem14939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem14940 {_2963 : Type'} (t : _2963) (t' : _2963) : (term22 _2963 t t') = (term23 _2963 t t').
Proof. exact (MK_COMB (@lem14939) (@lem14936 _2963 t t')). Qed.
Lemma lem14946 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem14947 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem14948 : term24 = (imp False).
Proof. exact (MK_COMB (@lem14947) (@lem14946)). Qed.
Lemma lem14951 {_2963 : Type'} (e : _2963) (e' : _2963) : (e = e') = (e = e').
Proof. exact (eq_refl (e = e')). Qed.
Lemma lem14952 {_2963 : Type'} (e : _2963) (e' : _2963) : (term25 _2963 e e') = (term26 _2963 e e').
Proof. exact (MK_COMB (@lem14948) (@lem14951 _2963 e e')). Qed.
Lemma lem14954 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem14955 {_2963 : Type'} (e : _2963) (e' : _2963) : (term26 _2963 e e') = True.
Proof. exact (@lem14954 (e = e')). Qed.
Lemma lem14956 {_2963 : Type'} (e : _2963) (e' : _2963) : (term25 _2963 e e') = True.
Proof. exact (TRANS (@lem14952 _2963 e e') (@lem14955 _2963 e e')). Qed.
Lemma lem14957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem14958 {_2963 : Type'} (e : _2963) (e' : _2963) : (term27 _2963 e e') = (imp True).
Proof. exact (MK_COMB (@lem14957) (@lem14956 _2963 e e')). Qed.
Lemma lem14962 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem14963 {_2963 : Type'} (t2 : _2963) (t1 : _2963) : (@COND _2963 True t1 t2) = t1.
Proof. exact (@lem14962 _2963 t2 t1). Qed.
Lemma lem14964 {_2963 : Type'} (e' : _2963) (t' : _2963) : (@COND _2963 True t' e') = t'.
Proof. exact (@lem14963 _2963 e' t'). Qed.
Lemma lem14965 {_2963 : Type'} (t : _2963) : (@eq _2963 t) = (@eq _2963 t).
Proof. exact (eq_refl (@eq _2963 t)). Qed.
Lemma lem14966 {_2963 : Type'} (e' : _2963) (t : _2963) (t' : _2963) : (t = (@COND _2963 True t' e')) = (t = t').
Proof. exact (MK_COMB (@lem14965 _2963 t) (@lem14964 _2963 e' t')). Qed.
Lemma lem14969 {_2963 : Type'} (e : _2963) (e' : _2963) (t : _2963) (t' : _2963) : (term28 _2963 e t t' e') = (term21 _2963 t t').
Proof. exact (MK_COMB (@lem14958 _2963 e e') (@lem14966 _2963 e' t t')). Qed.
Lemma lem14971 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem14972 {_2963 : Type'} (t : _2963) (t' : _2963) : (term21 _2963 t t') = (t = t').
Proof. exact (@lem14971 (t = t')). Qed.
Lemma lem14975 {_2963 : Type'} (e : _2963) (e' : _2963) (t : _2963) (t' : _2963) : (term28 _2963 e t t' e') = (t = t').
Proof. exact (TRANS (@lem14969 _2963 e e' t t') (@lem14972 _2963 t t')). Qed.
Lemma lem14976 {_2963 : Type'} (e : _2963) (e' : _2963) (t : _2963) (t' : _2963) : (term20 _2963 e t t' e') = (term29 _2963 t t').
Proof. exact (MK_COMB (@lem14940 _2963 t t') (@lem14975 _2963 e e' t t')). Qed.
Lemma lem14980 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem14981 {_2963 : Type'} (t : _2963) (t' : _2963) : (term29 _2963 t t') = True.
Proof. exact (@lem14980 (t = t')). Qed.
Lemma lem14982 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term20 _2963 e t t' e') = True.
Proof. exact (TRANS (@lem14976 _2963 e e' t t') (@lem14981 _2963 t t')). Qed.
Lemma lem14983 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term15 _2963 e t t' e') = True.
Proof. exact (TRANS (@lem14931 _2963 e t t' e') (@lem14982 _2963 e t t' e')). Qed.
Lemma lem14984 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : True = (term15 _2963 e t t' e').
Proof. exact (SYM (@lem14983 _2963 e t t' e')). Qed.
Lemma lem14985 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : term15 _2963 e t t' e'.
Proof. exact (EQ_MP (@lem14984 _2963 e t t' e') (@lem0)). Qed.
Lemma lem14987 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem14988 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : (term19 _2963 e t t' e') = True.
Proof. exact (@lem14987 (term30 _2963 e t t' e')). Qed.
Lemma lem14989 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : True = (term19 _2963 e t t' e').
Proof. exact (SYM (@lem14988 _2963 e t t' e')). Qed.
Lemma lem14990 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) : term19 _2963 e t t' e'.
Proof. exact (EQ_MP (@lem14989 _2963 e t t' e') (@lem0)). Qed.
Lemma lem14991 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : term9 _2963 e t g' t' e'.
Proof. exact (EQ_MP (@lem14928 _2963 e t t' e' g' h1) (@lem14990 _2963 e t t' e')). Qed.
Lemma lem14992 {_2963 : Type'} (e : _2963) (t : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : term9 _2963 e t g' t' e'.
Proof. exact (EQ_MP (@lem14915 _2963 e t t' e' g' h1) (@lem14985 _2963 e t t' e')). Qed.
Lemma lem14994 {_2963 : Type'} (e : _2963) (t : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term9 _2963 e t g' t' e'.
Proof. exact (or_elim (@lem14882 g') (fun h0 : g' = True => @lem14992 _2963 e t t' e' g' h0) (fun h0 : g' = False => @lem14991 _2963 e t t' e' g' h0)). Qed.
Lemma lem14995 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term8 _2963 t e g' t' e'.
Proof. exact (EQ_MP (@lem14879 _2963 t e g' t' e') (@lem14994 _2963 e t g' t' e')). Qed.
