Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_SUBSET_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1157_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3239808 (a : Prop) (b : Prop) (h1 : term0 a b) : term0 a b.
Proof. exact (h1). Qed.
Lemma lem3239809 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3239810 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term0 a b) : a -> b.
Proof. exact (@lem3239808 a b h2 (@lem3239809 a b h1)). Qed.
Lemma lem3239811 (a : Prop) (b : Prop) (h1 : a = b) : term1 a b.
Proof. exact (fun h0 : term0 a b => @lem3239810 a b h1 h0). Qed.
Lemma lem3239812 (a : Prop) (b : Prop) (h1 : term0 a b) : term0 a b.
Proof. exact (h1). Qed.
Lemma lem3239813 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term0 a b) : a -> b.
Proof. exact (@lem3239811 a b h1 (@lem3239812 a b h2)). Qed.
Lemma lem3239814 (a : Prop) (b : Prop) (h1 : term0 a b) : term0 a b.
Proof. exact (fun h0 : a = b => @lem3239813 a b h0 h1). Qed.
Lemma lem3239815 (a : Prop) (b : Prop) : term2 a b.
Proof. exact (fun h0 : term0 a b => @lem3239814 a b h0). Qed.
Lemma lem3239817 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term3 A t u P.
Proof. exact (h1). Qed.
Lemma lem3239818 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term4 A t' t u' u) : term4 A t' t u' u.
Proof. exact (h1). Qed.
Lemma lem3239819 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (h1 : @SUBSET A u' u) : @SUBSET A u' u.
Proof. exact (h1). Qed.
Lemma lem3239820 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (h1 : @SUBSET A t' t) : @SUBSET A t' t.
Proof. exact (h1). Qed.
Lemma lem3239821 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term3 A t u P.
Proof. exact (h1). Qed.
Lemma lem3239822 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term5 A t u P s.
Proof. exact (@lem3239821 A t u P h1 s). Qed.
Lemma lem3239823 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (s : A -> Prop) : (term5 A t u P s) = (term6 A t u P s).
Proof. exact (eq_refl (term5 A t u P s)). Qed.
Lemma lem3239824 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term6 A t u P s.
Proof. exact (EQ_MP (@lem3239823 A t u P s) (@lem3239822 A s t u P h1)). Qed.
Lemma lem3239825 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term7 A s t u) : term7 A s t u.
Proof. exact (h1). Qed.
Lemma lem3239826 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : term7 A s t u) : P s.
Proof. exact (@lem3239824 A s t u P h1 (@lem3239825 A s t u h2)). Qed.
Lemma lem3239827 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term7 A s t u) : term8 A t u P s.
Proof. exact (fun h0 : term3 A t u P => @lem3239826 A P s t u h0 h1). Qed.
Lemma lem3239828 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term3 A t u P.
Proof. exact (h1). Qed.
Lemma lem3239829 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : term7 A s t u) : P s.
Proof. exact (@lem3239827 A P s t u h2 (@lem3239828 A t u P h1)). Qed.
Lemma lem3239830 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term6 A t u P s.
Proof. exact (fun h0 : term7 A s t u => @lem3239829 A P s t u h1 h0). Qed.
Lemma lem3239831 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term3 A t u P.
Proof. exact (fun s : A -> Prop => @lem3239830 A s t u P h1). Qed.
Lemma lem3239832 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : term9 A t u P.
Proof. exact (fun h0 : term3 A t u P => @lem3239831 A t u P h0). Qed.
Lemma lem3239833 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term3 A t u P.
Proof. exact (@lem3239832 A t u P (@lem3239817 A t u P h1)). Qed.
Lemma lem3239834 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term5 A t u P s.
Proof. exact (@lem3239833 A t u P h1 s). Qed.
Lemma lem3239835 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (s : A -> Prop) : (term5 A t u P s) = (term6 A t u P s).
Proof. exact (eq_refl (term5 A t u P s)). Qed.
Lemma lem3239838 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term6 A t u P s.
Proof. exact (EQ_MP (@lem3239835 A t u P s) (@lem3239834 A s t u P h1)). Qed.
Lemma lem3239839 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term6 A t u P s.
Proof. exact (@lem3239838 A s t u P h1). Qed.
Lemma lem3239840 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term10 A t u P t' u'.
Proof. exact (@lem3239839 A (@UNION A t' u') t u P h1). Qed.
Lemma lem3239851 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : @SUBSET A t' t) (h2 : @SUBSET A u' u) : term4 A u' u t' t.
Proof. exact (conj (@lem3239819 A u' u h2) (@lem3239820 A t' t h1)). Qed.
Lemma lem3239857 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3239858 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3239857 A s t). Qed.
Lemma lem3239859 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (@SUBSET A u' u) = (term11 A u' u).
Proof. exact (@lem3239858 A u' u). Qed.
Lemma lem3239866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3239867 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term12 A u' u) = (term13 A u' u).
Proof. exact (MK_COMB (@lem3239866) (@lem3239859 A u' u)). Qed.
Lemma lem3239869 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3239870 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3239869 A s t). Qed.
Lemma lem3239871 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (@SUBSET A t' t) = (term11 A t' t).
Proof. exact (@lem3239870 A t' t). Qed.
Lemma lem3239878 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term4 A u' u t' t) = (term14 A u' u t' t).
Proof. exact (MK_COMB (@lem3239867 A u' u) (@lem3239871 A t' t)). Qed.
Lemma lem3239881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3239882 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term15 A u' u t' t) = (term16 A u' u t' t).
Proof. exact (MK_COMB (@lem3239881) (@lem3239878 A u' u t' t)). Qed.
Lemma lem3239884 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3239885 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3239884 A s t). Qed.
Lemma lem3239886 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term17 A t' u' t u) = (term18 A t' u' t u).
Proof. exact (@lem3239885 A (@UNION A t' u') (@UNION A t u)). Qed.
Lemma lem3239893 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term19 A t' u' t u) = (term20 A t' u' t u).
Proof. exact (MK_COMB (@lem3239882 A u' u t' t) (@lem3239886 A t' u' t u)). Qed.
Lemma lem3239896 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term20 A t' u' t u) = (term19 A t' u' t u).
Proof. exact (SYM (@lem3239893 A t' u' t u)). Qed.
Lemma lem3239908 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3239909 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3239908 A P x). Qed.
Lemma lem3239910 {A : Type'} (u' : A -> Prop) (x : A) : (@IN A x u') = (u' x).
Proof. exact (@lem3239909 A u' x). Qed.
Lemma lem3239911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3239912 {A : Type'} (u' : A -> Prop) (x : A) : (term21 A x u') = (term22 A u' x).
Proof. exact (MK_COMB (@lem3239911) (@lem3239910 A u' x)). Qed.
Lemma lem3239914 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3239915 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3239914 A P x). Qed.
Lemma lem3239916 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3239915 A u x). Qed.
Lemma lem3239917 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term23 A u' x u) = (term24 A u' u x).
Proof. exact (MK_COMB (@lem3239912 A u' x) (@lem3239916 A u x)). Qed.
Lemma lem3239920 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term25 A u' u) = (term26 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3239917 A u' u x)). Qed.
Lemma lem3239921 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3239922 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term11 A u' u) = (term27 A u' u).
Proof. exact (MK_COMB (@lem3239921 A) (@lem3239920 A u' u)). Qed.
Lemma lem3239927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3239928 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term13 A u' u) = (term28 A u' u).
Proof. exact (MK_COMB (@lem3239927) (@lem3239922 A u' u)). Qed.
Lemma lem3239936 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3239937 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3239936 A P x). Qed.
Lemma lem3239938 {A : Type'} (t' : A -> Prop) (x : A) : (@IN A x t') = (t' x).
Proof. exact (@lem3239937 A t' x). Qed.
Lemma lem3239939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3239940 {A : Type'} (t' : A -> Prop) (x : A) : (term21 A x t') = (term22 A t' x).
Proof. exact (MK_COMB (@lem3239939) (@lem3239938 A t' x)). Qed.
Lemma lem3239942 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3239943 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3239942 A P x). Qed.
Lemma lem3239944 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3239943 A t x). Qed.
Lemma lem3239945 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term23 A t' x t) = (term24 A t' t x).
Proof. exact (MK_COMB (@lem3239940 A t' x) (@lem3239944 A t x)). Qed.
Lemma lem3239948 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term25 A t' t) = (term26 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3239945 A t' t x)). Qed.
Lemma lem3239949 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3239950 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term11 A t' t) = (term27 A t' t).
Proof. exact (MK_COMB (@lem3239949 A) (@lem3239948 A t' t)). Qed.
Lemma lem3239955 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term14 A u' u t' t) = (term29 A u' u t' t).
Proof. exact (MK_COMB (@lem3239928 A u' u) (@lem3239950 A t' t)). Qed.
Lemma lem3239958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3239959 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term16 A u' u t' t) = (term30 A u' u t' t).
Proof. exact (MK_COMB (@lem3239958) (@lem3239955 A u' u t' t)). Qed.
Lemma lem3239967 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3239968 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (@lem3239967 A s x t). Qed.
Lemma lem3239969 {A : Type'} (t' : A -> Prop) (x : A) (u' : A -> Prop) : (term31 A x t' u') = (term32 A t' x u').
Proof. exact (@lem3239968 A t' x u'). Qed.
Lemma lem3239973 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3239974 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3239973 A P x). Qed.
Lemma lem3239975 {A : Type'} (t' : A -> Prop) (x : A) : (@IN A x t') = (t' x).
Proof. exact (@lem3239974 A t' x). Qed.
Lemma lem3239976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3239977 {A : Type'} (t' : A -> Prop) (x : A) : (term33 A x t') = (term34 A t' x).
Proof. exact (MK_COMB (@lem3239976) (@lem3239975 A t' x)). Qed.
Lemma lem3239979 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3239980 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3239979 A P x). Qed.
Lemma lem3239981 {A : Type'} (u' : A -> Prop) (x : A) : (@IN A x u') = (u' x).
Proof. exact (@lem3239980 A u' x). Qed.
Lemma lem3239982 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (x : A) : (term32 A t' x u') = (term35 A t' u' x).
Proof. exact (MK_COMB (@lem3239977 A t' x) (@lem3239981 A u' x)). Qed.
Lemma lem3239985 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (x : A) : (term31 A x t' u') = (term35 A t' u' x).
Proof. exact (TRANS (@lem3239969 A t' x u') (@lem3239982 A t' u' x)). Qed.
Lemma lem3239986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3239987 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (x : A) : (term36 A x t' u') = (term37 A t' u' x).
Proof. exact (MK_COMB (@lem3239986) (@lem3239985 A t' u' x)). Qed.
Lemma lem3239989 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3239990 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (@lem3239989 A s x t). Qed.
Lemma lem3239991 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term31 A x t u) = (term32 A t x u).
Proof. exact (@lem3239990 A t x u). Qed.
Lemma lem3239995 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3239996 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3239995 A P x). Qed.
Lemma lem3239997 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3239996 A t x). Qed.
Lemma lem3239998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3239999 {A : Type'} (t : A -> Prop) (x : A) : (term33 A x t) = (term34 A t x).
Proof. exact (MK_COMB (@lem3239998) (@lem3239997 A t x)). Qed.
Lemma lem3240001 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3240002 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3240001 A P x). Qed.
Lemma lem3240003 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3240002 A u x). Qed.
Lemma lem3240004 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term32 A t x u) = (term35 A t u x).
Proof. exact (MK_COMB (@lem3239999 A t x) (@lem3240003 A u x)). Qed.
Lemma lem3240007 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term31 A x t u) = (term35 A t u x).
Proof. exact (TRANS (@lem3239991 A t x u) (@lem3240004 A t u x)). Qed.
Lemma lem3240008 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term38 A t' u' x t u) = (term39 A t' u' t u x).
Proof. exact (MK_COMB (@lem3239987 A t' u' x) (@lem3240007 A t u x)). Qed.
Lemma lem3240011 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term40 A t' u' t u) = (term41 A t' u' t u).
Proof. exact (fun_ext (fun x : A => @lem3240008 A t' u' t u x)). Qed.
Lemma lem3240012 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240013 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term18 A t' u' t u) = (term42 A t' u' t u).
Proof. exact (MK_COMB (@lem3240012 A) (@lem3240011 A t' u' t u)). Qed.
Lemma lem3240018 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term20 A t' u' t u) = (term43 A t' u' t u).
Proof. exact (MK_COMB (@lem3239959 A u' u t' t) (@lem3240013 A t' u' t u)). Qed.
Lemma lem3240021 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term43 A t' u' t u) = (term20 A t' u' t u).
Proof. exact (SYM (@lem3240018 A t' u' t u)). Qed.
Lemma lem3240023 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3240024 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term43 A t' u' t u) = (term45 A t' u' t u).
Proof. exact (@lem3240023 (term43 A t' u' t u)). Qed.
Lemma lem3240025 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term45 A t' u' t u) = (term43 A t' u' t u).
Proof. exact (SYM (@lem3240024 A t' u' t u)). Qed.
Lemma lem3240026 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term46 A t' u' t u) : term46 A t' u' t u.
Proof. exact (h1). Qed.
Lemma lem3240029 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term45 A t' u' t u) : term45 A t' u' t u.
Proof. exact (h1). Qed.
Lemma lem3240030 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term47 A t' u' t u.
Proof. exact (fun h0 : term45 A t' u' t u => @lem3240029 A t' u' t u h0). Qed.
Lemma lem3240031 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A t' u' t u) : term47 A t' u' t u.
Proof. exact (h1). Qed.
Lemma lem3240032 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term45 A t' u' t u) : term45 A t' u' t u.
Proof. exact (h1). Qed.
Lemma lem3240033 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term45 A t' u' t u) (h2 : term47 A t' u' t u) : term45 A t' u' t u.
Proof. exact (@lem3240031 A t' u' t u h2 (@lem3240032 A t' u' t u h1)). Qed.
Lemma lem3240034 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term45 A t' u' t u) : term48 A t' u' t u.
Proof. exact (fun h0 : term47 A t' u' t u => @lem3240033 A t' u' t u h1 h0). Qed.
Lemma lem3240035 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A t' u' t u) : term47 A t' u' t u.
Proof. exact (h1). Qed.
Lemma lem3240036 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term45 A t' u' t u) (h2 : term47 A t' u' t u) : term45 A t' u' t u.
Proof. exact (@lem3240034 A t' u' t u h1 (@lem3240035 A t' u' t u h2)). Qed.
Lemma lem3240037 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term47 A t' u' t u) : term47 A t' u' t u.
Proof. exact (fun h0 : term45 A t' u' t u => @lem3240036 A t' u' t u h0 h1). Qed.
Lemma lem3240038 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term49 A t' u' t u.
Proof. exact (fun h0 : term47 A t' u' t u => @lem3240037 A t' u' t u h0). Qed.
Lemma lem3240041 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term47 A t' u' t u.
Proof. exact (@lem3240038 A t' u' t u (@lem3240030 A t' u' t u)). Qed.
Lemma lem3240042 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term47 A t' u' t u.
Proof. exact (@lem3240041 A t' u' t u). Qed.
Lemma lem3240060 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3240061 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term45 A t' u' t u) = (term50 A t' u' t u).
Proof. exact (@lem3240060 (term46 A t' u' t u)). Qed.
Lemma lem3240063 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3240064 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term50 A t' u' t u) = (term43 A t' u' t u).
Proof. exact (@lem3240063 (term43 A t' u' t u)). Qed.
Lemma lem3240067 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term45 A t' u' t u) = (term43 A t' u' t u).
Proof. exact (TRANS (@lem3240061 A t' u' t u) (@lem3240064 A t' u' t u)). Qed.
Lemma lem3240092 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term52 A u' t u) = (term53 A u' t u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3240067 A t' u' t u)). Qed.
Lemma lem3240093 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240094 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term54 A u' t u) = (term55 A u' t u).
Proof. exact (MK_COMB (@lem3240093 A) (@lem3240092 A u' t u)). Qed.
Lemma lem3240099 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term56 A t u) = (term57 A t u).
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3240094 A u' t u)). Qed.
Lemma lem3240100 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240101 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term58 A t u) = (term59 A t u).
Proof. exact (MK_COMB (@lem3240100 A) (@lem3240099 A t u)). Qed.
Lemma lem3240106 {A : Type'} (u : A -> Prop) : (term60 A u) = (term61 A u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3240101 A t u)). Qed.
Lemma lem3240107 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240108 {A : Type'} (u : A -> Prop) : (term62 A u) = (term63 A u).
Proof. exact (MK_COMB (@lem3240107 A) (@lem3240106 A u)). Qed.
Lemma lem3240113 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3240108 A u)). Qed.
Lemma lem3240114 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240123 {A : Type'} : (term66 A) = (term67 A).
Proof. exact (MK_COMB (@lem3240114 A) (@lem3240113 A)). Qed.
Lemma lem3240136 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term39 A t' u' t u x) = (term39 A t' u' t u x).
Proof. exact (eq_refl (term39 A t' u' t u x)). Qed.
Lemma lem3240137 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term41 A t' u' t u) = (term41 A t' u' t u).
Proof. exact (fun_ext (fun x : A => @lem3240136 A t' u' t u x)). Qed.
Lemma lem3240138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240139 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term42 A t' u' t u) = (term42 A t' u' t u).
Proof. exact (MK_COMB (@lem3240138 A) (@lem3240137 A t' u' t u)). Qed.
Lemma lem3240144 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term24 A t' t x) = (term24 A t' t x).
Proof. exact (eq_refl (term24 A t' t x)). Qed.
Lemma lem3240145 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term26 A t' t) = (term26 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3240144 A t' t x)). Qed.
Lemma lem3240146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240147 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term27 A t' t) = (term27 A t' t).
Proof. exact (MK_COMB (@lem3240146 A) (@lem3240145 A t' t)). Qed.
Lemma lem3240152 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term24 A u' u x) = (term24 A u' u x).
Proof. exact (eq_refl (term24 A u' u x)). Qed.
Lemma lem3240153 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term26 A u' u) = (term26 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3240152 A u' u x)). Qed.
Lemma lem3240154 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240155 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term27 A u' u) = (term27 A u' u).
Proof. exact (MK_COMB (@lem3240154 A) (@lem3240153 A u' u)). Qed.
Lemma lem3240156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3240157 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term28 A u' u) = (term28 A u' u).
Proof. exact (MK_COMB (@lem3240156) (@lem3240155 A u' u)). Qed.
Lemma lem3240158 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term29 A u' u t' t) = (term29 A u' u t' t).
Proof. exact (MK_COMB (@lem3240157 A u' u) (@lem3240147 A t' t)). Qed.
Lemma lem3240159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3240160 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term30 A u' u t' t) = (term30 A u' u t' t).
Proof. exact (MK_COMB (@lem3240159) (@lem3240158 A u' u t' t)). Qed.
Lemma lem3240161 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term43 A t' u' t u) = (term43 A t' u' t u).
Proof. exact (MK_COMB (@lem3240160 A u' u t' t) (@lem3240139 A t' u' t u)). Qed.
Lemma lem3240162 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term53 A u' t u) = (term53 A u' t u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3240161 A t' u' t u)). Qed.
Lemma lem3240163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240164 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term55 A u' t u) = (term55 A u' t u).
Proof. exact (MK_COMB (@lem3240163 A) (@lem3240162 A u' t u)). Qed.
Lemma lem3240165 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term57 A t u) = (term57 A t u).
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3240164 A u' t u)). Qed.
Lemma lem3240166 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240167 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term59 A t u) = (term59 A t u).
Proof. exact (MK_COMB (@lem3240166 A) (@lem3240165 A t u)). Qed.
Lemma lem3240168 {A : Type'} (u : A -> Prop) : (term61 A u) = (term61 A u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3240167 A t u)). Qed.
Lemma lem3240169 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240170 {A : Type'} (u : A -> Prop) : (term63 A u) = (term63 A u).
Proof. exact (MK_COMB (@lem3240169 A) (@lem3240168 A u)). Qed.
Lemma lem3240171 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3240170 A u)). Qed.
Lemma lem3240172 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240173 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (MK_COMB (@lem3240172 A) (@lem3240171 A)). Qed.
Lemma lem3240232 {A : Type'} : (term66 A) = (term67 A).
Proof. exact (TRANS (@lem3240123 A) (@lem3240173 A)). Qed.
Lemma lem3240233 {A : Type'} : (term67 A) = (term66 A).
Proof. exact (SYM (@lem3240232 A)). Qed.
Lemma lem3240234 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term29 A u' u t' t.
Proof. exact (h1). Qed.
Lemma lem3240237 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3240238 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term35 A t u x) = (term68 A t u x).
Proof. exact (@lem3240237 (term35 A t u x)). Qed.
Lemma lem3240239 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term68 A t u x) = (term35 A t u x).
Proof. exact (SYM (@lem3240238 A t u x)). Qed.
Lemma lem3240240 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term69 A t u x) : term69 A t u x.
Proof. exact (h1). Qed.
Lemma lem3240247 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term24 A u' u x) = (term70 A u' u x).
Proof. exact (@lem17265 (u' x) (u x)). Qed.
Lemma lem3240248 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term26 A u' u) = (term71 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3240247 A u' u x)). Qed.
Lemma lem3240249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240250 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term27 A u' u) = (term72 A u' u).
Proof. exact (MK_COMB (@lem3240249 A) (@lem3240248 A u' u)). Qed.
Lemma lem3240257 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term24 A t' t x) = (term70 A t' t x).
Proof. exact (@lem17265 (t' x) (t x)). Qed.
Lemma lem3240258 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term26 A t' t) = (term71 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3240257 A t' t x)). Qed.
Lemma lem3240259 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240260 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term27 A t' t) = (term72 A t' t).
Proof. exact (MK_COMB (@lem3240259 A) (@lem3240258 A t' t)). Qed.
Lemma lem3240261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3240262 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term28 A u' u) = (term73 A u' u).
Proof. exact (MK_COMB (@lem3240261) (@lem3240250 A u' u)). Qed.
Lemma lem3240331 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term29 A u' u t' t) = (term74 A u' u t' t).
Proof. exact (MK_COMB (@lem3240262 A u' u) (@lem3240260 A t' t)). Qed.
Lemma lem3240332 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term74 A u' u t' t.
Proof. exact (EQ_MP (@lem3240331 A u' u t' t) (@lem3240234 A u' u t' t h1)). Qed.
Lemma lem3240342 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term35 A t' u' x) : term35 A t' u' x.
Proof. exact (h1). Qed.
Lemma lem3240353 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term69 A t u x) = (term75 A t u x).
Proof. exact (@lem17160 (t x) (u x)). Qed.
Lemma lem3240365 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term70 A t' t x) = (term70 A t' t x).
Proof. exact (eq_refl (term70 A t' t x)). Qed.
Lemma lem3240366 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term71 A t' t) = (term71 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3240365 A t' t x)). Qed.
Lemma lem3240367 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240368 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term72 A t' t) = (term72 A t' t).
Proof. exact (MK_COMB (@lem3240367 A) (@lem3240366 A t' t)). Qed.
Lemma lem3240379 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term70 A u' u x) = (term70 A u' u x).
Proof. exact (eq_refl (term70 A u' u x)). Qed.
Lemma lem3240380 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term71 A u' u) = (term71 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3240379 A u' u x)). Qed.
Lemma lem3240381 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240382 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term72 A u' u) = (term72 A u' u).
Proof. exact (MK_COMB (@lem3240381 A) (@lem3240380 A u' u)). Qed.
Lemma lem3240383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3240384 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term73 A u' u) = (term73 A u' u).
Proof. exact (MK_COMB (@lem3240383) (@lem3240382 A u' u)). Qed.
Lemma lem3240385 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) : (term74 A u' u t' t) = (term74 A u' u t' t).
Proof. exact (MK_COMB (@lem3240384 A u' u) (@lem3240368 A t' t)). Qed.
Lemma lem3240386 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term74 A u' u t' t.
Proof. exact (EQ_MP (@lem3240385 A u' u t' t) (@lem3240332 A u' u t' t h1)). Qed.
Lemma lem3240396 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term35 A t' u' x) : term35 A t' u' x.
Proof. exact (h1). Qed.
Lemma lem3240410 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term69 A t u x) : term75 A t u x.
Proof. exact (EQ_MP (@lem3240353 A t u x) (@lem3240240 A t u x h1)). Qed.
Lemma lem3240413 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term72 A t' t.
Proof. exact (proj2 (@lem3240386 A u' u t' t h1)). Qed.
Lemma lem3240414 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term72 A u' u.
Proof. exact (proj1 (@lem3240386 A u' u t' t h1)). Qed.
Lemma lem3240445 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term70 A t' t x) = (term70 A t' t x).
Proof. exact (eq_refl (term70 A t' t x)). Qed.
Lemma lem3240446 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term71 A t' t) = (term71 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3240445 A t' t x)). Qed.
Lemma lem3240447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240449 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term72 A t' t) = (term72 A t' t).
Proof. exact (MK_COMB (@lem3240447 A) (@lem3240446 A t' t)). Qed.
Lemma lem3240450 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term72 A t' t.
Proof. exact (EQ_MP (@lem3240449 A t' t) (@lem3240413 A u' u t' t h1)). Qed.
Lemma lem3240454 {A : Type'} (t' : A -> Prop) (x : A) (h1 : t' x) : t' x.
Proof. exact (h1). Qed.
Lemma lem3240470 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term70 A u' u x) = (term70 A u' u x).
Proof. exact (eq_refl (term70 A u' u x)). Qed.
Lemma lem3240471 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term71 A u' u) = (term71 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3240470 A u' u x)). Qed.
Lemma lem3240472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240474 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term72 A u' u) = (term72 A u' u).
Proof. exact (MK_COMB (@lem3240472 A) (@lem3240471 A u' u)). Qed.
Lemma lem3240475 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term72 A u' u.
Proof. exact (EQ_MP (@lem3240474 A u' u) (@lem3240414 A u' u t' t h1)). Qed.
Lemma lem3240492 {A : Type'} (u' : A -> Prop) (x : A) (h1 : u' x) : u' x.
Proof. exact (h1). Qed.
Lemma lem3240496 {A : Type'} (_33220 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term76 A t' t _33220.
Proof. exact (@lem3240450 A u' u t' t h1 _33220). Qed.
Lemma lem3240497 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (_33220 : A) : (term76 A t' t _33220) = (term70 A t' t _33220).
Proof. exact (eq_refl (term76 A t' t _33220)). Qed.
Lemma lem3240499 {A : Type'} (_33221 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term76 A u' u _33221.
Proof. exact (@lem3240475 A u' u t' t h1 _33221). Qed.
Lemma lem3240500 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (_33221 : A) : (term76 A u' u _33221) = (term70 A u' u _33221).
Proof. exact (eq_refl (term76 A u' u _33221)). Qed.
Lemma lem3240506 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term69 A t u x) : term77 A t x.
Proof. exact (proj1 (@lem3240410 A t u x h1)). Qed.
Lemma lem3240520 {A : Type'} (_33220 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term70 A t' t _33220.
Proof. exact (EQ_MP (@lem3240497 A t' t _33220) (@lem3240496 A _33220 u' u t' t h1)). Qed.
Lemma lem3240522 {A : Type'} (t' : A -> Prop) (x : A) (h1 : t' x) : t' x.
Proof. exact (h1). Qed.
Lemma lem3240526 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term69 A t u x) : term77 A u x.
Proof. exact (proj2 (@lem3240410 A t u x h1)). Qed.
Lemma lem3240532 {A : Type'} (_33221 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term70 A u' u _33221.
Proof. exact (EQ_MP (@lem3240500 A u' u _33221) (@lem3240499 A _33221 u' u t' t h1)). Qed.
Lemma lem3240540 {A : Type'} (u' : A -> Prop) (x : A) (h1 : u' x) : u' x.
Proof. exact (h1). Qed.
Lemma lem3240542 {A : Type'} (t' : A -> Prop) (x : A) (h1 : t' x) : t' x.
Proof. exact (h1). Qed.
Lemma lem3240543 {A : Type'} (t' : A -> Prop) (x : A) (h1 : t' x) : term78 A t' x.
Proof. exact (fun h0 : term77 A t' x => @lem3240542 A t' x h1). Qed.
Lemma lem3240545 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3240546 {A : Type'} (t' : A -> Prop) (x : A) : (term78 A t' x) = (t' x).
Proof. exact (@lem3240545 (t' x)). Qed.
Lemma lem3240547 {A : Type'} (t' : A -> Prop) (x : A) (h1 : t' x) : t' x.
Proof. exact (EQ_MP (@lem3240546 A t' x) (@lem3240543 A t' x h1)). Qed.
Lemma lem3240553 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3240554 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : (term70 A t' t _33220) = (term80 A t t' _33220).
Proof. exact (@lem3240553 (t _33220) (term77 A t' _33220)). Qed.
Lemma lem3240560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3240561 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : (term81 A t' t _33220) = (term82 A t t' _33220).
Proof. exact (MK_COMB (@lem3240560) (@lem3240554 A t t' _33220)). Qed.
Lemma lem3240567 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : (term80 A t t' _33220) = (term80 A t t' _33220).
Proof. exact (eq_refl (term80 A t t' _33220)). Qed.
Lemma lem3240568 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : ((term70 A t' t _33220) = (term80 A t t' _33220)) = ((term80 A t t' _33220) = (term80 A t t' _33220)).
Proof. exact (MK_COMB (@lem3240561 A t t' _33220) (@lem3240567 A t t' _33220)). Qed.
Lemma lem3240570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3240571 (x : Prop) : (x = x) = True.
Proof. exact (@lem3240570 Prop x). Qed.
Lemma lem3240572 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : ((term80 A t t' _33220) = (term80 A t t' _33220)) = True.
Proof. exact (@lem3240571 (term80 A t t' _33220)). Qed.
Lemma lem3240573 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : ((term70 A t' t _33220) = (term80 A t t' _33220)) = True.
Proof. exact (TRANS (@lem3240568 A t t' _33220) (@lem3240572 A t t' _33220)). Qed.
Lemma lem3240574 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : True = ((term70 A t' t _33220) = (term80 A t t' _33220)).
Proof. exact (SYM (@lem3240573 A t t' _33220)). Qed.
Lemma lem3240575 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (_33220 : A) : (term70 A t' t _33220) = (term80 A t t' _33220).
Proof. exact (EQ_MP (@lem3240574 A t t' _33220) (@lem0)). Qed.
Lemma lem3240576 {A : Type'} (_33220 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term80 A t t' _33220.
Proof. exact (EQ_MP (@lem3240575 A t t' _33220) (@lem3240520 A _33220 u' u t' t h1)). Qed.
Lemma lem3240578 (b : Prop) (a : Prop) : (a \/ b) = (term83 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3240579 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (_33220 : A) : (term80 A t t' _33220) = (term84 A t' t _33220).
Proof. exact (@lem3240578 (term77 A t' _33220) (t _33220)). Qed.
Lemma lem3240581 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3240582 {A : Type'} (t' : A -> Prop) (_33220 : A) : (term85 A t' _33220) = (t' _33220).
Proof. exact (@lem3240581 (t' _33220)). Qed.
Lemma lem3240583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3240584 {A : Type'} (t' : A -> Prop) (_33220 : A) : (term86 A t' _33220) = (term22 A t' _33220).
Proof. exact (MK_COMB (@lem3240583) (@lem3240582 A t' _33220)). Qed.
Lemma lem3240585 {A : Type'} (t : A -> Prop) (_33220 : A) : (t _33220) = (t _33220).
Proof. exact (eq_refl (t _33220)). Qed.
Lemma lem3240586 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (_33220 : A) : (term84 A t' t _33220) = (term24 A t' t _33220).
Proof. exact (MK_COMB (@lem3240584 A t' _33220) (@lem3240585 A t _33220)). Qed.
Lemma lem3240587 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (_33220 : A) : (term80 A t t' _33220) = (term24 A t' t _33220).
Proof. exact (TRANS (@lem3240579 A t' t _33220) (@lem3240586 A t' t _33220)). Qed.
Lemma lem3240590 {A : Type'} (_33220 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term24 A t' t _33220.
Proof. exact (EQ_MP (@lem3240587 A t' t _33220) (@lem3240576 A _33220 u' u t' t h1)). Qed.
Lemma lem3240591 {A : Type'} (_33220 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term24 A t' t _33220.
Proof. exact (@lem3240590 A _33220 u' u t' t h1). Qed.
Lemma lem3240592 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term24 A t' t x.
Proof. exact (@lem3240591 A x u' u t' t h1). Qed.
Lemma lem3240595 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : t' x) (h2 : term29 A u' u t' t) : t x.
Proof. exact (@lem3240592 A x u' u t' t h2 (@lem3240547 A t' x h1)). Qed.
Lemma lem3240596 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : t' x) (h2 : term29 A u' u t' t) : term78 A t x.
Proof. exact (fun h0 : term77 A t x => @lem3240595 A x u' u t' t h1 h2). Qed.
Lemma lem3240598 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3240599 {A : Type'} (t : A -> Prop) (x : A) : (term78 A t x) = (t x).
Proof. exact (@lem3240598 (t x)). Qed.
Lemma lem3240600 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : t' x) (h2 : term29 A u' u t' t) : t x.
Proof. exact (EQ_MP (@lem3240599 A t x) (@lem3240596 A x u' u t' t h1 h2)). Qed.
Lemma lem3240603 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3240605 {A : Type'} (t : A -> Prop) (x : A) : (term77 A t x) = (term87 A t x).
Proof. exact (@lem3240603 (t x)). Qed.
Lemma lem3240608 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term69 A t u x) : term87 A t x.
Proof. exact (EQ_MP (@lem3240605 A t x) (@lem3240506 A t u x h1)). Qed.
Lemma lem3240611 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (@lem3240608 A t u x h1 (@lem3240600 A x u' u t' t h2 h3)). Qed.
Lemma lem3240612 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : term88.
Proof. exact (fun h0 : ~ False => @lem3240611 A x u' u t' t h1 h2 h3). Qed.
Lemma lem3240614 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3240615 : term88 = False.
Proof. exact (@lem3240614 False). Qed.
Lemma lem3240616 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240615) (@lem3240612 A x u' u t' t h1 h2 h3)). Qed.
Lemma lem3240618 {A : Type'} (u' : A -> Prop) (x : A) (h1 : u' x) : u' x.
Proof. exact (h1). Qed.
Lemma lem3240619 {A : Type'} (u' : A -> Prop) (x : A) (h1 : u' x) : term78 A u' x.
Proof. exact (fun h0 : term77 A u' x => @lem3240618 A u' x h1). Qed.
Lemma lem3240621 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3240622 {A : Type'} (u' : A -> Prop) (x : A) : (term78 A u' x) = (u' x).
Proof. exact (@lem3240621 (u' x)). Qed.
Lemma lem3240623 {A : Type'} (u' : A -> Prop) (x : A) (h1 : u' x) : u' x.
Proof. exact (EQ_MP (@lem3240622 A u' x) (@lem3240619 A u' x h1)). Qed.
Lemma lem3240629 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3240630 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : (term70 A u' u _33221) = (term80 A u u' _33221).
Proof. exact (@lem3240629 (u _33221) (term77 A u' _33221)). Qed.
Lemma lem3240636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3240637 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : (term81 A u' u _33221) = (term82 A u u' _33221).
Proof. exact (MK_COMB (@lem3240636) (@lem3240630 A u u' _33221)). Qed.
Lemma lem3240643 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : (term80 A u u' _33221) = (term80 A u u' _33221).
Proof. exact (eq_refl (term80 A u u' _33221)). Qed.
Lemma lem3240644 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : ((term70 A u' u _33221) = (term80 A u u' _33221)) = ((term80 A u u' _33221) = (term80 A u u' _33221)).
Proof. exact (MK_COMB (@lem3240637 A u u' _33221) (@lem3240643 A u u' _33221)). Qed.
Lemma lem3240646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3240647 (x : Prop) : (x = x) = True.
Proof. exact (@lem3240646 Prop x). Qed.
Lemma lem3240648 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : ((term80 A u u' _33221) = (term80 A u u' _33221)) = True.
Proof. exact (@lem3240647 (term80 A u u' _33221)). Qed.
Lemma lem3240649 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : ((term70 A u' u _33221) = (term80 A u u' _33221)) = True.
Proof. exact (TRANS (@lem3240644 A u u' _33221) (@lem3240648 A u u' _33221)). Qed.
Lemma lem3240650 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : True = ((term70 A u' u _33221) = (term80 A u u' _33221)).
Proof. exact (SYM (@lem3240649 A u u' _33221)). Qed.
Lemma lem3240651 {A : Type'} (u : A -> Prop) (u' : A -> Prop) (_33221 : A) : (term70 A u' u _33221) = (term80 A u u' _33221).
Proof. exact (EQ_MP (@lem3240650 A u u' _33221) (@lem0)). Qed.
Lemma lem3240652 {A : Type'} (_33221 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term80 A u u' _33221.
Proof. exact (EQ_MP (@lem3240651 A u u' _33221) (@lem3240532 A _33221 u' u t' t h1)). Qed.
Lemma lem3240654 (b : Prop) (a : Prop) : (a \/ b) = (term83 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3240655 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (_33221 : A) : (term80 A u u' _33221) = (term84 A u' u _33221).
Proof. exact (@lem3240654 (term77 A u' _33221) (u _33221)). Qed.
Lemma lem3240657 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3240658 {A : Type'} (u' : A -> Prop) (_33221 : A) : (term85 A u' _33221) = (u' _33221).
Proof. exact (@lem3240657 (u' _33221)). Qed.
Lemma lem3240659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3240660 {A : Type'} (u' : A -> Prop) (_33221 : A) : (term86 A u' _33221) = (term22 A u' _33221).
Proof. exact (MK_COMB (@lem3240659) (@lem3240658 A u' _33221)). Qed.
Lemma lem3240661 {A : Type'} (u : A -> Prop) (_33221 : A) : (u _33221) = (u _33221).
Proof. exact (eq_refl (u _33221)). Qed.
Lemma lem3240662 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (_33221 : A) : (term84 A u' u _33221) = (term24 A u' u _33221).
Proof. exact (MK_COMB (@lem3240660 A u' _33221) (@lem3240661 A u _33221)). Qed.
Lemma lem3240663 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (_33221 : A) : (term80 A u u' _33221) = (term24 A u' u _33221).
Proof. exact (TRANS (@lem3240655 A u' u _33221) (@lem3240662 A u' u _33221)). Qed.
Lemma lem3240666 {A : Type'} (_33221 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term24 A u' u _33221.
Proof. exact (EQ_MP (@lem3240663 A u' u _33221) (@lem3240652 A _33221 u' u t' t h1)). Qed.
Lemma lem3240667 {A : Type'} (_33221 : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term24 A u' u _33221.
Proof. exact (@lem3240666 A _33221 u' u t' t h1). Qed.
Lemma lem3240668 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term24 A u' u x.
Proof. exact (@lem3240667 A x u' u t' t h1). Qed.
Lemma lem3240671 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : u' x) (h2 : term29 A u' u t' t) : u x.
Proof. exact (@lem3240668 A x u' u t' t h2 (@lem3240623 A u' x h1)). Qed.
Lemma lem3240672 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : u' x) (h2 : term29 A u' u t' t) : term78 A u x.
Proof. exact (fun h0 : term77 A u x => @lem3240671 A x u' u t' t h1 h2). Qed.
Lemma lem3240674 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3240675 {A : Type'} (u : A -> Prop) (x : A) : (term78 A u x) = (u x).
Proof. exact (@lem3240674 (u x)). Qed.
Lemma lem3240676 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : u' x) (h2 : term29 A u' u t' t) : u x.
Proof. exact (EQ_MP (@lem3240675 A u x) (@lem3240672 A x u' u t' t h1 h2)). Qed.
Lemma lem3240679 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3240681 {A : Type'} (u : A -> Prop) (x : A) : (term77 A u x) = (term87 A u x).
Proof. exact (@lem3240679 (u x)). Qed.
Lemma lem3240684 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term69 A t u x) : term87 A u x.
Proof. exact (EQ_MP (@lem3240681 A u x) (@lem3240526 A t u x h1)). Qed.
Lemma lem3240687 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (@lem3240684 A t u x h1 (@lem3240676 A x u' u t' t h2 h3)). Qed.
Lemma lem3240688 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : term88.
Proof. exact (fun h0 : ~ False => @lem3240687 A x u' u t' t h1 h2 h3). Qed.
Lemma lem3240690 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3240691 : term88 = False.
Proof. exact (@lem3240690 False). Qed.
Lemma lem3240692 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240691) (@lem3240688 A x u' u t' t h1 h2 h3)). Qed.
Lemma lem3240693 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : (u' x) = False.
Proof. exact (prop_ext (fun h4 : u' x => @lem3240692 A x u' u t' t h1 h2 h3) (fun h4 : False => @lem3240540 A u' x h2)). Qed.
Lemma lem3240694 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240693 A x u' u t' t h1 h2 h3) (@lem3240540 A u' x h2)). Qed.
Lemma lem3240695 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : (t' x) = False.
Proof. exact (prop_ext (fun h4 : t' x => @lem3240616 A x u' u t' t h1 h2 h3) (fun h4 : False => @lem3240522 A t' x h2)). Qed.
Lemma lem3240696 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240695 A x u' u t' t h1 h2 h3) (@lem3240522 A t' x h2)). Qed.
Lemma lem3240697 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : (u' x) = False.
Proof. exact (prop_ext (fun h4 : u' x => @lem3240694 A x u' u t' t h1 h2 h3) (fun h4 : False => @lem3240492 A u' x h2)). Qed.
Lemma lem3240698 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240697 A x u' u t' t h1 h2 h3) (@lem3240492 A u' x h2)). Qed.
Lemma lem3240699 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : (t' x) = False.
Proof. exact (prop_ext (fun h4 : t' x => @lem3240696 A x u' u t' t h1 h2 h3) (fun h4 : False => @lem3240454 A t' x h2)). Qed.
Lemma lem3240700 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240699 A x u' u t' t h1 h2 h3) (@lem3240454 A t' x h2)). Qed.
Lemma lem3240701 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : (u' x) = False.
Proof. exact (prop_ext (fun h4 : u' x => @lem3240698 A x u' u t' t h1 h2 h3) (fun h4 : False => @lem3240492 A u' x h2)). Qed.
Lemma lem3240702 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : u' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240701 A x u' u t' t h1 h2 h3) (@lem3240492 A u' x h2)). Qed.
Lemma lem3240703 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : (t' x) = False.
Proof. exact (prop_ext (fun h4 : t' x => @lem3240700 A x u' u t' t h1 h2 h3) (fun h4 : False => @lem3240454 A t' x h2)). Qed.
Lemma lem3240704 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term69 A t u x) (h2 : t' x) (h3 : term29 A u' u t' t) : False.
Proof. exact (EQ_MP (@lem3240703 A x u' u t' t h1 h2 h3) (@lem3240454 A t' x h2)). Qed.
Lemma lem3240705 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term69 A t u x) (h2 : term29 A u' u t' t) (h3 : term35 A t' u' x) : False.
Proof. exact (or_elim (@lem3240396 A t' u' x h3) (fun h0 : t' x => @lem3240704 A x u' u t' t h1 h0 h2) (fun h0 : u' x => @lem3240702 A x u' u t' t h1 h0 h2)). Qed.
Lemma lem3240706 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term69 A t u x) (h2 : term29 A u' u t' t) (h3 : term35 A t' u' x) : (term35 A t' u' x) = False.
Proof. exact (prop_ext (fun h4 : term35 A t' u' x => @lem3240705 A u t t' u' x h1 h2 h3) (fun h4 : False => @lem3240396 A t' u' x h3)). Qed.
Lemma lem3240707 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term69 A t u x) (h2 : term29 A u' u t' t) (h3 : term35 A t' u' x) : False.
Proof. exact (EQ_MP (@lem3240706 A u t t' u' x h1 h2 h3) (@lem3240396 A t' u' x h3)). Qed.
Lemma lem3240708 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term69 A t u x) (h2 : term29 A u' u t' t) (h3 : term35 A t' u' x) : (term35 A t' u' x) = False.
Proof. exact (prop_ext (fun h4 : term35 A t' u' x => @lem3240707 A u t t' u' x h1 h2 h3) (fun h4 : False => @lem3240342 A t' u' x h3)). Qed.
Lemma lem3240709 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term69 A t u x) (h2 : term29 A u' u t' t) (h3 : term35 A t' u' x) : False.
Proof. exact (EQ_MP (@lem3240708 A u t t' u' x h1 h2 h3) (@lem3240342 A t' u' x h3)). Qed.
Lemma lem3240710 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term69 A t u x) (h2 : term29 A u' u t' t) (h3 : term35 A t' u' x) : (term69 A t u x) = False.
Proof. exact (prop_ext (fun h4 : term69 A t u x => @lem3240709 A u t t' u' x h1 h2 h3) (fun h4 : False => @lem3240240 A t u x h1)). Qed.
Lemma lem3240711 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term69 A t u x) (h2 : term29 A u' u t' t) (h3 : term35 A t' u' x) : False.
Proof. exact (EQ_MP (@lem3240710 A u t t' u' x h1 h2 h3) (@lem3240240 A t u x h1)). Qed.
Lemma lem3240712 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term29 A u' u t' t) (h2 : term35 A t' u' x) : term68 A t u x.
Proof. exact (fun h0 : term69 A t u x => @lem3240711 A u t t' u' x h0 h1 h2). Qed.
Lemma lem3240713 {A : Type'} (u : A -> Prop) (t : A -> Prop) (t' : A -> Prop) (u' : A -> Prop) (x : A) (h1 : term29 A u' u t' t) (h2 : term35 A t' u' x) : term35 A t u x.
Proof. exact (EQ_MP (@lem3240239 A t u x) (@lem3240712 A u t t' u' x h1 h2)). Qed.
Lemma lem3240714 {A : Type'} (x : A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term39 A t' u' t u x.
Proof. exact (fun h0 : term35 A t' u' x => @lem3240713 A u t t' u' x h1 h0). Qed.
Lemma lem3240719 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term29 A u' u t' t) : term42 A t' u' t u.
Proof. exact (fun x : A => @lem3240714 A x u' u t' t h1). Qed.
Lemma lem3240720 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term43 A t' u' t u.
Proof. exact (fun h0 : term29 A u' u t' t => @lem3240719 A u' u t' t h0). Qed.
Lemma lem3240725 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term55 A u' t u.
Proof. exact (fun t' : A -> Prop => @lem3240720 A t' u' t u). Qed.
Lemma lem3240730 {A : Type'} (t : A -> Prop) (u : A -> Prop) : term59 A t u.
Proof. exact (fun u' : A -> Prop => @lem3240725 A u' t u). Qed.
Lemma lem3240735 {A : Type'} (u : A -> Prop) : term63 A u.
Proof. exact (fun t : A -> Prop => @lem3240730 A t u). Qed.
Lemma lem3240740 {A : Type'} : term67 A.
Proof. exact (fun u : A -> Prop => @lem3240735 A u). Qed.
Lemma lem3240741 {A : Type'} : term66 A.
Proof. exact (EQ_MP (@lem3240233 A) (@lem3240740 A)). Qed.
Lemma lem3240742 {A : Type'} (u : A -> Prop) : term89 A u.
Proof. exact (@lem3240741 A u). Qed.
Lemma lem3240743 {A : Type'} (u : A -> Prop) : (term89 A u) = (term62 A u).
Proof. exact (eq_refl (term89 A u)). Qed.
Lemma lem3240744 {A : Type'} (u : A -> Prop) : term62 A u.
Proof. exact (EQ_MP (@lem3240743 A u) (@lem3240742 A u)). Qed.
Lemma lem3240745 {A : Type'} (u : A -> Prop) (t : A -> Prop) : term90 A u t.
Proof. exact (@lem3240744 A u t). Qed.
Lemma lem3240746 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term90 A u t) = (term58 A t u).
Proof. exact (eq_refl (term90 A u t)). Qed.
Lemma lem3240747 {A : Type'} (t : A -> Prop) (u : A -> Prop) : term58 A t u.
Proof. exact (EQ_MP (@lem3240746 A t u) (@lem3240745 A u t)). Qed.
Lemma lem3240748 {A : Type'} (t : A -> Prop) (u : A -> Prop) (u' : A -> Prop) : term91 A t u u'.
Proof. exact (@lem3240747 A t u u'). Qed.
Lemma lem3240749 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term91 A t u u') = (term54 A u' t u).
Proof. exact (eq_refl (term91 A t u u')). Qed.
Lemma lem3240750 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term54 A u' t u.
Proof. exact (EQ_MP (@lem3240749 A u' t u) (@lem3240748 A t u u')). Qed.
Lemma lem3240751 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (t' : A -> Prop) : term92 A u' t u t'.
Proof. exact (@lem3240750 A u' t u t'). Qed.
Lemma lem3240752 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term92 A u' t u t') = (term45 A t' u' t u).
Proof. exact (eq_refl (term92 A u' t u t')). Qed.
Lemma lem3240753 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term45 A t' u' t u.
Proof. exact (EQ_MP (@lem3240752 A t' u' t u) (@lem3240751 A u' t u t')). Qed.
Lemma lem3240755 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term45 A t' u' t u.
Proof. exact (@lem3240042 A t' u' t u (@lem3240753 A t' u' t u)). Qed.
Lemma lem3240756 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term46 A t' u' t u) : False.
Proof. exact (@lem3240755 A t' u' t u (@lem3240026 A t' u' t u h1)). Qed.
Lemma lem3240757 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term46 A t' u' t u) : (term46 A t' u' t u) = False.
Proof. exact (prop_ext (fun h2 : term46 A t' u' t u => @lem3240756 A t' u' t u h1) (fun h2 : False => @lem3240026 A t' u' t u h1)). Qed.
Lemma lem3240758 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term46 A t' u' t u) : False.
Proof. exact (EQ_MP (@lem3240757 A t' u' t u h1) (@lem3240026 A t' u' t u h1)). Qed.
Lemma lem3240759 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term45 A t' u' t u.
Proof. exact (fun h0 : term46 A t' u' t u => @lem3240758 A t' u' t u h0). Qed.
Lemma lem3240760 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term43 A t' u' t u.
Proof. exact (EQ_MP (@lem3240025 A t' u' t u) (@lem3240759 A t' u' t u)). Qed.
Lemma lem3240761 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term20 A t' u' t u.
Proof. exact (EQ_MP (@lem3240021 A t' u' t u) (@lem3240760 A t' u' t u)). Qed.
Lemma lem3240762 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term19 A t' u' t u.
Proof. exact (EQ_MP (@lem3239896 A t' u' t u) (@lem3240761 A t' u' t u)). Qed.
Lemma lem3240763 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : @SUBSET A t' t) (h2 : @SUBSET A u' u) : term17 A t' u' t u.
Proof. exact (@lem3240762 A t' u' t u (@lem3239851 A t' t u' u h1 h2)). Qed.
Lemma lem3240764 {A : Type'} (P : type686 A) (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : @SUBSET A t' t) (h3 : @SUBSET A u' u) : term93 A P t' u'.
Proof. exact (@lem3239840 A t' u' t u P h1 (@lem3240763 A t' t u' u h2 h3)). Qed.
Lemma lem3240765 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term4 A t' t u' u) : @SUBSET A u' u.
Proof. exact (proj2 (@lem3239818 A t' t u' u h1)). Qed.
Lemma lem3240766 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term4 A t' t u' u) : @SUBSET A t' t.
Proof. exact (proj1 (@lem3239818 A t' t u' u h1)). Qed.
Lemma lem3240767 {A : Type'} (P : type686 A) (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : @SUBSET A t' t) (h3 : @SUBSET A u' u) : (@SUBSET A u' u) = (term93 A P t' u').
Proof. exact (prop_ext (fun h4 : @SUBSET A u' u => @lem3240764 A P t' t u' u h1 h2 h3) (fun h4 : term93 A P t' u' => @lem3239819 A u' u h3)). Qed.
Lemma lem3240768 {A : Type'} (P : type686 A) (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : @SUBSET A t' t) (h3 : @SUBSET A u' u) : term93 A P t' u'.
Proof. exact (EQ_MP (@lem3240767 A P t' t u' u h1 h2 h3) (@lem3239819 A u' u h3)). Qed.
Lemma lem3240769 {A : Type'} (P : type686 A) (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : @SUBSET A t' t) (h3 : @SUBSET A u' u) : (@SUBSET A t' t) = (term93 A P t' u').
Proof. exact (prop_ext (fun h4 : @SUBSET A t' t => @lem3240768 A P t' t u' u h1 h2 h3) (fun h4 : term93 A P t' u' => @lem3239820 A t' t h2)). Qed.
Lemma lem3240770 {A : Type'} (P : type686 A) (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : @SUBSET A t' t) (h3 : @SUBSET A u' u) : term93 A P t' u'.
Proof. exact (EQ_MP (@lem3240769 A P t' t u' u h1 h2 h3) (@lem3239820 A t' t h2)). Qed.
Lemma lem3240771 {A : Type'} (P : type686 A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term3 A t u P) (h2 : term4 A t' t u' u) (h3 : @SUBSET A t' t) : (@SUBSET A u' u) = (term93 A P t' u').
Proof. exact (prop_ext (fun h4 : @SUBSET A u' u => @lem3240770 A P t' t u' u h1 h3 h4) (fun h4 : term93 A P t' u' => @lem3240765 A t' t u' u h2)). Qed.
Lemma lem3240772 {A : Type'} (P : type686 A) (u' : A -> Prop) (u : A -> Prop) (t' : A -> Prop) (t : A -> Prop) (h1 : term3 A t u P) (h2 : term4 A t' t u' u) (h3 : @SUBSET A t' t) : term93 A P t' u'.
Proof. exact (EQ_MP (@lem3240771 A P u' u t' t h1 h2 h3) (@lem3240765 A t' t u' u h2)). Qed.
Lemma lem3240773 {A : Type'} (P : type686 A) (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : term4 A t' t u' u) : (@SUBSET A t' t) = (term93 A P t' u').
Proof. exact (prop_ext (fun h3 : @SUBSET A t' t => @lem3240772 A P u' u t' t h1 h2 h3) (fun h3 : term93 A P t' u' => @lem3240766 A t' t u' u h2)). Qed.
Lemma lem3240774 {A : Type'} (P : type686 A) (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (h1 : term3 A t u P) (h2 : term4 A t' t u' u) : term93 A P t' u'.
Proof. exact (EQ_MP (@lem3240773 A P t' t u' u h1 h2) (@lem3240766 A t' t u' u h2)). Qed.
Lemma lem3240775 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term94 A t u P t' u'.
Proof. exact (fun h0 : term4 A t' t u' u => @lem3240774 A P t' t u' u h1 h0). Qed.
Lemma lem3240780 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term95 A t u P t'.
Proof. exact (fun u' : A -> Prop => @lem3240775 A t' u' t u P h1). Qed.
Lemma lem3240785 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term96 A t u P.
Proof. exact (fun t' : A -> Prop => @lem3240780 A t' t u P h1). Qed.
Lemma lem3240786 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : (term3 A t u P) = (term96 A t u P).
Proof. exact (prop_ext (fun h2 : term3 A t u P => @lem3240785 A t u P h1) (fun h2 : term96 A t u P => @lem3239817 A t u P h1)). Qed.
Lemma lem3240787 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term3 A t u P) : term96 A t u P.
Proof. exact (EQ_MP (@lem3240786 A t u P h1) (@lem3239817 A t u P h1)). Qed.
Lemma lem3240788 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : term97 A t u P.
Proof. exact (fun h0 : term3 A t u P => @lem3240787 A t u P h0). Qed.
Lemma lem3240789 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term96 A t u P) : term96 A t u P.
Proof. exact (h1). Qed.
Lemma lem3240790 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term7 A s t u) : term7 A s t u.
Proof. exact (h1). Qed.
Lemma lem3240791 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term96 A t u P) : term98 A u P s t.
Proof. exact (@lem3240789 A t u P h1 (@INTER A s t)). Qed.
Lemma lem3240792 {A : Type'} (u : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term98 A u P s t) = (term99 A u P s t).
Proof. exact (eq_refl (term98 A u P s t)). Qed.
Lemma lem3240793 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term96 A t u P) : term99 A u P s t.
Proof. exact (EQ_MP (@lem3240792 A u P s t) (@lem3240791 A s t u P h1)). Qed.
Lemma lem3240794 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term96 A t u P) : term100 A P t s u.
Proof. exact (@lem3240793 A s t u P h1 (@INTER A s u)). Qed.
Lemma lem3240795 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term100 A P t s u) = (term101 A P t s u).
Proof. exact (eq_refl (term100 A P t s u)). Qed.
Lemma lem3240796 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term96 A t u P) : term101 A P t s u.
Proof. exact (EQ_MP (@lem3240795 A P t s u) (@lem3240794 A s t u P h1)). Qed.
Lemma lem3240798 (p : Prop) (q : Prop) (r : Prop) : term102 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem3240799 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (s : A -> Prop) : term103 A t u P s.
Proof. exact (@lem3240798 (term104 A t s u) (term105 A P t s u) (P s)). Qed.
Lemma lem3240801 (a : Prop) (b : Prop) : term0 a b.
Proof. exact (@lem3239815 a b (@lem1157 a b)). Qed.
Lemma lem3240802 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (s : A -> Prop) : term106 A t u P s.
Proof. exact (@lem3240801 (term105 A P t s u) (P s)). Qed.
Lemma lem3240803 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3240814 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : term107 A s t u P.
Proof. exact (conj (@lem3240790 A s t u h2) (@lem3240789 A t u P h1)). Qed.
Lemma lem3240820 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3240821 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3240820 A s t). Qed.
Lemma lem3240822 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term7 A s t u) = (term108 A s t u).
Proof. exact (@lem3240821 A s (@UNION A t u)). Qed.
Lemma lem3240829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3240830 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term109 A s t u) = (term110 A s t u).
Proof. exact (MK_COMB (@lem3240829) (@lem3240822 A s t u)). Qed.
Lemma lem3240844 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3240845 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3240844 A s t). Qed.
Lemma lem3240846 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (@SUBSET A t' t) = (term11 A t' t).
Proof. exact (@lem3240845 A t' t). Qed.
Lemma lem3240853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3240854 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term12 A t' t) = (term13 A t' t).
Proof. exact (MK_COMB (@lem3240853) (@lem3240846 A t' t)). Qed.
Lemma lem3240856 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3240857 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3240856 A s t). Qed.
Lemma lem3240858 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (@SUBSET A u' u) = (term11 A u' u).
Proof. exact (@lem3240857 A u' u). Qed.
Lemma lem3240865 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term4 A t' t u' u) = (term14 A t' t u' u).
Proof. exact (MK_COMB (@lem3240854 A t' t) (@lem3240858 A u' u)). Qed.
Lemma lem3240868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3240869 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term15 A t' t u' u) = (term16 A t' t u' u).
Proof. exact (MK_COMB (@lem3240868) (@lem3240865 A t' t u' u)). Qed.
Lemma lem3240870 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3240871 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term94 A t u P t' u') = (term111 A t u P t' u').
Proof. exact (MK_COMB (@lem3240869 A t' t u' u) (@lem3240870 A P t' u')). Qed.
Lemma lem3240874 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term112 A t u P t') = (term113 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3240871 A t u P t' u')). Qed.
Lemma lem3240875 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240876 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term95 A t u P t') = (term114 A t u P t').
Proof. exact (MK_COMB (@lem3240875 A) (@lem3240874 A t u P t')). Qed.
Lemma lem3240881 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term115 A t u P) = (term116 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3240876 A t u P t')). Qed.
Lemma lem3240882 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3240883 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term96 A t u P) = (term117 A t u P).
Proof. exact (MK_COMB (@lem3240882 A) (@lem3240881 A t u P)). Qed.
Lemma lem3240888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term107 A s t u P) = (term118 A s t u P).
Proof. exact (MK_COMB (@lem3240830 A s t u) (@lem3240883 A t u P)). Qed.
Lemma lem3240891 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3240892 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term119 A s t u P) = (term120 A s t u P).
Proof. exact (MK_COMB (@lem3240891) (@lem3240888 A s t u P)). Qed.
Lemma lem3240896 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3240897 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3240896 A s t). Qed.
Lemma lem3240898 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term121 A s t) = (term122 A s t).
Proof. exact (@lem3240897 A (@INTER A s t) t). Qed.
Lemma lem3240905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3240906 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term123 A s t) = (term124 A s t).
Proof. exact (MK_COMB (@lem3240905) (@lem3240898 A s t)). Qed.
Lemma lem3240908 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3240909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3240908 A s t). Qed.
Lemma lem3240910 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term121 A s u) = (term122 A s u).
Proof. exact (@lem3240909 A (@INTER A s u) u). Qed.
Lemma lem3240917 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term104 A t s u) = (term125 A t s u).
Proof. exact (MK_COMB (@lem3240906 A s t) (@lem3240910 A s u)). Qed.
Lemma lem3240920 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term126 A P t s u) = (term127 A P t s u).
Proof. exact (MK_COMB (@lem3240892 A s t u P) (@lem3240917 A t s u)). Qed.
Lemma lem3240923 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term127 A P t s u) = (term126 A P t s u).
Proof. exact (SYM (@lem3240920 A P t s u)). Qed.
Lemma lem3240935 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3240936 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3240935 A P x). Qed.
Lemma lem3240937 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3240936 A s x). Qed.
Lemma lem3240938 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3240939 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3240938) (@lem3240937 A s x)). Qed.
Lemma lem3240941 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3240942 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (@lem3240941 A s x t). Qed.
Lemma lem3240943 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term31 A x t u) = (term32 A t x u).
Proof. exact (@lem3240942 A t x u). Qed.
Lemma lem3240947 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3240948 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3240947 A P x). Qed.
Lemma lem3240949 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3240948 A t x). Qed.
Lemma lem3240950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3240951 {A : Type'} (t : A -> Prop) (x : A) : (term33 A x t) = (term34 A t x).
Proof. exact (MK_COMB (@lem3240950) (@lem3240949 A t x)). Qed.
Lemma lem3240953 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3240954 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3240953 A P x). Qed.
Lemma lem3240955 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3240954 A u x). Qed.
Lemma lem3240956 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term32 A t x u) = (term35 A t u x).
Proof. exact (MK_COMB (@lem3240951 A t x) (@lem3240955 A u x)). Qed.
Lemma lem3240959 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term31 A x t u) = (term35 A t u x).
Proof. exact (TRANS (@lem3240943 A t x u) (@lem3240956 A t u x)). Qed.
Lemma lem3240960 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term128 A s x t u) = (term129 A s t u x).
Proof. exact (MK_COMB (@lem3240939 A s x) (@lem3240959 A t u x)). Qed.
Lemma lem3240963 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term130 A s t u) = (term131 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3240960 A s t u x)). Qed.
Lemma lem3240964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3240965 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term108 A s t u) = (term132 A s t u).
Proof. exact (MK_COMB (@lem3240964 A) (@lem3240963 A s t u)). Qed.
Lemma lem3240970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3240971 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term110 A s t u) = (term133 A s t u).
Proof. exact (MK_COMB (@lem3240970) (@lem3240965 A s t u)). Qed.
Lemma lem3240991 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3240992 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3240991 A P x). Qed.
Lemma lem3240993 {A : Type'} (t' : A -> Prop) (x : A) : (@IN A x t') = (t' x).
Proof. exact (@lem3240992 A t' x). Qed.
Lemma lem3240994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3240995 {A : Type'} (t' : A -> Prop) (x : A) : (term21 A x t') = (term22 A t' x).
Proof. exact (MK_COMB (@lem3240994) (@lem3240993 A t' x)). Qed.
Lemma lem3240997 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3240998 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3240997 A P x). Qed.
Lemma lem3240999 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3240998 A t x). Qed.
Lemma lem3241000 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term23 A t' x t) = (term24 A t' t x).
Proof. exact (MK_COMB (@lem3240995 A t' x) (@lem3240999 A t x)). Qed.
Lemma lem3241003 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term25 A t' t) = (term26 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3241000 A t' t x)). Qed.
Lemma lem3241004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241005 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term11 A t' t) = (term27 A t' t).
Proof. exact (MK_COMB (@lem3241004 A) (@lem3241003 A t' t)). Qed.
Lemma lem3241010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241011 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term13 A t' t) = (term28 A t' t).
Proof. exact (MK_COMB (@lem3241010) (@lem3241005 A t' t)). Qed.
Lemma lem3241019 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241020 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241019 A P x). Qed.
Lemma lem3241021 {A : Type'} (u' : A -> Prop) (x : A) : (@IN A x u') = (u' x).
Proof. exact (@lem3241020 A u' x). Qed.
Lemma lem3241022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3241023 {A : Type'} (u' : A -> Prop) (x : A) : (term21 A x u') = (term22 A u' x).
Proof. exact (MK_COMB (@lem3241022) (@lem3241021 A u' x)). Qed.
Lemma lem3241025 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241026 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241025 A P x). Qed.
Lemma lem3241027 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3241026 A u x). Qed.
Lemma lem3241028 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term23 A u' x u) = (term24 A u' u x).
Proof. exact (MK_COMB (@lem3241023 A u' x) (@lem3241027 A u x)). Qed.
Lemma lem3241031 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term25 A u' u) = (term26 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3241028 A u' u x)). Qed.
Lemma lem3241032 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241033 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term11 A u' u) = (term27 A u' u).
Proof. exact (MK_COMB (@lem3241032 A) (@lem3241031 A u' u)). Qed.
Lemma lem3241038 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term14 A t' t u' u) = (term29 A t' t u' u).
Proof. exact (MK_COMB (@lem3241011 A t' t) (@lem3241033 A u' u)). Qed.
Lemma lem3241041 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3241042 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term16 A t' t u' u) = (term30 A t' t u' u).
Proof. exact (MK_COMB (@lem3241041) (@lem3241038 A t' t u' u)). Qed.
Lemma lem3241043 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3241044 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term111 A t u P t' u') = (term134 A t u P t' u').
Proof. exact (MK_COMB (@lem3241042 A t' t u' u) (@lem3241043 A P t' u')). Qed.
Lemma lem3241047 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term113 A t u P t') = (term135 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3241044 A t u P t' u')). Qed.
Lemma lem3241048 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241049 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term114 A t u P t') = (term136 A t u P t').
Proof. exact (MK_COMB (@lem3241048 A) (@lem3241047 A t u P t')). Qed.
Lemma lem3241054 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term116 A t u P) = (term137 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3241049 A t u P t')). Qed.
Lemma lem3241055 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241056 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term117 A t u P) = (term138 A t u P).
Proof. exact (MK_COMB (@lem3241055 A) (@lem3241054 A t u P)). Qed.
Lemma lem3241061 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term118 A s t u P) = (term139 A s t u P).
Proof. exact (MK_COMB (@lem3240971 A s t u) (@lem3241056 A t u P)). Qed.
Lemma lem3241064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3241065 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term120 A s t u P) = (term140 A s t u P).
Proof. exact (MK_COMB (@lem3241064) (@lem3241061 A s t u P)). Qed.
Lemma lem3241075 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3241076 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (@lem3241075 A s x t). Qed.
Lemma lem3241080 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241081 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241080 A P x). Qed.
Lemma lem3241082 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3241081 A s x). Qed.
Lemma lem3241083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241084 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3241083) (@lem3241082 A s x)). Qed.
Lemma lem3241086 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241087 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241086 A P x). Qed.
Lemma lem3241088 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3241087 A t x). Qed.
Lemma lem3241089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term142 A s x t) = (term145 A s t x).
Proof. exact (MK_COMB (@lem3241084 A s x) (@lem3241088 A t x)). Qed.
Lemma lem3241092 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term141 A x s t) = (term145 A s t x).
Proof. exact (TRANS (@lem3241076 A s x t) (@lem3241089 A s t x)). Qed.
Lemma lem3241093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3241094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term146 A x s t) = (term147 A s t x).
Proof. exact (MK_COMB (@lem3241093) (@lem3241092 A s t x)). Qed.
Lemma lem3241096 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241097 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241096 A P x). Qed.
Lemma lem3241098 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3241097 A t x). Qed.
Lemma lem3241099 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term148 A s x t) = (term149 A s t x).
Proof. exact (MK_COMB (@lem3241094 A s t x) (@lem3241098 A t x)). Qed.
Lemma lem3241102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term151 A s t).
Proof. exact (fun_ext (fun x : A => @lem3241099 A s t x)). Qed.
Lemma lem3241103 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term122 A s t) = (term152 A s t).
Proof. exact (MK_COMB (@lem3241103 A) (@lem3241102 A s t)). Qed.
Lemma lem3241109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241110 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term153 A s t).
Proof. exact (MK_COMB (@lem3241109) (@lem3241104 A s t)). Qed.
Lemma lem3241118 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3241119 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (@lem3241118 A s x t). Qed.
Lemma lem3241120 {A : Type'} (s : A -> Prop) (x : A) (u : A -> Prop) : (term141 A x s u) = (term142 A s x u).
Proof. exact (@lem3241119 A s x u). Qed.
Lemma lem3241124 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241125 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241124 A P x). Qed.
Lemma lem3241126 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3241125 A s x). Qed.
Lemma lem3241127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241128 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3241127) (@lem3241126 A s x)). Qed.
Lemma lem3241130 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241131 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241130 A P x). Qed.
Lemma lem3241132 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3241131 A u x). Qed.
Lemma lem3241133 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term142 A s x u) = (term145 A s u x).
Proof. exact (MK_COMB (@lem3241128 A s x) (@lem3241132 A u x)). Qed.
Lemma lem3241136 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term141 A x s u) = (term145 A s u x).
Proof. exact (TRANS (@lem3241120 A s x u) (@lem3241133 A s u x)). Qed.
Lemma lem3241137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3241138 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term146 A x s u) = (term147 A s u x).
Proof. exact (MK_COMB (@lem3241137) (@lem3241136 A s u x)). Qed.
Lemma lem3241140 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3241141 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3241140 A P x). Qed.
Lemma lem3241142 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3241141 A u x). Qed.
Lemma lem3241143 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term148 A s x u) = (term149 A s u x).
Proof. exact (MK_COMB (@lem3241138 A s u x) (@lem3241142 A u x)). Qed.
Lemma lem3241146 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term150 A s u) = (term151 A s u).
Proof. exact (fun_ext (fun x : A => @lem3241143 A s u x)). Qed.
Lemma lem3241147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241148 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term122 A s u) = (term152 A s u).
Proof. exact (MK_COMB (@lem3241147 A) (@lem3241146 A s u)). Qed.
Lemma lem3241153 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term125 A t s u) = (term154 A t s u).
Proof. exact (MK_COMB (@lem3241110 A s t) (@lem3241148 A s u)). Qed.
Lemma lem3241156 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term127 A P t s u) = (term155 A P t s u).
Proof. exact (MK_COMB (@lem3241065 A s t u P) (@lem3241153 A t s u)). Qed.
Lemma lem3241159 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term155 A P t s u) = (term127 A P t s u).
Proof. exact (SYM (@lem3241156 A P t s u)). Qed.
Lemma lem3241161 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3241162 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term155 A P t s u) = (term156 A P t s u).
Proof. exact (@lem3241161 (term155 A P t s u)). Qed.
Lemma lem3241163 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term156 A P t s u) = (term155 A P t s u).
Proof. exact (SYM (@lem3241162 A P t s u)). Qed.
Lemma lem3241164 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term157 A P t s u) : term157 A P t s u.
Proof. exact (h1). Qed.
Lemma lem3241167 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term156 A P t s u) : term156 A P t s u.
Proof. exact (h1). Qed.
Lemma lem3241168 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term158 A P t s u.
Proof. exact (fun h0 : term156 A P t s u => @lem3241167 A P t s u h0). Qed.
Lemma lem3241169 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term158 A P t s u) : term158 A P t s u.
Proof. exact (h1). Qed.
Lemma lem3241170 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term156 A P t s u) : term156 A P t s u.
Proof. exact (h1). Qed.
Lemma lem3241171 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term156 A P t s u) (h2 : term158 A P t s u) : term156 A P t s u.
Proof. exact (@lem3241169 A P t s u h2 (@lem3241170 A P t s u h1)). Qed.
Lemma lem3241172 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term156 A P t s u) : term159 A P t s u.
Proof. exact (fun h0 : term158 A P t s u => @lem3241171 A P t s u h1 h0). Qed.
Lemma lem3241173 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term158 A P t s u) : term158 A P t s u.
Proof. exact (h1). Qed.
Lemma lem3241174 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term156 A P t s u) (h2 : term158 A P t s u) : term156 A P t s u.
Proof. exact (@lem3241172 A P t s u h1 (@lem3241173 A P t s u h2)). Qed.
Lemma lem3241175 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term158 A P t s u) : term158 A P t s u.
Proof. exact (fun h0 : term156 A P t s u => @lem3241174 A P t s u h0 h1). Qed.
Lemma lem3241176 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term160 A P t s u.
Proof. exact (fun h0 : term158 A P t s u => @lem3241175 A P t s u h0). Qed.
Lemma lem3241179 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term158 A P t s u.
Proof. exact (@lem3241176 A P t s u (@lem3241168 A P t s u)). Qed.
Lemma lem3241180 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term158 A P t s u.
Proof. exact (@lem3241179 A P t s u). Qed.
Lemma lem3241198 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3241199 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term156 A P t s u) = (term161 A P t s u).
Proof. exact (@lem3241198 (term157 A P t s u)). Qed.
Lemma lem3241201 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3241202 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term161 A P t s u) = (term155 A P t s u).
Proof. exact (@lem3241201 (term155 A P t s u)). Qed.
Lemma lem3241205 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term156 A P t s u) = (term155 A P t s u).
Proof. exact (TRANS (@lem3241199 A P t s u) (@lem3241202 A P t s u)). Qed.
Lemma lem3241258 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term162 A t s u) = (term163 A t s u).
Proof. exact (fun_ext (fun P : type686 A => @lem3241205 A P t s u)). Qed.
Lemma lem3241259 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3241260 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term164 A t s u) = (term165 A t s u).
Proof. exact (MK_COMB (@lem3241259 A) (@lem3241258 A t s u)). Qed.
Lemma lem3241265 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term166 A s u) = (term167 A s u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3241260 A t s u)). Qed.
Lemma lem3241266 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241267 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term168 A s u) = (term169 A s u).
Proof. exact (MK_COMB (@lem3241266 A) (@lem3241265 A s u)). Qed.
Lemma lem3241272 {A : Type'} (u : A -> Prop) : (term170 A u) = (term171 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3241267 A s u)). Qed.
Lemma lem3241273 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241274 {A : Type'} (u : A -> Prop) : (term172 A u) = (term173 A u).
Proof. exact (MK_COMB (@lem3241273 A) (@lem3241272 A u)). Qed.
Lemma lem3241279 {A : Type'} : (term174 A) = (term175 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3241274 A u)). Qed.
Lemma lem3241280 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241289 {A : Type'} : (term176 A) = (term177 A).
Proof. exact (MK_COMB (@lem3241280 A) (@lem3241279 A)). Qed.
Lemma lem3241298 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term149 A s u x) = (term149 A s u x).
Proof. exact (eq_refl (term149 A s u x)). Qed.
Lemma lem3241299 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term151 A s u) = (term151 A s u).
Proof. exact (fun_ext (fun x : A => @lem3241298 A s u x)). Qed.
Lemma lem3241300 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241301 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term152 A s u) = (term152 A s u).
Proof. exact (MK_COMB (@lem3241300 A) (@lem3241299 A s u)). Qed.
Lemma lem3241310 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term149 A s t x) = (term149 A s t x).
Proof. exact (eq_refl (term149 A s t x)). Qed.
Lemma lem3241311 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term151 A s t).
Proof. exact (fun_ext (fun x : A => @lem3241310 A s t x)). Qed.
Lemma lem3241312 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241313 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A s t) = (term152 A s t).
Proof. exact (MK_COMB (@lem3241312 A) (@lem3241311 A s t)). Qed.
Lemma lem3241314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241315 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term153 A s t) = (term153 A s t).
Proof. exact (MK_COMB (@lem3241314) (@lem3241313 A s t)). Qed.
Lemma lem3241316 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term154 A t s u) = (term154 A t s u).
Proof. exact (MK_COMB (@lem3241315 A s t) (@lem3241301 A s u)). Qed.
Lemma lem3241317 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3241322 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term24 A u' u x) = (term24 A u' u x).
Proof. exact (eq_refl (term24 A u' u x)). Qed.
Lemma lem3241323 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term26 A u' u) = (term26 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3241322 A u' u x)). Qed.
Lemma lem3241324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241325 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term27 A u' u) = (term27 A u' u).
Proof. exact (MK_COMB (@lem3241324 A) (@lem3241323 A u' u)). Qed.
Lemma lem3241330 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term24 A t' t x) = (term24 A t' t x).
Proof. exact (eq_refl (term24 A t' t x)). Qed.
Lemma lem3241331 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term26 A t' t) = (term26 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3241330 A t' t x)). Qed.
Lemma lem3241332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241333 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term27 A t' t) = (term27 A t' t).
Proof. exact (MK_COMB (@lem3241332 A) (@lem3241331 A t' t)). Qed.
Lemma lem3241334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241335 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term28 A t' t) = (term28 A t' t).
Proof. exact (MK_COMB (@lem3241334) (@lem3241333 A t' t)). Qed.
Lemma lem3241336 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term29 A t' t u' u) = (term29 A t' t u' u).
Proof. exact (MK_COMB (@lem3241335 A t' t) (@lem3241325 A u' u)). Qed.
Lemma lem3241337 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3241338 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term30 A t' t u' u) = (term30 A t' t u' u).
Proof. exact (MK_COMB (@lem3241337) (@lem3241336 A t' t u' u)). Qed.
Lemma lem3241339 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term134 A t u P t' u') = (term134 A t u P t' u').
Proof. exact (MK_COMB (@lem3241338 A t' t u' u) (@lem3241317 A P t' u')). Qed.
Lemma lem3241340 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term135 A t u P t') = (term135 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3241339 A t u P t' u')). Qed.
Lemma lem3241341 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241342 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term136 A t u P t') = (term136 A t u P t').
Proof. exact (MK_COMB (@lem3241341 A) (@lem3241340 A t u P t')). Qed.
Lemma lem3241343 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term137 A t u P) = (term137 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3241342 A t u P t')). Qed.
Lemma lem3241344 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241345 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term138 A t u P) = (term138 A t u P).
Proof. exact (MK_COMB (@lem3241344 A) (@lem3241343 A t u P)). Qed.
Lemma lem3241354 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term129 A s t u x) = (term129 A s t u x).
Proof. exact (eq_refl (term129 A s t u x)). Qed.
Lemma lem3241355 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term131 A s t u) = (term131 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3241354 A s t u x)). Qed.
Lemma lem3241356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241357 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term132 A s t u) = (term132 A s t u).
Proof. exact (MK_COMB (@lem3241356 A) (@lem3241355 A s t u)). Qed.
Lemma lem3241358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241359 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term133 A s t u) = (term133 A s t u).
Proof. exact (MK_COMB (@lem3241358) (@lem3241357 A s t u)). Qed.
Lemma lem3241360 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term139 A s t u P) = (term139 A s t u P).
Proof. exact (MK_COMB (@lem3241359 A s t u) (@lem3241345 A t u P)). Qed.
Lemma lem3241361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3241362 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term140 A s t u P) = (term140 A s t u P).
Proof. exact (MK_COMB (@lem3241361) (@lem3241360 A s t u P)). Qed.
Lemma lem3241363 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term155 A P t s u) = (term155 A P t s u).
Proof. exact (MK_COMB (@lem3241362 A s t u P) (@lem3241316 A t s u)). Qed.
Lemma lem3241364 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term163 A t s u) = (term163 A t s u).
Proof. exact (fun_ext (fun P : type686 A => @lem3241363 A P t s u)). Qed.
Lemma lem3241365 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3241366 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term165 A t s u) = (term165 A t s u).
Proof. exact (MK_COMB (@lem3241365 A) (@lem3241364 A t s u)). Qed.
Lemma lem3241367 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term167 A s u) = (term167 A s u).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3241366 A t s u)). Qed.
Lemma lem3241368 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241369 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term169 A s u) = (term169 A s u).
Proof. exact (MK_COMB (@lem3241368 A) (@lem3241367 A s u)). Qed.
Lemma lem3241370 {A : Type'} (u : A -> Prop) : (term171 A u) = (term171 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3241369 A s u)). Qed.
Lemma lem3241371 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241372 {A : Type'} (u : A -> Prop) : (term173 A u) = (term173 A u).
Proof. exact (MK_COMB (@lem3241371 A) (@lem3241370 A u)). Qed.
Lemma lem3241373 {A : Type'} : (term175 A) = (term175 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3241372 A u)). Qed.
Lemma lem3241374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241375 {A : Type'} : (term177 A) = (term177 A).
Proof. exact (MK_COMB (@lem3241374 A) (@lem3241373 A)). Qed.
Lemma lem3241470 {A : Type'} : (term176 A) = (term177 A).
Proof. exact (TRANS (@lem3241289 A) (@lem3241375 A)). Qed.
Lemma lem3241471 {A : Type'} : (term177 A) = (term176 A).
Proof. exact (SYM (@lem3241470 A)). Qed.
Lemma lem3241472 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term139 A s t u P.
Proof. exact (h1). Qed.
Lemma lem3241474 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3241475 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term154 A t s u) = (term178 A t s u).
Proof. exact (@lem3241474 (term154 A t s u)). Qed.
Lemma lem3241476 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term178 A t s u) = (term154 A t s u).
Proof. exact (SYM (@lem3241475 A t s u)). Qed.
Lemma lem3241477 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term179 A t s u) : term179 A t s u.
Proof. exact (h1). Qed.
Lemma lem3241488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term129 A s t u x) = (term180 A s t u x).
Proof. exact (@lem17265 (s x) (term35 A t u x)). Qed.
Lemma lem3241489 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term131 A s t u) = (term181 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3241488 A s t u x)). Qed.
Lemma lem3241490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3241491 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term132 A s t u) = (term182 A s t u).
Proof. exact (MK_COMB (@lem3241490 A) (@lem3241489 A s t u)). Qed.
Lemma lem3241498 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term183 A t' t x) = (term184 A t' t x).
Proof. exact (@lem17362 (t' x) (t x)). Qed.
Lemma lem3241499 {A : Type'} (P : A -> Prop) : (term185 A P) = (term186 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3241500 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term187 A t' t) = (term188 A t' t).
Proof. exact (@lem3241499 A (term26 A t' t)). Qed.
Lemma lem3241501 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term189 A t' t x) = (term24 A t' t x).
Proof. exact (eq_refl (term189 A t' t x)). Qed.
Lemma lem3241502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3241503 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term190 A t' t x) = (term183 A t' t x).
Proof. exact (MK_COMB (@lem3241502) (@lem3241501 A t' t x)). Qed.
Lemma lem3241504 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term190 A t' t x) = (term184 A t' t x).
Proof. exact (TRANS (@lem3241503 A t' t x) (@lem3241498 A t' t x)). Qed.
Lemma lem3241505 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term191 A t' t) = (term192 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3241504 A t' t x)). Qed.
Lemma lem3241506 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241507 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term188 A t' t) = (term193 A t' t).
Proof. exact (MK_COMB (@lem3241506 A) (@lem3241505 A t' t)). Qed.
Lemma lem3241508 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term187 A t' t) = (term193 A t' t).
Proof. exact (TRANS (@lem3241500 A t' t) (@lem3241507 A t' t)). Qed.
Lemma lem3241515 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term183 A u' u x) = (term184 A u' u x).
Proof. exact (@lem17362 (u' x) (u x)). Qed.
Lemma lem3241516 {A : Type'} (P : A -> Prop) : (term185 A P) = (term186 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3241517 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term187 A u' u) = (term188 A u' u).
Proof. exact (@lem3241516 A (term26 A u' u)). Qed.
Lemma lem3241518 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term189 A u' u x) = (term24 A u' u x).
Proof. exact (eq_refl (term189 A u' u x)). Qed.
Lemma lem3241519 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3241520 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term190 A u' u x) = (term183 A u' u x).
Proof. exact (MK_COMB (@lem3241519) (@lem3241518 A u' u x)). Qed.
Lemma lem3241521 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term190 A u' u x) = (term184 A u' u x).
Proof. exact (TRANS (@lem3241520 A u' u x) (@lem3241515 A u' u x)). Qed.
Lemma lem3241522 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term191 A u' u) = (term192 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3241521 A u' u x)). Qed.
Lemma lem3241523 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241524 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term188 A u' u) = (term193 A u' u).
Proof. exact (MK_COMB (@lem3241523 A) (@lem3241522 A u' u)). Qed.
Lemma lem3241525 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term187 A u' u) = (term193 A u' u).
Proof. exact (TRANS (@lem3241517 A u' u) (@lem3241524 A u' u)). Qed.
Lemma lem3241526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241527 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term194 A t' t) = (term195 A t' t).
Proof. exact (MK_COMB (@lem3241526) (@lem3241508 A t' t)). Qed.
Lemma lem3241528 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term196 A t' t u' u) = (term197 A t' t u' u).
Proof. exact (MK_COMB (@lem3241527 A t' t) (@lem3241525 A u' u)). Qed.
Lemma lem3241529 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term198 A t' t u' u) = (term196 A t' t u' u).
Proof. exact (@lem17045 (term27 A t' t) (term27 A u' u)). Qed.
Lemma lem3241530 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term198 A t' t u' u) = (term197 A t' t u' u).
Proof. exact (TRANS (@lem3241529 A t' t u' u) (@lem3241528 A t' t u' u)). Qed.
Lemma lem3241531 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3241532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241533 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term199 A t' t u' u) = (term200 A t' t u' u).
Proof. exact (MK_COMB (@lem3241532) (@lem3241530 A t' t u' u)). Qed.
Lemma lem3241534 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term201 A t u P t' u') = (term202 A t u P t' u').
Proof. exact (MK_COMB (@lem3241533 A t' t u' u) (@lem3241531 A P t' u')). Qed.
Lemma lem3241535 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term134 A t u P t' u') = (term201 A t u P t' u').
Proof. exact (@lem17265 (term29 A t' t u' u) (term93 A P t' u')). Qed.
Lemma lem3241536 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term134 A t u P t' u') = (term202 A t u P t' u').
Proof. exact (TRANS (@lem3241535 A t u P t' u') (@lem3241534 A t u P t' u')). Qed.
Lemma lem3241537 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term135 A t u P t') = (term203 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3241536 A t u P t' u')). Qed.
Lemma lem3241538 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241539 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term136 A t u P t') = (term204 A t u P t').
Proof. exact (MK_COMB (@lem3241538 A) (@lem3241537 A t u P t')). Qed.
Lemma lem3241540 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term137 A t u P) = (term205 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3241539 A t u P t')). Qed.
Lemma lem3241541 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241542 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term138 A t u P) = (term206 A t u P).
Proof. exact (MK_COMB (@lem3241541 A) (@lem3241540 A t u P)). Qed.
Lemma lem3241543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3241544 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term133 A s t u) = (term207 A s t u).
Proof. exact (MK_COMB (@lem3241543) (@lem3241491 A s t u)). Qed.
Lemma lem3241545 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term139 A s t u P) = (term208 A s t u P).
Proof. exact (MK_COMB (@lem3241544 A s t u) (@lem3241542 A t u P)). Qed.
Lemma lem3241704 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3241705 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (@lem3241704 A P Q). Qed.
Lemma lem3241706 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term211 A t' t u' u) = (term212 A t' t u' u).
Proof. exact (@lem3241705 A (term192 A t' t) (term192 A u' u)). Qed.
Lemma lem3241707 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term213 A t' t x) = (term184 A t' t x).
Proof. exact (eq_refl (term213 A t' t x)). Qed.
Lemma lem3241708 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term214 A t' t) = (term192 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3241707 A t' t x)). Qed.
Lemma lem3241709 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241710 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term215 A t' t) = (term193 A t' t).
Proof. exact (MK_COMB (@lem3241709 A) (@lem3241708 A t' t)). Qed.
Lemma lem3241711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241712 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term216 A t' t) = (term195 A t' t).
Proof. exact (MK_COMB (@lem3241711) (@lem3241710 A t' t)). Qed.
Lemma lem3241713 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term213 A u' u x) = (term184 A u' u x).
Proof. exact (eq_refl (term213 A u' u x)). Qed.
Lemma lem3241714 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term214 A u' u) = (term192 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3241713 A u' u x)). Qed.
Lemma lem3241715 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241716 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term215 A u' u) = (term193 A u' u).
Proof. exact (MK_COMB (@lem3241715 A) (@lem3241714 A u' u)). Qed.
Lemma lem3241717 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term211 A t' t u' u) = (term197 A t' t u' u).
Proof. exact (MK_COMB (@lem3241712 A t' t) (@lem3241716 A u' u)). Qed.
Lemma lem3241718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3241719 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term217 A t' t u' u) = (term218 A t' t u' u).
Proof. exact (MK_COMB (@lem3241718) (@lem3241717 A t' t u' u)). Qed.
Lemma lem3241720 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term213 A t' t x) = (term184 A t' t x).
Proof. exact (eq_refl (term213 A t' t x)). Qed.
Lemma lem3241721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241722 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term219 A t' t x) = (term220 A t' t x).
Proof. exact (MK_COMB (@lem3241721) (@lem3241720 A t' t x)). Qed.
Lemma lem3241723 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term213 A u' u x) = (term184 A u' u x).
Proof. exact (eq_refl (term213 A u' u x)). Qed.
Lemma lem3241724 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term221 A t' t u' u x) = (term222 A t' t u' u x).
Proof. exact (MK_COMB (@lem3241722 A t' t x) (@lem3241723 A u' u x)). Qed.
Lemma lem3241725 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term223 A t' t u' u) = (term224 A t' t u' u).
Proof. exact (fun_ext (fun x : A => @lem3241724 A t' t u' u x)). Qed.
Lemma lem3241726 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241727 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term212 A t' t u' u) = (term225 A t' t u' u).
Proof. exact (MK_COMB (@lem3241726 A) (@lem3241725 A t' t u' u)). Qed.
Lemma lem3241728 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : ((term211 A t' t u' u) = (term212 A t' t u' u)) = ((term197 A t' t u' u) = (term225 A t' t u' u)).
Proof. exact (MK_COMB (@lem3241719 A t' t u' u) (@lem3241727 A t' t u' u)). Qed.
Lemma lem3241729 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term197 A t' t u' u) = (term225 A t' t u' u).
Proof. exact (EQ_MP (@lem3241728 A t' t u' u) (@lem3241706 A t' t u' u)). Qed.
Lemma lem3241730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241731 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term200 A t' t u' u) = (term226 A t' t u' u).
Proof. exact (MK_COMB (@lem3241730) (@lem3241729 A t' t u' u)). Qed.
Lemma lem3241732 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3241733 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term202 A t u P t' u') = (term227 A t u P t' u').
Proof. exact (MK_COMB (@lem3241731 A t' t u' u) (@lem3241732 A P t' u')). Qed.
Lemma lem3241735 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3241736 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (@lem3241735 A P Q). Qed.
Lemma lem3241737 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term230 A t u P t' u') = (term231 A t u P t' u').
Proof. exact (@lem3241736 A (term224 A t' t u' u) (term93 A P t' u')). Qed.
Lemma lem3241738 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term232 A t' t u' u x) = (term222 A t' t u' u x).
Proof. exact (eq_refl (term232 A t' t u' u x)). Qed.
Lemma lem3241739 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term233 A t' t u' u) = (term224 A t' t u' u).
Proof. exact (fun_ext (fun x : A => @lem3241738 A t' t u' u x)). Qed.
Lemma lem3241740 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241741 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term234 A t' t u' u) = (term225 A t' t u' u).
Proof. exact (MK_COMB (@lem3241740 A) (@lem3241739 A t' t u' u)). Qed.
Lemma lem3241742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241743 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term235 A t' t u' u) = (term226 A t' t u' u).
Proof. exact (MK_COMB (@lem3241742) (@lem3241741 A t' t u' u)). Qed.
Lemma lem3241744 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3241745 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term230 A t u P t' u') = (term227 A t u P t' u').
Proof. exact (MK_COMB (@lem3241743 A t' t u' u) (@lem3241744 A P t' u')). Qed.
Lemma lem3241746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3241747 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term236 A t u P t' u') = (term237 A t u P t' u').
Proof. exact (MK_COMB (@lem3241746) (@lem3241745 A t u P t' u')). Qed.
Lemma lem3241748 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term232 A t' t u' u x) = (term222 A t' t u' u x).
Proof. exact (eq_refl (term232 A t' t u' u x)). Qed.
Lemma lem3241749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241750 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term238 A t' t u' u x) = (term239 A t' t u' u x).
Proof. exact (MK_COMB (@lem3241749) (@lem3241748 A t' t u' u x)). Qed.
Lemma lem3241751 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3241752 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term240 A t u x P t' u') = (term241 A t u x P t' u').
Proof. exact (MK_COMB (@lem3241750 A t' t u' u x) (@lem3241751 A P t' u')). Qed.
Lemma lem3241753 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term242 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (fun_ext (fun x : A => @lem3241752 A t u x P t' u')). Qed.
Lemma lem3241754 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241755 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term231 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (MK_COMB (@lem3241754 A) (@lem3241753 A t u P t' u')). Qed.
Lemma lem3241756 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : ((term230 A t u P t' u') = (term231 A t u P t' u')) = ((term227 A t u P t' u') = (term244 A t u P t' u')).
Proof. exact (MK_COMB (@lem3241747 A t u P t' u') (@lem3241755 A t u P t' u')). Qed.
Lemma lem3241757 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term227 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (EQ_MP (@lem3241756 A t u P t' u') (@lem3241737 A t u P t' u')). Qed.
Lemma lem3241758 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term202 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (TRANS (@lem3241733 A t u P t' u') (@lem3241757 A t u P t' u')). Qed.
Lemma lem3241759 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term203 A t u P t') = (term245 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3241758 A t u P t' u')). Qed.
Lemma lem3241760 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241761 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term204 A t u P t') = (term246 A t u P t').
Proof. exact (MK_COMB (@lem3241760 A) (@lem3241759 A t u P t')). Qed.
Lemma lem3241763 {A B : Type'} (P : type1413 A B) : (term247 A B P) = (term248 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3241764 {A : Type'} (P : type672 A) : (term249 A P) = (term250 A P).
Proof. exact (@lem3241763 (A -> Prop) A P). Qed.
Lemma lem3241765 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term251 A t u P t') = (term252 A t u P t').
Proof. exact (@lem3241764 A (term253 A t u P t')). Qed.
Lemma lem3241766 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term254 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (eq_refl (term254 A t u P t' u')). Qed.
Lemma lem3241767 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3241768 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (x : A) : (term255 A t u P t' u' x) = (term256 A t u P t' u' x).
Proof. exact (MK_COMB (@lem3241766 A t u P t' u') (@lem3241767 A x)). Qed.
Lemma lem3241769 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term256 A t u P t' u' x) = (term241 A t u x P t' u').
Proof. exact (eq_refl (term256 A t u P t' u' x)). Qed.
Lemma lem3241770 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term255 A t u P t' u' x) = (term241 A t u x P t' u').
Proof. exact (TRANS (@lem3241768 A t u P t' u' x) (@lem3241769 A t u x P t' u')). Qed.
Lemma lem3241771 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term257 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (fun_ext (fun x : A => @lem3241770 A t u x P t' u')). Qed.
Lemma lem3241772 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241773 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term258 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (MK_COMB (@lem3241772 A) (@lem3241771 A t u P t' u')). Qed.
Lemma lem3241774 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term259 A t u P t') = (term245 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3241773 A t u P t' u')). Qed.
Lemma lem3241775 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241776 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term251 A t u P t') = (term246 A t u P t').
Proof. exact (MK_COMB (@lem3241775 A) (@lem3241774 A t u P t')). Qed.
Lemma lem3241777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3241778 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term260 A t u P t') = (term261 A t u P t').
Proof. exact (MK_COMB (@lem3241777) (@lem3241776 A t u P t')). Qed.
Lemma lem3241779 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term254 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (eq_refl (term254 A t u P t' u')). Qed.
Lemma lem3241780 {A : Type'} (x : type684 A) (u' : A -> Prop) : (x u') = (x u').
Proof. exact (eq_refl (x u')). Qed.
Lemma lem3241781 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (x : type684 A) (u' : A -> Prop) : (term262 A t u P t' x u') = (term263 A t u P t' x u').
Proof. exact (MK_COMB (@lem3241779 A t u P t' u') (@lem3241780 A x u')). Qed.
Lemma lem3241782 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term263 A t u P t' x u') = (term264 A t u x P t' u').
Proof. exact (eq_refl (term263 A t u P t' x u')). Qed.
Lemma lem3241783 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term262 A t u P t' x u') = (term264 A t u x P t' u').
Proof. exact (TRANS (@lem3241781 A t u P t' x u') (@lem3241782 A t u x P t' u')). Qed.
Lemma lem3241784 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term265 A t u P t' x) = (term266 A t u x P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3241783 A t u x P t' u')). Qed.
Lemma lem3241785 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241786 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term267 A t u P t' x) = (term268 A t u x P t').
Proof. exact (MK_COMB (@lem3241785 A) (@lem3241784 A t u x P t')). Qed.
Lemma lem3241787 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term269 A t u P t') = (term270 A t u P t').
Proof. exact (fun_ext (fun x : type684 A => @lem3241786 A t u x P t')). Qed.
Lemma lem3241788 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3241789 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term252 A t u P t') = (term271 A t u P t').
Proof. exact (MK_COMB (@lem3241788 A) (@lem3241787 A t u P t')). Qed.
Lemma lem3241790 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term251 A t u P t') = (term252 A t u P t')) = ((term246 A t u P t') = (term271 A t u P t')).
Proof. exact (MK_COMB (@lem3241778 A t u P t') (@lem3241789 A t u P t')). Qed.
Lemma lem3241791 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term246 A t u P t') = (term271 A t u P t').
Proof. exact (EQ_MP (@lem3241790 A t u P t') (@lem3241765 A t u P t')). Qed.
Lemma lem3241792 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term204 A t u P t') = (term271 A t u P t').
Proof. exact (TRANS (@lem3241761 A t u P t') (@lem3241791 A t u P t')). Qed.
Lemma lem3241793 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term205 A t u P) = (term272 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3241792 A t u P t')). Qed.
Lemma lem3241794 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241795 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term206 A t u P) = (term273 A t u P).
Proof. exact (MK_COMB (@lem3241794 A) (@lem3241793 A t u P)). Qed.
Lemma lem3241797 {A B : Type'} (P : type1413 A B) : (term247 A B P) = (term248 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3241798 {A : Type'} (P : type597 A) : (term274 A P) = (term275 A P).
Proof. exact (@lem3241797 (A -> Prop) (type684 A) P). Qed.
Lemma lem3241799 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term276 A t u P) = (term277 A t u P).
Proof. exact (@lem3241798 A (term278 A t u P)). Qed.
Lemma lem3241800 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term279 A t u P t') = (term270 A t u P t').
Proof. exact (eq_refl (term279 A t u P t')). Qed.
Lemma lem3241801 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3241802 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (x : type684 A) : (term280 A t u P t' x) = (term281 A t u P t' x).
Proof. exact (MK_COMB (@lem3241800 A t u P t') (@lem3241801 A x)). Qed.
Lemma lem3241803 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term281 A t u P t' x) = (term268 A t u x P t').
Proof. exact (eq_refl (term281 A t u P t' x)). Qed.
Lemma lem3241804 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term280 A t u P t' x) = (term268 A t u x P t').
Proof. exact (TRANS (@lem3241802 A t u P t' x) (@lem3241803 A t u x P t')). Qed.
Lemma lem3241805 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term282 A t u P t') = (term270 A t u P t').
Proof. exact (fun_ext (fun x : type684 A => @lem3241804 A t u x P t')). Qed.
Lemma lem3241806 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3241807 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term283 A t u P t') = (term271 A t u P t').
Proof. exact (MK_COMB (@lem3241806 A) (@lem3241805 A t u P t')). Qed.
Lemma lem3241808 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term284 A t u P) = (term272 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3241807 A t u P t')). Qed.
Lemma lem3241809 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241810 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term276 A t u P) = (term273 A t u P).
Proof. exact (MK_COMB (@lem3241809 A) (@lem3241808 A t u P)). Qed.
Lemma lem3241811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3241812 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term285 A t u P) = (term286 A t u P).
Proof. exact (MK_COMB (@lem3241811) (@lem3241810 A t u P)). Qed.
Lemma lem3241813 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term279 A t u P t') = (term270 A t u P t').
Proof. exact (eq_refl (term279 A t u P t')). Qed.
Lemma lem3241814 {A : Type'} (x : type638 A) (t' : A -> Prop) : (x t') = (x t').
Proof. exact (eq_refl (x t')). Qed.
Lemma lem3241815 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (x : type638 A) (t' : A -> Prop) : (term287 A t u P x t') = (term288 A t u P x t').
Proof. exact (MK_COMB (@lem3241813 A t u P t') (@lem3241814 A x t')). Qed.
Lemma lem3241816 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) (t' : A -> Prop) : (term288 A t u P x t') = (term289 A t u x P t').
Proof. exact (eq_refl (term288 A t u P x t')). Qed.
Lemma lem3241817 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) (t' : A -> Prop) : (term287 A t u P x t') = (term289 A t u x P t').
Proof. exact (TRANS (@lem3241815 A t u P x t') (@lem3241816 A t u x P t')). Qed.
Lemma lem3241818 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term290 A t u P x) = (term291 A t u x P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3241817 A t u x P t')). Qed.
Lemma lem3241819 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3241820 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term292 A t u P x) = (term293 A t u x P).
Proof. exact (MK_COMB (@lem3241819 A) (@lem3241818 A t u x P)). Qed.
Lemma lem3241821 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term294 A t u P) = (term295 A t u P).
Proof. exact (fun_ext (fun x : type638 A => @lem3241820 A t u x P)). Qed.
Lemma lem3241822 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem3241823 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term277 A t u P) = (term296 A t u P).
Proof. exact (MK_COMB (@lem3241822 A) (@lem3241821 A t u P)). Qed.
Lemma lem3241824 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term276 A t u P) = (term277 A t u P)) = ((term273 A t u P) = (term296 A t u P)).
Proof. exact (MK_COMB (@lem3241812 A t u P) (@lem3241823 A t u P)). Qed.
Lemma lem3241825 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term273 A t u P) = (term296 A t u P).
Proof. exact (EQ_MP (@lem3241824 A t u P) (@lem3241799 A t u P)). Qed.
Lemma lem3241826 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term206 A t u P) = (term296 A t u P).
Proof. exact (TRANS (@lem3241795 A t u P) (@lem3241825 A t u P)). Qed.
Lemma lem3241827 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term207 A s t u) = (term207 A s t u).
Proof. exact (eq_refl (term207 A s t u)). Qed.
Lemma lem3241828 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term208 A s t u P) = (term297 A s t u P).
Proof. exact (MK_COMB (@lem3241827 A s t u) (@lem3241826 A t u P)). Qed.
Lemma lem3241830 {A : Type'} (P : Prop) (Q : A -> Prop) : (term298 A P Q) = (term299 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3241831 {A : Type'} (P : Prop) (Q : type139 A) : (term300 A P Q) = (term301 A P Q).
Proof. exact (@lem3241830 (type638 A) P Q). Qed.
Lemma lem3241832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term302 A s t u P) = (term303 A s t u P).
Proof. exact (@lem3241831 A (term182 A s t u) (term295 A t u P)). Qed.
Lemma lem3241833 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term304 A t u P x) = (term293 A t u x P).
Proof. exact (eq_refl (term304 A t u P x)). Qed.
Lemma lem3241834 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term305 A t u P) = (term295 A t u P).
Proof. exact (fun_ext (fun x : type638 A => @lem3241833 A t u x P)). Qed.
Lemma lem3241835 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem3241836 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term306 A t u P) = (term296 A t u P).
Proof. exact (MK_COMB (@lem3241835 A) (@lem3241834 A t u P)). Qed.
Lemma lem3241837 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term207 A s t u) = (term207 A s t u).
Proof. exact (eq_refl (term207 A s t u)). Qed.
Lemma lem3241838 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term302 A s t u P) = (term297 A s t u P).
Proof. exact (MK_COMB (@lem3241837 A s t u) (@lem3241836 A t u P)). Qed.
Lemma lem3241839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3241840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term307 A s t u P) = (term308 A s t u P).
Proof. exact (MK_COMB (@lem3241839) (@lem3241838 A s t u P)). Qed.
Lemma lem3241841 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term304 A t u P x) = (term293 A t u x P).
Proof. exact (eq_refl (term304 A t u P x)). Qed.
Lemma lem3241842 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term207 A s t u) = (term207 A s t u).
Proof. exact (eq_refl (term207 A s t u)). Qed.
Lemma lem3241843 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term309 A s t u P x) = (term310 A s t u x P).
Proof. exact (MK_COMB (@lem3241842 A s t u) (@lem3241841 A t u x P)). Qed.
Lemma lem3241844 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term311 A s t u P) = (term312 A s t u P).
Proof. exact (fun_ext (fun x : type638 A => @lem3241843 A s t u x P)). Qed.
Lemma lem3241845 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem3241846 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term303 A s t u P) = (term313 A s t u P).
Proof. exact (MK_COMB (@lem3241845 A) (@lem3241844 A s t u P)). Qed.
Lemma lem3241847 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term302 A s t u P) = (term303 A s t u P)) = ((term297 A s t u P) = (term313 A s t u P)).
Proof. exact (MK_COMB (@lem3241840 A s t u P) (@lem3241846 A s t u P)). Qed.
Lemma lem3241848 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term297 A s t u P) = (term313 A s t u P).
Proof. exact (EQ_MP (@lem3241847 A s t u P) (@lem3241832 A s t u P)). Qed.
Lemma lem3241850 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term208 A s t u P) = (term313 A s t u P).
Proof. exact (TRANS (@lem3241828 A s t u P) (@lem3241848 A s t u P)). Qed.
Lemma lem3241851 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term139 A s t u P) = (term313 A s t u P).
Proof. exact (TRANS (@lem3241545 A s t u P) (@lem3241850 A s t u P)). Qed.
Lemma lem3241852 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term313 A s t u P.
Proof. exact (EQ_MP (@lem3241851 A s t u P) (@lem3241472 A s t u P h1)). Qed.
Lemma lem3241863 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term314 A s t x) = (term315 A s t x).
Proof. exact (@lem17362 (term145 A s t x) (t x)). Qed.
Lemma lem3241864 {A : Type'} (P : A -> Prop) : (term185 A P) = (term186 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3241865 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term316 A s t) = (term317 A s t).
Proof. exact (@lem3241864 A (term151 A s t)). Qed.
Lemma lem3241866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term318 A s t x) = (term149 A s t x).
Proof. exact (eq_refl (term318 A s t x)). Qed.
Lemma lem3241867 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3241868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term319 A s t x) = (term314 A s t x).
Proof. exact (MK_COMB (@lem3241867) (@lem3241866 A s t x)). Qed.
Lemma lem3241869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term319 A s t x) = (term315 A s t x).
Proof. exact (TRANS (@lem3241868 A s t x) (@lem3241863 A s t x)). Qed.
Lemma lem3241870 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term320 A s t) = (term321 A s t).
Proof. exact (fun_ext (fun x : A => @lem3241869 A s t x)). Qed.
Lemma lem3241871 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241872 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term317 A s t) = (term322 A s t).
Proof. exact (MK_COMB (@lem3241871 A) (@lem3241870 A s t)). Qed.
Lemma lem3241873 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term316 A s t) = (term322 A s t).
Proof. exact (TRANS (@lem3241865 A s t) (@lem3241872 A s t)). Qed.
Lemma lem3241884 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term314 A s u x) = (term315 A s u x).
Proof. exact (@lem17362 (term145 A s u x) (u x)). Qed.
Lemma lem3241885 {A : Type'} (P : A -> Prop) : (term185 A P) = (term186 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3241886 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term316 A s u) = (term317 A s u).
Proof. exact (@lem3241885 A (term151 A s u)). Qed.
Lemma lem3241887 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term318 A s u x) = (term149 A s u x).
Proof. exact (eq_refl (term318 A s u x)). Qed.
Lemma lem3241888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3241889 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term319 A s u x) = (term314 A s u x).
Proof. exact (MK_COMB (@lem3241888) (@lem3241887 A s u x)). Qed.
Lemma lem3241890 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term319 A s u x) = (term315 A s u x).
Proof. exact (TRANS (@lem3241889 A s u x) (@lem3241884 A s u x)). Qed.
Lemma lem3241891 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term320 A s u) = (term321 A s u).
Proof. exact (fun_ext (fun x : A => @lem3241890 A s u x)). Qed.
Lemma lem3241892 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3241893 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term317 A s u) = (term322 A s u).
Proof. exact (MK_COMB (@lem3241892 A) (@lem3241891 A s u)). Qed.
Lemma lem3241894 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term316 A s u) = (term322 A s u).
Proof. exact (TRANS (@lem3241886 A s u) (@lem3241893 A s u)). Qed.
Lemma lem3241895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3241896 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term323 A s t) = (term324 A s t).
Proof. exact (MK_COMB (@lem3241895) (@lem3241873 A s t)). Qed.
Lemma lem3241897 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term325 A t s u) = (term326 A t s u).
Proof. exact (MK_COMB (@lem3241896 A s t) (@lem3241894 A s u)). Qed.
Lemma lem3241898 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term179 A t s u) = (term325 A t s u).
Proof. exact (@lem17045 (term152 A s t) (term152 A s u)). Qed.
Lemma lem3241899 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term179 A t s u) = (term326 A t s u).
Proof. exact (TRANS (@lem3241898 A t s u) (@lem3241897 A t s u)). Qed.
Lemma lem3241998 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3241999 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (@lem3241998 A P Q). Qed.
Lemma lem3242000 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term327 A t s u) = (term328 A t s u).
Proof. exact (@lem3241999 A (term321 A s t) (term321 A s u)). Qed.
Lemma lem3242001 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term329 A s t x) = (term315 A s t x).
Proof. exact (eq_refl (term329 A s t x)). Qed.
Lemma lem3242002 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term330 A s t) = (term321 A s t).
Proof. exact (fun_ext (fun x : A => @lem3242001 A s t x)). Qed.
Lemma lem3242003 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3242004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term331 A s t) = (term322 A s t).
Proof. exact (MK_COMB (@lem3242003 A) (@lem3242002 A s t)). Qed.
Lemma lem3242005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3242006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term332 A s t) = (term324 A s t).
Proof. exact (MK_COMB (@lem3242005) (@lem3242004 A s t)). Qed.
Lemma lem3242007 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term329 A s u x) = (term315 A s u x).
Proof. exact (eq_refl (term329 A s u x)). Qed.
Lemma lem3242008 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term330 A s u) = (term321 A s u).
Proof. exact (fun_ext (fun x : A => @lem3242007 A s u x)). Qed.
Lemma lem3242009 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3242010 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term331 A s u) = (term322 A s u).
Proof. exact (MK_COMB (@lem3242009 A) (@lem3242008 A s u)). Qed.
Lemma lem3242011 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term327 A t s u) = (term326 A t s u).
Proof. exact (MK_COMB (@lem3242006 A s t) (@lem3242010 A s u)). Qed.
Lemma lem3242012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3242013 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term333 A t s u) = (term334 A t s u).
Proof. exact (MK_COMB (@lem3242012) (@lem3242011 A t s u)). Qed.
Lemma lem3242014 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term329 A s t x) = (term315 A s t x).
Proof. exact (eq_refl (term329 A s t x)). Qed.
Lemma lem3242015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3242016 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term335 A s t x) = (term336 A s t x).
Proof. exact (MK_COMB (@lem3242015) (@lem3242014 A s t x)). Qed.
Lemma lem3242017 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term329 A s u x) = (term315 A s u x).
Proof. exact (eq_refl (term329 A s u x)). Qed.
Lemma lem3242018 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term337 A t s u x) = (term338 A t s u x).
Proof. exact (MK_COMB (@lem3242016 A s t x) (@lem3242017 A s u x)). Qed.
Lemma lem3242019 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term339 A t s u) = (term340 A t s u).
Proof. exact (fun_ext (fun x : A => @lem3242018 A t s u x)). Qed.
Lemma lem3242020 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3242021 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term328 A t s u) = (term341 A t s u).
Proof. exact (MK_COMB (@lem3242020 A) (@lem3242019 A t s u)). Qed.
Lemma lem3242022 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : ((term327 A t s u) = (term328 A t s u)) = ((term326 A t s u) = (term341 A t s u)).
Proof. exact (MK_COMB (@lem3242013 A t s u) (@lem3242021 A t s u)). Qed.
Lemma lem3242024 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term326 A t s u) = (term341 A t s u).
Proof. exact (EQ_MP (@lem3242022 A t s u) (@lem3242000 A t s u)). Qed.
Lemma lem3242025 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term179 A t s u) = (term341 A t s u).
Proof. exact (TRANS (@lem3241899 A t s u) (@lem3242024 A t s u)). Qed.
Lemma lem3242026 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term179 A t s u) : term341 A t s u.
Proof. exact (EQ_MP (@lem3242025 A t s u) (@lem3241477 A t s u h1)). Qed.
Lemma lem3242027 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term338 A t s u x) : term338 A t s u x.
Proof. exact (h1). Qed.
Lemma lem3242029 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3242034 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3242035 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3242034 A Prop f x). Qed.
Lemma lem3242037 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3242035 A u x). Qed.
Lemma lem3242038 {A : Type'} (u : A -> Prop) (x : A) : (term77 A u x) = (term342 A u x).
Proof. exact (MK_COMB (@lem3242029) (@lem3242037 A u x)). Qed.
Lemma lem3242043 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3242044 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3242043 A Prop f x). Qed.
Lemma lem3242046 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3242044 A u x). Qed.
Lemma lem3242051 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3242052 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3242051 A Prop f x). Qed.
Lemma lem3242054 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3242052 A s x). Qed.
Lemma lem3242055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242056 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term343 A s x).
Proof. exact (MK_COMB (@lem3242055) (@lem3242054 A s x)). Qed.
Lemma lem3242057 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term145 A s u x) = (term344 A s u x).
Proof. exact (MK_COMB (@lem3242056 A s x) (@lem3242046 A u x)). Qed.
Lemma lem3242058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242059 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term345 A s u x) = (term346 A s u x).
Proof. exact (MK_COMB (@lem3242058) (@lem3242057 A s u x)). Qed.
Lemma lem3242060 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term315 A s u x) = (term347 A s u x).
Proof. exact (MK_COMB (@lem3242059 A s u x) (@lem3242038 A u x)). Qed.
Lemma lem3242061 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3242066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3242067 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3242066 A Prop f x). Qed.
Lemma lem3242069 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3242067 A t x). Qed.
Lemma lem3242070 {A : Type'} (t : A -> Prop) (x : A) : (term77 A t x) = (term342 A t x).
Proof. exact (MK_COMB (@lem3242061) (@lem3242069 A t x)). Qed.
Lemma lem3242075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3242076 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3242075 A Prop f x). Qed.
Lemma lem3242078 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3242076 A t x). Qed.
Lemma lem3242083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3242084 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3242083 A Prop f x). Qed.
Lemma lem3242086 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3242084 A s x). Qed.
Lemma lem3242087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242088 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term343 A s x).
Proof. exact (MK_COMB (@lem3242087) (@lem3242086 A s x)). Qed.
Lemma lem3242089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term145 A s t x) = (term344 A s t x).
Proof. exact (MK_COMB (@lem3242088 A s x) (@lem3242078 A t x)). Qed.
Lemma lem3242090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term345 A s t x) = (term346 A s t x).
Proof. exact (MK_COMB (@lem3242090) (@lem3242089 A s t x)). Qed.
Lemma lem3242092 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term315 A s t x) = (term347 A s t x).
Proof. exact (MK_COMB (@lem3242091 A s t x) (@lem3242070 A t x)). Qed.
Lemma lem3242093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3242094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term336 A s t x) = (term348 A s t x).
Proof. exact (MK_COMB (@lem3242093) (@lem3242092 A s t x)). Qed.
Lemma lem3242095 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term338 A t s u x) = (term349 A t s u x).
Proof. exact (MK_COMB (@lem3242094 A s t x) (@lem3242060 A s u x)). Qed.
Lemma lem3242096 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term338 A t s u x) : term349 A t s u x.
Proof. exact (EQ_MP (@lem3242095 A t s u x) (@lem3242027 A t s u x h1)). Qed.
Lemma lem3242280 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : term347 A s t x.
Proof. exact (h1). Qed.
Lemma lem3242281 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : term347 A s u x.
Proof. exact (h1). Qed.
Lemma lem3242283 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : term344 A s t x.
Proof. exact (proj1 (@lem3242280 A s t x h1)). Qed.
Lemma lem3242287 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : term344 A s u x.
Proof. exact (proj1 (@lem3242281 A s u x h1)). Qed.
Lemma lem3242525 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : term342 A t x.
Proof. exact (proj2 (@lem3242280 A s t x h1)). Qed.
Lemma lem3242589 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : term342 A u x.
Proof. exact (proj2 (@lem3242281 A s u x h1)). Qed.
Lemma lem3242643 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem3242283 A s t x h1)). Qed.
Lemma lem3242644 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : term350 A t x.
Proof. exact (fun h0 : term342 A t x => @lem3242643 A s t x h1). Qed.
Lemma lem3242646 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3242647 {A : Type'} (t : A -> Prop) (x : A) : (term350 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3242646 (@I (A -> Prop) t x)). Qed.
Lemma lem3242648 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3242647 A t x) (@lem3242644 A s t x h1)). Qed.
Lemma lem3242651 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3242653 {A : Type'} (t : A -> Prop) (x : A) : (term342 A t x) = (term351 A t x).
Proof. exact (@lem3242651 (@I (A -> Prop) t x)). Qed.
Lemma lem3242656 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : term351 A t x.
Proof. exact (EQ_MP (@lem3242653 A t x) (@lem3242525 A s t x h1)). Qed.
Lemma lem3242659 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : False.
Proof. exact (@lem3242656 A s t x h1 (@lem3242648 A s t x h1)). Qed.
Lemma lem3242660 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : term88.
Proof. exact (fun h0 : ~ False => @lem3242659 A s t x h1). Qed.
Lemma lem3242662 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3242663 : term88 = False.
Proof. exact (@lem3242662 False). Qed.
Lemma lem3242664 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term347 A s t x) : False.
Proof. exact (EQ_MP (@lem3242663) (@lem3242660 A s t x h1)). Qed.
Lemma lem3242666 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : @I (A -> Prop) u x.
Proof. exact (proj2 (@lem3242287 A s u x h1)). Qed.
Lemma lem3242667 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : term350 A u x.
Proof. exact (fun h0 : term342 A u x => @lem3242666 A s u x h1). Qed.
Lemma lem3242669 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3242670 {A : Type'} (u : A -> Prop) (x : A) : (term350 A u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3242669 (@I (A -> Prop) u x)). Qed.
Lemma lem3242671 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : @I (A -> Prop) u x.
Proof. exact (EQ_MP (@lem3242670 A u x) (@lem3242667 A s u x h1)). Qed.
Lemma lem3242674 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3242676 {A : Type'} (u : A -> Prop) (x : A) : (term342 A u x) = (term351 A u x).
Proof. exact (@lem3242674 (@I (A -> Prop) u x)). Qed.
Lemma lem3242679 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : term351 A u x.
Proof. exact (EQ_MP (@lem3242676 A u x) (@lem3242589 A s u x h1)). Qed.
Lemma lem3242682 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : False.
Proof. exact (@lem3242679 A s u x h1 (@lem3242671 A s u x h1)). Qed.
Lemma lem3242683 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : term88.
Proof. exact (fun h0 : ~ False => @lem3242682 A s u x h1). Qed.
Lemma lem3242685 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3242686 : term88 = False.
Proof. exact (@lem3242685 False). Qed.
Lemma lem3242687 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term347 A s u x) : False.
Proof. exact (EQ_MP (@lem3242686) (@lem3242683 A s u x h1)). Qed.
Lemma lem3242688 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term338 A t s u x) : False.
Proof. exact (or_elim (@lem3242096 A t s u x h1) (fun h0 : term347 A s t x => @lem3242664 A s t x h0) (fun h0 : term347 A s u x => @lem3242687 A s u x h0)). Qed.
Lemma lem3242689 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term139 A s t u P) (h2 : term338 A t s u x) : False.
Proof. exact (ex_elim (@lem3241852 A s t u P h1) (fun x' : type638 A => fun h0 : term312 A s t u P x' => @lem3242688 A t s u x h2)). Qed.
Lemma lem3242690 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term179 A t s u) (h2 : term139 A s t u P) : False.
Proof. exact (ex_elim (@lem3242026 A t s u h1) (fun x : A => fun h0 : term340 A t s u x => @lem3242689 A P t s u x h2 h0)). Qed.
Lemma lem3242691 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term179 A t s u) (h2 : term139 A s t u P) : (term179 A t s u) = False.
Proof. exact (prop_ext (fun h3 : term179 A t s u => @lem3242690 A s t u P h1 h2) (fun h3 : False => @lem3241477 A t s u h1)). Qed.
Lemma lem3242692 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term179 A t s u) (h2 : term139 A s t u P) : False.
Proof. exact (EQ_MP (@lem3242691 A s t u P h1 h2) (@lem3241477 A t s u h1)). Qed.
Lemma lem3242693 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term178 A t s u.
Proof. exact (fun h0 : term179 A t s u => @lem3242692 A s t u P h0 h1). Qed.
Lemma lem3242694 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term154 A t s u.
Proof. exact (EQ_MP (@lem3241476 A t s u) (@lem3242693 A s t u P h1)). Qed.
Lemma lem3242695 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term155 A P t s u.
Proof. exact (fun h0 : term139 A s t u P => @lem3242694 A s t u P h0). Qed.
Lemma lem3242700 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term165 A t s u.
Proof. exact (fun P : type686 A => @lem3242695 A P t s u). Qed.
Lemma lem3242705 {A : Type'} (s : A -> Prop) (u : A -> Prop) : term169 A s u.
Proof. exact (fun t : A -> Prop => @lem3242700 A t s u). Qed.
Lemma lem3242710 {A : Type'} (u : A -> Prop) : term173 A u.
Proof. exact (fun s : A -> Prop => @lem3242705 A s u). Qed.
Lemma lem3242715 {A : Type'} : term177 A.
Proof. exact (fun u : A -> Prop => @lem3242710 A u). Qed.
Lemma lem3242716 {A : Type'} : term176 A.
Proof. exact (EQ_MP (@lem3241471 A) (@lem3242715 A)). Qed.
Lemma lem3242717 {A : Type'} (u : A -> Prop) : term352 A u.
Proof. exact (@lem3242716 A u). Qed.
Lemma lem3242718 {A : Type'} (u : A -> Prop) : (term352 A u) = (term172 A u).
Proof. exact (eq_refl (term352 A u)). Qed.
Lemma lem3242719 {A : Type'} (u : A -> Prop) : term172 A u.
Proof. exact (EQ_MP (@lem3242718 A u) (@lem3242717 A u)). Qed.
Lemma lem3242720 {A : Type'} (u : A -> Prop) (s : A -> Prop) : term353 A u s.
Proof. exact (@lem3242719 A u s). Qed.
Lemma lem3242721 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term353 A u s) = (term168 A s u).
Proof. exact (eq_refl (term353 A u s)). Qed.
Lemma lem3242722 {A : Type'} (s : A -> Prop) (u : A -> Prop) : term168 A s u.
Proof. exact (EQ_MP (@lem3242721 A s u) (@lem3242720 A u s)). Qed.
Lemma lem3242723 {A : Type'} (s : A -> Prop) (u : A -> Prop) (t : A -> Prop) : term354 A s u t.
Proof. exact (@lem3242722 A s u t). Qed.
Lemma lem3242724 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term354 A s u t) = (term164 A t s u).
Proof. exact (eq_refl (term354 A s u t)). Qed.
Lemma lem3242725 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term164 A t s u.
Proof. exact (EQ_MP (@lem3242724 A t s u) (@lem3242723 A s u t)). Qed.
Lemma lem3242726 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (P : type686 A) : term355 A t s u P.
Proof. exact (@lem3242725 A t s u P). Qed.
Lemma lem3242727 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term355 A t s u P) = (term156 A P t s u).
Proof. exact (eq_refl (term355 A t s u P)). Qed.
Lemma lem3242728 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term156 A P t s u.
Proof. exact (EQ_MP (@lem3242727 A P t s u) (@lem3242726 A t s u P)). Qed.
Lemma lem3242730 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term156 A P t s u.
Proof. exact (@lem3241180 A P t s u (@lem3242728 A P t s u)). Qed.
Lemma lem3242731 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term157 A P t s u) : False.
Proof. exact (@lem3242730 A P t s u (@lem3241164 A P t s u h1)). Qed.
Lemma lem3242732 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term157 A P t s u) : (term157 A P t s u) = False.
Proof. exact (prop_ext (fun h2 : term157 A P t s u => @lem3242731 A P t s u h1) (fun h2 : False => @lem3241164 A P t s u h1)). Qed.
Lemma lem3242733 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (h1 : term157 A P t s u) : False.
Proof. exact (EQ_MP (@lem3242732 A P t s u h1) (@lem3241164 A P t s u h1)). Qed.
Lemma lem3242734 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term156 A P t s u.
Proof. exact (fun h0 : term157 A P t s u => @lem3242733 A P t s u h0). Qed.
Lemma lem3242735 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term155 A P t s u.
Proof. exact (EQ_MP (@lem3241163 A P t s u) (@lem3242734 A P t s u)). Qed.
Lemma lem3242736 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term127 A P t s u.
Proof. exact (EQ_MP (@lem3241159 A P t s u) (@lem3242735 A P t s u)). Qed.
Lemma lem3242737 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term126 A P t s u.
Proof. exact (EQ_MP (@lem3240923 A P t s u) (@lem3242736 A P t s u)). Qed.
Lemma lem3242738 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : term104 A t s u.
Proof. exact (@lem3242737 A P t s u (@lem3240814 A P s t u h1 h2)). Qed.
Lemma lem3242749 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : term107 A s t u P.
Proof. exact (conj (@lem3240790 A s t u h2) (@lem3240789 A t u P h1)). Qed.
Lemma lem3242755 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3242756 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3242755 A s t). Qed.
Lemma lem3242757 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term7 A s t u) = (term108 A s t u).
Proof. exact (@lem3242756 A s (@UNION A t u)). Qed.
Lemma lem3242764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242765 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term109 A s t u) = (term110 A s t u).
Proof. exact (MK_COMB (@lem3242764) (@lem3242757 A s t u)). Qed.
Lemma lem3242779 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3242780 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3242779 A s t). Qed.
Lemma lem3242781 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (@SUBSET A t' t) = (term11 A t' t).
Proof. exact (@lem3242780 A t' t). Qed.
Lemma lem3242788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242789 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term12 A t' t) = (term13 A t' t).
Proof. exact (MK_COMB (@lem3242788) (@lem3242781 A t' t)). Qed.
Lemma lem3242791 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3242792 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term11 A s t).
Proof. exact (@lem3242791 A s t). Qed.
Lemma lem3242793 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (@SUBSET A u' u) = (term11 A u' u).
Proof. exact (@lem3242792 A u' u). Qed.
Lemma lem3242800 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term4 A t' t u' u) = (term14 A t' t u' u).
Proof. exact (MK_COMB (@lem3242789 A t' t) (@lem3242793 A u' u)). Qed.
Lemma lem3242803 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3242804 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term15 A t' t u' u) = (term16 A t' t u' u).
Proof. exact (MK_COMB (@lem3242803) (@lem3242800 A t' t u' u)). Qed.
Lemma lem3242805 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3242806 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term94 A t u P t' u') = (term111 A t u P t' u').
Proof. exact (MK_COMB (@lem3242804 A t' t u' u) (@lem3242805 A P t' u')). Qed.
Lemma lem3242809 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term112 A t u P t') = (term113 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3242806 A t u P t' u')). Qed.
Lemma lem3242810 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3242811 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term95 A t u P t') = (term114 A t u P t').
Proof. exact (MK_COMB (@lem3242810 A) (@lem3242809 A t u P t')). Qed.
Lemma lem3242816 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term115 A t u P) = (term116 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3242811 A t u P t')). Qed.
Lemma lem3242817 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3242818 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term96 A t u P) = (term117 A t u P).
Proof. exact (MK_COMB (@lem3242817 A) (@lem3242816 A t u P)). Qed.
Lemma lem3242823 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term107 A s t u P) = (term118 A s t u P).
Proof. exact (MK_COMB (@lem3242765 A s t u) (@lem3242818 A t u P)). Qed.
Lemma lem3242826 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3242827 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term119 A s t u P) = (term120 A s t u P).
Proof. exact (MK_COMB (@lem3242826) (@lem3242823 A s t u P)). Qed.
Lemma lem3242831 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term356 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3242832 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term356 A s t).
Proof. exact (@lem3242831 A s t). Qed.
Lemma lem3242833 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : ((term357 A t s u) = s) = (term358 A t u s).
Proof. exact (@lem3242832 A (term357 A t s u) s). Qed.
Lemma lem3242842 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term359 A P t u s) = (term360 A P t u s).
Proof. exact (MK_COMB (@lem3242827 A s t u P) (@lem3242833 A t u s)). Qed.
Lemma lem3242845 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term360 A P t u s) = (term359 A P t u s).
Proof. exact (SYM (@lem3242842 A P t u s)). Qed.
Lemma lem3242857 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3242858 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3242857 A P x). Qed.
Lemma lem3242859 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3242858 A s x). Qed.
Lemma lem3242860 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3242861 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3242860) (@lem3242859 A s x)). Qed.
Lemma lem3242863 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3242864 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (@lem3242863 A s x t). Qed.
Lemma lem3242865 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term31 A x t u) = (term32 A t x u).
Proof. exact (@lem3242864 A t x u). Qed.
Lemma lem3242869 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3242870 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3242869 A P x). Qed.
Lemma lem3242871 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3242870 A t x). Qed.
Lemma lem3242872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3242873 {A : Type'} (t : A -> Prop) (x : A) : (term33 A x t) = (term34 A t x).
Proof. exact (MK_COMB (@lem3242872) (@lem3242871 A t x)). Qed.
Lemma lem3242875 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3242876 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3242875 A P x). Qed.
Lemma lem3242877 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3242876 A u x). Qed.
Lemma lem3242878 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term32 A t x u) = (term35 A t u x).
Proof. exact (MK_COMB (@lem3242873 A t x) (@lem3242877 A u x)). Qed.
Lemma lem3242881 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term31 A x t u) = (term35 A t u x).
Proof. exact (TRANS (@lem3242865 A t x u) (@lem3242878 A t u x)). Qed.
Lemma lem3242882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term128 A s x t u) = (term129 A s t u x).
Proof. exact (MK_COMB (@lem3242861 A s x) (@lem3242881 A t u x)). Qed.
Lemma lem3242885 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term130 A s t u) = (term131 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3242882 A s t u x)). Qed.
Lemma lem3242886 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3242887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term108 A s t u) = (term132 A s t u).
Proof. exact (MK_COMB (@lem3242886 A) (@lem3242885 A s t u)). Qed.
Lemma lem3242892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242893 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term110 A s t u) = (term133 A s t u).
Proof. exact (MK_COMB (@lem3242892) (@lem3242887 A s t u)). Qed.
Lemma lem3242913 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3242914 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3242913 A P x). Qed.
Lemma lem3242915 {A : Type'} (t' : A -> Prop) (x : A) : (@IN A x t') = (t' x).
Proof. exact (@lem3242914 A t' x). Qed.
Lemma lem3242916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3242917 {A : Type'} (t' : A -> Prop) (x : A) : (term21 A x t') = (term22 A t' x).
Proof. exact (MK_COMB (@lem3242916) (@lem3242915 A t' x)). Qed.
Lemma lem3242919 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3242920 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3242919 A P x). Qed.
Lemma lem3242921 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3242920 A t x). Qed.
Lemma lem3242922 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term23 A t' x t) = (term24 A t' t x).
Proof. exact (MK_COMB (@lem3242917 A t' x) (@lem3242921 A t x)). Qed.
Lemma lem3242925 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term25 A t' t) = (term26 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3242922 A t' t x)). Qed.
Lemma lem3242926 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3242927 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term11 A t' t) = (term27 A t' t).
Proof. exact (MK_COMB (@lem3242926 A) (@lem3242925 A t' t)). Qed.
Lemma lem3242932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3242933 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term13 A t' t) = (term28 A t' t).
Proof. exact (MK_COMB (@lem3242932) (@lem3242927 A t' t)). Qed.
Lemma lem3242941 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3242942 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3242941 A P x). Qed.
Lemma lem3242943 {A : Type'} (u' : A -> Prop) (x : A) : (@IN A x u') = (u' x).
Proof. exact (@lem3242942 A u' x). Qed.
Lemma lem3242944 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3242945 {A : Type'} (u' : A -> Prop) (x : A) : (term21 A x u') = (term22 A u' x).
Proof. exact (MK_COMB (@lem3242944) (@lem3242943 A u' x)). Qed.
Lemma lem3242947 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3242948 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3242947 A P x). Qed.
Lemma lem3242949 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3242948 A u x). Qed.
Lemma lem3242950 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term23 A u' x u) = (term24 A u' u x).
Proof. exact (MK_COMB (@lem3242945 A u' x) (@lem3242949 A u x)). Qed.
Lemma lem3242953 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term25 A u' u) = (term26 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3242950 A u' u x)). Qed.
Lemma lem3242954 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3242955 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term11 A u' u) = (term27 A u' u).
Proof. exact (MK_COMB (@lem3242954 A) (@lem3242953 A u' u)). Qed.
Lemma lem3242960 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term14 A t' t u' u) = (term29 A t' t u' u).
Proof. exact (MK_COMB (@lem3242933 A t' t) (@lem3242955 A u' u)). Qed.
Lemma lem3242963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3242964 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term16 A t' t u' u) = (term30 A t' t u' u).
Proof. exact (MK_COMB (@lem3242963) (@lem3242960 A t' t u' u)). Qed.
Lemma lem3242965 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3242966 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term111 A t u P t' u') = (term134 A t u P t' u').
Proof. exact (MK_COMB (@lem3242964 A t' t u' u) (@lem3242965 A P t' u')). Qed.
Lemma lem3242969 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term113 A t u P t') = (term135 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3242966 A t u P t' u')). Qed.
Lemma lem3242970 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3242971 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term114 A t u P t') = (term136 A t u P t').
Proof. exact (MK_COMB (@lem3242970 A) (@lem3242969 A t u P t')). Qed.
Lemma lem3242976 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term116 A t u P) = (term137 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3242971 A t u P t')). Qed.
Lemma lem3242977 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3242978 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term117 A t u P) = (term138 A t u P).
Proof. exact (MK_COMB (@lem3242977 A) (@lem3242976 A t u P)). Qed.
Lemma lem3242983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term118 A s t u P) = (term139 A s t u P).
Proof. exact (MK_COMB (@lem3242893 A s t u) (@lem3242978 A t u P)). Qed.
Lemma lem3242986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3242987 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term120 A s t u P) = (term140 A s t u P).
Proof. exact (MK_COMB (@lem3242986) (@lem3242983 A s t u P)). Qed.
Lemma lem3242995 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3242996 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (@lem3242995 A s x t). Qed.
Lemma lem3242997 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) : (term361 A x t s u) = (term362 A t x s u).
Proof. exact (@lem3242996 A (@INTER A s t) x (@INTER A s u)). Qed.
Lemma lem3243001 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3243002 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (@lem3243001 A s x t). Qed.
Lemma lem3243006 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3243007 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3243006 A P x). Qed.
Lemma lem3243008 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3243007 A s x). Qed.
Lemma lem3243009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243010 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3243009) (@lem3243008 A s x)). Qed.
Lemma lem3243012 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3243013 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3243012 A P x). Qed.
Lemma lem3243014 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3243013 A t x). Qed.
Lemma lem3243015 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term142 A s x t) = (term145 A s t x).
Proof. exact (MK_COMB (@lem3243010 A s x) (@lem3243014 A t x)). Qed.
Lemma lem3243018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term141 A x s t) = (term145 A s t x).
Proof. exact (TRANS (@lem3243002 A s x t) (@lem3243015 A s t x)). Qed.
Lemma lem3243019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243020 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term363 A x s t) = (term364 A s t x).
Proof. exact (MK_COMB (@lem3243019) (@lem3243018 A s t x)). Qed.
Lemma lem3243022 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3243023 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term141 A x s t) = (term142 A s x t).
Proof. exact (@lem3243022 A s x t). Qed.
Lemma lem3243024 {A : Type'} (s : A -> Prop) (x : A) (u : A -> Prop) : (term141 A x s u) = (term142 A s x u).
Proof. exact (@lem3243023 A s x u). Qed.
Lemma lem3243028 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3243029 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3243028 A P x). Qed.
Lemma lem3243030 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3243029 A s x). Qed.
Lemma lem3243031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243032 {A : Type'} (s : A -> Prop) (x : A) : (term143 A x s) = (term144 A s x).
Proof. exact (MK_COMB (@lem3243031) (@lem3243030 A s x)). Qed.
Lemma lem3243034 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3243035 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3243034 A P x). Qed.
Lemma lem3243036 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3243035 A u x). Qed.
Lemma lem3243037 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term142 A s x u) = (term145 A s u x).
Proof. exact (MK_COMB (@lem3243032 A s x) (@lem3243036 A u x)). Qed.
Lemma lem3243040 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term141 A x s u) = (term145 A s u x).
Proof. exact (TRANS (@lem3243024 A s x u) (@lem3243037 A s u x)). Qed.
Lemma lem3243041 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term362 A t x s u) = (term365 A t s u x).
Proof. exact (MK_COMB (@lem3243020 A s t x) (@lem3243040 A s u x)). Qed.
Lemma lem3243044 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term361 A x t s u) = (term365 A t s u x).
Proof. exact (TRANS (@lem3242997 A t x s u) (@lem3243041 A t s u x)). Qed.
Lemma lem3243045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3243046 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term366 A x t s u) = (term367 A t s u x).
Proof. exact (MK_COMB (@lem3243045) (@lem3243044 A t s u x)). Qed.
Lemma lem3243048 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3243049 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3243048 A P x). Qed.
Lemma lem3243050 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3243049 A s x). Qed.
Lemma lem3243051 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : ((term361 A x t s u) = (@IN A x s)) = ((term365 A t s u x) = (s x)).
Proof. exact (MK_COMB (@lem3243046 A t s u x) (@lem3243050 A s x)). Qed.
Lemma lem3243054 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term368 A t u s) = (term369 A t u s).
Proof. exact (fun_ext (fun x : A => @lem3243051 A t u s x)). Qed.
Lemma lem3243055 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3243056 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term358 A t u s) = (term370 A t u s).
Proof. exact (MK_COMB (@lem3243055 A) (@lem3243054 A t u s)). Qed.
Lemma lem3243061 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term360 A P t u s) = (term371 A P t u s).
Proof. exact (MK_COMB (@lem3242987 A s t u P) (@lem3243056 A t u s)). Qed.
Lemma lem3243064 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term371 A P t u s) = (term360 A P t u s).
Proof. exact (SYM (@lem3243061 A P t u s)). Qed.
Lemma lem3243066 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3243067 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term371 A P t u s) = (term372 A P t u s).
Proof. exact (@lem3243066 (term371 A P t u s)). Qed.
Lemma lem3243068 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term372 A P t u s) = (term371 A P t u s).
Proof. exact (SYM (@lem3243067 A P t u s)). Qed.
Lemma lem3243069 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term373 A P t u s) : term373 A P t u s.
Proof. exact (h1). Qed.
Lemma lem3243072 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term372 A P t u s) : term372 A P t u s.
Proof. exact (h1). Qed.
Lemma lem3243073 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term374 A P t u s.
Proof. exact (fun h0 : term372 A P t u s => @lem3243072 A P t u s h0). Qed.
Lemma lem3243074 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term374 A P t u s) : term374 A P t u s.
Proof. exact (h1). Qed.
Lemma lem3243075 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term372 A P t u s) : term372 A P t u s.
Proof. exact (h1). Qed.
Lemma lem3243076 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term372 A P t u s) (h2 : term374 A P t u s) : term372 A P t u s.
Proof. exact (@lem3243074 A P t u s h2 (@lem3243075 A P t u s h1)). Qed.
Lemma lem3243077 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term372 A P t u s) : term375 A P t u s.
Proof. exact (fun h0 : term374 A P t u s => @lem3243076 A P t u s h1 h0). Qed.
Lemma lem3243078 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term374 A P t u s) : term374 A P t u s.
Proof. exact (h1). Qed.
Lemma lem3243079 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term372 A P t u s) (h2 : term374 A P t u s) : term372 A P t u s.
Proof. exact (@lem3243077 A P t u s h1 (@lem3243078 A P t u s h2)). Qed.
Lemma lem3243080 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term374 A P t u s) : term374 A P t u s.
Proof. exact (fun h0 : term372 A P t u s => @lem3243079 A P t u s h0 h1). Qed.
Lemma lem3243081 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term376 A P t u s.
Proof. exact (fun h0 : term374 A P t u s => @lem3243080 A P t u s h0). Qed.
Lemma lem3243084 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term374 A P t u s.
Proof. exact (@lem3243081 A P t u s (@lem3243073 A P t u s)). Qed.
Lemma lem3243085 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term374 A P t u s.
Proof. exact (@lem3243084 A P t u s). Qed.
Lemma lem3243103 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3243104 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term372 A P t u s) = (term377 A P t u s).
Proof. exact (@lem3243103 (term373 A P t u s)). Qed.
Lemma lem3243106 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3243107 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term377 A P t u s) = (term371 A P t u s).
Proof. exact (@lem3243106 (term371 A P t u s)). Qed.
Lemma lem3243110 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term372 A P t u s) = (term371 A P t u s).
Proof. exact (TRANS (@lem3243104 A P t u s) (@lem3243107 A P t u s)). Qed.
Lemma lem3243155 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term378 A t u s) = (term379 A t u s).
Proof. exact (fun_ext (fun P : type686 A => @lem3243110 A P t u s)). Qed.
Lemma lem3243156 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3243157 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term380 A t u s) = (term381 A t u s).
Proof. exact (MK_COMB (@lem3243156 A) (@lem3243155 A t u s)). Qed.
Lemma lem3243162 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term382 A u s) = (term383 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3243157 A t u s)). Qed.
Lemma lem3243163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243164 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term384 A u s) = (term385 A u s).
Proof. exact (MK_COMB (@lem3243163 A) (@lem3243162 A u s)). Qed.
Lemma lem3243169 {A : Type'} (s : A -> Prop) : (term386 A s) = (term387 A s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3243164 A u s)). Qed.
Lemma lem3243170 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243171 {A : Type'} (s : A -> Prop) : (term388 A s) = (term389 A s).
Proof. exact (MK_COMB (@lem3243170 A) (@lem3243169 A s)). Qed.
Lemma lem3243176 {A : Type'} : (term390 A) = (term391 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3243171 A s)). Qed.
Lemma lem3243177 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243186 {A : Type'} : (term392 A) = (term393 A).
Proof. exact (MK_COMB (@lem3243177 A) (@lem3243176 A)). Qed.
Lemma lem3243203 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : ((term365 A t s u x) = (s x)) = ((term365 A t s u x) = (s x)).
Proof. exact (eq_refl ((term365 A t s u x) = (s x))). Qed.
Lemma lem3243204 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term369 A t u s) = (term369 A t u s).
Proof. exact (fun_ext (fun x : A => @lem3243203 A t u s x)). Qed.
Lemma lem3243205 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3243206 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term370 A t u s) = (term370 A t u s).
Proof. exact (MK_COMB (@lem3243205 A) (@lem3243204 A t u s)). Qed.
Lemma lem3243207 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3243212 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term24 A u' u x) = (term24 A u' u x).
Proof. exact (eq_refl (term24 A u' u x)). Qed.
Lemma lem3243213 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term26 A u' u) = (term26 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3243212 A u' u x)). Qed.
Lemma lem3243214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3243215 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term27 A u' u) = (term27 A u' u).
Proof. exact (MK_COMB (@lem3243214 A) (@lem3243213 A u' u)). Qed.
Lemma lem3243220 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term24 A t' t x) = (term24 A t' t x).
Proof. exact (eq_refl (term24 A t' t x)). Qed.
Lemma lem3243221 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term26 A t' t) = (term26 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3243220 A t' t x)). Qed.
Lemma lem3243222 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3243223 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term27 A t' t) = (term27 A t' t).
Proof. exact (MK_COMB (@lem3243222 A) (@lem3243221 A t' t)). Qed.
Lemma lem3243224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243225 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term28 A t' t) = (term28 A t' t).
Proof. exact (MK_COMB (@lem3243224) (@lem3243223 A t' t)). Qed.
Lemma lem3243226 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term29 A t' t u' u) = (term29 A t' t u' u).
Proof. exact (MK_COMB (@lem3243225 A t' t) (@lem3243215 A u' u)). Qed.
Lemma lem3243227 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3243228 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term30 A t' t u' u) = (term30 A t' t u' u).
Proof. exact (MK_COMB (@lem3243227) (@lem3243226 A t' t u' u)). Qed.
Lemma lem3243229 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term134 A t u P t' u') = (term134 A t u P t' u').
Proof. exact (MK_COMB (@lem3243228 A t' t u' u) (@lem3243207 A P t' u')). Qed.
Lemma lem3243230 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term135 A t u P t') = (term135 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3243229 A t u P t' u')). Qed.
Lemma lem3243231 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243232 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term136 A t u P t') = (term136 A t u P t').
Proof. exact (MK_COMB (@lem3243231 A) (@lem3243230 A t u P t')). Qed.
Lemma lem3243233 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term137 A t u P) = (term137 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3243232 A t u P t')). Qed.
Lemma lem3243234 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243235 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term138 A t u P) = (term138 A t u P).
Proof. exact (MK_COMB (@lem3243234 A) (@lem3243233 A t u P)). Qed.
Lemma lem3243244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term129 A s t u x) = (term129 A s t u x).
Proof. exact (eq_refl (term129 A s t u x)). Qed.
Lemma lem3243245 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term131 A s t u) = (term131 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3243244 A s t u x)). Qed.
Lemma lem3243246 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3243247 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term132 A s t u) = (term132 A s t u).
Proof. exact (MK_COMB (@lem3243246 A) (@lem3243245 A s t u)). Qed.
Lemma lem3243248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243249 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term133 A s t u) = (term133 A s t u).
Proof. exact (MK_COMB (@lem3243248) (@lem3243247 A s t u)). Qed.
Lemma lem3243250 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term139 A s t u P) = (term139 A s t u P).
Proof. exact (MK_COMB (@lem3243249 A s t u) (@lem3243235 A t u P)). Qed.
Lemma lem3243251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3243252 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term140 A s t u P) = (term140 A s t u P).
Proof. exact (MK_COMB (@lem3243251) (@lem3243250 A s t u P)). Qed.
Lemma lem3243253 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term371 A P t u s) = (term371 A P t u s).
Proof. exact (MK_COMB (@lem3243252 A s t u P) (@lem3243206 A t u s)). Qed.
Lemma lem3243254 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term379 A t u s) = (term379 A t u s).
Proof. exact (fun_ext (fun P : type686 A => @lem3243253 A P t u s)). Qed.
Lemma lem3243255 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3243256 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term381 A t u s) = (term381 A t u s).
Proof. exact (MK_COMB (@lem3243255 A) (@lem3243254 A t u s)). Qed.
Lemma lem3243257 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term383 A u s) = (term383 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3243256 A t u s)). Qed.
Lemma lem3243258 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243259 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term385 A u s) = (term385 A u s).
Proof. exact (MK_COMB (@lem3243258 A) (@lem3243257 A u s)). Qed.
Lemma lem3243260 {A : Type'} (s : A -> Prop) : (term387 A s) = (term387 A s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3243259 A u s)). Qed.
Lemma lem3243261 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243262 {A : Type'} (s : A -> Prop) : (term389 A s) = (term389 A s).
Proof. exact (MK_COMB (@lem3243261 A) (@lem3243260 A s)). Qed.
Lemma lem3243263 {A : Type'} : (term391 A) = (term391 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3243262 A s)). Qed.
Lemma lem3243264 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243265 {A : Type'} : (term393 A) = (term393 A).
Proof. exact (MK_COMB (@lem3243264 A) (@lem3243263 A)). Qed.
Lemma lem3243350 {A : Type'} : (term392 A) = (term393 A).
Proof. exact (TRANS (@lem3243186 A) (@lem3243265 A)). Qed.
Lemma lem3243351 {A : Type'} : (term393 A) = (term392 A).
Proof. exact (SYM (@lem3243350 A)). Qed.
Lemma lem3243352 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term139 A s t u P.
Proof. exact (h1). Qed.
Lemma lem3243354 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3243355 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : ((term365 A t s u x) = (s x)) = (term394 A t u s x).
Proof. exact (@lem3243354 ((term365 A t s u x) = (s x))). Qed.
Lemma lem3243356 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term394 A t u s x) = ((term365 A t s u x) = (s x)).
Proof. exact (SYM (@lem3243355 A t u s x)). Qed.
Lemma lem3243357 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term395 A t u s x) : term395 A t u s x.
Proof. exact (h1). Qed.
Lemma lem3243368 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term129 A s t u x) = (term180 A s t u x).
Proof. exact (@lem17265 (s x) (term35 A t u x)). Qed.
Lemma lem3243369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term131 A s t u) = (term181 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3243368 A s t u x)). Qed.
Lemma lem3243370 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3243371 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term132 A s t u) = (term182 A s t u).
Proof. exact (MK_COMB (@lem3243370 A) (@lem3243369 A s t u)). Qed.
Lemma lem3243378 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term183 A t' t x) = (term184 A t' t x).
Proof. exact (@lem17362 (t' x) (t x)). Qed.
Lemma lem3243379 {A : Type'} (P : A -> Prop) : (term185 A P) = (term186 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3243380 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term187 A t' t) = (term188 A t' t).
Proof. exact (@lem3243379 A (term26 A t' t)). Qed.
Lemma lem3243381 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term189 A t' t x) = (term24 A t' t x).
Proof. exact (eq_refl (term189 A t' t x)). Qed.
Lemma lem3243382 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243383 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term190 A t' t x) = (term183 A t' t x).
Proof. exact (MK_COMB (@lem3243382) (@lem3243381 A t' t x)). Qed.
Lemma lem3243384 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term190 A t' t x) = (term184 A t' t x).
Proof. exact (TRANS (@lem3243383 A t' t x) (@lem3243378 A t' t x)). Qed.
Lemma lem3243385 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term191 A t' t) = (term192 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3243384 A t' t x)). Qed.
Lemma lem3243386 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243387 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term188 A t' t) = (term193 A t' t).
Proof. exact (MK_COMB (@lem3243386 A) (@lem3243385 A t' t)). Qed.
Lemma lem3243388 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term187 A t' t) = (term193 A t' t).
Proof. exact (TRANS (@lem3243380 A t' t) (@lem3243387 A t' t)). Qed.
Lemma lem3243395 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term183 A u' u x) = (term184 A u' u x).
Proof. exact (@lem17362 (u' x) (u x)). Qed.
Lemma lem3243396 {A : Type'} (P : A -> Prop) : (term185 A P) = (term186 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3243397 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term187 A u' u) = (term188 A u' u).
Proof. exact (@lem3243396 A (term26 A u' u)). Qed.
Lemma lem3243398 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term189 A u' u x) = (term24 A u' u x).
Proof. exact (eq_refl (term189 A u' u x)). Qed.
Lemma lem3243399 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243400 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term190 A u' u x) = (term183 A u' u x).
Proof. exact (MK_COMB (@lem3243399) (@lem3243398 A u' u x)). Qed.
Lemma lem3243401 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term190 A u' u x) = (term184 A u' u x).
Proof. exact (TRANS (@lem3243400 A u' u x) (@lem3243395 A u' u x)). Qed.
Lemma lem3243402 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term191 A u' u) = (term192 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3243401 A u' u x)). Qed.
Lemma lem3243403 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243404 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term188 A u' u) = (term193 A u' u).
Proof. exact (MK_COMB (@lem3243403 A) (@lem3243402 A u' u)). Qed.
Lemma lem3243405 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term187 A u' u) = (term193 A u' u).
Proof. exact (TRANS (@lem3243397 A u' u) (@lem3243404 A u' u)). Qed.
Lemma lem3243406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243407 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term194 A t' t) = (term195 A t' t).
Proof. exact (MK_COMB (@lem3243406) (@lem3243388 A t' t)). Qed.
Lemma lem3243408 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term196 A t' t u' u) = (term197 A t' t u' u).
Proof. exact (MK_COMB (@lem3243407 A t' t) (@lem3243405 A u' u)). Qed.
Lemma lem3243409 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term198 A t' t u' u) = (term196 A t' t u' u).
Proof. exact (@lem17045 (term27 A t' t) (term27 A u' u)). Qed.
Lemma lem3243410 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term198 A t' t u' u) = (term197 A t' t u' u).
Proof. exact (TRANS (@lem3243409 A t' t u' u) (@lem3243408 A t' t u' u)). Qed.
Lemma lem3243411 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3243412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243413 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term199 A t' t u' u) = (term200 A t' t u' u).
Proof. exact (MK_COMB (@lem3243412) (@lem3243410 A t' t u' u)). Qed.
Lemma lem3243414 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term201 A t u P t' u') = (term202 A t u P t' u').
Proof. exact (MK_COMB (@lem3243413 A t' t u' u) (@lem3243411 A P t' u')). Qed.
Lemma lem3243415 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term134 A t u P t' u') = (term201 A t u P t' u').
Proof. exact (@lem17265 (term29 A t' t u' u) (term93 A P t' u')). Qed.
Lemma lem3243416 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term134 A t u P t' u') = (term202 A t u P t' u').
Proof. exact (TRANS (@lem3243415 A t u P t' u') (@lem3243414 A t u P t' u')). Qed.
Lemma lem3243417 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term135 A t u P t') = (term203 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3243416 A t u P t' u')). Qed.
Lemma lem3243418 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243419 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term136 A t u P t') = (term204 A t u P t').
Proof. exact (MK_COMB (@lem3243418 A) (@lem3243417 A t u P t')). Qed.
Lemma lem3243420 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term137 A t u P) = (term205 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3243419 A t u P t')). Qed.
Lemma lem3243421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243422 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term138 A t u P) = (term206 A t u P).
Proof. exact (MK_COMB (@lem3243421 A) (@lem3243420 A t u P)). Qed.
Lemma lem3243423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243424 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term133 A s t u) = (term207 A s t u).
Proof. exact (MK_COMB (@lem3243423) (@lem3243371 A s t u)). Qed.
Lemma lem3243425 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term139 A s t u P) = (term208 A s t u P).
Proof. exact (MK_COMB (@lem3243424 A s t u) (@lem3243422 A t u P)). Qed.
Lemma lem3243584 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3243585 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (@lem3243584 A P Q). Qed.
Lemma lem3243586 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term211 A t' t u' u) = (term212 A t' t u' u).
Proof. exact (@lem3243585 A (term192 A t' t) (term192 A u' u)). Qed.
Lemma lem3243587 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term213 A t' t x) = (term184 A t' t x).
Proof. exact (eq_refl (term213 A t' t x)). Qed.
Lemma lem3243588 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term214 A t' t) = (term192 A t' t).
Proof. exact (fun_ext (fun x : A => @lem3243587 A t' t x)). Qed.
Lemma lem3243589 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243590 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term215 A t' t) = (term193 A t' t).
Proof. exact (MK_COMB (@lem3243589 A) (@lem3243588 A t' t)). Qed.
Lemma lem3243591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243592 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term216 A t' t) = (term195 A t' t).
Proof. exact (MK_COMB (@lem3243591) (@lem3243590 A t' t)). Qed.
Lemma lem3243593 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term213 A u' u x) = (term184 A u' u x).
Proof. exact (eq_refl (term213 A u' u x)). Qed.
Lemma lem3243594 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term214 A u' u) = (term192 A u' u).
Proof. exact (fun_ext (fun x : A => @lem3243593 A u' u x)). Qed.
Lemma lem3243595 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243596 {A : Type'} (u' : A -> Prop) (u : A -> Prop) : (term215 A u' u) = (term193 A u' u).
Proof. exact (MK_COMB (@lem3243595 A) (@lem3243594 A u' u)). Qed.
Lemma lem3243597 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term211 A t' t u' u) = (term197 A t' t u' u).
Proof. exact (MK_COMB (@lem3243592 A t' t) (@lem3243596 A u' u)). Qed.
Lemma lem3243598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3243599 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term217 A t' t u' u) = (term218 A t' t u' u).
Proof. exact (MK_COMB (@lem3243598) (@lem3243597 A t' t u' u)). Qed.
Lemma lem3243600 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term213 A t' t x) = (term184 A t' t x).
Proof. exact (eq_refl (term213 A t' t x)). Qed.
Lemma lem3243601 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243602 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A) : (term219 A t' t x) = (term220 A t' t x).
Proof. exact (MK_COMB (@lem3243601) (@lem3243600 A t' t x)). Qed.
Lemma lem3243603 {A : Type'} (u' : A -> Prop) (u : A -> Prop) (x : A) : (term213 A u' u x) = (term184 A u' u x).
Proof. exact (eq_refl (term213 A u' u x)). Qed.
Lemma lem3243604 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term221 A t' t u' u x) = (term222 A t' t u' u x).
Proof. exact (MK_COMB (@lem3243602 A t' t x) (@lem3243603 A u' u x)). Qed.
Lemma lem3243605 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term223 A t' t u' u) = (term224 A t' t u' u).
Proof. exact (fun_ext (fun x : A => @lem3243604 A t' t u' u x)). Qed.
Lemma lem3243606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243607 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term212 A t' t u' u) = (term225 A t' t u' u).
Proof. exact (MK_COMB (@lem3243606 A) (@lem3243605 A t' t u' u)). Qed.
Lemma lem3243608 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : ((term211 A t' t u' u) = (term212 A t' t u' u)) = ((term197 A t' t u' u) = (term225 A t' t u' u)).
Proof. exact (MK_COMB (@lem3243599 A t' t u' u) (@lem3243607 A t' t u' u)). Qed.
Lemma lem3243609 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term197 A t' t u' u) = (term225 A t' t u' u).
Proof. exact (EQ_MP (@lem3243608 A t' t u' u) (@lem3243586 A t' t u' u)). Qed.
Lemma lem3243610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243611 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term200 A t' t u' u) = (term226 A t' t u' u).
Proof. exact (MK_COMB (@lem3243610) (@lem3243609 A t' t u' u)). Qed.
Lemma lem3243612 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3243613 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term202 A t u P t' u') = (term227 A t u P t' u').
Proof. exact (MK_COMB (@lem3243611 A t' t u' u) (@lem3243612 A P t' u')). Qed.
Lemma lem3243615 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3243616 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (@lem3243615 A P Q). Qed.
Lemma lem3243617 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term230 A t u P t' u') = (term231 A t u P t' u').
Proof. exact (@lem3243616 A (term224 A t' t u' u) (term93 A P t' u')). Qed.
Lemma lem3243618 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term232 A t' t u' u x) = (term222 A t' t u' u x).
Proof. exact (eq_refl (term232 A t' t u' u x)). Qed.
Lemma lem3243619 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term233 A t' t u' u) = (term224 A t' t u' u).
Proof. exact (fun_ext (fun x : A => @lem3243618 A t' t u' u x)). Qed.
Lemma lem3243620 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243621 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term234 A t' t u' u) = (term225 A t' t u' u).
Proof. exact (MK_COMB (@lem3243620 A) (@lem3243619 A t' t u' u)). Qed.
Lemma lem3243622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243623 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) : (term235 A t' t u' u) = (term226 A t' t u' u).
Proof. exact (MK_COMB (@lem3243622) (@lem3243621 A t' t u' u)). Qed.
Lemma lem3243624 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3243625 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term230 A t u P t' u') = (term227 A t u P t' u').
Proof. exact (MK_COMB (@lem3243623 A t' t u' u) (@lem3243624 A P t' u')). Qed.
Lemma lem3243626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3243627 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term236 A t u P t' u') = (term237 A t u P t' u').
Proof. exact (MK_COMB (@lem3243626) (@lem3243625 A t u P t' u')). Qed.
Lemma lem3243628 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term232 A t' t u' u x) = (term222 A t' t u' u x).
Proof. exact (eq_refl (term232 A t' t u' u x)). Qed.
Lemma lem3243629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243630 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (u' : A -> Prop) (u : A -> Prop) (x : A) : (term238 A t' t u' u x) = (term239 A t' t u' u x).
Proof. exact (MK_COMB (@lem3243629) (@lem3243628 A t' t u' u x)). Qed.
Lemma lem3243631 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term93 A P t' u').
Proof. exact (eq_refl (term93 A P t' u')). Qed.
Lemma lem3243632 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term240 A t u x P t' u') = (term241 A t u x P t' u').
Proof. exact (MK_COMB (@lem3243630 A t' t u' u x) (@lem3243631 A P t' u')). Qed.
Lemma lem3243633 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term242 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (fun_ext (fun x : A => @lem3243632 A t u x P t' u')). Qed.
Lemma lem3243634 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243635 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term231 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (MK_COMB (@lem3243634 A) (@lem3243633 A t u P t' u')). Qed.
Lemma lem3243636 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : ((term230 A t u P t' u') = (term231 A t u P t' u')) = ((term227 A t u P t' u') = (term244 A t u P t' u')).
Proof. exact (MK_COMB (@lem3243627 A t u P t' u') (@lem3243635 A t u P t' u')). Qed.
Lemma lem3243637 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term227 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (EQ_MP (@lem3243636 A t u P t' u') (@lem3243617 A t u P t' u')). Qed.
Lemma lem3243638 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term202 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (TRANS (@lem3243613 A t u P t' u') (@lem3243637 A t u P t' u')). Qed.
Lemma lem3243639 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term203 A t u P t') = (term245 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3243638 A t u P t' u')). Qed.
Lemma lem3243640 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243641 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term204 A t u P t') = (term246 A t u P t').
Proof. exact (MK_COMB (@lem3243640 A) (@lem3243639 A t u P t')). Qed.
Lemma lem3243643 {A B : Type'} (P : type1413 A B) : (term247 A B P) = (term248 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3243644 {A : Type'} (P : type672 A) : (term249 A P) = (term250 A P).
Proof. exact (@lem3243643 (A -> Prop) A P). Qed.
Lemma lem3243645 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term251 A t u P t') = (term252 A t u P t').
Proof. exact (@lem3243644 A (term253 A t u P t')). Qed.
Lemma lem3243646 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term254 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (eq_refl (term254 A t u P t' u')). Qed.
Lemma lem3243647 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3243648 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) (x : A) : (term255 A t u P t' u' x) = (term256 A t u P t' u' x).
Proof. exact (MK_COMB (@lem3243646 A t u P t' u') (@lem3243647 A x)). Qed.
Lemma lem3243649 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term256 A t u P t' u' x) = (term241 A t u x P t' u').
Proof. exact (eq_refl (term256 A t u P t' u' x)). Qed.
Lemma lem3243650 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term255 A t u P t' u' x) = (term241 A t u x P t' u').
Proof. exact (TRANS (@lem3243648 A t u P t' u' x) (@lem3243649 A t u x P t' u')). Qed.
Lemma lem3243651 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term257 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (fun_ext (fun x : A => @lem3243650 A t u x P t' u')). Qed.
Lemma lem3243652 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3243653 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term258 A t u P t' u') = (term244 A t u P t' u').
Proof. exact (MK_COMB (@lem3243652 A) (@lem3243651 A t u P t' u')). Qed.
Lemma lem3243654 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term259 A t u P t') = (term245 A t u P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3243653 A t u P t' u')). Qed.
Lemma lem3243655 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243656 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term251 A t u P t') = (term246 A t u P t').
Proof. exact (MK_COMB (@lem3243655 A) (@lem3243654 A t u P t')). Qed.
Lemma lem3243657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3243658 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term260 A t u P t') = (term261 A t u P t').
Proof. exact (MK_COMB (@lem3243657) (@lem3243656 A t u P t')). Qed.
Lemma lem3243659 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term254 A t u P t' u') = (term243 A t u P t' u').
Proof. exact (eq_refl (term254 A t u P t' u')). Qed.
Lemma lem3243660 {A : Type'} (x : type684 A) (u' : A -> Prop) : (x u') = (x u').
Proof. exact (eq_refl (x u')). Qed.
Lemma lem3243661 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (x : type684 A) (u' : A -> Prop) : (term262 A t u P t' x u') = (term263 A t u P t' x u').
Proof. exact (MK_COMB (@lem3243659 A t u P t' u') (@lem3243660 A x u')). Qed.
Lemma lem3243662 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term263 A t u P t' x u') = (term264 A t u x P t' u').
Proof. exact (eq_refl (term263 A t u P t' x u')). Qed.
Lemma lem3243663 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term262 A t u P t' x u') = (term264 A t u x P t' u').
Proof. exact (TRANS (@lem3243661 A t u P t' x u') (@lem3243662 A t u x P t' u')). Qed.
Lemma lem3243664 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term265 A t u P t' x) = (term266 A t u x P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3243663 A t u x P t' u')). Qed.
Lemma lem3243665 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243666 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term267 A t u P t' x) = (term268 A t u x P t').
Proof. exact (MK_COMB (@lem3243665 A) (@lem3243664 A t u x P t')). Qed.
Lemma lem3243667 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term269 A t u P t') = (term270 A t u P t').
Proof. exact (fun_ext (fun x : type684 A => @lem3243666 A t u x P t')). Qed.
Lemma lem3243668 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3243669 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term252 A t u P t') = (term271 A t u P t').
Proof. exact (MK_COMB (@lem3243668 A) (@lem3243667 A t u P t')). Qed.
Lemma lem3243670 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : ((term251 A t u P t') = (term252 A t u P t')) = ((term246 A t u P t') = (term271 A t u P t')).
Proof. exact (MK_COMB (@lem3243658 A t u P t') (@lem3243669 A t u P t')). Qed.
Lemma lem3243671 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term246 A t u P t') = (term271 A t u P t').
Proof. exact (EQ_MP (@lem3243670 A t u P t') (@lem3243645 A t u P t')). Qed.
Lemma lem3243672 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term204 A t u P t') = (term271 A t u P t').
Proof. exact (TRANS (@lem3243641 A t u P t') (@lem3243671 A t u P t')). Qed.
Lemma lem3243673 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term205 A t u P) = (term272 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3243672 A t u P t')). Qed.
Lemma lem3243674 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243675 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term206 A t u P) = (term273 A t u P).
Proof. exact (MK_COMB (@lem3243674 A) (@lem3243673 A t u P)). Qed.
Lemma lem3243677 {A B : Type'} (P : type1413 A B) : (term247 A B P) = (term248 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3243678 {A : Type'} (P : type597 A) : (term274 A P) = (term275 A P).
Proof. exact (@lem3243677 (A -> Prop) (type684 A) P). Qed.
Lemma lem3243679 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term276 A t u P) = (term277 A t u P).
Proof. exact (@lem3243678 A (term278 A t u P)). Qed.
Lemma lem3243680 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term279 A t u P t') = (term270 A t u P t').
Proof. exact (eq_refl (term279 A t u P t')). Qed.
Lemma lem3243681 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3243682 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) (x : type684 A) : (term280 A t u P t' x) = (term281 A t u P t' x).
Proof. exact (MK_COMB (@lem3243680 A t u P t') (@lem3243681 A x)). Qed.
Lemma lem3243683 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term281 A t u P t' x) = (term268 A t u x P t').
Proof. exact (eq_refl (term281 A t u P t' x)). Qed.
Lemma lem3243684 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type684 A) (P : type686 A) (t' : A -> Prop) : (term280 A t u P t' x) = (term268 A t u x P t').
Proof. exact (TRANS (@lem3243682 A t u P t' x) (@lem3243683 A t u x P t')). Qed.
Lemma lem3243685 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term282 A t u P t') = (term270 A t u P t').
Proof. exact (fun_ext (fun x : type684 A => @lem3243684 A t u x P t')). Qed.
Lemma lem3243686 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3243687 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term283 A t u P t') = (term271 A t u P t').
Proof. exact (MK_COMB (@lem3243686 A) (@lem3243685 A t u P t')). Qed.
Lemma lem3243688 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term284 A t u P) = (term272 A t u P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3243687 A t u P t')). Qed.
Lemma lem3243689 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243690 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term276 A t u P) = (term273 A t u P).
Proof. exact (MK_COMB (@lem3243689 A) (@lem3243688 A t u P)). Qed.
Lemma lem3243691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3243692 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term285 A t u P) = (term286 A t u P).
Proof. exact (MK_COMB (@lem3243691) (@lem3243690 A t u P)). Qed.
Lemma lem3243693 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term279 A t u P t') = (term270 A t u P t').
Proof. exact (eq_refl (term279 A t u P t')). Qed.
Lemma lem3243694 {A : Type'} (x : type638 A) (t' : A -> Prop) : (x t') = (x t').
Proof. exact (eq_refl (x t')). Qed.
Lemma lem3243695 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (x : type638 A) (t' : A -> Prop) : (term287 A t u P x t') = (term288 A t u P x t').
Proof. exact (MK_COMB (@lem3243693 A t u P t') (@lem3243694 A x t')). Qed.
Lemma lem3243696 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) (t' : A -> Prop) : (term288 A t u P x t') = (term289 A t u x P t').
Proof. exact (eq_refl (term288 A t u P x t')). Qed.
Lemma lem3243697 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) (t' : A -> Prop) : (term287 A t u P x t') = (term289 A t u x P t').
Proof. exact (TRANS (@lem3243695 A t u P x t') (@lem3243696 A t u x P t')). Qed.
Lemma lem3243698 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term290 A t u P x) = (term291 A t u x P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3243697 A t u x P t')). Qed.
Lemma lem3243699 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3243700 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term292 A t u P x) = (term293 A t u x P).
Proof. exact (MK_COMB (@lem3243699 A) (@lem3243698 A t u x P)). Qed.
Lemma lem3243701 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term294 A t u P) = (term295 A t u P).
Proof. exact (fun_ext (fun x : type638 A => @lem3243700 A t u x P)). Qed.
Lemma lem3243702 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem3243703 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term277 A t u P) = (term296 A t u P).
Proof. exact (MK_COMB (@lem3243702 A) (@lem3243701 A t u P)). Qed.
Lemma lem3243704 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term276 A t u P) = (term277 A t u P)) = ((term273 A t u P) = (term296 A t u P)).
Proof. exact (MK_COMB (@lem3243692 A t u P) (@lem3243703 A t u P)). Qed.
Lemma lem3243705 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term273 A t u P) = (term296 A t u P).
Proof. exact (EQ_MP (@lem3243704 A t u P) (@lem3243679 A t u P)). Qed.
Lemma lem3243706 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term206 A t u P) = (term296 A t u P).
Proof. exact (TRANS (@lem3243675 A t u P) (@lem3243705 A t u P)). Qed.
Lemma lem3243707 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term207 A s t u) = (term207 A s t u).
Proof. exact (eq_refl (term207 A s t u)). Qed.
Lemma lem3243708 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term208 A s t u P) = (term297 A s t u P).
Proof. exact (MK_COMB (@lem3243707 A s t u) (@lem3243706 A t u P)). Qed.
Lemma lem3243710 {A : Type'} (P : Prop) (Q : A -> Prop) : (term298 A P Q) = (term299 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3243711 {A : Type'} (P : Prop) (Q : type139 A) : (term300 A P Q) = (term301 A P Q).
Proof. exact (@lem3243710 (type638 A) P Q). Qed.
Lemma lem3243712 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term302 A s t u P) = (term303 A s t u P).
Proof. exact (@lem3243711 A (term182 A s t u) (term295 A t u P)). Qed.
Lemma lem3243713 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term304 A t u P x) = (term293 A t u x P).
Proof. exact (eq_refl (term304 A t u P x)). Qed.
Lemma lem3243714 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term305 A t u P) = (term295 A t u P).
Proof. exact (fun_ext (fun x : type638 A => @lem3243713 A t u x P)). Qed.
Lemma lem3243715 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem3243716 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term306 A t u P) = (term296 A t u P).
Proof. exact (MK_COMB (@lem3243715 A) (@lem3243714 A t u P)). Qed.
Lemma lem3243717 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term207 A s t u) = (term207 A s t u).
Proof. exact (eq_refl (term207 A s t u)). Qed.
Lemma lem3243718 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term302 A s t u P) = (term297 A s t u P).
Proof. exact (MK_COMB (@lem3243717 A s t u) (@lem3243716 A t u P)). Qed.
Lemma lem3243719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3243720 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term307 A s t u P) = (term308 A s t u P).
Proof. exact (MK_COMB (@lem3243719) (@lem3243718 A s t u P)). Qed.
Lemma lem3243721 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term304 A t u P x) = (term293 A t u x P).
Proof. exact (eq_refl (term304 A t u P x)). Qed.
Lemma lem3243722 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term207 A s t u) = (term207 A s t u).
Proof. exact (eq_refl (term207 A s t u)). Qed.
Lemma lem3243723 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : type638 A) (P : type686 A) : (term309 A s t u P x) = (term310 A s t u x P).
Proof. exact (MK_COMB (@lem3243722 A s t u) (@lem3243721 A t u x P)). Qed.
Lemma lem3243724 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term311 A s t u P) = (term312 A s t u P).
Proof. exact (fun_ext (fun x : type638 A => @lem3243723 A s t u x P)). Qed.
Lemma lem3243725 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem3243726 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term303 A s t u P) = (term313 A s t u P).
Proof. exact (MK_COMB (@lem3243725 A) (@lem3243724 A s t u P)). Qed.
Lemma lem3243727 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : ((term302 A s t u P) = (term303 A s t u P)) = ((term297 A s t u P) = (term313 A s t u P)).
Proof. exact (MK_COMB (@lem3243720 A s t u P) (@lem3243726 A s t u P)). Qed.
Lemma lem3243728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term297 A s t u P) = (term313 A s t u P).
Proof. exact (EQ_MP (@lem3243727 A s t u P) (@lem3243712 A s t u P)). Qed.
Lemma lem3243730 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term208 A s t u P) = (term313 A s t u P).
Proof. exact (TRANS (@lem3243708 A s t u P) (@lem3243728 A s t u P)). Qed.
Lemma lem3243731 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term139 A s t u P) = (term313 A s t u P).
Proof. exact (TRANS (@lem3243425 A s t u P) (@lem3243730 A s t u P)). Qed.
Lemma lem3243732 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term313 A s t u P.
Proof. exact (EQ_MP (@lem3243731 A s t u P) (@lem3243352 A s t u P h1)). Qed.
Lemma lem3243741 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term396 A s t x) = (term397 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3243753 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term396 A s u x) = (term397 A s u x).
Proof. exact (@lem17045 (s x) (u x)). Qed.
Lemma lem3243757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243758 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term398 A s t x) = (term399 A s t x).
Proof. exact (MK_COMB (@lem3243757) (@lem3243741 A s t x)). Qed.
Lemma lem3243759 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term400 A t s u x) = (term401 A t s u x).
Proof. exact (MK_COMB (@lem3243758 A s t x) (@lem3243753 A s u x)). Qed.
Lemma lem3243760 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term402 A t s u x) = (term400 A t s u x).
Proof. exact (@lem17160 (term145 A s t x) (term145 A s u x)). Qed.
Lemma lem3243761 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term402 A t s u x) = (term401 A t s u x).
Proof. exact (TRANS (@lem3243760 A t s u x) (@lem3243759 A t s u x)). Qed.
Lemma lem3243766 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3243767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243768 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term403 A t s u x) = (term404 A t s u x).
Proof. exact (MK_COMB (@lem3243767) (@lem3243761 A t s u x)). Qed.
Lemma lem3243769 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term405 A t u s x) = (term406 A t u s x).
Proof. exact (MK_COMB (@lem3243768 A t s u x) (@lem3243766 A s x)). Qed.
Lemma lem3243774 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term407 A t u s x) = (term407 A t u s x).
Proof. exact (eq_refl (term407 A t u s x)). Qed.
Lemma lem3243775 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term408 A t u s x) = (term409 A t u s x).
Proof. exact (MK_COMB (@lem3243774 A t u s x) (@lem3243769 A t u s x)). Qed.
Lemma lem3243776 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term395 A t u s x) = (term408 A t u s x).
Proof. exact (@lem17646 (term365 A t s u x) (s x)). Qed.
Lemma lem3243781 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term395 A t u s x) = (term409 A t u s x).
Proof. exact (TRANS (@lem3243776 A t u s x) (@lem3243775 A t u s x)). Qed.
Lemma lem3243782 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term395 A t u s x) : term409 A t u s x.
Proof. exact (EQ_MP (@lem3243781 A t u s x) (@lem3243357 A t u s x h1)). Qed.
Lemma lem3243783 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term310 A s t u x' P.
Proof. exact (h1). Qed.
Lemma lem3243788 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243789 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243788 A Prop f x). Qed.
Lemma lem3243791 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3243789 A s x). Qed.
Lemma lem3243792 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243798 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243797 A Prop f x). Qed.
Lemma lem3243800 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3243798 A u x). Qed.
Lemma lem3243801 {A : Type'} (u : A -> Prop) (x : A) : (term77 A u x) = (term342 A u x).
Proof. exact (MK_COMB (@lem3243792) (@lem3243800 A u x)). Qed.
Lemma lem3243802 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243808 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243807 A Prop f x). Qed.
Lemma lem3243810 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3243808 A s x). Qed.
Lemma lem3243811 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term342 A s x).
Proof. exact (MK_COMB (@lem3243802) (@lem3243810 A s x)). Qed.
Lemma lem3243812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243813 {A : Type'} (s : A -> Prop) (x : A) : (term410 A s x) = (term411 A s x).
Proof. exact (MK_COMB (@lem3243812) (@lem3243811 A s x)). Qed.
Lemma lem3243814 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term397 A s u x) = (term412 A s u x).
Proof. exact (MK_COMB (@lem3243813 A s x) (@lem3243801 A u x)). Qed.
Lemma lem3243815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243820 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243821 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243820 A Prop f x). Qed.
Lemma lem3243823 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3243821 A t x). Qed.
Lemma lem3243824 {A : Type'} (t : A -> Prop) (x : A) : (term77 A t x) = (term342 A t x).
Proof. exact (MK_COMB (@lem3243815) (@lem3243823 A t x)). Qed.
Lemma lem3243825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243831 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243830 A Prop f x). Qed.
Lemma lem3243833 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3243831 A s x). Qed.
Lemma lem3243834 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term342 A s x).
Proof. exact (MK_COMB (@lem3243825) (@lem3243833 A s x)). Qed.
Lemma lem3243835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243836 {A : Type'} (s : A -> Prop) (x : A) : (term410 A s x) = (term411 A s x).
Proof. exact (MK_COMB (@lem3243835) (@lem3243834 A s x)). Qed.
Lemma lem3243837 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term397 A s t x) = (term412 A s t x).
Proof. exact (MK_COMB (@lem3243836 A s x) (@lem3243824 A t x)). Qed.
Lemma lem3243838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243839 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term399 A s t x) = (term413 A s t x).
Proof. exact (MK_COMB (@lem3243838) (@lem3243837 A s t x)). Qed.
Lemma lem3243840 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term401 A t s u x) = (term414 A t s u x).
Proof. exact (MK_COMB (@lem3243839 A s t x) (@lem3243814 A s u x)). Qed.
Lemma lem3243841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243842 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term404 A t s u x) = (term415 A t s u x).
Proof. exact (MK_COMB (@lem3243841) (@lem3243840 A t s u x)). Qed.
Lemma lem3243843 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term406 A t u s x) = (term416 A t u s x).
Proof. exact (MK_COMB (@lem3243842 A t s u x) (@lem3243791 A s x)). Qed.
Lemma lem3243844 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243849 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243850 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243849 A Prop f x). Qed.
Lemma lem3243852 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3243850 A s x). Qed.
Lemma lem3243853 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term342 A s x).
Proof. exact (MK_COMB (@lem3243844) (@lem3243852 A s x)). Qed.
Lemma lem3243858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243859 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243858 A Prop f x). Qed.
Lemma lem3243861 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3243859 A u x). Qed.
Lemma lem3243866 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243867 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243866 A Prop f x). Qed.
Lemma lem3243869 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3243867 A s x). Qed.
Lemma lem3243870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243871 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term343 A s x).
Proof. exact (MK_COMB (@lem3243870) (@lem3243869 A s x)). Qed.
Lemma lem3243872 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term145 A s u x) = (term344 A s u x).
Proof. exact (MK_COMB (@lem3243871 A s x) (@lem3243861 A u x)). Qed.
Lemma lem3243877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243878 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243877 A Prop f x). Qed.
Lemma lem3243880 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3243878 A t x). Qed.
Lemma lem3243885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243886 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243885 A Prop f x). Qed.
Lemma lem3243888 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3243886 A s x). Qed.
Lemma lem3243889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243890 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term343 A s x).
Proof. exact (MK_COMB (@lem3243889) (@lem3243888 A s x)). Qed.
Lemma lem3243891 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term145 A s t x) = (term344 A s t x).
Proof. exact (MK_COMB (@lem3243890 A s x) (@lem3243880 A t x)). Qed.
Lemma lem3243892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243893 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term364 A s t x) = (term417 A s t x).
Proof. exact (MK_COMB (@lem3243892) (@lem3243891 A s t x)). Qed.
Lemma lem3243894 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term365 A t s u x) = (term418 A t s u x).
Proof. exact (MK_COMB (@lem3243893 A s t x) (@lem3243872 A s u x)). Qed.
Lemma lem3243895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243896 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term419 A t s u x) = (term420 A t s u x).
Proof. exact (MK_COMB (@lem3243895) (@lem3243894 A t s u x)). Qed.
Lemma lem3243897 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term421 A t u s x) = (term422 A t u s x).
Proof. exact (MK_COMB (@lem3243896 A t s u x) (@lem3243853 A s x)). Qed.
Lemma lem3243898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3243899 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term407 A t u s x) = (term423 A t u s x).
Proof. exact (MK_COMB (@lem3243898) (@lem3243897 A t u s x)). Qed.
Lemma lem3243900 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) : (term409 A t u s x) = (term424 A t u s x).
Proof. exact (MK_COMB (@lem3243899 A t u s x) (@lem3243843 A t u s x)). Qed.
Lemma lem3243901 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term395 A t u s x) : term424 A t u s x.
Proof. exact (EQ_MP (@lem3243900 A t u s x) (@lem3243782 A t u s x h1)). Qed.
Lemma lem3243902 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3243909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243910 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3243909 (A -> Prop) (type672 A) f x). Qed.
Lemma lem3243911 {A : Type'} (t' : A -> Prop) : (@UNION A t') = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t').
Proof. exact (@lem3243910 A (@UNION A) t'). Qed.
Lemma lem3243912 {A : Type'} (u' : A -> Prop) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem3243913 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) : (@UNION A t' u') = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t' u').
Proof. exact (MK_COMB (@lem3243911 A t') (@lem3243912 A u')). Qed.
Lemma lem3243915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243916 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem3243915 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem3243917 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t' u') = (term425 A t' u').
Proof. exact (@lem3243916 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t') u'). Qed.
Lemma lem3243919 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) : (@UNION A t' u') = (term425 A t' u').
Proof. exact (TRANS (@lem3243913 A t' u') (@lem3243917 A t' u')). Qed.
Lemma lem3243920 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term426 A P t' u').
Proof. exact (MK_COMB (@lem3243902 A P) (@lem3243919 A t' u')). Qed.
Lemma lem3243922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243923 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3243922 (A -> Prop) Prop f x). Qed.
Lemma lem3243924 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term426 A P t' u') = (term427 A P t' u').
Proof. exact (@lem3243923 A P (term425 A t' u')). Qed.
Lemma lem3243925 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term93 A P t' u') = (term427 A P t' u').
Proof. exact (TRANS (@lem3243920 A P t' u') (@lem3243924 A P t' u')). Qed.
Lemma lem3243926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243927 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem3243934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243935 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3243934 (A -> Prop) (type684 A) f x). Qed.
Lemma lem3243936 {A : Type'} (x' : type638 A) (t' : A -> Prop) : (x' t') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t').
Proof. exact (@lem3243935 A x' t'). Qed.
Lemma lem3243937 {A : Type'} (u' : A -> Prop) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem3243938 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u').
Proof. exact (MK_COMB (@lem3243936 A x' t') (@lem3243937 A u')). Qed.
Lemma lem3243940 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243941 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3243940 (A -> Prop) A f x). Qed.
Lemma lem3243942 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u') = (term428 A x' t' u').
Proof. exact (@lem3243941 A (@I ((A -> Prop) -> (A -> Prop) -> A) x' t') u'). Qed.
Lemma lem3243944 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (term428 A x' t' u').
Proof. exact (TRANS (@lem3243938 A x' t' u') (@lem3243942 A x' t' u')). Qed.
Lemma lem3243945 {A : Type'} (u : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term429 A u x' t' u') = (term430 A u x' t' u').
Proof. exact (MK_COMB (@lem3243927 A u) (@lem3243944 A x' t' u')). Qed.
Lemma lem3243947 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243948 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243947 A Prop f x). Qed.
Lemma lem3243949 {A : Type'} (u : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term430 A u x' t' u') = (term431 A u x' t' u').
Proof. exact (@lem3243948 A u (term428 A x' t' u')). Qed.
Lemma lem3243950 {A : Type'} (u : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term429 A u x' t' u') = (term431 A u x' t' u').
Proof. exact (TRANS (@lem3243945 A u x' t' u') (@lem3243949 A u x' t' u')). Qed.
Lemma lem3243951 {A : Type'} (u : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term432 A u x' t' u') = (term433 A u x' t' u').
Proof. exact (MK_COMB (@lem3243926) (@lem3243950 A u x' t' u')). Qed.
Lemma lem3243952 {A : Type'} (u' : A -> Prop) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem3243959 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243960 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3243959 (A -> Prop) (type684 A) f x). Qed.
Lemma lem3243961 {A : Type'} (x' : type638 A) (t' : A -> Prop) : (x' t') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t').
Proof. exact (@lem3243960 A x' t'). Qed.
Lemma lem3243962 {A : Type'} (u' : A -> Prop) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem3243963 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u').
Proof. exact (MK_COMB (@lem3243961 A x' t') (@lem3243962 A u')). Qed.
Lemma lem3243965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243966 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3243965 (A -> Prop) A f x). Qed.
Lemma lem3243967 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u') = (term428 A x' t' u').
Proof. exact (@lem3243966 A (@I ((A -> Prop) -> (A -> Prop) -> A) x' t') u'). Qed.
Lemma lem3243969 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (term428 A x' t' u').
Proof. exact (TRANS (@lem3243963 A x' t' u') (@lem3243967 A x' t' u')). Qed.
Lemma lem3243970 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term434 A x' t' u') = (term435 A x' t' u').
Proof. exact (MK_COMB (@lem3243952 A u') (@lem3243969 A x' t' u')). Qed.
Lemma lem3243972 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243973 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3243972 A Prop f x). Qed.
Lemma lem3243974 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term435 A x' t' u') = (term436 A x' t' u').
Proof. exact (@lem3243973 A u' (term428 A x' t' u')). Qed.
Lemma lem3243975 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term434 A x' t' u') = (term436 A x' t' u').
Proof. exact (TRANS (@lem3243970 A x' t' u') (@lem3243974 A x' t' u')). Qed.
Lemma lem3243976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3243977 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term437 A x' t' u') = (term438 A x' t' u').
Proof. exact (MK_COMB (@lem3243976) (@lem3243975 A x' t' u')). Qed.
Lemma lem3243978 {A : Type'} (u : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term439 A u x' t' u') = (term440 A u x' t' u').
Proof. exact (MK_COMB (@lem3243977 A x' t' u') (@lem3243951 A u x' t' u')). Qed.
Lemma lem3243979 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3243980 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3243987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243988 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3243987 (A -> Prop) (type684 A) f x). Qed.
Lemma lem3243989 {A : Type'} (x' : type638 A) (t' : A -> Prop) : (x' t') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t').
Proof. exact (@lem3243988 A x' t'). Qed.
Lemma lem3243990 {A : Type'} (u' : A -> Prop) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem3243991 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u').
Proof. exact (MK_COMB (@lem3243989 A x' t') (@lem3243990 A u')). Qed.
Lemma lem3243993 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3243994 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3243993 (A -> Prop) A f x). Qed.
Lemma lem3243995 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u') = (term428 A x' t' u').
Proof. exact (@lem3243994 A (@I ((A -> Prop) -> (A -> Prop) -> A) x' t') u'). Qed.
Lemma lem3243997 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (term428 A x' t' u').
Proof. exact (TRANS (@lem3243991 A x' t' u') (@lem3243995 A x' t' u')). Qed.
Lemma lem3243998 {A : Type'} (t : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term429 A t x' t' u') = (term430 A t x' t' u').
Proof. exact (MK_COMB (@lem3243980 A t) (@lem3243997 A x' t' u')). Qed.
Lemma lem3244000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3244001 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3244000 A Prop f x). Qed.
Lemma lem3244002 {A : Type'} (t : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term430 A t x' t' u') = (term431 A t x' t' u').
Proof. exact (@lem3244001 A t (term428 A x' t' u')). Qed.
Lemma lem3244003 {A : Type'} (t : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term429 A t x' t' u') = (term431 A t x' t' u').
Proof. exact (TRANS (@lem3243998 A t x' t' u') (@lem3244002 A t x' t' u')). Qed.
Lemma lem3244004 {A : Type'} (t : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term432 A t x' t' u') = (term433 A t x' t' u').
Proof. exact (MK_COMB (@lem3243979) (@lem3244003 A t x' t' u')). Qed.
Lemma lem3244005 {A : Type'} (t' : A -> Prop) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem3244012 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3244013 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3244012 (A -> Prop) (type684 A) f x). Qed.
Lemma lem3244014 {A : Type'} (x' : type638 A) (t' : A -> Prop) : (x' t') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t').
Proof. exact (@lem3244013 A x' t'). Qed.
Lemma lem3244015 {A : Type'} (u' : A -> Prop) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem3244016 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u').
Proof. exact (MK_COMB (@lem3244014 A x' t') (@lem3244015 A u')). Qed.
Lemma lem3244018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3244019 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3244018 (A -> Prop) A f x). Qed.
Lemma lem3244020 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A) x' t' u') = (term428 A x' t' u').
Proof. exact (@lem3244019 A (@I ((A -> Prop) -> (A -> Prop) -> A) x' t') u'). Qed.
Lemma lem3244022 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (x' t' u') = (term428 A x' t' u').
Proof. exact (TRANS (@lem3244016 A x' t' u') (@lem3244020 A x' t' u')). Qed.
Lemma lem3244023 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term441 A x' t' u') = (term442 A x' t' u').
Proof. exact (MK_COMB (@lem3244005 A t') (@lem3244022 A x' t' u')). Qed.
Lemma lem3244025 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3244026 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3244025 A Prop f x). Qed.
Lemma lem3244027 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term442 A x' t' u') = (term443 A x' t' u').
Proof. exact (@lem3244026 A t' (term428 A x' t' u')). Qed.
Lemma lem3244028 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term441 A x' t' u') = (term443 A x' t' u').
Proof. exact (TRANS (@lem3244023 A x' t' u') (@lem3244027 A x' t' u')). Qed.
Lemma lem3244029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3244030 {A : Type'} (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term444 A x' t' u') = (term445 A x' t' u').
Proof. exact (MK_COMB (@lem3244029) (@lem3244028 A x' t' u')). Qed.
Lemma lem3244031 {A : Type'} (t : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term446 A t x' t' u') = (term447 A t x' t' u').
Proof. exact (MK_COMB (@lem3244030 A x' t' u') (@lem3244004 A t x' t' u')). Qed.
Lemma lem3244032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3244033 {A : Type'} (t : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term448 A t x' t' u') = (term449 A t x' t' u').
Proof. exact (MK_COMB (@lem3244032) (@lem3244031 A t x' t' u')). Qed.
Lemma lem3244034 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term450 A t u x' t' u') = (term451 A t u x' t' u').
Proof. exact (MK_COMB (@lem3244033 A t x' t' u') (@lem3243978 A u x' t' u')). Qed.
Lemma lem3244035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3244036 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (t' : A -> Prop) (u' : A -> Prop) : (term452 A t u x' t' u') = (term453 A t u x' t' u').
Proof. exact (MK_COMB (@lem3244035) (@lem3244034 A t u x' t' u')). Qed.
Lemma lem3244037 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term454 A t u x' P t' u') = (term455 A t u x' P t' u').
Proof. exact (MK_COMB (@lem3244036 A t u x' t' u') (@lem3243925 A P t' u')). Qed.
Lemma lem3244038 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (t' : A -> Prop) : (term456 A t u x' P t') = (term457 A t u x' P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3244037 A t u x' P t' u')). Qed.
Lemma lem3244039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3244040 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (t' : A -> Prop) : (term289 A t u x' P t') = (term458 A t u x' P t').
Proof. exact (MK_COMB (@lem3244039 A) (@lem3244038 A t u x' P t')). Qed.
Lemma lem3244041 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) : (term291 A t u x' P) = (term459 A t u x' P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3244040 A t u x' P t')). Qed.
Lemma lem3244042 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3244043 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) : (term293 A t u x' P) = (term460 A t u x' P).
Proof. exact (MK_COMB (@lem3244042 A) (@lem3244041 A t u x' P)). Qed.
Lemma lem3244048 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3244049 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3244048 A Prop f x). Qed.
Lemma lem3244051 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem3244049 A u x). Qed.
Lemma lem3244056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3244057 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3244056 A Prop f x). Qed.
Lemma lem3244059 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3244057 A t x). Qed.
Lemma lem3244060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3244061 {A : Type'} (t : A -> Prop) (x : A) : (term34 A t x) = (term461 A t x).
Proof. exact (MK_COMB (@lem3244060) (@lem3244059 A t x)). Qed.
Lemma lem3244062 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term35 A t u x) = (term462 A t u x).
Proof. exact (MK_COMB (@lem3244061 A t x) (@lem3244051 A u x)). Qed.
Lemma lem3244063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3244068 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3244069 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3244068 A Prop f x). Qed.
Lemma lem3244071 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3244069 A s x). Qed.
Lemma lem3244072 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (term342 A s x).
Proof. exact (MK_COMB (@lem3244063) (@lem3244071 A s x)). Qed.
Lemma lem3244073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3244074 {A : Type'} (s : A -> Prop) (x : A) : (term410 A s x) = (term411 A s x).
Proof. exact (MK_COMB (@lem3244073) (@lem3244072 A s x)). Qed.
Lemma lem3244075 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term180 A s t u x) = (term463 A s t u x).
Proof. exact (MK_COMB (@lem3244074 A s x) (@lem3244062 A t u x)). Qed.
Lemma lem3244076 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term181 A s t u) = (term464 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3244075 A s t u x)). Qed.
Lemma lem3244077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3244078 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term182 A s t u) = (term465 A s t u).
Proof. exact (MK_COMB (@lem3244077 A) (@lem3244076 A s t u)). Qed.
Lemma lem3244079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3244080 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term207 A s t u) = (term466 A s t u).
Proof. exact (MK_COMB (@lem3244079) (@lem3244078 A s t u)). Qed.
Lemma lem3244081 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) : (term310 A s t u x' P) = (term467 A s t u x' P).
Proof. exact (MK_COMB (@lem3244080 A s t u) (@lem3244043 A t u x' P)). Qed.
Lemma lem3244082 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term467 A s t u x' P.
Proof. exact (EQ_MP (@lem3244081 A s t u x' P) (@lem3243783 A s t u x' P h1)). Qed.
Lemma lem3244084 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term465 A s t u.
Proof. exact (proj1 (@lem3244082 A s t u x' P h1)). Qed.
Lemma lem3244085 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term422 A t u s x) : term422 A t u s x.
Proof. exact (h1). Qed.
Lemma lem3244086 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term416 A t u s x.
Proof. exact (h1). Qed.
Lemma lem3244088 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term422 A t u s x) : term418 A t s u x.
Proof. exact (proj1 (@lem3244085 A t u s x h1)). Qed.
Lemma lem3244089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term344 A s t x.
Proof. exact (h1). Qed.
Lemma lem3244090 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term344 A s u x) : term344 A s u x.
Proof. exact (h1). Qed.
Lemma lem3244096 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term414 A t s u x.
Proof. exact (proj1 (@lem3244086 A t u s x h1)). Qed.
Lemma lem3244097 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term412 A s u x.
Proof. exact (proj2 (@lem3244096 A t u s x h1)). Qed.
Lemma lem3244098 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term412 A s t x.
Proof. exact (proj1 (@lem3244096 A t u s x h1)). Qed.
Lemma lem3244391 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3244395 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3244488 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3244589 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3244603 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term463 A s t u x) = (term463 A s t u x).
Proof. exact (eq_refl (term463 A s t u x)). Qed.
Lemma lem3244604 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term464 A s t u) = (term464 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3244603 A s t u x)). Qed.
Lemma lem3244605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3244607 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term465 A s t u) = (term465 A s t u).
Proof. exact (MK_COMB (@lem3244605 A) (@lem3244604 A s t u)). Qed.
Lemma lem3244608 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term465 A s t u.
Proof. exact (EQ_MP (@lem3244607 A s t u) (@lem3244084 A s t u x' P h1)). Qed.
Lemma lem3244682 {A : Type'} (u : A -> Prop) (x : A) (h1 : term342 A u x) : term342 A u x.
Proof. exact (h1). Qed.
Lemma lem3244686 {A : Type'} (t : A -> Prop) (x : A) (h1 : term342 A t x) : term342 A t x.
Proof. exact (h1). Qed.
Lemma lem3244732 {A : Type'} (_33244 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term468 A s t u _33244.
Proof. exact (@lem3244608 A s t u x' P h1 _33244). Qed.
Lemma lem3244733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (_33244 : A) : (term468 A s t u _33244) = (term463 A s t u _33244).
Proof. exact (eq_refl (term468 A s t u _33244)). Qed.
Lemma lem3244788 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term422 A t u s x) : term342 A s x.
Proof. exact (proj2 (@lem3244085 A t u s x h1)). Qed.
Lemma lem3244852 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term422 A t u s x) : term342 A s x.
Proof. exact (proj2 (@lem3244085 A t u s x h1)). Qed.
Lemma lem3244918 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3244920 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3244982 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3245048 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term342 A s x.
Proof. exact (h1). Qed.
Lemma lem3245106 {A : Type'} (_33244 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term463 A s t u _33244.
Proof. exact (EQ_MP (@lem3244733 A s t u _33244) (@lem3244732 A _33244 s t u x' P h1)). Qed.
Lemma lem3245110 {A : Type'} (u : A -> Prop) (x : A) (h1 : term342 A u x) : term342 A u x.
Proof. exact (h1). Qed.
Lemma lem3245112 {A : Type'} (t : A -> Prop) (x : A) (h1 : term342 A t x) : term342 A t x.
Proof. exact (h1). Qed.
Lemma lem3245162 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3244089 A s t x h1)). Qed.
Lemma lem3245163 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term350 A s x.
Proof. exact (fun h0 : term342 A s x => @lem3245162 A s t x h1). Qed.
Lemma lem3245165 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245166 {A : Type'} (s : A -> Prop) (x : A) : (term350 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3245165 (@I (A -> Prop) s x)). Qed.
Lemma lem3245167 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3245166 A s x) (@lem3245163 A s t x h1)). Qed.
Lemma lem3245170 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3245172 {A : Type'} (s : A -> Prop) (x : A) : (term342 A s x) = (term351 A s x).
Proof. exact (@lem3245170 (@I (A -> Prop) s x)). Qed.
Lemma lem3245175 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term422 A t u s x) : term351 A s x.
Proof. exact (EQ_MP (@lem3245172 A s x) (@lem3244788 A t u s x h1)). Qed.
Lemma lem3245178 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s t x) (h2 : term422 A t u s x) : False.
Proof. exact (@lem3245175 A t u s x h2 (@lem3245167 A s t x h1)). Qed.
Lemma lem3245179 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s t x) (h2 : term422 A t u s x) : term88.
Proof. exact (fun h0 : ~ False => @lem3245178 A t u s x h1 h2). Qed.
Lemma lem3245181 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245182 : term88 = False.
Proof. exact (@lem3245181 False). Qed.
Lemma lem3245183 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s t x) (h2 : term422 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245182) (@lem3245179 A t u s x h1 h2)). Qed.
Lemma lem3245185 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term344 A s u x) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem3244090 A s u x h1)). Qed.
Lemma lem3245186 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term344 A s u x) : term350 A s x.
Proof. exact (fun h0 : term342 A s x => @lem3245185 A s u x h1). Qed.
Lemma lem3245188 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245189 {A : Type'} (s : A -> Prop) (x : A) : (term350 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3245188 (@I (A -> Prop) s x)). Qed.
Lemma lem3245190 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term344 A s u x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3245189 A s x) (@lem3245186 A s u x h1)). Qed.
Lemma lem3245193 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3245195 {A : Type'} (s : A -> Prop) (x : A) : (term342 A s x) = (term351 A s x).
Proof. exact (@lem3245193 (@I (A -> Prop) s x)). Qed.
Lemma lem3245198 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term422 A t u s x) : term351 A s x.
Proof. exact (EQ_MP (@lem3245195 A s x) (@lem3244852 A t u s x h1)). Qed.
Lemma lem3245201 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s u x) (h2 : term422 A t u s x) : False.
Proof. exact (@lem3245198 A t u s x h2 (@lem3245190 A s u x h1)). Qed.
Lemma lem3245202 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s u x) (h2 : term422 A t u s x) : term88.
Proof. exact (fun h0 : ~ False => @lem3245201 A t u s x h1 h2). Qed.
Lemma lem3245204 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245205 : term88 = False.
Proof. exact (@lem3245204 False). Qed.
Lemma lem3245206 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term344 A s u x) (h2 : term422 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245205) (@lem3245202 A t u s x h1 h2)). Qed.
Lemma lem3245208 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3244086 A t u s x h1)). Qed.
Lemma lem3245209 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term350 A s x.
Proof. exact (fun h0 : term342 A s x => @lem3245208 A t u s x h1). Qed.
Lemma lem3245211 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245212 {A : Type'} (s : A -> Prop) (x : A) : (term350 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3245211 (@I (A -> Prop) s x)). Qed.
Lemma lem3245213 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3245212 A s x) (@lem3245209 A t u s x h1)). Qed.
Lemma lem3245216 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3245218 {A : Type'} (s : A -> Prop) (x : A) : (term342 A s x) = (term351 A s x).
Proof. exact (@lem3245216 (@I (A -> Prop) s x)). Qed.
Lemma lem3245221 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term351 A s x.
Proof. exact (EQ_MP (@lem3245218 A s x) (@lem3244918 A s x h1)). Qed.
Lemma lem3245224 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (@lem3245221 A s x h1 (@lem3245213 A t u s x h2)). Qed.
Lemma lem3245225 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : term88.
Proof. exact (fun h0 : ~ False => @lem3245224 A t u s x h1 h2). Qed.
Lemma lem3245227 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245228 : term88 = False.
Proof. exact (@lem3245227 False). Qed.
Lemma lem3245229 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245228) (@lem3245225 A t u s x h1 h2)). Qed.
Lemma lem3245231 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3244086 A t u s x h1)). Qed.
Lemma lem3245232 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term350 A s x.
Proof. exact (fun h0 : term342 A s x => @lem3245231 A t u s x h1). Qed.
Lemma lem3245234 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245235 {A : Type'} (s : A -> Prop) (x : A) : (term350 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3245234 (@I (A -> Prop) s x)). Qed.
Lemma lem3245236 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3245235 A s x) (@lem3245232 A t u s x h1)). Qed.
Lemma lem3245239 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3245241 {A : Type'} (s : A -> Prop) (x : A) : (term342 A s x) = (term351 A s x).
Proof. exact (@lem3245239 (@I (A -> Prop) s x)). Qed.
Lemma lem3245244 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term351 A s x.
Proof. exact (EQ_MP (@lem3245241 A s x) (@lem3244982 A s x h1)). Qed.
Lemma lem3245247 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (@lem3245244 A s x h1 (@lem3245236 A t u s x h2)). Qed.
Lemma lem3245248 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : term88.
Proof. exact (fun h0 : ~ False => @lem3245247 A t u s x h1 h2). Qed.
Lemma lem3245250 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245251 : term88 = False.
Proof. exact (@lem3245250 False). Qed.
Lemma lem3245252 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245251) (@lem3245248 A t u s x h1 h2)). Qed.
Lemma lem3245254 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3244086 A t u s x h1)). Qed.
Lemma lem3245255 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term350 A s x.
Proof. exact (fun h0 : term342 A s x => @lem3245254 A t u s x h1). Qed.
Lemma lem3245257 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245258 {A : Type'} (s : A -> Prop) (x : A) : (term350 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3245257 (@I (A -> Prop) s x)). Qed.
Lemma lem3245259 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3245258 A s x) (@lem3245255 A t u s x h1)). Qed.
Lemma lem3245262 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3245264 {A : Type'} (s : A -> Prop) (x : A) : (term342 A s x) = (term351 A s x).
Proof. exact (@lem3245262 (@I (A -> Prop) s x)). Qed.
Lemma lem3245267 {A : Type'} (s : A -> Prop) (x : A) (h1 : term342 A s x) : term351 A s x.
Proof. exact (EQ_MP (@lem3245264 A s x) (@lem3245048 A s x h1)). Qed.
Lemma lem3245270 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (@lem3245267 A s x h1 (@lem3245259 A t u s x h2)). Qed.
Lemma lem3245271 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : term88.
Proof. exact (fun h0 : ~ False => @lem3245270 A t u s x h1 h2). Qed.
Lemma lem3245273 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245274 : term88 = False.
Proof. exact (@lem3245273 False). Qed.
Lemma lem3245275 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245274) (@lem3245271 A t u s x h1 h2)). Qed.
Lemma lem3245277 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3244086 A t u s x h1)). Qed.
Lemma lem3245278 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : term350 A s x.
Proof. exact (fun h0 : term342 A s x => @lem3245277 A t u s x h1). Qed.
Lemma lem3245280 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245281 {A : Type'} (s : A -> Prop) (x : A) : (term350 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3245280 (@I (A -> Prop) s x)). Qed.
Lemma lem3245282 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term416 A t u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3245281 A s x) (@lem3245278 A t u s x h1)). Qed.
Lemma lem3245284 {A : Type'} (u : A -> Prop) (x : A) (h1 : term342 A u x) : term342 A u x.
Proof. exact (h1). Qed.
Lemma lem3245285 {A : Type'} (u : A -> Prop) (x : A) (h1 : term342 A u x) : term469 A u x.
Proof. exact (fun h0 : @I (A -> Prop) u x => @lem3245284 A u x h1). Qed.
Lemma lem3245287 (p : Prop) : (term470 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3245288 {A : Type'} (u : A -> Prop) (x : A) : (term469 A u x) = (term342 A u x).
Proof. exact (@lem3245287 (@I (A -> Prop) u x)). Qed.
Lemma lem3245289 {A : Type'} (u : A -> Prop) (x : A) (h1 : term342 A u x) : term342 A u x.
Proof. exact (EQ_MP (@lem3245288 A u x) (@lem3245285 A u x h1)). Qed.
Lemma lem3245295 (q : Prop) (p : Prop) (r : Prop) : (term471 p q r) = (term471 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3245296 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (_33244 : A) : (term463 A s t u _33244) = (term472 A t s u _33244).
Proof. exact (@lem3245295 (@I (A -> Prop) t _33244) (term342 A s _33244) (@I (A -> Prop) u _33244)). Qed.
Lemma lem3245310 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3245311 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33244 : A) : (term473 A s u _33244) = (term474 A u s _33244).
Proof. exact (@lem3245310 (@I (A -> Prop) u _33244) (term342 A s _33244)). Qed.
Lemma lem3245317 {A : Type'} (t : A -> Prop) (_33244 : A) : (term461 A t _33244) = (term461 A t _33244).
Proof. exact (eq_refl (term461 A t _33244)). Qed.
Lemma lem3245318 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (_33244 : A) : (term472 A t s u _33244) = (term475 A t u s _33244).
Proof. exact (MK_COMB (@lem3245317 A t _33244) (@lem3245311 A u s _33244)). Qed.
Lemma lem3245329 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (_33244 : A) : (term463 A s t u _33244) = (term475 A t u s _33244).
Proof. exact (TRANS (@lem3245296 A t s u _33244) (@lem3245318 A t u s _33244)). Qed.
Lemma lem3245330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3245331 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (_33244 : A) : (term476 A s t u _33244) = (term477 A t u s _33244).
Proof. exact (MK_COMB (@lem3245330) (@lem3245329 A t u s _33244)). Qed.
Lemma lem3245345 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3245346 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33244 : A) : (term473 A s u _33244) = (term474 A u s _33244).
Proof. exact (@lem3245345 (@I (A -> Prop) u _33244) (term342 A s _33244)). Qed.
Lemma lem3245352 {A : Type'} (t : A -> Prop) (_33244 : A) : (term461 A t _33244) = (term461 A t _33244).
Proof. exact (eq_refl (term461 A t _33244)). Qed.
Lemma lem3245353 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (_33244 : A) : (term472 A t s u _33244) = (term475 A t u s _33244).
Proof. exact (MK_COMB (@lem3245352 A t _33244) (@lem3245346 A u s _33244)). Qed.
Lemma lem3245364 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (_33244 : A) : ((term463 A s t u _33244) = (term472 A t s u _33244)) = ((term475 A t u s _33244) = (term475 A t u s _33244)).
Proof. exact (MK_COMB (@lem3245331 A t u s _33244) (@lem3245353 A t u s _33244)). Qed.
Lemma lem3245366 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3245367 (x : Prop) : (x = x) = True.
Proof. exact (@lem3245366 Prop x). Qed.
Lemma lem3245368 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (_33244 : A) : ((term475 A t u s _33244) = (term475 A t u s _33244)) = True.
Proof. exact (@lem3245367 (term475 A t u s _33244)). Qed.
Lemma lem3245369 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (_33244 : A) : ((term463 A s t u _33244) = (term472 A t s u _33244)) = True.
Proof. exact (TRANS (@lem3245364 A t u s _33244) (@lem3245368 A t u s _33244)). Qed.
Lemma lem3245370 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (_33244 : A) : True = ((term463 A s t u _33244) = (term472 A t s u _33244)).
Proof. exact (SYM (@lem3245369 A t s u _33244)). Qed.
Lemma lem3245371 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (_33244 : A) : (term463 A s t u _33244) = (term472 A t s u _33244).
Proof. exact (EQ_MP (@lem3245370 A t s u _33244) (@lem0)). Qed.
Lemma lem3245372 {A : Type'} (_33244 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term472 A t s u _33244.
Proof. exact (EQ_MP (@lem3245371 A t s u _33244) (@lem3245106 A _33244 s t u x' P h1)). Qed.
Lemma lem3245374 (b : Prop) (a : Prop) : (a \/ b) = (term83 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3245375 {A : Type'} (s : A -> Prop) (u : A -> Prop) (t : A -> Prop) (_33244 : A) : (term472 A t s u _33244) = (term478 A s u t _33244).
Proof. exact (@lem3245374 (term473 A s u _33244) (@I (A -> Prop) t _33244)). Qed.
Lemma lem3245377 (a : Prop) (b : Prop) : (term479 a b) = (term480 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3245378 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33244 : A) : (term481 A s u _33244) = (term482 A s u _33244).
Proof. exact (@lem3245377 (term342 A s _33244) (@I (A -> Prop) u _33244)). Qed.
Lemma lem3245380 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3245381 {A : Type'} (s : A -> Prop) (_33244 : A) : (term483 A s _33244) = (@I (A -> Prop) s _33244).
Proof. exact (@lem3245380 (@I (A -> Prop) s _33244)). Qed.
Lemma lem3245382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3245383 {A : Type'} (s : A -> Prop) (_33244 : A) : (term484 A s _33244) = (term343 A s _33244).
Proof. exact (MK_COMB (@lem3245382) (@lem3245381 A s _33244)). Qed.
Lemma lem3245384 {A : Type'} (u : A -> Prop) (_33244 : A) : (term342 A u _33244) = (term342 A u _33244).
Proof. exact (eq_refl (term342 A u _33244)). Qed.
Lemma lem3245385 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33244 : A) : (term482 A s u _33244) = (term485 A s u _33244).
Proof. exact (MK_COMB (@lem3245383 A s _33244) (@lem3245384 A u _33244)). Qed.
Lemma lem3245386 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33244 : A) : (term481 A s u _33244) = (term485 A s u _33244).
Proof. exact (TRANS (@lem3245378 A s u _33244) (@lem3245385 A s u _33244)). Qed.
Lemma lem3245387 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3245388 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33244 : A) : (term486 A s u _33244) = (term487 A s u _33244).
Proof. exact (MK_COMB (@lem3245387) (@lem3245386 A s u _33244)). Qed.
Lemma lem3245389 {A : Type'} (t : A -> Prop) (_33244 : A) : (@I (A -> Prop) t _33244) = (@I (A -> Prop) t _33244).
Proof. exact (eq_refl (@I (A -> Prop) t _33244)). Qed.
Lemma lem3245390 {A : Type'} (s : A -> Prop) (u : A -> Prop) (t : A -> Prop) (_33244 : A) : (term478 A s u t _33244) = (term488 A s u t _33244).
Proof. exact (MK_COMB (@lem3245388 A s u _33244) (@lem3245389 A t _33244)). Qed.
Lemma lem3245391 {A : Type'} (s : A -> Prop) (u : A -> Prop) (t : A -> Prop) (_33244 : A) : (term472 A t s u _33244) = (term488 A s u t _33244).
Proof. exact (TRANS (@lem3245375 A s u t _33244) (@lem3245390 A s u t _33244)). Qed.
Lemma lem3245393 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A u x) (h2 : term416 A t u s x) : term485 A s u x.
Proof. exact (conj (@lem3245282 A t u s x h2) (@lem3245289 A u x h1)). Qed.
Lemma lem3245395 {A : Type'} (_33244 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term488 A s u t _33244.
Proof. exact (EQ_MP (@lem3245391 A s u t _33244) (@lem3245372 A _33244 s t u x' P h1)). Qed.
Lemma lem3245396 {A : Type'} (_33244 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term488 A s u t _33244.
Proof. exact (@lem3245395 A _33244 s t u x' P h1). Qed.
Lemma lem3245397 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term310 A s t u x' P) : term488 A s u t x.
Proof. exact (@lem3245396 A x s t u x' P h1). Qed.
Lemma lem3245400 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A u x) (h2 : term310 A s t u x' P) (h3 : term416 A t u s x) : @I (A -> Prop) t x.
Proof. exact (@lem3245397 A x s t u x' P h2 (@lem3245393 A t u s x h1 h3)). Qed.
Lemma lem3245401 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A u x) (h2 : term310 A s t u x' P) (h3 : term416 A t u s x) : term350 A t x.
Proof. exact (fun h0 : term342 A t x => @lem3245400 A x' P t u s x h1 h2 h3). Qed.
Lemma lem3245403 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245404 {A : Type'} (t : A -> Prop) (x : A) : (term350 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3245403 (@I (A -> Prop) t x)). Qed.
Lemma lem3245405 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A u x) (h2 : term310 A s t u x' P) (h3 : term416 A t u s x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3245404 A t x) (@lem3245401 A x' P t u s x h1 h2 h3)). Qed.
Lemma lem3245408 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3245410 {A : Type'} (t : A -> Prop) (x : A) : (term342 A t x) = (term351 A t x).
Proof. exact (@lem3245408 (@I (A -> Prop) t x)). Qed.
Lemma lem3245413 {A : Type'} (t : A -> Prop) (x : A) (h1 : term342 A t x) : term351 A t x.
Proof. exact (EQ_MP (@lem3245410 A t x) (@lem3245112 A t x h1)). Qed.
Lemma lem3245416 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (@lem3245413 A t x h1 (@lem3245405 A x' P t u s x h2 h3 h4)). Qed.
Lemma lem3245417 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : term88.
Proof. exact (fun h0 : ~ False => @lem3245416 A x' P t u s x h1 h2 h3 h4). Qed.
Lemma lem3245419 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3245420 : term88 = False.
Proof. exact (@lem3245419 False). Qed.
Lemma lem3245421 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245420) (@lem3245417 A x' P t u s x h1 h2 h3 h4)). Qed.
Lemma lem3245422 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : (term342 A t x) = False.
Proof. exact (prop_ext (fun h5 : term342 A t x => @lem3245421 A x' P t u s x h1 h2 h3 h4) (fun h5 : False => @lem3245112 A t x h1)). Qed.
Lemma lem3245423 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245422 A x' P t u s x h1 h2 h3 h4) (@lem3245112 A t x h1)). Qed.
Lemma lem3245424 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : (term342 A u x) = False.
Proof. exact (prop_ext (fun h5 : term342 A u x => @lem3245423 A x' P t u s x h1 h2 h3 h4) (fun h5 : False => @lem3245110 A u x h2)). Qed.
Lemma lem3245425 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245424 A x' P t u s x h1 h2 h3 h4) (@lem3245110 A u x h2)). Qed.
Lemma lem3245426 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245275 A t u s x h1 h2) (fun h3 : False => @lem3245048 A s x h1)). Qed.
Lemma lem3245427 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245426 A t u s x h1 h2) (@lem3245048 A s x h1)). Qed.
Lemma lem3245428 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245252 A t u s x h1 h2) (fun h3 : False => @lem3244982 A s x h1)). Qed.
Lemma lem3245429 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245428 A t u s x h1 h2) (@lem3244982 A s x h1)). Qed.
Lemma lem3245430 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245229 A t u s x h1 h2) (fun h3 : False => @lem3244920 A s x h1)). Qed.
Lemma lem3245431 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245430 A t u s x h1 h2) (@lem3244920 A s x h1)). Qed.
Lemma lem3245432 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245431 A t u s x h1 h2) (fun h3 : False => @lem3244918 A s x h1)). Qed.
Lemma lem3245433 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245432 A t u s x h1 h2) (@lem3244918 A s x h1)). Qed.
Lemma lem3245434 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : (term342 A t x) = False.
Proof. exact (prop_ext (fun h5 : term342 A t x => @lem3245425 A x' P t u s x h1 h2 h3 h4) (fun h5 : False => @lem3244686 A t x h1)). Qed.
Lemma lem3245435 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245434 A x' P t u s x h1 h2 h3 h4) (@lem3244686 A t x h1)). Qed.
Lemma lem3245436 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : (term342 A u x) = False.
Proof. exact (prop_ext (fun h5 : term342 A u x => @lem3245435 A x' P t u s x h1 h2 h3 h4) (fun h5 : False => @lem3244682 A u x h2)). Qed.
Lemma lem3245437 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245436 A x' P t u s x h1 h2 h3 h4) (@lem3244682 A u x h2)). Qed.
Lemma lem3245438 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245427 A t u s x h1 h2) (fun h3 : False => @lem3244589 A s x h1)). Qed.
Lemma lem3245439 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245438 A t u s x h1 h2) (@lem3244589 A s x h1)). Qed.
Lemma lem3245440 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245429 A t u s x h1 h2) (fun h3 : False => @lem3244488 A s x h1)). Qed.
Lemma lem3245441 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245440 A t u s x h1 h2) (@lem3244488 A s x h1)). Qed.
Lemma lem3245442 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245433 A t u s x h1 h2) (fun h3 : False => @lem3244395 A s x h1)). Qed.
Lemma lem3245443 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245442 A t u s x h1 h2) (@lem3244395 A s x h1)). Qed.
Lemma lem3245444 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245443 A t u s x h1 h2) (fun h3 : False => @lem3244391 A s x h1)). Qed.
Lemma lem3245445 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245444 A t u s x h1 h2) (@lem3244391 A s x h1)). Qed.
Lemma lem3245446 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : (term342 A t x) = False.
Proof. exact (prop_ext (fun h5 : term342 A t x => @lem3245437 A x' P t u s x h1 h2 h3 h4) (fun h5 : False => @lem3244686 A t x h1)). Qed.
Lemma lem3245447 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245446 A x' P t u s x h1 h2 h3 h4) (@lem3244686 A t x h1)). Qed.
Lemma lem3245448 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : (term342 A u x) = False.
Proof. exact (prop_ext (fun h5 : term342 A u x => @lem3245447 A x' P t u s x h1 h2 h3 h4) (fun h5 : False => @lem3244682 A u x h2)). Qed.
Lemma lem3245449 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A t x) (h2 : term342 A u x) (h3 : term310 A s t u x' P) (h4 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245448 A x' P t u s x h1 h2 h3 h4) (@lem3244682 A u x h2)). Qed.
Lemma lem3245450 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245439 A t u s x h1 h2) (fun h3 : False => @lem3244589 A s x h1)). Qed.
Lemma lem3245451 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245450 A t u s x h1 h2) (@lem3244589 A s x h1)). Qed.
Lemma lem3245452 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245441 A t u s x h1 h2) (fun h3 : False => @lem3244488 A s x h1)). Qed.
Lemma lem3245453 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245452 A t u s x h1 h2) (@lem3244488 A s x h1)). Qed.
Lemma lem3245454 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245445 A t u s x h1 h2) (fun h3 : False => @lem3244395 A s x h1)). Qed.
Lemma lem3245455 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245454 A t u s x h1 h2) (@lem3244395 A s x h1)). Qed.
Lemma lem3245456 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : (term342 A s x) = False.
Proof. exact (prop_ext (fun h3 : term342 A s x => @lem3245455 A t u s x h1 h2) (fun h3 : False => @lem3244391 A s x h1)). Qed.
Lemma lem3245457 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (EQ_MP (@lem3245456 A t u s x h1 h2) (@lem3244391 A s x h1)). Qed.
Lemma lem3245458 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A u x) (h2 : term310 A s t u x' P) (h3 : term416 A t u s x) : False.
Proof. exact (or_elim (@lem3244098 A t u s x h3) (fun h0 : term342 A s x => @lem3245451 A t u s x h0 h3) (fun h0 : term342 A t x => @lem3245449 A x' P t u s x h0 h1 h2 h3)). Qed.
Lemma lem3245459 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term342 A s x) (h2 : term416 A t u s x) : False.
Proof. exact (or_elim (@lem3244098 A t u s x h2) (fun h0 : term342 A s x => @lem3245457 A t u s x h1 h2) (fun h0 : term342 A t x => @lem3245453 A t u s x h1 h2)). Qed.
Lemma lem3245460 {A : Type'} (x' : type638 A) (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term310 A s t u x' P) (h2 : term416 A t u s x) : False.
Proof. exact (or_elim (@lem3244097 A t u s x h2) (fun h0 : term342 A s x => @lem3245459 A t u s x h0 h2) (fun h0 : term342 A u x => @lem3245458 A x' P t u s x h0 h1 h2)). Qed.
Lemma lem3245461 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (x : A) (h1 : term422 A t u s x) : False.
Proof. exact (or_elim (@lem3244088 A t u s x h1) (fun h0 : term344 A s t x => @lem3245183 A t u s x h0 h1) (fun h0 : term344 A s u x => @lem3245206 A t u s x h0 h1)). Qed.
Lemma lem3245462 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : type638 A) (P : type686 A) (h1 : term395 A t u s x) (h2 : term310 A s t u x' P) : False.
Proof. exact (or_elim (@lem3243901 A t u s x h1) (fun h0 : term422 A t u s x => @lem3245461 A t u s x h0) (fun h0 : term416 A t u s x => @lem3245460 A x' P t u s x h2 h0)). Qed.
Lemma lem3245463 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term395 A t u s x) (h2 : term139 A s t u P) : False.
Proof. exact (ex_elim (@lem3243732 A s t u P h2) (fun x' : type638 A => fun h0 : term312 A s t u P x' => @lem3245462 A x s t u x' P h1 h0)). Qed.
Lemma lem3245464 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term395 A t u s x) (h2 : term139 A s t u P) : (term395 A t u s x) = False.
Proof. exact (prop_ext (fun h3 : term395 A t u s x => @lem3245463 A x s t u P h1 h2) (fun h3 : False => @lem3243357 A t u s x h1)). Qed.
Lemma lem3245465 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term395 A t u s x) (h2 : term139 A s t u P) : False.
Proof. exact (EQ_MP (@lem3245464 A x s t u P h1 h2) (@lem3243357 A t u s x h1)). Qed.
Lemma lem3245466 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term394 A t u s x.
Proof. exact (fun h0 : term395 A t u s x => @lem3245465 A x s t u P h0 h1). Qed.
Lemma lem3245467 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : (term365 A t s u x) = (s x).
Proof. exact (EQ_MP (@lem3243356 A t u s x) (@lem3245466 A x s t u P h1)). Qed.
Lemma lem3245472 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term139 A s t u P) : term370 A t u s.
Proof. exact (fun x : A => @lem3245467 A x s t u P h1). Qed.
Lemma lem3245473 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term371 A P t u s.
Proof. exact (fun h0 : term139 A s t u P => @lem3245472 A s t u P h0). Qed.
Lemma lem3245478 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term381 A t u s.
Proof. exact (fun P : type686 A => @lem3245473 A P t u s). Qed.
Lemma lem3245483 {A : Type'} (u : A -> Prop) (s : A -> Prop) : term385 A u s.
Proof. exact (fun t : A -> Prop => @lem3245478 A t u s). Qed.
Lemma lem3245488 {A : Type'} (s : A -> Prop) : term389 A s.
Proof. exact (fun u : A -> Prop => @lem3245483 A u s). Qed.
Lemma lem3245493 {A : Type'} : term393 A.
Proof. exact (fun s : A -> Prop => @lem3245488 A s). Qed.
Lemma lem3245494 {A : Type'} : term392 A.
Proof. exact (EQ_MP (@lem3243351 A) (@lem3245493 A)). Qed.
Lemma lem3245495 {A : Type'} (s : A -> Prop) : term489 A s.
Proof. exact (@lem3245494 A s). Qed.
Lemma lem3245496 {A : Type'} (s : A -> Prop) : (term489 A s) = (term388 A s).
Proof. exact (eq_refl (term489 A s)). Qed.
Lemma lem3245497 {A : Type'} (s : A -> Prop) : term388 A s.
Proof. exact (EQ_MP (@lem3245496 A s) (@lem3245495 A s)). Qed.
Lemma lem3245498 {A : Type'} (s : A -> Prop) (u : A -> Prop) : term490 A s u.
Proof. exact (@lem3245497 A s u). Qed.
Lemma lem3245499 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term490 A s u) = (term384 A u s).
Proof. exact (eq_refl (term490 A s u)). Qed.
Lemma lem3245500 {A : Type'} (u : A -> Prop) (s : A -> Prop) : term384 A u s.
Proof. exact (EQ_MP (@lem3245499 A u s) (@lem3245498 A s u)). Qed.
Lemma lem3245501 {A : Type'} (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) : term491 A u s t.
Proof. exact (@lem3245500 A u s t). Qed.
Lemma lem3245502 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term491 A u s t) = (term380 A t u s).
Proof. exact (eq_refl (term491 A u s t)). Qed.
Lemma lem3245503 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term380 A t u s.
Proof. exact (EQ_MP (@lem3245502 A t u s) (@lem3245501 A u s t)). Qed.
Lemma lem3245504 {A : Type'} (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (P : type686 A) : term492 A t u s P.
Proof. exact (@lem3245503 A t u s P). Qed.
Lemma lem3245505 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : (term492 A t u s P) = (term372 A P t u s).
Proof. exact (eq_refl (term492 A t u s P)). Qed.
Lemma lem3245506 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term372 A P t u s.
Proof. exact (EQ_MP (@lem3245505 A P t u s) (@lem3245504 A t u s P)). Qed.
Lemma lem3245508 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term372 A P t u s.
Proof. exact (@lem3243085 A P t u s (@lem3245506 A P t u s)). Qed.
Lemma lem3245509 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term373 A P t u s) : False.
Proof. exact (@lem3245508 A P t u s (@lem3243069 A P t u s h1)). Qed.
Lemma lem3245510 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term373 A P t u s) : (term373 A P t u s) = False.
Proof. exact (prop_ext (fun h2 : term373 A P t u s => @lem3245509 A P t u s h1) (fun h2 : False => @lem3243069 A P t u s h1)). Qed.
Lemma lem3245511 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) (h1 : term373 A P t u s) : False.
Proof. exact (EQ_MP (@lem3245510 A P t u s h1) (@lem3243069 A P t u s h1)). Qed.
Lemma lem3245512 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term372 A P t u s.
Proof. exact (fun h0 : term373 A P t u s => @lem3245511 A P t u s h0). Qed.
Lemma lem3245513 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term371 A P t u s.
Proof. exact (EQ_MP (@lem3243068 A P t u s) (@lem3245512 A P t u s)). Qed.
Lemma lem3245514 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term360 A P t u s.
Proof. exact (EQ_MP (@lem3243064 A P t u s) (@lem3245513 A P t u s)). Qed.
Lemma lem3245515 {A : Type'} (P : type686 A) (t : A -> Prop) (u : A -> Prop) (s : A -> Prop) : term359 A P t u s.
Proof. exact (EQ_MP (@lem3242845 A P t u s) (@lem3245514 A P t u s)). Qed.
Lemma lem3245516 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : (term357 A t s u) = s.
Proof. exact (@lem3245515 A P t u s (@lem3242749 A P s t u h1 h2)). Qed.
Lemma lem3245517 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : (term105 A P t s u) = (P s).
Proof. exact (MK_COMB (@lem3240803 A P) (@lem3245516 A P s t u h1 h2)). Qed.
Lemma lem3245518 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : term493 A t u P s.
Proof. exact (@lem3240802 A t u P s (@lem3245517 A P s t u h1 h2)). Qed.
Lemma lem3245519 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : term494 A t u P s.
Proof. exact (conj (@lem3242738 A P s t u h1 h2) (@lem3245518 A P s t u h1 h2)). Qed.
Lemma lem3245520 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : term495 A t u P s.
Proof. exact (@lem3240799 A t u P s (@lem3245519 A P s t u h1 h2)). Qed.
Lemma lem3245521 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term96 A t u P) (h2 : term7 A s t u) : P s.
Proof. exact (@lem3245520 A P s t u h1 h2 (@lem3240796 A s t u P h1)). Qed.
Lemma lem3245522 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term96 A t u P) : term6 A t u P s.
Proof. exact (fun h0 : term7 A s t u => @lem3245521 A P s t u h1 h0). Qed.
Lemma lem3245527 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) (h1 : term96 A t u P) : term3 A t u P.
Proof. exact (fun s : A -> Prop => @lem3245522 A s t u P h1). Qed.
Lemma lem3245528 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : term496 A t u P.
Proof. exact (fun h0 : term96 A t u P => @lem3245527 A t u P h0). Qed.
Lemma lem3245529 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : term497 A t u P.
Proof. exact (conj (@lem3240788 A t u P) (@lem3245528 A t u P)). Qed.
Lemma lem3245530 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term497 A t u P) = ((term3 A t u P) = (term96 A t u P)).
Proof. exact (@lem32 (term3 A t u P) (term96 A t u P)). Qed.
Lemma lem3245531 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term3 A t u P) = (term96 A t u P).
Proof. exact (EQ_MP (@lem3245530 A t u P) (@lem3245529 A t u P)). Qed.
Lemma lem3245536 {A : Type'} (t : A -> Prop) (P : type686 A) : term498 A t P.
Proof. exact (fun u : A -> Prop => @lem3245531 A t u P). Qed.
Lemma lem3245541 {A : Type'} (P : type686 A) : term499 A P.
Proof. exact (fun t : A -> Prop => @lem3245536 A t P). Qed.
