Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_SUBSET_STRONG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3360781 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3360782 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3360781 A s t). Qed.
Lemma lem3360783 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term0 A t s).
Proof. exact (@lem3360782 A t s). Qed.
Lemma lem3360790 {A : Type'} (t : A -> Prop) (u : type686 A) : (term1 A t u) = (term1 A t u).
Proof. exact (eq_refl (term1 A t u)). Qed.
Lemma lem3360791 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term2 A u t s) = (term3 A u t s).
Proof. exact (MK_COMB (@lem3360790 A t u) (@lem3360783 A t s)). Qed.
Lemma lem3360794 {A : Type'} (u : type686 A) (s : A -> Prop) : (term4 A u s) = (term5 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360791 A u t s)). Qed.
Lemma lem3360795 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3360796 {A : Type'} (u : type686 A) (s : A -> Prop) : (term6 A u s) = (term7 A u s).
Proof. exact (MK_COMB (@lem3360795 A) (@lem3360794 A u s)). Qed.
Lemma lem3360801 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360802 {A : Type'} (u : type686 A) (s : A -> Prop) : (term8 A u s) = (term9 A u s).
Proof. exact (MK_COMB (@lem3360801) (@lem3360796 A u s)). Qed.
Lemma lem3360804 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3360805 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3360804 A s t). Qed.
Lemma lem3360806 {A : Type'} (u : type686 A) (s : A -> Prop) : (term10 A u s) = (term11 A u s).
Proof. exact (@lem3360805 A (@INTERS A u) s). Qed.
Lemma lem3360813 {A : Type'} (u : type686 A) (s : A -> Prop) : (term12 A u s) = (term13 A u s).
Proof. exact (MK_COMB (@lem3360802 A u s) (@lem3360806 A u s)). Qed.
Lemma lem3360816 {A : Type'} (u : type686 A) : (term14 A u) = (term15 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3360813 A u s)). Qed.
Lemma lem3360817 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360818 {A : Type'} (u : type686 A) : (term16 A u) = (term17 A u).
Proof. exact (MK_COMB (@lem3360817 A) (@lem3360816 A u)). Qed.
Lemma lem3360823 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (fun_ext (fun u : type686 A => @lem3360818 A u)). Qed.
Lemma lem3360824 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3360825 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem3360824 A) (@lem3360823 A)). Qed.
Lemma lem3360830 {A : Type'} : (term21 A) = (term20 A).
Proof. exact (SYM (@lem3360825 A)). Qed.
Lemma lem3360848 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3360849 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3360848 (A -> Prop) P x). Qed.
Lemma lem3360850 {A : Type'} (u : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t u) = (u t).
Proof. exact (@lem3360849 A u t). Qed.
Lemma lem3360851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3360852 {A : Type'} (u : type686 A) (t : A -> Prop) : (term1 A t u) = (term22 A u t).
Proof. exact (MK_COMB (@lem3360851) (@lem3360850 A u t)). Qed.
Lemma lem3360860 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3360861 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3360860 A P x). Qed.
Lemma lem3360862 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3360861 A t x). Qed.
Lemma lem3360863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360864 {A : Type'} (t : A -> Prop) (x : A) : (term23 A x t) = (term24 A t x).
Proof. exact (MK_COMB (@lem3360863) (@lem3360862 A t x)). Qed.
Lemma lem3360866 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3360867 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3360866 A P x). Qed.
Lemma lem3360868 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3360867 A s x). Qed.
Lemma lem3360869 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term25 A t x s) = (term26 A t s x).
Proof. exact (MK_COMB (@lem3360864 A t x) (@lem3360868 A s x)). Qed.
Lemma lem3360872 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term27 A t s) = (term28 A t s).
Proof. exact (fun_ext (fun x : A => @lem3360869 A t s x)). Qed.
Lemma lem3360873 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360874 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term0 A t s) = (term29 A t s).
Proof. exact (MK_COMB (@lem3360873 A) (@lem3360872 A t s)). Qed.
Lemma lem3360879 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term3 A u t s) = (term30 A u t s).
Proof. exact (MK_COMB (@lem3360852 A u t) (@lem3360874 A t s)). Qed.
Lemma lem3360882 {A : Type'} (u : type686 A) (s : A -> Prop) : (term5 A u s) = (term31 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360879 A u t s)). Qed.
Lemma lem3360883 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3360884 {A : Type'} (u : type686 A) (s : A -> Prop) : (term7 A u s) = (term32 A u s).
Proof. exact (MK_COMB (@lem3360883 A) (@lem3360882 A u s)). Qed.
Lemma lem3360889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360890 {A : Type'} (u : type686 A) (s : A -> Prop) : (term9 A u s) = (term33 A u s).
Proof. exact (MK_COMB (@lem3360889) (@lem3360884 A u s)). Qed.
Lemma lem3360898 {A : Type'} (s : type686 A) (x : A) : (term34 A x s) = (term35 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3360899 {A : Type'} (s : type686 A) (x : A) : (term34 A x s) = (term35 A s x).
Proof. exact (@lem3360898 A s x). Qed.
Lemma lem3360900 {A : Type'} (u : type686 A) (x : A) : (term34 A x u) = (term35 A u x).
Proof. exact (@lem3360899 A u x). Qed.
Lemma lem3360908 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3360909 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3360908 (A -> Prop) P x). Qed.
Lemma lem3360910 {A : Type'} (u : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t u) = (u t).
Proof. exact (@lem3360909 A u t). Qed.
Lemma lem3360911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360912 {A : Type'} (u : type686 A) (t : A -> Prop) : (term36 A t u) = (term37 A u t).
Proof. exact (MK_COMB (@lem3360911) (@lem3360910 A u t)). Qed.
Lemma lem3360914 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3360915 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3360914 A P x). Qed.
Lemma lem3360916 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3360915 A t x). Qed.
Lemma lem3360917 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term38 A u x t) = (term39 A u t x).
Proof. exact (MK_COMB (@lem3360912 A u t) (@lem3360916 A t x)). Qed.
Lemma lem3360920 {A : Type'} (u : type686 A) (x : A) : (term40 A u x) = (term41 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3360917 A u t x)). Qed.
Lemma lem3360921 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360922 {A : Type'} (u : type686 A) (x : A) : (term35 A u x) = (term42 A u x).
Proof. exact (MK_COMB (@lem3360921 A) (@lem3360920 A u x)). Qed.
Lemma lem3360927 {A : Type'} (u : type686 A) (x : A) : (term34 A x u) = (term42 A u x).
Proof. exact (TRANS (@lem3360900 A u x) (@lem3360922 A u x)). Qed.
Lemma lem3360928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3360929 {A : Type'} (u : type686 A) (x : A) : (term43 A x u) = (term44 A u x).
Proof. exact (MK_COMB (@lem3360928) (@lem3360927 A u x)). Qed.
Lemma lem3360931 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3360932 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3360931 A P x). Qed.
Lemma lem3360933 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3360932 A s x). Qed.
Lemma lem3360934 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) : (term45 A u x s) = (term46 A u s x).
Proof. exact (MK_COMB (@lem3360929 A u x) (@lem3360933 A s x)). Qed.
Lemma lem3360937 {A : Type'} (u : type686 A) (s : A -> Prop) : (term47 A u s) = (term48 A u s).
Proof. exact (fun_ext (fun x : A => @lem3360934 A u s x)). Qed.
Lemma lem3360938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3360939 {A : Type'} (u : type686 A) (s : A -> Prop) : (term11 A u s) = (term49 A u s).
Proof. exact (MK_COMB (@lem3360938 A) (@lem3360937 A u s)). Qed.
Lemma lem3360944 {A : Type'} (u : type686 A) (s : A -> Prop) : (term13 A u s) = (term50 A u s).
Proof. exact (MK_COMB (@lem3360890 A u s) (@lem3360939 A u s)). Qed.
Lemma lem3360947 {A : Type'} (u : type686 A) : (term15 A u) = (term51 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3360944 A u s)). Qed.
Lemma lem3360948 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3360949 {A : Type'} (u : type686 A) : (term17 A u) = (term52 A u).
Proof. exact (MK_COMB (@lem3360948 A) (@lem3360947 A u)). Qed.
Lemma lem3360954 {A : Type'} : (term19 A) = (term53 A).
Proof. exact (fun_ext (fun u : type686 A => @lem3360949 A u)). Qed.
Lemma lem3360955 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3360956 {A : Type'} : (term21 A) = (term54 A).
Proof. exact (MK_COMB (@lem3360955 A) (@lem3360954 A)). Qed.
Lemma lem3360961 {A : Type'} : (term54 A) = (term21 A).
Proof. exact (SYM (@lem3360956 A)). Qed.
Lemma lem3360963 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3360964 {A : Type'} : (term54 A) = (term56 A).
Proof. exact (@lem3360963 (term54 A)). Qed.
Lemma lem3360965 {A : Type'} : (term56 A) = (term54 A).
Proof. exact (SYM (@lem3360964 A)). Qed.
Lemma lem3360966 {A : Type'} (h1 : term57 A) : term57 A.
Proof. exact (h1). Qed.
Lemma lem3360969 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (h1). Qed.
Lemma lem3360970 {A : Type'} : term58 A.
Proof. exact (fun h0 : term56 A => @lem3360969 A h0). Qed.
Lemma lem3360971 {A : Type'} (h1 : term58 A) : term58 A.
Proof. exact (h1). Qed.
Lemma lem3360972 {A : Type'} (h1 : term56 A) : term56 A.
Proof. exact (h1). Qed.
Lemma lem3360973 {A : Type'} (h1 : term56 A) (h2 : term58 A) : term56 A.
Proof. exact (@lem3360971 A h2 (@lem3360972 A h1)). Qed.
Lemma lem3360974 {A : Type'} (h1 : term56 A) : term59 A.
Proof. exact (fun h0 : term58 A => @lem3360973 A h1 h0). Qed.
Lemma lem3360975 {A : Type'} (h1 : term58 A) : term58 A.
Proof. exact (h1). Qed.
Lemma lem3360976 {A : Type'} (h1 : term56 A) (h2 : term58 A) : term56 A.
Proof. exact (@lem3360974 A h1 (@lem3360975 A h2)). Qed.
Lemma lem3360977 {A : Type'} (h1 : term58 A) : term58 A.
Proof. exact (fun h0 : term56 A => @lem3360976 A h0 h1). Qed.
Lemma lem3360978 {A : Type'} : term60 A.
Proof. exact (fun h0 : term58 A => @lem3360977 A h0). Qed.
Lemma lem3360981 {A : Type'} : term58 A.
Proof. exact (@lem3360978 A (@lem3360970 A)). Qed.
Lemma lem3360982 {A : Type'} : term58 A.
Proof. exact (@lem3360981 A). Qed.
Lemma lem3360984 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3360985 {A : Type'} : (term56 A) = (term61 A).
Proof. exact (@lem3360984 (term57 A)). Qed.
Lemma lem3360987 (t : Prop) : (term62 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3360988 {A : Type'} : (term61 A) = (term54 A).
Proof. exact (@lem3360987 (term54 A)). Qed.
Lemma lem3361051 {A : Type'} : (term56 A) = (term54 A).
Proof. exact (TRANS (@lem3360985 A) (@lem3360988 A)). Qed.
Lemma lem3361052 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3361057 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term39 A u t x) = (term39 A u t x).
Proof. exact (eq_refl (term39 A u t x)). Qed.
Lemma lem3361058 {A : Type'} (u : type686 A) (x : A) : (term41 A u x) = (term41 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3361057 A u t x)). Qed.
Lemma lem3361059 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3361060 {A : Type'} (u : type686 A) (x : A) : (term42 A u x) = (term42 A u x).
Proof. exact (MK_COMB (@lem3361059 A) (@lem3361058 A u x)). Qed.
Lemma lem3361061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361062 {A : Type'} (u : type686 A) (x : A) : (term44 A u x) = (term44 A u x).
Proof. exact (MK_COMB (@lem3361061) (@lem3361060 A u x)). Qed.
Lemma lem3361063 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) : (term46 A u s x) = (term46 A u s x).
Proof. exact (MK_COMB (@lem3361062 A u x) (@lem3361052 A s x)). Qed.
Lemma lem3361064 {A : Type'} (u : type686 A) (s : A -> Prop) : (term48 A u s) = (term48 A u s).
Proof. exact (fun_ext (fun x : A => @lem3361063 A u s x)). Qed.
Lemma lem3361065 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3361066 {A : Type'} (u : type686 A) (s : A -> Prop) : (term49 A u s) = (term49 A u s).
Proof. exact (MK_COMB (@lem3361065 A) (@lem3361064 A u s)). Qed.
Lemma lem3361071 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term26 A t s x) = (term26 A t s x).
Proof. exact (eq_refl (term26 A t s x)). Qed.
Lemma lem3361072 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term28 A t s) = (term28 A t s).
Proof. exact (fun_ext (fun x : A => @lem3361071 A t s x)). Qed.
Lemma lem3361073 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3361074 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term29 A t s).
Proof. exact (MK_COMB (@lem3361073 A) (@lem3361072 A t s)). Qed.
Lemma lem3361077 {A : Type'} (u : type686 A) (t : A -> Prop) : (term22 A u t) = (term22 A u t).
Proof. exact (eq_refl (term22 A u t)). Qed.
Lemma lem3361078 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term30 A u t s) = (term30 A u t s).
Proof. exact (MK_COMB (@lem3361077 A u t) (@lem3361074 A t s)). Qed.
Lemma lem3361079 {A : Type'} (u : type686 A) (s : A -> Prop) : (term31 A u s) = (term31 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3361078 A u t s)). Qed.
Lemma lem3361080 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3361081 {A : Type'} (u : type686 A) (s : A -> Prop) : (term32 A u s) = (term32 A u s).
Proof. exact (MK_COMB (@lem3361080 A) (@lem3361079 A u s)). Qed.
Lemma lem3361082 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361083 {A : Type'} (u : type686 A) (s : A -> Prop) : (term33 A u s) = (term33 A u s).
Proof. exact (MK_COMB (@lem3361082) (@lem3361081 A u s)). Qed.
Lemma lem3361084 {A : Type'} (u : type686 A) (s : A -> Prop) : (term50 A u s) = (term50 A u s).
Proof. exact (MK_COMB (@lem3361083 A u s) (@lem3361066 A u s)). Qed.
Lemma lem3361085 {A : Type'} (u : type686 A) : (term51 A u) = (term51 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3361084 A u s)). Qed.
Lemma lem3361086 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3361087 {A : Type'} (u : type686 A) : (term52 A u) = (term52 A u).
Proof. exact (MK_COMB (@lem3361086 A) (@lem3361085 A u)). Qed.
Lemma lem3361088 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (fun_ext (fun u : type686 A => @lem3361087 A u)). Qed.
Lemma lem3361089 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3361090 {A : Type'} : (term54 A) = (term54 A).
Proof. exact (MK_COMB (@lem3361089 A) (@lem3361088 A)). Qed.
Lemma lem3361139 {A : Type'} : (term56 A) = (term54 A).
Proof. exact (TRANS (@lem3361051 A) (@lem3361090 A)). Qed.
Lemma lem3361140 {A : Type'} : (term54 A) = (term56 A).
Proof. exact (SYM (@lem3361139 A)). Qed.
Lemma lem3361141 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : term32 A u s) : term32 A u s.
Proof. exact (h1). Qed.
Lemma lem3361142 {A : Type'} (u : type686 A) (x : A) (h1 : term42 A u x) : term42 A u x.
Proof. exact (h1). Qed.
Lemma lem3361144 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3361145 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (term63 A s x).
Proof. exact (@lem3361144 (s x)). Qed.
Lemma lem3361146 {A : Type'} (s : A -> Prop) (x : A) : (term63 A s x) = (s x).
Proof. exact (SYM (@lem3361145 A s x)). Qed.
Lemma lem3361147 {A : Type'} (s : A -> Prop) (x : A) (h1 : term64 A s x) : term64 A s x.
Proof. exact (h1). Qed.
Lemma lem3361155 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term26 A t s x) = (term65 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3361156 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term28 A t s) = (term66 A t s).
Proof. exact (fun_ext (fun x : A => @lem3361155 A t s x)). Qed.
Lemma lem3361157 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3361158 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term67 A t s).
Proof. exact (MK_COMB (@lem3361157 A) (@lem3361156 A t s)). Qed.
Lemma lem3361160 {A : Type'} (u : type686 A) (t : A -> Prop) : (term22 A u t) = (term22 A u t).
Proof. exact (eq_refl (term22 A u t)). Qed.
Lemma lem3361161 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term30 A u t s) = (term68 A u t s).
Proof. exact (MK_COMB (@lem3361160 A u t) (@lem3361158 A t s)). Qed.
Lemma lem3361162 {A : Type'} (u : type686 A) (s : A -> Prop) : (term31 A u s) = (term69 A u s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3361161 A u t s)). Qed.
Lemma lem3361163 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3361228 {A : Type'} (u : type686 A) (s : A -> Prop) : (term32 A u s) = (term70 A u s).
Proof. exact (MK_COMB (@lem3361163 A) (@lem3361162 A u s)). Qed.
Lemma lem3361229 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : term32 A u s) : term70 A u s.
Proof. exact (EQ_MP (@lem3361228 A u s) (@lem3361141 A u s h1)). Qed.
Lemma lem3361236 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term39 A u t x) = (term71 A u t x).
Proof. exact (@lem17265 (u t) (t x)). Qed.
Lemma lem3361237 {A : Type'} (u : type686 A) (x : A) : (term41 A u x) = (term72 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3361236 A u t x)). Qed.
Lemma lem3361238 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3361291 {A : Type'} (u : type686 A) (x : A) : (term42 A u x) = (term73 A u x).
Proof. exact (MK_COMB (@lem3361238 A) (@lem3361237 A u x)). Qed.
Lemma lem3361292 {A : Type'} (u : type686 A) (x : A) (h1 : term42 A u x) : term73 A u x.
Proof. exact (EQ_MP (@lem3361291 A u x) (@lem3361142 A u x h1)). Qed.
Lemma lem3361298 {A : Type'} (s : A -> Prop) (x : A) (h1 : term64 A s x) : term64 A s x.
Proof. exact (h1). Qed.
Lemma lem3361299 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term68 A u t s.
Proof. exact (h1). Qed.
Lemma lem3361304 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3361305 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3361304 A Prop f x). Qed.
Lemma lem3361307 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3361305 A t x). Qed.
Lemma lem3361308 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3361313 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3361314 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3361313 (A -> Prop) Prop f x). Qed.
Lemma lem3361316 {A : Type'} (u : type686 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem3361314 A u t). Qed.
Lemma lem3361317 {A : Type'} (u : type686 A) (t : A -> Prop) : (term74 A u t) = (term75 A u t).
Proof. exact (MK_COMB (@lem3361308) (@lem3361316 A u t)). Qed.
Lemma lem3361318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3361319 {A : Type'} (u : type686 A) (t : A -> Prop) : (term76 A u t) = (term77 A u t).
Proof. exact (MK_COMB (@lem3361318) (@lem3361317 A u t)). Qed.
Lemma lem3361320 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term71 A u t x) = (term78 A u t x).
Proof. exact (MK_COMB (@lem3361319 A u t) (@lem3361307 A t x)). Qed.
Lemma lem3361321 {A : Type'} (u : type686 A) (x : A) : (term72 A u x) = (term79 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3361320 A u t x)). Qed.
Lemma lem3361322 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3361323 {A : Type'} (u : type686 A) (x : A) : (term73 A u x) = (term80 A u x).
Proof. exact (MK_COMB (@lem3361322 A) (@lem3361321 A u x)). Qed.
Lemma lem3361324 {A : Type'} (u : type686 A) (x : A) (h1 : term42 A u x) : term80 A u x.
Proof. exact (EQ_MP (@lem3361323 A u x) (@lem3361292 A u x h1)). Qed.
Lemma lem3361325 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3361330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3361331 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3361330 A Prop f x). Qed.
Lemma lem3361333 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3361331 A s x). Qed.
Lemma lem3361334 {A : Type'} (s : A -> Prop) (x : A) : (term64 A s x) = (term81 A s x).
Proof. exact (MK_COMB (@lem3361325) (@lem3361333 A s x)). Qed.
Lemma lem3361340 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3361341 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3361340 A Prop f x). Qed.
Lemma lem3361343 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3361341 A s x). Qed.
Lemma lem3361344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3361349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3361350 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3361349 A Prop f x). Qed.
Lemma lem3361352 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3361350 A t x). Qed.
Lemma lem3361353 {A : Type'} (t : A -> Prop) (x : A) : (term64 A t x) = (term81 A t x).
Proof. exact (MK_COMB (@lem3361344) (@lem3361352 A t x)). Qed.
Lemma lem3361354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3361355 {A : Type'} (t : A -> Prop) (x : A) : (term82 A t x) = (term83 A t x).
Proof. exact (MK_COMB (@lem3361354) (@lem3361353 A t x)). Qed.
Lemma lem3361356 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term65 A t s x) = (term84 A t s x).
Proof. exact (MK_COMB (@lem3361355 A t x) (@lem3361343 A s x)). Qed.
Lemma lem3361357 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term66 A t s) = (term85 A t s).
Proof. exact (fun_ext (fun x : A => @lem3361356 A t s x)). Qed.
Lemma lem3361358 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3361359 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term67 A t s) = (term86 A t s).
Proof. exact (MK_COMB (@lem3361358 A) (@lem3361357 A t s)). Qed.
Lemma lem3361364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3361365 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3361364 (A -> Prop) Prop f x). Qed.
Lemma lem3361367 {A : Type'} (u : type686 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem3361365 A u t). Qed.
Lemma lem3361368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3361369 {A : Type'} (u : type686 A) (t : A -> Prop) : (term22 A u t) = (term87 A u t).
Proof. exact (MK_COMB (@lem3361368) (@lem3361367 A u t)). Qed.
Lemma lem3361370 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) : (term68 A u t s) = (term88 A u t s).
Proof. exact (MK_COMB (@lem3361369 A u t) (@lem3361359 A t s)). Qed.
Lemma lem3361371 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term88 A u t s.
Proof. exact (EQ_MP (@lem3361370 A u t s) (@lem3361299 A u t s h1)). Qed.
Lemma lem3361372 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term86 A t s.
Proof. exact (proj2 (@lem3361371 A u t s h1)). Qed.
Lemma lem3361381 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term78 A u t x) = (term78 A u t x).
Proof. exact (eq_refl (term78 A u t x)). Qed.
Lemma lem3361382 {A : Type'} (u : type686 A) (x : A) : (term79 A u x) = (term79 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3361381 A u t x)). Qed.
Lemma lem3361383 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3361385 {A : Type'} (u : type686 A) (x : A) : (term80 A u x) = (term80 A u x).
Proof. exact (MK_COMB (@lem3361383 A) (@lem3361382 A u x)). Qed.
Lemma lem3361386 {A : Type'} (u : type686 A) (x : A) (h1 : term42 A u x) : term80 A u x.
Proof. exact (EQ_MP (@lem3361385 A u x) (@lem3361324 A u x h1)). Qed.
Lemma lem3361402 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term84 A t s x) = (term84 A t s x).
Proof. exact (eq_refl (term84 A t s x)). Qed.
Lemma lem3361403 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term85 A t s) = (term85 A t s).
Proof. exact (fun_ext (fun x : A => @lem3361402 A t s x)). Qed.
Lemma lem3361404 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3361406 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term86 A t s) = (term86 A t s).
Proof. exact (MK_COMB (@lem3361404 A) (@lem3361403 A t s)). Qed.
Lemma lem3361407 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term86 A t s.
Proof. exact (EQ_MP (@lem3361406 A t s) (@lem3361372 A u t s h1)). Qed.
Lemma lem3361408 {A : Type'} (_35068 : A -> Prop) (u : type686 A) (x : A) (h1 : term42 A u x) : term89 A u x _35068.
Proof. exact (@lem3361386 A u x h1 _35068). Qed.
Lemma lem3361409 {A : Type'} (u : type686 A) (_35068 : A -> Prop) (x : A) : (term89 A u x _35068) = (term78 A u _35068 x).
Proof. exact (eq_refl (term89 A u x _35068)). Qed.
Lemma lem3361411 {A : Type'} (_35069 : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term90 A t s _35069.
Proof. exact (@lem3361407 A u t s h1 _35069). Qed.
Lemma lem3361412 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35069 : A) : (term90 A t s _35069) = (term84 A t s _35069).
Proof. exact (eq_refl (term90 A t s _35069)). Qed.
Lemma lem3361419 {A : Type'} (_35068 : A -> Prop) (u : type686 A) (x : A) (h1 : term42 A u x) : term78 A u _35068 x.
Proof. exact (EQ_MP (@lem3361409 A u _35068 x) (@lem3361408 A _35068 u x h1)). Qed.
Lemma lem3361421 {A : Type'} (s : A -> Prop) (x : A) (h1 : term64 A s x) : term81 A s x.
Proof. exact (EQ_MP (@lem3361334 A s x) (@lem3361298 A s x h1)). Qed.
Lemma lem3361429 {A : Type'} (_35069 : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term84 A t s _35069.
Proof. exact (EQ_MP (@lem3361412 A t s _35069) (@lem3361411 A _35069 u t s h1)). Qed.
Lemma lem3361431 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : @I ((A -> Prop) -> Prop) u t.
Proof. exact (proj1 (@lem3361371 A u t s h1)). Qed.
Lemma lem3361432 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term91 A u t.
Proof. exact (fun h0 : term75 A u t => @lem3361431 A u t s h1). Qed.
Lemma lem3361434 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3361435 {A : Type'} (u : type686 A) (t : A -> Prop) : (term91 A u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem3361434 (@I ((A -> Prop) -> Prop) u t)). Qed.
Lemma lem3361436 {A : Type'} (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : @I ((A -> Prop) -> Prop) u t.
Proof. exact (EQ_MP (@lem3361435 A u t) (@lem3361432 A u t s h1)). Qed.
Lemma lem3361442 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3361443 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : (term78 A u _35068 x) = (term93 A x u _35068).
Proof. exact (@lem3361442 (@I (A -> Prop) _35068 x) (term75 A u _35068)). Qed.
Lemma lem3361449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3361450 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : (term94 A u _35068 x) = (term95 A x u _35068).
Proof. exact (MK_COMB (@lem3361449) (@lem3361443 A x u _35068)). Qed.
Lemma lem3361456 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : (term93 A x u _35068) = (term93 A x u _35068).
Proof. exact (eq_refl (term93 A x u _35068)). Qed.
Lemma lem3361457 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : ((term78 A u _35068 x) = (term93 A x u _35068)) = ((term93 A x u _35068) = (term93 A x u _35068)).
Proof. exact (MK_COMB (@lem3361450 A x u _35068) (@lem3361456 A x u _35068)). Qed.
Lemma lem3361459 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3361460 (x : Prop) : (x = x) = True.
Proof. exact (@lem3361459 Prop x). Qed.
Lemma lem3361461 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : ((term93 A x u _35068) = (term93 A x u _35068)) = True.
Proof. exact (@lem3361460 (term93 A x u _35068)). Qed.
Lemma lem3361462 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : ((term78 A u _35068 x) = (term93 A x u _35068)) = True.
Proof. exact (TRANS (@lem3361457 A x u _35068) (@lem3361461 A x u _35068)). Qed.
Lemma lem3361463 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : True = ((term78 A u _35068 x) = (term93 A x u _35068)).
Proof. exact (SYM (@lem3361462 A x u _35068)). Qed.
Lemma lem3361464 {A : Type'} (x : A) (u : type686 A) (_35068 : A -> Prop) : (term78 A u _35068 x) = (term93 A x u _35068).
Proof. exact (EQ_MP (@lem3361463 A x u _35068) (@lem0)). Qed.
Lemma lem3361465 {A : Type'} (_35068 : A -> Prop) (u : type686 A) (x : A) (h1 : term42 A u x) : term93 A x u _35068.
Proof. exact (EQ_MP (@lem3361464 A x u _35068) (@lem3361419 A _35068 u x h1)). Qed.
Lemma lem3361467 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3361468 {A : Type'} (u : type686 A) (_35068 : A -> Prop) (x : A) : (term93 A x u _35068) = (term97 A u _35068 x).
Proof. exact (@lem3361467 (term75 A u _35068) (@I (A -> Prop) _35068 x)). Qed.
Lemma lem3361470 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3361471 {A : Type'} (u : type686 A) (_35068 : A -> Prop) : (term98 A u _35068) = (@I ((A -> Prop) -> Prop) u _35068).
Proof. exact (@lem3361470 (@I ((A -> Prop) -> Prop) u _35068)). Qed.
Lemma lem3361472 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361473 {A : Type'} (u : type686 A) (_35068 : A -> Prop) : (term99 A u _35068) = (term100 A u _35068).
Proof. exact (MK_COMB (@lem3361472) (@lem3361471 A u _35068)). Qed.
Lemma lem3361474 {A : Type'} (_35068 : A -> Prop) (x : A) : (@I (A -> Prop) _35068 x) = (@I (A -> Prop) _35068 x).
Proof. exact (eq_refl (@I (A -> Prop) _35068 x)). Qed.
Lemma lem3361475 {A : Type'} (u : type686 A) (_35068 : A -> Prop) (x : A) : (term97 A u _35068 x) = (term101 A u _35068 x).
Proof. exact (MK_COMB (@lem3361473 A u _35068) (@lem3361474 A _35068 x)). Qed.
Lemma lem3361476 {A : Type'} (u : type686 A) (_35068 : A -> Prop) (x : A) : (term93 A x u _35068) = (term101 A u _35068 x).
Proof. exact (TRANS (@lem3361468 A u _35068 x) (@lem3361475 A u _35068 x)). Qed.
Lemma lem3361479 {A : Type'} (_35068 : A -> Prop) (u : type686 A) (x : A) (h1 : term42 A u x) : term101 A u _35068 x.
Proof. exact (EQ_MP (@lem3361476 A u _35068 x) (@lem3361465 A _35068 u x h1)). Qed.
Lemma lem3361480 {A : Type'} (_35068 : A -> Prop) (u : type686 A) (x : A) (h1 : term42 A u x) : term101 A u _35068 x.
Proof. exact (@lem3361479 A _35068 u x h1). Qed.
Lemma lem3361481 {A : Type'} (t : A -> Prop) (u : type686 A) (x : A) (h1 : term42 A u x) : term101 A u t x.
Proof. exact (@lem3361480 A t u x h1). Qed.
Lemma lem3361484 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term68 A u t s) : @I (A -> Prop) t x.
Proof. exact (@lem3361481 A t u x h1 (@lem3361436 A u t s h2)). Qed.
Lemma lem3361485 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term68 A u t s) : term102 A t x.
Proof. exact (fun h0 : term81 A t x => @lem3361484 A x u t s h1 h2). Qed.
Lemma lem3361487 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3361488 {A : Type'} (t : A -> Prop) (x : A) : (term102 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3361487 (@I (A -> Prop) t x)). Qed.
Lemma lem3361489 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term68 A u t s) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3361488 A t x) (@lem3361485 A x u t s h1 h2)). Qed.
Lemma lem3361495 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3361496 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : (term84 A t s _35069) = (term103 A s t _35069).
Proof. exact (@lem3361495 (@I (A -> Prop) s _35069) (term81 A t _35069)). Qed.
Lemma lem3361502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3361503 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : (term104 A t s _35069) = (term105 A s t _35069).
Proof. exact (MK_COMB (@lem3361502) (@lem3361496 A s t _35069)). Qed.
Lemma lem3361509 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : (term103 A s t _35069) = (term103 A s t _35069).
Proof. exact (eq_refl (term103 A s t _35069)). Qed.
Lemma lem3361510 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : ((term84 A t s _35069) = (term103 A s t _35069)) = ((term103 A s t _35069) = (term103 A s t _35069)).
Proof. exact (MK_COMB (@lem3361503 A s t _35069) (@lem3361509 A s t _35069)). Qed.
Lemma lem3361512 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3361513 (x : Prop) : (x = x) = True.
Proof. exact (@lem3361512 Prop x). Qed.
Lemma lem3361514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : ((term103 A s t _35069) = (term103 A s t _35069)) = True.
Proof. exact (@lem3361513 (term103 A s t _35069)). Qed.
Lemma lem3361515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : ((term84 A t s _35069) = (term103 A s t _35069)) = True.
Proof. exact (TRANS (@lem3361510 A s t _35069) (@lem3361514 A s t _35069)). Qed.
Lemma lem3361516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : True = ((term84 A t s _35069) = (term103 A s t _35069)).
Proof. exact (SYM (@lem3361515 A s t _35069)). Qed.
Lemma lem3361517 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_35069 : A) : (term84 A t s _35069) = (term103 A s t _35069).
Proof. exact (EQ_MP (@lem3361516 A s t _35069) (@lem0)). Qed.
Lemma lem3361518 {A : Type'} (_35069 : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term103 A s t _35069.
Proof. exact (EQ_MP (@lem3361517 A s t _35069) (@lem3361429 A _35069 u t s h1)). Qed.
Lemma lem3361520 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3361521 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35069 : A) : (term103 A s t _35069) = (term106 A t s _35069).
Proof. exact (@lem3361520 (term81 A t _35069) (@I (A -> Prop) s _35069)). Qed.
Lemma lem3361523 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3361524 {A : Type'} (t : A -> Prop) (_35069 : A) : (term107 A t _35069) = (@I (A -> Prop) t _35069).
Proof. exact (@lem3361523 (@I (A -> Prop) t _35069)). Qed.
Lemma lem3361525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3361526 {A : Type'} (t : A -> Prop) (_35069 : A) : (term108 A t _35069) = (term109 A t _35069).
Proof. exact (MK_COMB (@lem3361525) (@lem3361524 A t _35069)). Qed.
Lemma lem3361527 {A : Type'} (s : A -> Prop) (_35069 : A) : (@I (A -> Prop) s _35069) = (@I (A -> Prop) s _35069).
Proof. exact (eq_refl (@I (A -> Prop) s _35069)). Qed.
Lemma lem3361528 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35069 : A) : (term106 A t s _35069) = (term110 A t s _35069).
Proof. exact (MK_COMB (@lem3361526 A t _35069) (@lem3361527 A s _35069)). Qed.
Lemma lem3361529 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_35069 : A) : (term103 A s t _35069) = (term110 A t s _35069).
Proof. exact (TRANS (@lem3361521 A t s _35069) (@lem3361528 A t s _35069)). Qed.
Lemma lem3361532 {A : Type'} (_35069 : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term110 A t s _35069.
Proof. exact (EQ_MP (@lem3361529 A t s _35069) (@lem3361518 A _35069 u t s h1)). Qed.
Lemma lem3361533 {A : Type'} (_35069 : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term110 A t s _35069.
Proof. exact (@lem3361532 A _35069 u t s h1). Qed.
Lemma lem3361534 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term68 A u t s) : term110 A t s x.
Proof. exact (@lem3361533 A x u t s h1). Qed.
Lemma lem3361537 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term68 A u t s) : @I (A -> Prop) s x.
Proof. exact (@lem3361534 A x u t s h2 (@lem3361489 A x u t s h1 h2)). Qed.
Lemma lem3361538 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term68 A u t s) : term102 A s x.
Proof. exact (fun h0 : term81 A s x => @lem3361537 A x u t s h1 h2). Qed.
Lemma lem3361540 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3361541 {A : Type'} (s : A -> Prop) (x : A) : (term102 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3361540 (@I (A -> Prop) s x)). Qed.
Lemma lem3361542 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term68 A u t s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3361541 A s x) (@lem3361538 A x u t s h1 h2)). Qed.
Lemma lem3361545 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3361547 {A : Type'} (s : A -> Prop) (x : A) : (term81 A s x) = (term111 A s x).
Proof. exact (@lem3361545 (@I (A -> Prop) s x)). Qed.
Lemma lem3361550 {A : Type'} (s : A -> Prop) (x : A) (h1 : term64 A s x) : term111 A s x.
Proof. exact (EQ_MP (@lem3361547 A s x) (@lem3361421 A s x h1)). Qed.
Lemma lem3361553 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term64 A s x) (h3 : term68 A u t s) : False.
Proof. exact (@lem3361550 A s x h2 (@lem3361542 A x u t s h1 h3)). Qed.
Lemma lem3361554 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term64 A s x) (h3 : term68 A u t s) : term112.
Proof. exact (fun h0 : ~ False => @lem3361553 A x u t s h1 h2 h3). Qed.
Lemma lem3361556 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3361557 : term112 = False.
Proof. exact (@lem3361556 False). Qed.
Lemma lem3361558 {A : Type'} (x : A) (u : type686 A) (t : A -> Prop) (s : A -> Prop) (h1 : term42 A u x) (h2 : term64 A s x) (h3 : term68 A u t s) : False.
Proof. exact (EQ_MP (@lem3361557) (@lem3361554 A x u t s h1 h2 h3)). Qed.
Lemma lem3361559 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) (h1 : term42 A u x) (h2 : term32 A u s) (h3 : term64 A s x) : False.
Proof. exact (ex_elim (@lem3361229 A u s h2) (fun t : A -> Prop => fun h0 : term69 A u s t => @lem3361558 A x u t s h1 h3 h0)). Qed.
Lemma lem3361560 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) (h1 : term42 A u x) (h2 : term32 A u s) (h3 : term64 A s x) : (term64 A s x) = False.
Proof. exact (prop_ext (fun h4 : term64 A s x => @lem3361559 A u s x h1 h2 h3) (fun h4 : False => @lem3361298 A s x h3)). Qed.
Lemma lem3361561 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) (h1 : term42 A u x) (h2 : term32 A u s) (h3 : term64 A s x) : False.
Proof. exact (EQ_MP (@lem3361560 A u s x h1 h2 h3) (@lem3361298 A s x h3)). Qed.
Lemma lem3361562 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) (h1 : term42 A u x) (h2 : term32 A u s) (h3 : term64 A s x) : (term64 A s x) = False.
Proof. exact (prop_ext (fun h4 : term64 A s x => @lem3361561 A u s x h1 h2 h3) (fun h4 : False => @lem3361147 A s x h3)). Qed.
Lemma lem3361563 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) (h1 : term42 A u x) (h2 : term32 A u s) (h3 : term64 A s x) : False.
Proof. exact (EQ_MP (@lem3361562 A u s x h1 h2 h3) (@lem3361147 A s x h3)). Qed.
Lemma lem3361564 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term42 A u x) (h2 : term32 A u s) : term63 A s x.
Proof. exact (fun h0 : term64 A s x => @lem3361563 A u s x h1 h2 h0). Qed.
Lemma lem3361565 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term42 A u x) (h2 : term32 A u s) : s x.
Proof. exact (EQ_MP (@lem3361146 A s x) (@lem3361564 A x u s h1 h2)). Qed.
Lemma lem3361566 {A : Type'} (x : A) (u : type686 A) (s : A -> Prop) (h1 : term32 A u s) : term46 A u s x.
Proof. exact (fun h0 : term42 A u x => @lem3361565 A x u s h0 h1). Qed.
Lemma lem3361571 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : term32 A u s) : term49 A u s.
Proof. exact (fun x : A => @lem3361566 A x u s h1). Qed.
Lemma lem3361572 {A : Type'} (u : type686 A) (s : A -> Prop) : term50 A u s.
Proof. exact (fun h0 : term32 A u s => @lem3361571 A u s h0). Qed.
Lemma lem3361577 {A : Type'} (u : type686 A) : term52 A u.
Proof. exact (fun s : A -> Prop => @lem3361572 A u s). Qed.
Lemma lem3361582 {A : Type'} : term54 A.
Proof. exact (fun u : type686 A => @lem3361577 A u). Qed.
Lemma lem3361583 {A : Type'} : term56 A.
Proof. exact (EQ_MP (@lem3361140 A) (@lem3361582 A)). Qed.
Lemma lem3361585 {A : Type'} : term56 A.
Proof. exact (@lem3360982 A (@lem3361583 A)). Qed.
Lemma lem3361586 {A : Type'} (h1 : term57 A) : False.
Proof. exact (@lem3361585 A (@lem3360966 A h1)). Qed.
Lemma lem3361587 {A : Type'} (h1 : term57 A) : (term57 A) = False.
Proof. exact (prop_ext (fun h2 : term57 A => @lem3361586 A h1) (fun h2 : False => @lem3360966 A h1)). Qed.
Lemma lem3361588 {A : Type'} (h1 : term57 A) : False.
Proof. exact (EQ_MP (@lem3361587 A h1) (@lem3360966 A h1)). Qed.
Lemma lem3361589 {A : Type'} : term56 A.
Proof. exact (fun h0 : term57 A => @lem3361588 A h0). Qed.
Lemma lem3361590 {A : Type'} : term54 A.
Proof. exact (EQ_MP (@lem3360965 A) (@lem3361589 A)). Qed.
Lemma lem3361591 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem3360961 A) (@lem3361590 A)). Qed.
Lemma lem3361592 {A : Type'} : term20 A.
Proof. exact (EQ_MP (@lem3360830 A) (@lem3361591 A)). Qed.
