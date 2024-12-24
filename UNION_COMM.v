Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_COMM_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3232859 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3232860 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3232859 A s t). Qed.
Lemma lem3232861 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@UNION A s t) = (@UNION A t s)) = (term1 A t s).
Proof. exact (@lem3232860 A (@UNION A s t) (@UNION A t s)). Qed.
Lemma lem3232870 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3232861 A t s)). Qed.
Lemma lem3232871 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232872 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (MK_COMB (@lem3232871 A) (@lem3232870 A s)). Qed.
Lemma lem3232877 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3232872 A s)). Qed.
Lemma lem3232878 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232879 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem3232878 A) (@lem3232877 A)). Qed.
Lemma lem3232884 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3232879 A)). Qed.
Lemma lem3232900 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3232901 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (@lem3232900 A s x t). Qed.
Lemma lem3232905 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232906 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232905 A P x). Qed.
Lemma lem3232907 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3232906 A s x). Qed.
Lemma lem3232908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3232909 {A : Type'} (s : A -> Prop) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (MK_COMB (@lem3232908) (@lem3232907 A s x)). Qed.
Lemma lem3232911 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232912 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232911 A P x). Qed.
Lemma lem3232913 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3232912 A t x). Qed.
Lemma lem3232914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A s x t) = (term14 A s t x).
Proof. exact (MK_COMB (@lem3232909 A s x) (@lem3232913 A t x)). Qed.
Lemma lem3232917 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term10 A x s t) = (term14 A s t x).
Proof. exact (TRANS (@lem3232901 A s x t) (@lem3232914 A s t x)). Qed.
Lemma lem3232918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3232919 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term15 A x s t) = (term16 A s t x).
Proof. exact (MK_COMB (@lem3232918) (@lem3232917 A s t x)). Qed.
Lemma lem3232921 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3232922 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (@lem3232921 A s x t). Qed.
Lemma lem3232923 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term10 A x t s) = (term11 A t x s).
Proof. exact (@lem3232922 A t x s). Qed.
Lemma lem3232927 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232928 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232927 A P x). Qed.
Lemma lem3232929 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3232928 A t x). Qed.
Lemma lem3232930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3232931 {A : Type'} (t : A -> Prop) (x : A) : (term12 A x t) = (term13 A t x).
Proof. exact (MK_COMB (@lem3232930) (@lem3232929 A t x)). Qed.
Lemma lem3232933 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3232934 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3232933 A P x). Qed.
Lemma lem3232935 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3232934 A s x). Qed.
Lemma lem3232936 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term11 A t x s) = (term14 A t s x).
Proof. exact (MK_COMB (@lem3232931 A t x) (@lem3232935 A s x)). Qed.
Lemma lem3232939 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term10 A x t s) = (term14 A t s x).
Proof. exact (TRANS (@lem3232923 A t x s) (@lem3232936 A t s x)). Qed.
Lemma lem3232940 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term10 A x s t) = (term10 A x t s)) = ((term14 A s t x) = (term14 A t s x)).
Proof. exact (MK_COMB (@lem3232919 A s t x) (@lem3232939 A t s x)). Qed.
Lemma lem3232943 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term17 A t s) = (term18 A t s).
Proof. exact (fun_ext (fun x : A => @lem3232940 A t s x)). Qed.
Lemma lem3232944 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3232945 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1 A t s) = (term19 A t s).
Proof. exact (MK_COMB (@lem3232944 A) (@lem3232943 A t s)). Qed.
Lemma lem3232950 {A : Type'} (s : A -> Prop) : (term3 A s) = (term20 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3232945 A t s)). Qed.
Lemma lem3232951 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232952 {A : Type'} (s : A -> Prop) : (term5 A s) = (term21 A s).
Proof. exact (MK_COMB (@lem3232951 A) (@lem3232950 A s)). Qed.
Lemma lem3232957 {A : Type'} : (term7 A) = (term22 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3232952 A s)). Qed.
Lemma lem3232958 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3232959 {A : Type'} : (term9 A) = (term23 A).
Proof. exact (MK_COMB (@lem3232958 A) (@lem3232957 A)). Qed.
Lemma lem3232964 {A : Type'} : (term23 A) = (term9 A).
Proof. exact (SYM (@lem3232959 A)). Qed.
Lemma lem3232966 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3232967 {A : Type'} : (term23 A) = (term25 A).
Proof. exact (@lem3232966 (term23 A)). Qed.
Lemma lem3232968 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (SYM (@lem3232967 A)). Qed.
Lemma lem3232969 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3232972 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3232973 {A : Type'} : term27 A.
Proof. exact (fun h0 : term25 A => @lem3232972 A h0). Qed.
Lemma lem3232974 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3232975 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3232976 {A : Type'} (h1 : term25 A) (h2 : term27 A) : term25 A.
Proof. exact (@lem3232974 A h2 (@lem3232975 A h1)). Qed.
Lemma lem3232977 {A : Type'} (h1 : term25 A) : term28 A.
Proof. exact (fun h0 : term27 A => @lem3232976 A h1 h0). Qed.
Lemma lem3232978 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3232979 {A : Type'} (h1 : term25 A) (h2 : term27 A) : term25 A.
Proof. exact (@lem3232977 A h1 (@lem3232978 A h2)). Qed.
Lemma lem3232980 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (fun h0 : term25 A => @lem3232979 A h0 h1). Qed.
Lemma lem3232981 {A : Type'} : term29 A.
Proof. exact (fun h0 : term27 A => @lem3232980 A h0). Qed.
Lemma lem3232984 {A : Type'} : term27 A.
Proof. exact (@lem3232981 A (@lem3232973 A)). Qed.
Lemma lem3232985 {A : Type'} : term27 A.
Proof. exact (@lem3232984 A). Qed.
Lemma lem3232987 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3232988 {A : Type'} : (term25 A) = (term30 A).
Proof. exact (@lem3232987 (term26 A)). Qed.
Lemma lem3232990 (t : Prop) : (term31 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3232991 {A : Type'} : (term30 A) = (term23 A).
Proof. exact (@lem3232990 (term23 A)). Qed.
Lemma lem3233012 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (TRANS (@lem3232988 A) (@lem3232991 A)). Qed.
Lemma lem3233025 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term14 A s t x) = (term14 A t s x)) = ((term14 A s t x) = (term14 A t s x)).
Proof. exact (eq_refl ((term14 A s t x) = (term14 A t s x))). Qed.
Lemma lem3233026 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term18 A t s) = (term18 A t s).
Proof. exact (fun_ext (fun x : A => @lem3233025 A t s x)). Qed.
Lemma lem3233027 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3233028 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term19 A t s) = (term19 A t s).
Proof. exact (MK_COMB (@lem3233027 A) (@lem3233026 A t s)). Qed.
Lemma lem3233029 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233028 A t s)). Qed.
Lemma lem3233030 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233031 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (MK_COMB (@lem3233030 A) (@lem3233029 A s)). Qed.
Lemma lem3233032 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233031 A s)). Qed.
Lemma lem3233033 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233034 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem3233033 A) (@lem3233032 A)). Qed.
Lemma lem3233059 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (TRANS (@lem3233012 A) (@lem3233034 A)). Qed.
Lemma lem3233060 {A : Type'} : (term23 A) = (term25 A).
Proof. exact (SYM (@lem3233059 A)). Qed.
Lemma lem3233062 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3233063 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term14 A s t x) = (term14 A t s x)) = (term32 A t s x).
Proof. exact (@lem3233062 ((term14 A s t x) = (term14 A t s x))). Qed.
Lemma lem3233064 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term32 A t s x) = ((term14 A s t x) = (term14 A t s x)).
Proof. exact (SYM (@lem3233063 A t s x)). Qed.
Lemma lem3233065 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : term33 A t s x.
Proof. exact (h1). Qed.
Lemma lem3233074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term34 A s t x) = (term35 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3233086 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term34 A t s x) = (term35 A t s x).
Proof. exact (@lem17160 (t x) (s x)). Qed.
Lemma lem3233089 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term14 A t s x) = (term14 A t s x).
Proof. exact (eq_refl (term14 A t s x)). Qed.
Lemma lem3233090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3233091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term36 A s t x) = (term37 A s t x).
Proof. exact (MK_COMB (@lem3233090) (@lem3233074 A s t x)). Qed.
Lemma lem3233092 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term38 A t s x) = (term39 A t s x).
Proof. exact (MK_COMB (@lem3233091 A s t x) (@lem3233089 A t s x)). Qed.
Lemma lem3233094 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term40 A s t x) = (term40 A s t x).
Proof. exact (eq_refl (term40 A s t x)). Qed.
Lemma lem3233095 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term41 A t s x) = (term42 A t s x).
Proof. exact (MK_COMB (@lem3233094 A s t x) (@lem3233086 A t s x)). Qed.
Lemma lem3233096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233097 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term43 A t s x) = (term44 A t s x).
Proof. exact (MK_COMB (@lem3233096) (@lem3233095 A t s x)). Qed.
Lemma lem3233098 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term45 A t s x) = (term46 A t s x).
Proof. exact (MK_COMB (@lem3233097 A t s x) (@lem3233092 A t s x)). Qed.
Lemma lem3233099 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term33 A t s x) = (term45 A t s x).
Proof. exact (@lem17646 (term14 A s t x) (term14 A t s x)). Qed.
Lemma lem3233104 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term33 A t s x) = (term46 A t s x).
Proof. exact (TRANS (@lem3233099 A t s x) (@lem3233098 A t s x)). Qed.
Lemma lem3233159 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : term46 A t s x.
Proof. exact (EQ_MP (@lem3233104 A t s x) (@lem3233065 A t s x h1)). Qed.
Lemma lem3233160 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term42 A t s x.
Proof. exact (h1). Qed.
Lemma lem3233161 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term39 A t s x.
Proof. exact (h1). Qed.
Lemma lem3233162 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term35 A t s x.
Proof. exact (proj2 (@lem3233160 A t s x h1)). Qed.
Lemma lem3233163 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term14 A s t x.
Proof. exact (proj1 (@lem3233160 A t s x h1)). Qed.
Lemma lem3233168 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term14 A t s x.
Proof. exact (proj2 (@lem3233161 A t s x h1)). Qed.
Lemma lem3233169 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term35 A s t x.
Proof. exact (proj1 (@lem3233161 A t s x h1)). Qed.
Lemma lem3233185 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3233197 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3233209 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3233221 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3233225 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term47 A s x.
Proof. exact (proj2 (@lem3233162 A t s x h1)). Qed.
Lemma lem3233227 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3233229 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term47 A t x.
Proof. exact (proj1 (@lem3233162 A t s x h1)). Qed.
Lemma lem3233233 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3233237 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term47 A t x.
Proof. exact (proj2 (@lem3233169 A t s x h1)). Qed.
Lemma lem3233239 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3233241 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term47 A s x.
Proof. exact (proj1 (@lem3233169 A t s x h1)). Qed.
Lemma lem3233245 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3233247 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3233248 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term48 A s x.
Proof. exact (fun h0 : term47 A s x => @lem3233247 A s x h1). Qed.
Lemma lem3233250 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233251 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (s x).
Proof. exact (@lem3233250 (s x)). Qed.
Lemma lem3233252 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3233251 A s x) (@lem3233248 A s x h1)). Qed.
Lemma lem3233255 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3233257 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term50 A s x).
Proof. exact (@lem3233255 (s x)). Qed.
Lemma lem3233260 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term50 A s x.
Proof. exact (EQ_MP (@lem3233257 A s x) (@lem3233225 A t s x h1)). Qed.
Lemma lem3233263 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : False.
Proof. exact (@lem3233260 A t s x h2 (@lem3233252 A s x h1)). Qed.
Lemma lem3233264 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3233263 A t s x h1 h2). Qed.
Lemma lem3233266 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233267 : term51 = False.
Proof. exact (@lem3233266 False). Qed.
Lemma lem3233268 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233267) (@lem3233264 A t s x h1 h2)). Qed.
Lemma lem3233270 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3233271 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term48 A t x.
Proof. exact (fun h0 : term47 A t x => @lem3233270 A t x h1). Qed.
Lemma lem3233273 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233274 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (t x).
Proof. exact (@lem3233273 (t x)). Qed.
Lemma lem3233275 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3233274 A t x) (@lem3233271 A t x h1)). Qed.
Lemma lem3233278 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3233280 {A : Type'} (t : A -> Prop) (x : A) : (term47 A t x) = (term50 A t x).
Proof. exact (@lem3233278 (t x)). Qed.
Lemma lem3233283 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term50 A t x.
Proof. exact (EQ_MP (@lem3233280 A t x) (@lem3233229 A t s x h1)). Qed.
Lemma lem3233286 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : False.
Proof. exact (@lem3233283 A t s x h2 (@lem3233275 A t x h1)). Qed.
Lemma lem3233287 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3233286 A t s x h1 h2). Qed.
Lemma lem3233289 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233290 : term51 = False.
Proof. exact (@lem3233289 False). Qed.
Lemma lem3233291 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233290) (@lem3233287 A t s x h1 h2)). Qed.
Lemma lem3233293 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3233294 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term48 A t x.
Proof. exact (fun h0 : term47 A t x => @lem3233293 A t x h1). Qed.
Lemma lem3233296 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233297 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (t x).
Proof. exact (@lem3233296 (t x)). Qed.
Lemma lem3233298 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3233297 A t x) (@lem3233294 A t x h1)). Qed.
Lemma lem3233301 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3233303 {A : Type'} (t : A -> Prop) (x : A) : (term47 A t x) = (term50 A t x).
Proof. exact (@lem3233301 (t x)). Qed.
Lemma lem3233306 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term50 A t x.
Proof. exact (EQ_MP (@lem3233303 A t x) (@lem3233237 A t s x h1)). Qed.
Lemma lem3233309 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : False.
Proof. exact (@lem3233306 A t s x h2 (@lem3233298 A t x h1)). Qed.
Lemma lem3233310 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3233309 A t s x h1 h2). Qed.
Lemma lem3233312 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233313 : term51 = False.
Proof. exact (@lem3233312 False). Qed.
Lemma lem3233314 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233313) (@lem3233310 A t s x h1 h2)). Qed.
Lemma lem3233316 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3233317 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term48 A s x.
Proof. exact (fun h0 : term47 A s x => @lem3233316 A s x h1). Qed.
Lemma lem3233319 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233320 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (s x).
Proof. exact (@lem3233319 (s x)). Qed.
Lemma lem3233321 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3233320 A s x) (@lem3233317 A s x h1)). Qed.
Lemma lem3233324 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3233326 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term50 A s x).
Proof. exact (@lem3233324 (s x)). Qed.
Lemma lem3233329 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term50 A s x.
Proof. exact (EQ_MP (@lem3233326 A s x) (@lem3233241 A t s x h1)). Qed.
Lemma lem3233332 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : False.
Proof. exact (@lem3233329 A t s x h2 (@lem3233321 A s x h1)). Qed.
Lemma lem3233333 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3233332 A t s x h1 h2). Qed.
Lemma lem3233335 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3233336 : term51 = False.
Proof. exact (@lem3233335 False). Qed.
Lemma lem3233337 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233336) (@lem3233333 A t s x h1 h2)). Qed.
Lemma lem3233338 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3233337 A t s x h1 h2) (fun h3 : False => @lem3233245 A s x h1)). Qed.
Lemma lem3233339 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233338 A t s x h1 h2) (@lem3233245 A s x h1)). Qed.
Lemma lem3233340 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3233314 A t s x h1 h2) (fun h3 : False => @lem3233239 A t x h1)). Qed.
Lemma lem3233341 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233340 A t s x h1 h2) (@lem3233239 A t x h1)). Qed.
Lemma lem3233342 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3233291 A t s x h1 h2) (fun h3 : False => @lem3233233 A t x h1)). Qed.
Lemma lem3233343 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233342 A t s x h1 h2) (@lem3233233 A t x h1)). Qed.
Lemma lem3233344 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3233268 A t s x h1 h2) (fun h3 : False => @lem3233227 A s x h1)). Qed.
Lemma lem3233345 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233344 A t s x h1 h2) (@lem3233227 A s x h1)). Qed.
Lemma lem3233346 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3233339 A t s x h1 h2) (fun h3 : False => @lem3233221 A s x h1)). Qed.
Lemma lem3233347 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233346 A t s x h1 h2) (@lem3233221 A s x h1)). Qed.
Lemma lem3233348 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3233341 A t s x h1 h2) (fun h3 : False => @lem3233209 A t x h1)). Qed.
Lemma lem3233349 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233348 A t s x h1 h2) (@lem3233209 A t x h1)). Qed.
Lemma lem3233350 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3233343 A t s x h1 h2) (fun h3 : False => @lem3233197 A t x h1)). Qed.
Lemma lem3233351 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233350 A t s x h1 h2) (@lem3233197 A t x h1)). Qed.
Lemma lem3233352 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3233345 A t s x h1 h2) (fun h3 : False => @lem3233185 A s x h1)). Qed.
Lemma lem3233353 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233352 A t s x h1 h2) (@lem3233185 A s x h1)). Qed.
Lemma lem3233354 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3233347 A t s x h1 h2) (fun h3 : False => @lem3233221 A s x h1)). Qed.
Lemma lem3233355 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233354 A t s x h1 h2) (@lem3233221 A s x h1)). Qed.
Lemma lem3233356 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3233349 A t s x h1 h2) (fun h3 : False => @lem3233209 A t x h1)). Qed.
Lemma lem3233357 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3233356 A t s x h1 h2) (@lem3233209 A t x h1)). Qed.
Lemma lem3233358 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3233351 A t s x h1 h2) (fun h3 : False => @lem3233197 A t x h1)). Qed.
Lemma lem3233359 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233358 A t s x h1 h2) (@lem3233197 A t x h1)). Qed.
Lemma lem3233360 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3233353 A t s x h1 h2) (fun h3 : False => @lem3233185 A s x h1)). Qed.
Lemma lem3233361 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3233360 A t s x h1 h2) (@lem3233185 A s x h1)). Qed.
Lemma lem3233362 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : False.
Proof. exact (or_elim (@lem3233168 A t s x h1) (fun h0 : t x => @lem3233357 A t s x h0 h1) (fun h0 : s x => @lem3233355 A t s x h0 h1)). Qed.
Lemma lem3233363 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : False.
Proof. exact (or_elim (@lem3233163 A t s x h1) (fun h0 : s x => @lem3233361 A t s x h0 h1) (fun h0 : t x => @lem3233359 A t s x h0 h1)). Qed.
Lemma lem3233364 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : False.
Proof. exact (or_elim (@lem3233159 A t s x h1) (fun h0 : term42 A t s x => @lem3233363 A t s x h0) (fun h0 : term39 A t s x => @lem3233362 A t s x h0)). Qed.
Lemma lem3233365 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : (term33 A t s x) = False.
Proof. exact (prop_ext (fun h2 : term33 A t s x => @lem3233364 A t s x h1) (fun h2 : False => @lem3233065 A t s x h1)). Qed.
Lemma lem3233366 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : False.
Proof. exact (EQ_MP (@lem3233365 A t s x h1) (@lem3233065 A t s x h1)). Qed.
Lemma lem3233367 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : term32 A t s x.
Proof. exact (fun h0 : term33 A t s x => @lem3233366 A t s x h0). Qed.
Lemma lem3233368 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term14 A s t x) = (term14 A t s x).
Proof. exact (EQ_MP (@lem3233064 A t s x) (@lem3233367 A t s x)). Qed.
Lemma lem3233373 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term19 A t s.
Proof. exact (fun x : A => @lem3233368 A t s x). Qed.
Lemma lem3233378 {A : Type'} (s : A -> Prop) : term21 A s.
Proof. exact (fun t : A -> Prop => @lem3233373 A t s). Qed.
Lemma lem3233383 {A : Type'} : term23 A.
Proof. exact (fun s : A -> Prop => @lem3233378 A s). Qed.
Lemma lem3233384 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3233060 A) (@lem3233383 A)). Qed.
Lemma lem3233386 {A : Type'} : term25 A.
Proof. exact (@lem3232985 A (@lem3233384 A)). Qed.
Lemma lem3233387 {A : Type'} (h1 : term26 A) : False.
Proof. exact (@lem3233386 A (@lem3232969 A h1)). Qed.
Lemma lem3233388 {A : Type'} (h1 : term26 A) : (term26 A) = False.
Proof. exact (prop_ext (fun h2 : term26 A => @lem3233387 A h1) (fun h2 : False => @lem3232969 A h1)). Qed.
Lemma lem3233389 {A : Type'} (h1 : term26 A) : False.
Proof. exact (EQ_MP (@lem3233388 A h1) (@lem3232969 A h1)). Qed.
Lemma lem3233390 {A : Type'} : term25 A.
Proof. exact (fun h0 : term26 A => @lem3233389 A h0). Qed.
Lemma lem3233391 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3232968 A) (@lem3233390 A)). Qed.
Lemma lem3233392 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3232964 A) (@lem3233391 A)). Qed.
Lemma lem3233393 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3232884 A) (@lem3233392 A)). Qed.
