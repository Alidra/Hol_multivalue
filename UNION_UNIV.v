Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_UNIV_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3235873 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3235874 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3235873 A s t). Qed.
Lemma lem3235875 {A : Type'} (s : A -> Prop) : ((@UNION A (@UNIV A) s) = (@UNIV A)) = (term1 A s).
Proof. exact (@lem3235874 A (@UNION A (@UNIV A) s) (@UNIV A)). Qed.
Lemma lem3235884 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3235875 A s)). Qed.
Lemma lem3235885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3235886 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3235885 A) (@lem3235884 A)). Qed.
Lemma lem3235891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3235892 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem3235891) (@lem3235886 A)). Qed.
Lemma lem3235900 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3235901 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3235900 A s t). Qed.
Lemma lem3235902 {A : Type'} (s : A -> Prop) : ((@UNION A s (@UNIV A)) = (@UNIV A)) = (term8 A s).
Proof. exact (@lem3235901 A (@UNION A s (@UNIV A)) (@UNIV A)). Qed.
Lemma lem3235911 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3235902 A s)). Qed.
Lemma lem3235912 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3235913 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3235912 A) (@lem3235911 A)). Qed.
Lemma lem3235918 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3235892 A) (@lem3235913 A)). Qed.
Lemma lem3235921 {A : Type'} : (term14 A) = (term13 A).
Proof. exact (SYM (@lem3235918 A)). Qed.
Lemma lem3235935 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3235936 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3235935 A s x t). Qed.
Lemma lem3235937 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = (term18 A x s).
Proof. exact (@lem3235936 A (@UNIV A) x s). Qed.
Lemma lem3235941 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3235942 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3235941 A x). Qed.
Lemma lem3235943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3235944 {A : Type'} (x : A) : (term19 A x) = (or True).
Proof. exact (MK_COMB (@lem3235943) (@lem3235942 A x)). Qed.
Lemma lem3235946 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3235947 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3235946 A P x). Qed.
Lemma lem3235948 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3235947 A s x). Qed.
Lemma lem3235949 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (term20 A s x).
Proof. exact (MK_COMB (@lem3235944 A x) (@lem3235948 A s x)). Qed.
Lemma lem3235951 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3235952 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = True.
Proof. exact (@lem3235951 (s x)). Qed.
Lemma lem3235953 {A : Type'} (x : A) (s : A -> Prop) : (term18 A x s) = True.
Proof. exact (TRANS (@lem3235949 A s x) (@lem3235952 A s x)). Qed.
Lemma lem3235954 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = True.
Proof. exact (TRANS (@lem3235937 A x s) (@lem3235953 A x s)). Qed.
Lemma lem3235955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3235956 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3235955) (@lem3235954 A x s)). Qed.
Lemma lem3235958 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3235959 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3235958 A x). Qed.
Lemma lem3235960 {A : Type'} (s : A -> Prop) (x : A) : ((term17 A x s) = (@IN A x (@UNIV A))) = (True = True).
Proof. exact (MK_COMB (@lem3235956 A x s) (@lem3235959 A x)). Qed.
Lemma lem3235962 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3235963 : (True = True) = True.
Proof. exact (@lem3235962 True). Qed.
Lemma lem3235964 {A : Type'} (s : A -> Prop) (x : A) : ((term17 A x s) = (@IN A x (@UNIV A))) = True.
Proof. exact (TRANS (@lem3235960 A s x) (@lem3235963)). Qed.
Lemma lem3235965 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3235964 A s x)). Qed.
Lemma lem3235966 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3235967 {A : Type'} (s : A -> Prop) : (term1 A s) = (term24 A).
Proof. exact (MK_COMB (@lem3235966 A) (@lem3235965 A s)). Qed.
Lemma lem3235969 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3235970 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem3235969 A t). Qed.
Lemma lem3235971 {A : Type'} : (term24 A) = True.
Proof. exact (@lem3235970 A True). Qed.
Lemma lem3235972 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3235967 A s) (@lem3235971 A)). Qed.
Lemma lem3235973 {A : Type'} : (term3 A) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3235972 A s)). Qed.
Lemma lem3235974 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3235975 {A : Type'} : (term5 A) = (term27 A).
Proof. exact (MK_COMB (@lem3235974 A) (@lem3235973 A)). Qed.
Lemma lem3235977 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3235978 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (@lem3235977 (A -> Prop) t). Qed.
Lemma lem3235979 {A : Type'} : (term27 A) = True.
Proof. exact (@lem3235978 A True). Qed.
Lemma lem3235980 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3235975 A) (@lem3235979 A)). Qed.
Lemma lem3235981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3235982 {A : Type'} : (term7 A) = (and True).
Proof. exact (MK_COMB (@lem3235981) (@lem3235980 A)). Qed.
Lemma lem3235994 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3235995 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3235994 A s x t). Qed.
Lemma lem3235996 {A : Type'} (s : A -> Prop) (x : A) : (term29 A x s) = (term30 A s x).
Proof. exact (@lem3235995 A s x (@UNIV A)). Qed.
Lemma lem3236000 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3236001 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3236000 A P x). Qed.
Lemma lem3236002 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3236001 A s x). Qed.
Lemma lem3236003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3236004 {A : Type'} (s : A -> Prop) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (MK_COMB (@lem3236003) (@lem3236002 A s x)). Qed.
Lemma lem3236006 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3236007 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3236006 A x). Qed.
Lemma lem3236008 {A : Type'} (s : A -> Prop) (x : A) : (term30 A s x) = (term33 A s x).
Proof. exact (MK_COMB (@lem3236004 A s x) (@lem3236007 A x)). Qed.
Lemma lem3236010 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem3236011 {A : Type'} (s : A -> Prop) (x : A) : (term33 A s x) = True.
Proof. exact (@lem3236010 (s x)). Qed.
Lemma lem3236012 {A : Type'} (s : A -> Prop) (x : A) : (term30 A s x) = True.
Proof. exact (TRANS (@lem3236008 A s x) (@lem3236011 A s x)). Qed.
Lemma lem3236013 {A : Type'} (x : A) (s : A -> Prop) : (term29 A x s) = True.
Proof. exact (TRANS (@lem3235996 A s x) (@lem3236012 A s x)). Qed.
Lemma lem3236014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3236015 {A : Type'} (x : A) (s : A -> Prop) : (term34 A x s) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3236014) (@lem3236013 A x s)). Qed.
Lemma lem3236017 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3236018 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3236017 A x). Qed.
Lemma lem3236019 {A : Type'} (s : A -> Prop) (x : A) : ((term29 A x s) = (@IN A x (@UNIV A))) = (True = True).
Proof. exact (MK_COMB (@lem3236015 A x s) (@lem3236018 A x)). Qed.
Lemma lem3236021 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3236022 : (True = True) = True.
Proof. exact (@lem3236021 True). Qed.
Lemma lem3236023 {A : Type'} (s : A -> Prop) (x : A) : ((term29 A x s) = (@IN A x (@UNIV A))) = True.
Proof. exact (TRANS (@lem3236019 A s x) (@lem3236022)). Qed.
Lemma lem3236024 {A : Type'} (s : A -> Prop) : (term35 A s) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3236023 A s x)). Qed.
Lemma lem3236025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3236026 {A : Type'} (s : A -> Prop) : (term8 A s) = (term24 A).
Proof. exact (MK_COMB (@lem3236025 A) (@lem3236024 A s)). Qed.
Lemma lem3236028 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3236029 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem3236028 A t). Qed.
Lemma lem3236030 {A : Type'} : (term24 A) = True.
Proof. exact (@lem3236029 A True). Qed.
Lemma lem3236031 {A : Type'} (s : A -> Prop) : (term8 A s) = True.
Proof. exact (TRANS (@lem3236026 A s) (@lem3236030 A)). Qed.
Lemma lem3236032 {A : Type'} : (term10 A) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3236031 A s)). Qed.
Lemma lem3236033 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3236034 {A : Type'} : (term12 A) = (term27 A).
Proof. exact (MK_COMB (@lem3236033 A) (@lem3236032 A)). Qed.
Lemma lem3236036 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3236037 {A : Type'} (t : Prop) : (term28 A t) = t.
Proof. exact (@lem3236036 (A -> Prop) t). Qed.
Lemma lem3236038 {A : Type'} : (term27 A) = True.
Proof. exact (@lem3236037 A True). Qed.
Lemma lem3236039 {A : Type'} : (term12 A) = True.
Proof. exact (TRANS (@lem3236034 A) (@lem3236038 A)). Qed.
Lemma lem3236040 {A : Type'} : (term14 A) = (True /\ True).
Proof. exact (MK_COMB (@lem3235982 A) (@lem3236039 A)). Qed.
Lemma lem3236042 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3236043 : (True /\ True) = True.
Proof. exact (@lem3236042 True). Qed.
Lemma lem3236044 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem3236040 A) (@lem3236043)). Qed.
Lemma lem3236045 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem3236044 A)). Qed.
Lemma lem3236046 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3236045 A) (@lem0)). Qed.
Lemma lem3236047 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3235921 A) (@lem3236046 A)). Qed.
