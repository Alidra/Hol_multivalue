Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_COMPLEMENT_term_abbrevs.
Require Import ARBITRARY_UNION_OF_COMPLEMENT_spec.
Require Import COMPL_COMPL_spec.
Require Import ETA_AX_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4860848 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4860849 {A : Type'} (s : A -> Prop) : (term0 A s) = ((term1 A s) = s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4860851 {A B : Type'} (t : A -> B) : term2 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem4860852 {A B : Type'} (t : A -> B) : (term2 A B t) = ((term3 A B t) = t).
Proof. exact (eq_refl (term2 A B t)). Qed.
Lemma lem4860853 {A B : Type'} (t : A -> B) : (term3 A B t) = t.
Proof. exact (EQ_MP (@lem4860852 A B t) (@lem4860851 A B t)). Qed.
Lemma lem4860854 {A : Type'} (P : type686 A) : term4 A P.
Proof. exact (@lem4860847 A P). Qed.
Lemma lem4860855 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4860856 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (EQ_MP (@lem4860855 A P) (@lem4860854 A P)). Qed.
Lemma lem4860857 {A : Type'} (P : type686 A) (s : A -> Prop) : term6 A P s.
Proof. exact (@lem4860856 A P s). Qed.
Lemma lem4860858 {A : Type'} (P : type686 A) (s : A -> Prop) : (term6 A P s) = ((@UNION_OF A (@ARBITRARY A) P s) = (term7 A P s)).
Proof. exact (eq_refl (term6 A P s)). Qed.
Lemma lem4860871 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term7 A P s).
Proof. exact (EQ_MP (@lem4860858 A P s) (@lem4860857 A P s)). Qed.
Lemma lem4860872 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term7 A P s).
Proof. exact (@lem4860871 A P s). Qed.
Lemma lem4860873 {A : Type'} (P : type686 A) (s : A -> Prop) : (term8 A P s) = (term9 A P s).
Proof. exact (@lem4860872 A (term10 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860875 {A B : Type'} (f : A -> B) (y : A) : (term11 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4860876 {A : Type'} (f : type686 A) (y : A -> Prop) : (term12 A f y) = (f y).
Proof. exact (@lem4860875 (A -> Prop) Prop f y). Qed.
Lemma lem4860877 {A : Type'} (P : type686 A) (s : A -> Prop) : (term13 A P s) = (term14 A P s).
Proof. exact (@lem4860876 A (term10 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860878 {A : Type'} (P : type686 A) (s : A -> Prop) : (term15 A P s) = (term16 A P s).
Proof. exact (eq_refl (term15 A P s)). Qed.
Lemma lem4860879 {A : Type'} (P : type686 A) : (term17 A P) = (term10 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860878 A P s)). Qed.
Lemma lem4860880 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4860881 {A : Type'} (P : type686 A) (s : A -> Prop) : (term13 A P s) = (term14 A P s).
Proof. exact (MK_COMB (@lem4860879 A P) (@lem4860880 A s)). Qed.
Lemma lem4860882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4860883 {A : Type'} (P : type686 A) (s : A -> Prop) : (term18 A P s) = (term19 A P s).
Proof. exact (MK_COMB (@lem4860882) (@lem4860881 A P s)). Qed.
Lemma lem4860884 {A : Type'} (P : type686 A) (s : A -> Prop) : (term14 A P s) = (term20 A P s).
Proof. exact (eq_refl (term14 A P s)). Qed.
Lemma lem4860885 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term13 A P s) = (term14 A P s)) = ((term14 A P s) = (term20 A P s)).
Proof. exact (MK_COMB (@lem4860883 A P s) (@lem4860884 A P s)). Qed.
Lemma lem4860886 {A : Type'} (P : type686 A) (s : A -> Prop) : (term14 A P s) = (term20 A P s).
Proof. exact (EQ_MP (@lem4860885 A P s) (@lem4860877 A P s)). Qed.
Lemma lem4860887 {A : Type'} (P : type686 A) : (term21 A P) = (term22 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860886 A P s)). Qed.
Lemma lem4860888 {A : Type'} : (@INTERSECTION_OF A (@ARBITRARY A)) = (@INTERSECTION_OF A (@ARBITRARY A)).
Proof. exact (eq_refl (@INTERSECTION_OF A (@ARBITRARY A))). Qed.
Lemma lem4860889 {A : Type'} (P : type686 A) : (term23 A P) = (term24 A P).
Proof. exact (MK_COMB (@lem4860888 A) (@lem4860887 A P)). Qed.
Lemma lem4860890 {A : Type'} (s : A -> Prop) : (term1 A s) = (term1 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem4860891 {A : Type'} (P : type686 A) (s : A -> Prop) : (term9 A P s) = (term25 A P s).
Proof. exact (MK_COMB (@lem4860889 A P) (@lem4860890 A s)). Qed.
Lemma lem4860892 {A : Type'} (P : type686 A) (s : A -> Prop) : (term8 A P s) = (term25 A P s).
Proof. exact (TRANS (@lem4860873 A P s) (@lem4860891 A P s)). Qed.
Lemma lem4860893 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term26 A P s).
Proof. exact (eq_refl (term26 A P s)). Qed.
Lemma lem4860894 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (term8 A P s)) = ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (term25 A P s)).
Proof. exact (MK_COMB (@lem4860893 A P s) (@lem4860892 A P s)). Qed.
Lemma lem4860897 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860894 A P s)). Qed.
Lemma lem4860898 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4860899 {A : Type'} (P : type686 A) : (term29 A P) = (term30 A P).
Proof. exact (MK_COMB (@lem4860898 A) (@lem4860897 A P)). Qed.
Lemma lem4860904 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4860899 A P)). Qed.
Lemma lem4860905 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4860906 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (MK_COMB (@lem4860905 A) (@lem4860904 A)). Qed.
Lemma lem4860911 {A : Type'} : (term34 A) = (term33 A).
Proof. exact (SYM (@lem4860906 A)). Qed.
Lemma lem4860923 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4860849 A s) (@lem4860848 A s)). Qed.
Lemma lem4860924 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4860923 A s). Qed.
Lemma lem4860925 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4860926 {A : Type'} (P : type686 A) (s : A -> Prop) : (term20 A P s) = (P s).
Proof. exact (MK_COMB (@lem4860925 A P) (@lem4860924 A s)). Qed.
Lemma lem4860927 {A : Type'} (P : type686 A) : (term22 A P) = (term35 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860926 A P s)). Qed.
Lemma lem4860928 {A : Type'} (t : type686 A) : (term35 A t) = t.
Proof. exact (@lem4860853 (A -> Prop) Prop t). Qed.
Lemma lem4860929 {A : Type'} (P : type686 A) : (term35 A P) = P.
Proof. exact (@lem4860928 A P). Qed.
Lemma lem4860930 {A : Type'} (P : type686 A) : (term22 A P) = P.
Proof. exact (TRANS (@lem4860927 A P) (@lem4860929 A P)). Qed.
Lemma lem4860931 {A : Type'} : (@INTERSECTION_OF A (@ARBITRARY A)) = (@INTERSECTION_OF A (@ARBITRARY A)).
Proof. exact (eq_refl (@INTERSECTION_OF A (@ARBITRARY A))). Qed.
Lemma lem4860932 {A : Type'} (P : type686 A) : (term24 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4860931 A) (@lem4860930 A P)). Qed.
Lemma lem4860934 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (EQ_MP (@lem4860849 A s) (@lem4860848 A s)). Qed.
Lemma lem4860935 {A : Type'} (s : A -> Prop) : (term1 A s) = s.
Proof. exact (@lem4860934 A s). Qed.
Lemma lem4860936 {A : Type'} (P : type686 A) (s : A -> Prop) : (term25 A P s) = (@INTERSECTION_OF A (@ARBITRARY A) P s).
Proof. exact (MK_COMB (@lem4860932 A P) (@lem4860935 A s)). Qed.
Lemma lem4860937 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = (term26 A P s).
Proof. exact (eq_refl (term26 A P s)). Qed.
Lemma lem4860938 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (term25 A P s)) = ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (@INTERSECTION_OF A (@ARBITRARY A) P s)).
Proof. exact (MK_COMB (@lem4860937 A P s) (@lem4860936 A P s)). Qed.
Lemma lem4860940 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4860941 (x : Prop) : (x = x) = True.
Proof. exact (@lem4860940 Prop x). Qed.
Lemma lem4860942 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (@INTERSECTION_OF A (@ARBITRARY A) P s)) = True.
Proof. exact (@lem4860941 (@INTERSECTION_OF A (@ARBITRARY A) P s)). Qed.
Lemma lem4860943 {A : Type'} (P : type686 A) (s : A -> Prop) : ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (term25 A P s)) = True.
Proof. exact (TRANS (@lem4860938 A P s) (@lem4860942 A P s)). Qed.
Lemma lem4860944 {A : Type'} (P : type686 A) : (term28 A P) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4860943 A P s)). Qed.
Lemma lem4860945 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4860946 {A : Type'} (P : type686 A) : (term30 A P) = (term37 A).
Proof. exact (MK_COMB (@lem4860945 A) (@lem4860944 A P)). Qed.
Lemma lem4860948 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4860949 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem4860948 (A -> Prop) t). Qed.
Lemma lem4860950 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4860949 A True). Qed.
Lemma lem4860951 {A : Type'} (P : type686 A) : (term30 A P) = True.
Proof. exact (TRANS (@lem4860946 A P) (@lem4860950 A)). Qed.
Lemma lem4860952 {A : Type'} : (term32 A) = (term40 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4860951 A P)). Qed.
Lemma lem4860953 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4860954 {A : Type'} : (term34 A) = (term41 A).
Proof. exact (MK_COMB (@lem4860953 A) (@lem4860952 A)). Qed.
Lemma lem4860956 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4860957 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (@lem4860956 (type686 A) t). Qed.
Lemma lem4860958 {A : Type'} : (term41 A) = True.
Proof. exact (@lem4860957 A True). Qed.
Lemma lem4860959 {A : Type'} : (term34 A) = True.
Proof. exact (TRANS (@lem4860954 A) (@lem4860958 A)). Qed.
Lemma lem4860960 {A : Type'} : True = (term34 A).
Proof. exact (SYM (@lem4860959 A)). Qed.
Lemma lem4860961 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem4860960 A) (@lem0)). Qed.
Lemma lem4860962 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem4860911 A) (@lem4860961 A)). Qed.
