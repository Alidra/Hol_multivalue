Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_INTER_term_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_INTERS_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import INTERS_2_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4868862 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4868863 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4868864 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4868863 A x) (@lem4868862 A x)). Qed.
Lemma lem4868865 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4868870 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4868871 {A : Type'} (P : type686 A) (h1 : term3 A) : term4 A P.
Proof. exact (@lem4868870 A h1 P). Qed.
Lemma lem4868872 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4868873 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (EQ_MP (@lem4868872 A P) (@lem4868871 A P h1)). Qed.
Lemma lem4868874 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term6 A P u.
Proof. exact (@lem4868873 A P h1 u). Qed.
Lemma lem4868875 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4868876 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4868875 A P u) (@lem4868874 A P u h1)). Qed.
Lemma lem4868877 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term8 A u P.
Proof. exact (h1). Qed.
Lemma lem4868878 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) (h2 : term3 A) : term9 A P u.
Proof. exact (@lem4868876 A P u h2 (@lem4868877 A u P h1)). Qed.
Lemma lem4868879 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term10 A P u.
Proof. exact (fun h0 : term3 A => @lem4868878 A u P h1 h0). Qed.
Lemma lem4868880 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4868881 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) (h2 : term3 A) : term9 A P u.
Proof. exact (@lem4868879 A u P h1 (@lem4868880 A h2)). Qed.
Lemma lem4868882 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (fun h0 : term8 A u P => @lem4868881 A u P h0 h1). Qed.
Lemma lem4868883 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (fun u : type686 A => @lem4868882 A P u h1). Qed.
Lemma lem4868884 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (fun P : type686 A => @lem4868883 A P h1). Qed.
Lemma lem4868885 {A : Type'} : term11 A.
Proof. exact (fun h0 : term3 A => @lem4868884 A h0). Qed.
Lemma lem4868886 {A : Type'} : term3 A.
Proof. exact (@lem4868885 A (@lem4868861 A)). Qed.
Lemma lem4868887 {A : Type'} (P : type686 A) : term4 A P.
Proof. exact (@lem4868886 A P). Qed.
Lemma lem4868888 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4868889 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (EQ_MP (@lem4868888 A P) (@lem4868887 A P)). Qed.
Lemma lem4868890 {A : Type'} (P : type686 A) (u : type686 A) : term6 A P u.
Proof. exact (@lem4868889 A P u). Qed.
Lemma lem4868891 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4868893 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (term12 _87260 s t) = (@INTER _87260 s t)) : (term12 _87260 s t) = (@INTER _87260 s t).
Proof. exact (h1). Qed.
Lemma lem4868894 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (term12 _87260 s t) = (@INTER _87260 s t)) : (@INTER _87260 s t) = (term12 _87260 s t).
Proof. exact (SYM (@lem4868893 _87260 s t h1)). Qed.
Lemma lem4868895 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (@INTER _87260 s t) = (term12 _87260 s t)) : (@INTER _87260 s t) = (term12 _87260 s t).
Proof. exact (h1). Qed.
Lemma lem4868896 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) (h1 : (@INTER _87260 s t) = (term12 _87260 s t)) : (term12 _87260 s t) = (@INTER _87260 s t).
Proof. exact (SYM (@lem4868895 _87260 s t h1)). Qed.
Lemma lem4868897 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : ((term12 _87260 s t) = (@INTER _87260 s t)) = ((@INTER _87260 s t) = (term12 _87260 s t)).
Proof. exact (prop_ext (fun h1 : (term12 _87260 s t) = (@INTER _87260 s t) => @lem4868894 _87260 s t h1) (fun h1 : (@INTER _87260 s t) = (term12 _87260 s t) => @lem4868896 _87260 s t h1)). Qed.
Lemma lem4868899 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : term13 _111835 s P t) : term13 _111835 s P t.
Proof. exact (h1). Qed.
Lemma lem4868900 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t.
Proof. exact (h1). Qed.
Lemma lem4868901 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s.
Proof. exact (h1). Qed.
Lemma lem4868903 {_87260 : Type'} (s : _87260 -> Prop) (t : _87260 -> Prop) : (@INTER _87260 s t) = (term12 _87260 s t).
Proof. exact (EQ_MP (@lem4868897 _87260 s t) (@lem3356566 _87260 s t)). Qed.
Lemma lem4868904 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) : (@INTER _111835 s t) = (term12 _111835 s t).
Proof. exact (@lem4868903 _111835 s t). Qed.
Lemma lem4868905 {_111835 : Type'} (P : type686 _111835) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P) = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P).
Proof. exact (eq_refl (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P)). Qed.
Lemma lem4868906 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) (t : _111835 -> Prop) : (term14 _111835 P s t) = (term15 _111835 P s t).
Proof. exact (MK_COMB (@lem4868905 _111835 P) (@lem4868904 _111835 s t)). Qed.
Lemma lem4868907 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) (t : _111835 -> Prop) : (term15 _111835 P s t) = (term14 _111835 P s t).
Proof. exact (SYM (@lem4868906 _111835 P s t)). Qed.
Lemma lem4868909 {A : Type'} (P : type686 A) (u : type686 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4868891 A P u) (@lem4868890 A P u)). Qed.
Lemma lem4868910 {_111835 : Type'} (P : type686 _111835) (u : type686 _111835) : term7 _111835 P u.
Proof. exact (@lem4868909 _111835 P u). Qed.
Lemma lem4868911 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) (t : _111835 -> Prop) : term16 _111835 P s t.
Proof. exact (@lem4868910 _111835 P (term17 _111835 s t)). Qed.
Lemma lem4868912 {_83983 : Type'} (P : _83983 -> Prop) : term18 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem4868913 {_83983 : Type'} (P : _83983 -> Prop) : (term18 _83983 P) = (term19 _83983 P).
Proof. exact (eq_refl (term18 _83983 P)). Qed.
Lemma lem4868914 {_83983 : Type'} (P : _83983 -> Prop) : term19 _83983 P.
Proof. exact (EQ_MP (@lem4868913 _83983 P) (@lem4868912 _83983 P)). Qed.
Lemma lem4868915 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term20 _83983 P a.
Proof. exact (@lem4868914 _83983 P a). Qed.
Lemma lem4868916 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term20 _83983 P a) = (term21 _83983 a P).
Proof. exact (eq_refl (term20 _83983 P a)). Qed.
Lemma lem4868917 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term21 _83983 a P.
Proof. exact (EQ_MP (@lem4868916 _83983 a P) (@lem4868915 _83983 P a)). Qed.
Lemma lem4868918 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term22 _83983 a P s.
Proof. exact (@lem4868917 _83983 a P s). Qed.
Lemma lem4868919 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term22 _83983 a P s) = ((term23 _83983 a s P) = (term24 _83983 a s P)).
Proof. exact (eq_refl (term22 _83983 a P s)). Qed.
Lemma lem4868924 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) = ((@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) = True).
Proof. exact (@lem7 (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s)). Qed.
Lemma lem4868926 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) = ((@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) = True).
Proof. exact (@lem7 (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t)). Qed.
Lemma lem4868929 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4868919 _83983 a s P) (@lem4868918 _83983 a P s)). Qed.
Lemma lem4868930 {_111835 : Type'} (a : _111835 -> Prop) (s : type686 _111835) (P : type686 _111835) : (term25 _111835 a s P) = (term26 _111835 a s P).
Proof. exact (@lem4868929 (_111835 -> Prop) a s P). Qed.
Lemma lem4868931 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) : (term27 _111835 s t P) = (term28 _111835 s t P).
Proof. exact (@lem4868930 _111835 s (@INSERT (_111835 -> Prop) t (@EMPTY (_111835 -> Prop))) (term29 _111835 P)). Qed.
Lemma lem4868932 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term30 _111835 P s') = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s').
Proof. exact (eq_refl (term30 _111835 P s')). Qed.
Lemma lem4868933 {_111835 : Type'} (s' : _111835 -> Prop) (s : _111835 -> Prop) (t : _111835 -> Prop) : (term31 _111835 s' s t) = (term31 _111835 s' s t).
Proof. exact (eq_refl (term31 _111835 s' s t)). Qed.
Lemma lem4868934 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) (s' : _111835 -> Prop) : (term32 _111835 s t P s') = (term33 _111835 s t P s').
Proof. exact (MK_COMB (@lem4868933 _111835 s' s t) (@lem4868932 _111835 P s')). Qed.
Lemma lem4868935 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) : (term34 _111835 s t P) = (term35 _111835 s t P).
Proof. exact (fun_ext (fun s' : _111835 -> Prop => @lem4868934 _111835 s t P s')). Qed.
Lemma lem4868936 {_111835 : Type'} : (@all (_111835 -> Prop)) = (@all (_111835 -> Prop)).
Proof. exact (eq_refl (@all (_111835 -> Prop))). Qed.
Lemma lem4868937 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) : (term27 _111835 s t P) = (term36 _111835 s t P).
Proof. exact (MK_COMB (@lem4868936 _111835) (@lem4868935 _111835 s t P)). Qed.
Lemma lem4868938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868939 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) : (term37 _111835 s t P) = (term38 _111835 s t P).
Proof. exact (MK_COMB (@lem4868938) (@lem4868937 _111835 s t P)). Qed.
Lemma lem4868940 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) : (term30 _111835 P s) = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s).
Proof. exact (eq_refl (term30 _111835 P s)). Qed.
Lemma lem4868941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868942 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) : (term39 _111835 P s) = (term40 _111835 P s).
Proof. exact (MK_COMB (@lem4868941) (@lem4868940 _111835 P s)). Qed.
Lemma lem4868943 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term30 _111835 P s') = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s').
Proof. exact (eq_refl (term30 _111835 P s')). Qed.
Lemma lem4868944 {_111835 : Type'} (s' : _111835 -> Prop) (t : _111835 -> Prop) : (term41 _111835 s' t) = (term41 _111835 s' t).
Proof. exact (eq_refl (term41 _111835 s' t)). Qed.
Lemma lem4868945 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) (s' : _111835 -> Prop) : (term42 _111835 t P s') = (term43 _111835 t P s').
Proof. exact (MK_COMB (@lem4868944 _111835 s' t) (@lem4868943 _111835 P s')). Qed.
Lemma lem4868946 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term44 _111835 t P) = (term45 _111835 t P).
Proof. exact (fun_ext (fun s' : _111835 -> Prop => @lem4868945 _111835 t P s')). Qed.
Lemma lem4868947 {_111835 : Type'} : (@all (_111835 -> Prop)) = (@all (_111835 -> Prop)).
Proof. exact (eq_refl (@all (_111835 -> Prop))). Qed.
Lemma lem4868948 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term46 _111835 t P) = (term47 _111835 t P).
Proof. exact (MK_COMB (@lem4868947 _111835) (@lem4868946 _111835 t P)). Qed.
Lemma lem4868949 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) : (term28 _111835 s t P) = (term48 _111835 s t P).
Proof. exact (MK_COMB (@lem4868942 _111835 P s) (@lem4868948 _111835 t P)). Qed.
Lemma lem4868950 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) : ((term27 _111835 s t P) = (term28 _111835 s t P)) = ((term36 _111835 s t P) = (term48 _111835 s t P)).
Proof. exact (MK_COMB (@lem4868939 _111835 s t P) (@lem4868949 _111835 s t P)). Qed.
Lemma lem4868951 {_111835 : Type'} (s : _111835 -> Prop) (t : _111835 -> Prop) (P : type686 _111835) : (term36 _111835 s t P) = (term48 _111835 s t P).
Proof. exact (EQ_MP (@lem4868950 _111835 s t P) (@lem4868931 _111835 s t P)). Qed.
Lemma lem4868955 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) = True.
Proof. exact (EQ_MP (@lem4868924 _111835 P s) (@lem4868901 _111835 P s h1)). Qed.
Lemma lem4868956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868957 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) : (term40 _111835 P s) = (and True).
Proof. exact (MK_COMB (@lem4868956) (@lem4868955 _111835 P s h1)). Qed.
Lemma lem4868959 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4868919 _83983 a s P) (@lem4868918 _83983 a P s)). Qed.
Lemma lem4868960 {_111835 : Type'} (a : _111835 -> Prop) (s : type686 _111835) (P : type686 _111835) : (term25 _111835 a s P) = (term26 _111835 a s P).
Proof. exact (@lem4868959 (_111835 -> Prop) a s P). Qed.
Lemma lem4868961 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term46 _111835 t P) = (term49 _111835 t P).
Proof. exact (@lem4868960 _111835 t (@EMPTY (_111835 -> Prop)) (term29 _111835 P)). Qed.
Lemma lem4868962 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term30 _111835 P s') = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s').
Proof. exact (eq_refl (term30 _111835 P s')). Qed.
Lemma lem4868963 {_111835 : Type'} (s' : _111835 -> Prop) (t : _111835 -> Prop) : (term41 _111835 s' t) = (term41 _111835 s' t).
Proof. exact (eq_refl (term41 _111835 s' t)). Qed.
Lemma lem4868964 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) (s' : _111835 -> Prop) : (term42 _111835 t P s') = (term43 _111835 t P s').
Proof. exact (MK_COMB (@lem4868963 _111835 s' t) (@lem4868962 _111835 P s')). Qed.
Lemma lem4868965 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term44 _111835 t P) = (term45 _111835 t P).
Proof. exact (fun_ext (fun s' : _111835 -> Prop => @lem4868964 _111835 t P s')). Qed.
Lemma lem4868966 {_111835 : Type'} : (@all (_111835 -> Prop)) = (@all (_111835 -> Prop)).
Proof. exact (eq_refl (@all (_111835 -> Prop))). Qed.
Lemma lem4868967 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term46 _111835 t P) = (term47 _111835 t P).
Proof. exact (MK_COMB (@lem4868966 _111835) (@lem4868965 _111835 t P)). Qed.
Lemma lem4868968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868969 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term50 _111835 t P) = (term51 _111835 t P).
Proof. exact (MK_COMB (@lem4868968) (@lem4868967 _111835 t P)). Qed.
Lemma lem4868970 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) : (term30 _111835 P t) = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t).
Proof. exact (eq_refl (term30 _111835 P t)). Qed.
Lemma lem4868971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868972 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) : (term39 _111835 P t) = (term40 _111835 P t).
Proof. exact (MK_COMB (@lem4868971) (@lem4868970 _111835 P t)). Qed.
Lemma lem4868973 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term30 _111835 P s') = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s').
Proof. exact (eq_refl (term30 _111835 P s')). Qed.
Lemma lem4868974 {_111835 : Type'} (s' : _111835 -> Prop) : (term52 _111835 s') = (term52 _111835 s').
Proof. exact (eq_refl (term52 _111835 s')). Qed.
Lemma lem4868975 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term53 _111835 P s') = (term54 _111835 P s').
Proof. exact (MK_COMB (@lem4868974 _111835 s') (@lem4868973 _111835 P s')). Qed.
Lemma lem4868976 {_111835 : Type'} (P : type686 _111835) : (term55 _111835 P) = (term56 _111835 P).
Proof. exact (fun_ext (fun s' : _111835 -> Prop => @lem4868975 _111835 P s')). Qed.
Lemma lem4868977 {_111835 : Type'} : (@all (_111835 -> Prop)) = (@all (_111835 -> Prop)).
Proof. exact (eq_refl (@all (_111835 -> Prop))). Qed.
Lemma lem4868978 {_111835 : Type'} (P : type686 _111835) : (term57 _111835 P) = (term58 _111835 P).
Proof. exact (MK_COMB (@lem4868977 _111835) (@lem4868976 _111835 P)). Qed.
Lemma lem4868979 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term49 _111835 t P) = (term59 _111835 t P).
Proof. exact (MK_COMB (@lem4868972 _111835 P t) (@lem4868978 _111835 P)). Qed.
Lemma lem4868980 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : ((term46 _111835 t P) = (term49 _111835 t P)) = ((term47 _111835 t P) = (term59 _111835 t P)).
Proof. exact (MK_COMB (@lem4868969 _111835 t P) (@lem4868979 _111835 t P)). Qed.
Lemma lem4868981 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) : (term47 _111835 t P) = (term59 _111835 t P).
Proof. exact (EQ_MP (@lem4868980 _111835 t P) (@lem4868961 _111835 t P)). Qed.
Lemma lem4868985 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) = True.
Proof. exact (EQ_MP (@lem4868926 _111835 P t) (@lem4868900 _111835 P t h1)). Qed.
Lemma lem4868986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868987 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term40 _111835 P t) = (and True).
Proof. exact (MK_COMB (@lem4868986) (@lem4868985 _111835 P t h1)). Qed.
Lemma lem4868994 {_111835 : Type'} (P : type686 _111835) : (term58 _111835 P) = (term58 _111835 P).
Proof. exact (eq_refl (term58 _111835 P)). Qed.
Lemma lem4868995 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term59 _111835 t P) = (term60 _111835 P).
Proof. exact (MK_COMB (@lem4868987 _111835 P t h1) (@lem4868994 _111835 P)). Qed.
Lemma lem4868997 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4868998 {_111835 : Type'} (P : type686 _111835) : (term60 _111835 P) = (term58 _111835 P).
Proof. exact (@lem4868997 (term58 _111835 P)). Qed.
Lemma lem4869005 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term59 _111835 t P) = (term58 _111835 P).
Proof. exact (TRANS (@lem4868995 _111835 P t h1) (@lem4868998 _111835 P)). Qed.
Lemma lem4869006 {_111835 : Type'} (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term47 _111835 t P) = (term58 _111835 P).
Proof. exact (TRANS (@lem4868981 _111835 t P) (@lem4869005 _111835 P t h1)). Qed.
Lemma lem4869007 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term48 _111835 s t P) = (term60 _111835 P).
Proof. exact (MK_COMB (@lem4868957 _111835 P s h1) (@lem4869006 _111835 P t h2)). Qed.
Lemma lem4869009 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4869010 {_111835 : Type'} (P : type686 _111835) : (term60 _111835 P) = (term58 _111835 P).
Proof. exact (@lem4869009 (term58 _111835 P)). Qed.
Lemma lem4869017 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term48 _111835 s t P) = (term58 _111835 P).
Proof. exact (TRANS (@lem4869007 _111835 s P t h1 h2) (@lem4869010 _111835 P)). Qed.
Lemma lem4869018 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term36 _111835 s t P) = (term58 _111835 P).
Proof. exact (TRANS (@lem4868951 _111835 s t P) (@lem4869017 _111835 s P t h1 h2)). Qed.
Lemma lem4869019 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (term58 _111835 P) = (term36 _111835 s t P).
Proof. exact (SYM (@lem4869018 _111835 s P t h1 h2)). Qed.
Lemma lem4869027 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4868865 A x (@lem4868864 A x)). Qed.
Lemma lem4869028 {_111835 : Type'} (x : _111835 -> Prop) : (@IN (_111835 -> Prop) x (@EMPTY (_111835 -> Prop))) = False.
Proof. exact (@lem4869027 (_111835 -> Prop) x). Qed.
Lemma lem4869029 {_111835 : Type'} (s' : _111835 -> Prop) : (@IN (_111835 -> Prop) s' (@EMPTY (_111835 -> Prop))) = False.
Proof. exact (@lem4869028 _111835 s'). Qed.
Lemma lem4869030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4869031 {_111835 : Type'} (s' : _111835 -> Prop) : (term52 _111835 s') = (imp False).
Proof. exact (MK_COMB (@lem4869030) (@lem4869029 _111835 s')). Qed.
Lemma lem4869032 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s') = (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s').
Proof. exact (eq_refl (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s')). Qed.
Lemma lem4869033 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term54 _111835 P s') = (term61 _111835 P s').
Proof. exact (MK_COMB (@lem4869031 _111835 s') (@lem4869032 _111835 P s')). Qed.
Lemma lem4869035 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4869036 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term61 _111835 P s') = True.
Proof. exact (@lem4869035 (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s')). Qed.
Lemma lem4869037 {_111835 : Type'} (P : type686 _111835) (s' : _111835 -> Prop) : (term54 _111835 P s') = True.
Proof. exact (TRANS (@lem4869033 _111835 P s') (@lem4869036 _111835 P s')). Qed.
Lemma lem4869038 {_111835 : Type'} (P : type686 _111835) : (term56 _111835 P) = (term62 _111835).
Proof. exact (fun_ext (fun s' : _111835 -> Prop => @lem4869037 _111835 P s')). Qed.
Lemma lem4869039 {_111835 : Type'} : (@all (_111835 -> Prop)) = (@all (_111835 -> Prop)).
Proof. exact (eq_refl (@all (_111835 -> Prop))). Qed.
Lemma lem4869040 {_111835 : Type'} (P : type686 _111835) : (term58 _111835 P) = (term63 _111835).
Proof. exact (MK_COMB (@lem4869039 _111835) (@lem4869038 _111835 P)). Qed.
Lemma lem4869042 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4869043 {_111835 : Type'} (t : Prop) : (term65 _111835 t) = t.
Proof. exact (@lem4869042 (_111835 -> Prop) t). Qed.
Lemma lem4869044 {_111835 : Type'} : (term63 _111835) = True.
Proof. exact (@lem4869043 _111835 True). Qed.
Lemma lem4869045 {_111835 : Type'} (P : type686 _111835) : (term58 _111835 P) = True.
Proof. exact (TRANS (@lem4869040 _111835 P) (@lem4869044 _111835)). Qed.
Lemma lem4869046 {_111835 : Type'} (P : type686 _111835) : True = (term58 _111835 P).
Proof. exact (SYM (@lem4869045 _111835 P)). Qed.
Lemma lem4869047 {_111835 : Type'} (P : type686 _111835) : term58 _111835 P.
Proof. exact (EQ_MP (@lem4869046 _111835 P) (@lem0)). Qed.
Lemma lem4869048 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : term36 _111835 s t P.
Proof. exact (EQ_MP (@lem4869019 _111835 s P t h1 h2) (@lem4869047 _111835 P)). Qed.
Lemma lem4869049 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : term15 _111835 P s t.
Proof. exact (@lem4868911 _111835 P s t (@lem4869048 _111835 s P t h1 h2)). Qed.
Lemma lem4869050 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : term14 _111835 P s t.
Proof. exact (EQ_MP (@lem4868907 _111835 P s t) (@lem4869049 _111835 s P t h1 h2)). Qed.
Lemma lem4869051 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : term13 _111835 s P t) : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t.
Proof. exact (proj2 (@lem4868899 _111835 s P t h1)). Qed.
Lemma lem4869052 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : term13 _111835 s P t) : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s.
Proof. exact (proj1 (@lem4868899 _111835 s P t h1)). Qed.
Lemma lem4869053 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) = (term14 _111835 P s t).
Proof. exact (prop_ext (fun h3 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t => @lem4869050 _111835 s P t h1 h2) (fun h3 : term14 _111835 P s t => @lem4868900 _111835 P t h2)). Qed.
Lemma lem4869054 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : term14 _111835 P s t.
Proof. exact (EQ_MP (@lem4869053 _111835 s P t h1 h2) (@lem4868900 _111835 P t h2)). Qed.
Lemma lem4869055 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) = (term14 _111835 P s t).
Proof. exact (prop_ext (fun h3 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s => @lem4869054 _111835 s P t h1 h2) (fun h3 : term14 _111835 P s t => @lem4868901 _111835 P s h1)). Qed.
Lemma lem4869056 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) : term14 _111835 P s t.
Proof. exact (EQ_MP (@lem4869055 _111835 s P t h1 h2) (@lem4868901 _111835 P s h1)). Qed.
Lemma lem4869057 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) (s : _111835 -> Prop) (h1 : term13 _111835 s P t) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P t) = (term14 _111835 P s t).
Proof. exact (prop_ext (fun h3 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P t => @lem4869056 _111835 s P t h2 h3) (fun h3 : term14 _111835 P s t => @lem4869051 _111835 s P t h1)). Qed.
Lemma lem4869058 {_111835 : Type'} (t : _111835 -> Prop) (P : type686 _111835) (s : _111835 -> Prop) (h1 : term13 _111835 s P t) (h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) : term14 _111835 P s t.
Proof. exact (EQ_MP (@lem4869057 _111835 t P s h1 h2) (@lem4869051 _111835 s P t h1)). Qed.
Lemma lem4869059 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : term13 _111835 s P t) : (@INTERSECTION_OF _111835 (@ARBITRARY _111835) P s) = (term14 _111835 P s t).
Proof. exact (prop_ext (fun h2 : @INTERSECTION_OF _111835 (@ARBITRARY _111835) P s => @lem4869058 _111835 t P s h1 h2) (fun h2 : term14 _111835 P s t => @lem4869052 _111835 s P t h1)). Qed.
Lemma lem4869060 {_111835 : Type'} (s : _111835 -> Prop) (P : type686 _111835) (t : _111835 -> Prop) (h1 : term13 _111835 s P t) : term14 _111835 P s t.
Proof. exact (EQ_MP (@lem4869059 _111835 s P t h1) (@lem4869052 _111835 s P t h1)). Qed.
Lemma lem4869061 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) (t : _111835 -> Prop) : term66 _111835 P s t.
Proof. exact (fun h0 : term13 _111835 s P t => @lem4869060 _111835 s P t h0). Qed.
Lemma lem4869066 {_111835 : Type'} (P : type686 _111835) (s : _111835 -> Prop) : term67 _111835 P s.
Proof. exact (fun t : _111835 -> Prop => @lem4869061 _111835 P s t). Qed.
Lemma lem4869071 {_111835 : Type'} (P : type686 _111835) : term68 _111835 P.
Proof. exact (fun s : _111835 -> Prop => @lem4869066 _111835 P s). Qed.
Lemma lem4869076 {_111835 : Type'} : term69 _111835.
Proof. exact (fun P : type686 _111835 => @lem4869071 _111835 P). Qed.
