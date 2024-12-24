Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_MULTICOUNT_term_abbrevs.
Require Import EQ_TRANS_spec.
Require Import MULT_AC_spec.
Require Import SUM_CONST_spec.
Require Import SUM_MULTICOUNT_GEN_spec.
Require Import thm0_spec.
Require Import thm1340396_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7158871 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7158872 {A B : Type'} (R : type1413 A B) (h1 : term0 A B) : term1 A B R.
Proof. exact (@lem7158871 A B h1 R). Qed.
Lemma lem7158873 {A B : Type'} (R : type1413 A B) : (term1 A B R) = (term2 A B R).
Proof. exact (eq_refl (term1 A B R)). Qed.
Lemma lem7158874 {A B : Type'} (R : type1413 A B) (h1 : term0 A B) : term2 A B R.
Proof. exact (EQ_MP (@lem7158873 A B R) (@lem7158872 A B R h1)). Qed.
Lemma lem7158875 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (h1 : term0 A B) : term3 A B R s.
Proof. exact (@lem7158874 A B R h1 s). Qed.
Lemma lem7158876 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term3 A B R s) = (term4 A B s R).
Proof. exact (eq_refl (term3 A B R s)). Qed.
Lemma lem7158877 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (h1 : term0 A B) : term4 A B s R.
Proof. exact (EQ_MP (@lem7158876 A B s R) (@lem7158875 A B R s h1)). Qed.
Lemma lem7158878 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term0 A B) : term5 A B s R t.
Proof. exact (@lem7158877 A B s R h1 t). Qed.
Lemma lem7158879 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term5 A B s R t) = (term6 A B s R t).
Proof. exact (eq_refl (term5 A B s R t)). Qed.
Lemma lem7158880 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term0 A B) : term6 A B s R t.
Proof. exact (EQ_MP (@lem7158879 A B s R t) (@lem7158878 A B s R t h1)). Qed.
Lemma lem7158881 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (h1 : term0 A B) : term7 A B s R t k.
Proof. exact (@lem7158880 A B s R t h1 k). Qed.
Lemma lem7158882 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term7 A B s R t k) = (term8 A B s R t k).
Proof. exact (eq_refl (term7 A B s R t k)). Qed.
Lemma lem7158883 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (h1 : term0 A B) : term8 A B s R t k.
Proof. exact (EQ_MP (@lem7158882 A B s R t k) (@lem7158881 A B s R t k h1)). Qed.
Lemma lem7158884 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term9 A B t s R k) : term9 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem7158885 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term0 A B) (h2 : term9 A B t s R k) : (term10 A B s t R) = (term11 B t k).
Proof. exact (@lem7158883 A B s R t k h1 (@lem7158884 A B t s R k h2)). Qed.
Lemma lem7158886 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term9 A B t s R k) : term12 A B s R t k.
Proof. exact (fun h0 : term0 A B => @lem7158885 A B t s R k h0 h1). Qed.
Lemma lem7158887 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7158888 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term0 A B) (h2 : term9 A B t s R k) : (term10 A B s t R) = (term11 B t k).
Proof. exact (@lem7158886 A B t s R k h2 (@lem7158887 A B h1)). Qed.
Lemma lem7158889 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (h1 : term0 A B) : term8 A B s R t k.
Proof. exact (fun h0 : term9 A B t s R k => @lem7158888 A B t s R k h1 h0). Qed.
Lemma lem7158890 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term0 A B) : term6 A B s R t.
Proof. exact (fun k : B -> nat => @lem7158889 A B s R t k h1). Qed.
Lemma lem7158891 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (h1 : term0 A B) : term4 A B s R.
Proof. exact (fun t : B -> Prop => @lem7158890 A B s R t h1). Qed.
Lemma lem7158892 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term13 A B s.
Proof. exact (fun R : type1413 A B => @lem7158891 A B s R h1). Qed.
Lemma lem7158893 {A B : Type'} (h1 : term0 A B) : term14 A B.
Proof. exact (fun s : A -> Prop => @lem7158892 A B s h1). Qed.
Lemma lem7158894 {A B : Type'} : term15 A B.
Proof. exact (fun h0 : term0 A B => @lem7158893 A B h0). Qed.
Lemma lem7158895 {A B : Type'} : term14 A B.
Proof. exact (@lem7158894 A B (@lem7158866 A B)). Qed.
Lemma lem7158896 {A B : Type'} (s : A -> Prop) : term16 A B s.
Proof. exact (@lem7158895 A B s). Qed.
Lemma lem7158897 {A B : Type'} (s : A -> Prop) : (term16 A B s) = (term13 A B s).
Proof. exact (eq_refl (term16 A B s)). Qed.
Lemma lem7158898 {A B : Type'} (s : A -> Prop) : term13 A B s.
Proof. exact (EQ_MP (@lem7158897 A B s) (@lem7158896 A B s)). Qed.
Lemma lem7158899 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term17 A B s R.
Proof. exact (@lem7158898 A B s R). Qed.
Lemma lem7158900 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term17 A B s R) = (term4 A B s R).
Proof. exact (eq_refl (term17 A B s R)). Qed.
Lemma lem7158901 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term4 A B s R.
Proof. exact (EQ_MP (@lem7158900 A B s R) (@lem7158899 A B s R)). Qed.
Lemma lem7158902 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term5 A B s R t.
Proof. exact (@lem7158901 A B s R t). Qed.
Lemma lem7158903 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term5 A B s R t) = (term6 A B s R t).
Proof. exact (eq_refl (term5 A B s R t)). Qed.
Lemma lem7158904 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term6 A B s R t.
Proof. exact (EQ_MP (@lem7158903 A B s R t) (@lem7158902 A B s R t)). Qed.
Lemma lem7158905 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term7 A B s R t k.
Proof. exact (@lem7158904 A B s R t k). Qed.
Lemma lem7158906 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term7 A B s R t k) = (term8 A B s R t k).
Proof. exact (eq_refl (term7 A B s R t k)). Qed.
Lemma lem7158908 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem7158909 {A : Type'} (x : A) (h1 : term18 A) : term19 A x.
Proof. exact (@lem7158908 A h1 x). Qed.
Lemma lem7158910 {A : Type'} (x : A) : (term19 A x) = (term20 A x).
Proof. exact (eq_refl (term19 A x)). Qed.
Lemma lem7158911 {A : Type'} (x : A) (h1 : term18 A) : term20 A x.
Proof. exact (EQ_MP (@lem7158910 A x) (@lem7158909 A x h1)). Qed.
Lemma lem7158912 {A : Type'} (x : A) (y : A) (h1 : term18 A) : term21 A x y.
Proof. exact (@lem7158911 A x h1 y). Qed.
Lemma lem7158913 {A : Type'} (y : A) (x : A) : (term21 A x y) = (term22 A y x).
Proof. exact (eq_refl (term21 A x y)). Qed.
Lemma lem7158914 {A : Type'} (y : A) (x : A) (h1 : term18 A) : term22 A y x.
Proof. exact (EQ_MP (@lem7158913 A y x) (@lem7158912 A x y h1)). Qed.
Lemma lem7158915 {A : Type'} (y : A) (x : A) (z : A) (h1 : term18 A) : term23 A y x z.
Proof. exact (@lem7158914 A y x h1 z). Qed.
Lemma lem7158916 {A : Type'} (y : A) (x : A) (z : A) : (term23 A y x z) = (term24 A y x z).
Proof. exact (eq_refl (term23 A y x z)). Qed.
Lemma lem7158917 {A : Type'} (y : A) (x : A) (z : A) (h1 : term18 A) : term24 A y x z.
Proof. exact (EQ_MP (@lem7158916 A y x z) (@lem7158915 A y x z h1)). Qed.
Lemma lem7158918 {A : Type'} (x : A) (y : A) (z : A) (h1 : term25 A x y z) : term25 A x y z.
Proof. exact (h1). Qed.
Lemma lem7158919 {A : Type'} (x : A) (y : A) (z : A) (h1 : term18 A) (h2 : term25 A x y z) : x = z.
Proof. exact (@lem7158917 A y x z h1 (@lem7158918 A x y z h2)). Qed.
Lemma lem7158920 {A : Type'} (x : A) (y : A) (z : A) (h1 : term25 A x y z) : term26 A x z.
Proof. exact (fun h0 : term18 A => @lem7158919 A x y z h0 h1). Qed.
Lemma lem7158921 {A : Type'} (x : A) (z : A) (h1 : term27 A x z) : term27 A x z.
Proof. exact (h1). Qed.
Lemma lem7158922 {A : Type'} (x : A) (z : A) (h1 : term27 A x z) : term26 A x z.
Proof. exact (ex_elim (@lem7158921 A x z h1) (fun y : A => fun h0 : term28 A x z y => @lem7158920 A x y z h0)). Qed.
Lemma lem7158923 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem7158924 {A : Type'} (x : A) (z : A) (h1 : term18 A) (h2 : term27 A x z) : x = z.
Proof. exact (@lem7158922 A x z h2 (@lem7158923 A h1)). Qed.
Lemma lem7158925 {A : Type'} (x : A) (z : A) (h1 : term18 A) : term29 A x z.
Proof. exact (fun h0 : term27 A x z => @lem7158924 A x z h1 h0). Qed.
Lemma lem7158926 {A : Type'} (x : A) (h1 : term18 A) : term30 A x.
Proof. exact (fun z : A => @lem7158925 A x z h1). Qed.
Lemma lem7158927 {A : Type'} (h1 : term18 A) : term31 A.
Proof. exact (fun x : A => @lem7158926 A x h1). Qed.
Lemma lem7158928 {A : Type'} : term32 A.
Proof. exact (fun h0 : term18 A => @lem7158927 A h0). Qed.
Lemma lem7158929 {A : Type'} : term31 A.
Proof. exact (@lem7158928 A (@lem403 A)). Qed.
Lemma lem7158930 {A : Type'} (x : A) : term33 A x.
Proof. exact (@lem7158929 A x). Qed.
Lemma lem7158931 {A : Type'} (x : A) : (term33 A x) = (term30 A x).
Proof. exact (eq_refl (term33 A x)). Qed.
Lemma lem7158932 {A : Type'} (x : A) : term30 A x.
Proof. exact (EQ_MP (@lem7158931 A x) (@lem7158930 A x)). Qed.
Lemma lem7158933 {A : Type'} (x : A) (z : A) : term34 A x z.
Proof. exact (@lem7158932 A x z). Qed.
Lemma lem7158934 {A : Type'} (x : A) (z : A) : (term34 A x z) = (term29 A x z).
Proof. exact (eq_refl (term34 A x z)). Qed.
Lemma lem7158936 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : term35 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem7158937 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term36 A B t s R k) : term36 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem7158938 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7158939 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : term37 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem7158940 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem7158942 {A : Type'} (x : A) (z : A) : term29 A x z.
Proof. exact (EQ_MP (@lem7158934 A x z) (@lem7158933 A x z)). Qed.
Lemma lem7158943 (x : real) (z : real) : term38 x z.
Proof. exact (@lem7158942 real x z). Qed.
Lemma lem7158944 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) : term39 A B s R k t.
Proof. exact (@lem7158943 (term10 A B s t R) (term40 B k t)). Qed.
Lemma lem7158946 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term8 A B s R t k.
Proof. exact (EQ_MP (@lem7158906 A B s R t k) (@lem7158905 A B s R t k)). Qed.
Lemma lem7158947 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term8 A B s R t k.
Proof. exact (@lem7158946 A B s R t k). Qed.
Lemma lem7158948 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : term41 A B s R t k.
Proof. exact (@lem7158947 A B s R t (term42 B k)). Qed.
Lemma lem7158949 {B : Type'} (j : B) (k : nat) : (term43 B k j) = k.
Proof. exact (eq_refl (term43 B k j)). Qed.
Lemma lem7158950 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term44 A B s R j) = (term44 A B s R j).
Proof. exact (eq_refl (term44 A B s R j)). Qed.
Lemma lem7158951 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : ((term45 A B s R j) = (term43 B k j)) = ((term45 A B s R j) = k).
Proof. exact (MK_COMB (@lem7158950 A B s R j) (@lem7158949 B j k)). Qed.
Lemma lem7158952 {B : Type'} (j : B) (t : B -> Prop) : (term46 B j t) = (term46 B j t).
Proof. exact (eq_refl (term46 B j t)). Qed.
Lemma lem7158953 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : (term47 A B t s R k j) = (term48 A B t s R j k).
Proof. exact (MK_COMB (@lem7158952 B j t) (@lem7158951 A B s R j k)). Qed.
Lemma lem7158954 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term49 A B t s R k) = (term50 A B t s R k).
Proof. exact (fun_ext (fun j : B => @lem7158953 A B t s R j k)). Qed.
Lemma lem7158955 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7158956 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term51 A B t s R k) = (term37 A B t s R k).
Proof. exact (MK_COMB (@lem7158955 B) (@lem7158954 A B t s R k)). Qed.
Lemma lem7158957 {B : Type'} (t : B -> Prop) : (term52 B t) = (term52 B t).
Proof. exact (eq_refl (term52 B t)). Qed.
Lemma lem7158958 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term53 A B t s R k) = (term36 A B t s R k).
Proof. exact (MK_COMB (@lem7158957 B t) (@lem7158956 A B t s R k)). Qed.
Lemma lem7158959 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem7158960 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term54 A B t s R k) = (term35 A B t s R k).
Proof. exact (MK_COMB (@lem7158959 A s) (@lem7158958 A B t s R k)). Qed.
Lemma lem7158961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7158962 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term55 A B t s R k) = (term56 A B t s R k).
Proof. exact (MK_COMB (@lem7158961) (@lem7158960 A B t s R k)). Qed.
Lemma lem7158963 {B : Type'} (i : B) (k : nat) : (term43 B k i) = k.
Proof. exact (eq_refl (term43 B k i)). Qed.
Lemma lem7158964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7158965 {B : Type'} (i : B) (k : nat) : (term57 B k i) = (real_of_num k).
Proof. exact (MK_COMB (@lem7158964) (@lem7158963 B i k)). Qed.
Lemma lem7158966 {B : Type'} (k : nat) : (term58 B k) = (term59 B k).
Proof. exact (fun_ext (fun i : B => @lem7158965 B i k)). Qed.
Lemma lem7158967 {B : Type'} (t : B -> Prop) : (@sum B t) = (@sum B t).
Proof. exact (eq_refl (@sum B t)). Qed.
Lemma lem7158968 {B : Type'} (t : B -> Prop) (k : nat) : (term60 B t k) = (term61 B t k).
Proof. exact (MK_COMB (@lem7158967 B t) (@lem7158966 B k)). Qed.
Lemma lem7158969 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term62 A B s t R) = (term62 A B s t R).
Proof. exact (eq_refl (term62 A B s t R)). Qed.
Lemma lem7158970 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : ((term10 A B s t R) = (term60 B t k)) = ((term10 A B s t R) = (term61 B t k)).
Proof. exact (MK_COMB (@lem7158969 A B s t R) (@lem7158968 B t k)). Qed.
Lemma lem7158971 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : (term41 A B s R t k) = (term63 A B s R t k).
Proof. exact (MK_COMB (@lem7158962 A B t s R k) (@lem7158970 A B s R t k)). Qed.
Lemma lem7158972 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : term63 A B s R t k.
Proof. exact (EQ_MP (@lem7158971 A B s R t k) (@lem7158948 A B s R t k)). Qed.
Lemma lem7158973 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7158975 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem7158977 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : term64 A B t s R k j.
Proof. exact (@lem7158939 A B t s R k h1 j). Qed.
Lemma lem7158978 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : (term64 A B t s R k j) = (term48 A B t s R j k).
Proof. exact (eq_refl (term64 A B t s R k j)). Qed.
Lemma lem7158979 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : term48 A B t s R j k.
Proof. exact (EQ_MP (@lem7158978 A B t s R j k) (@lem7158977 A B j t s R k h1)). Qed.
Lemma lem7158980 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : (term48 A B t s R j k) = ((term48 A B t s R j k) = True).
Proof. exact (@lem7 (term48 A B t s R j k)). Qed.
Lemma lem7158985 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7158973 A s) (@lem7158938 A s h1)). Qed.
Lemma lem7158986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7158987 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term52 A s) = (and True).
Proof. exact (MK_COMB (@lem7158986) (@lem7158985 A s h1)). Qed.
Lemma lem7158991 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7158975 B t) (@lem7158940 B t h1)). Qed.
Lemma lem7158992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7158993 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (term52 B t) = (and True).
Proof. exact (MK_COMB (@lem7158992) (@lem7158991 B t h1)). Qed.
Lemma lem7158999 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term48 A B t s R j k) = True.
Proof. exact (EQ_MP (@lem7158980 A B t s R j k) (@lem7158979 A B j t s R k h1)). Qed.
Lemma lem7159000 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term48 A B t s R j k) = True.
Proof. exact (@lem7158999 A B j t s R k h1). Qed.
Lemma lem7159001 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term50 A B t s R k) = (term65 B).
Proof. exact (fun_ext (fun j : B => @lem7159000 A B j t s R k h1)). Qed.
Lemma lem7159002 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7159003 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term37 A B t s R k) = (term66 B).
Proof. exact (MK_COMB (@lem7159002 B) (@lem7159001 A B t s R k h1)). Qed.
Lemma lem7159005 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7159006 {B : Type'} (t : Prop) : (term67 B t) = t.
Proof. exact (@lem7159005 B t). Qed.
Lemma lem7159007 {B : Type'} : (term66 B) = True.
Proof. exact (@lem7159006 B True). Qed.
Lemma lem7159008 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term37 A B t s R k) = True.
Proof. exact (TRANS (@lem7159003 A B t s R k h1) (@lem7159007 B)). Qed.
Lemma lem7159009 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE B t) : (term36 A B t s R k) = (True /\ True).
Proof. exact (MK_COMB (@lem7158993 B t h2) (@lem7159008 A B t s R k h1)). Qed.
Lemma lem7159011 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7159012 : (True /\ True) = True.
Proof. exact (@lem7159011 True). Qed.
Lemma lem7159013 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE B t) : (term36 A B t s R k) = True.
Proof. exact (TRANS (@lem7159009 A B s R k t h1 h2) (@lem7159012)). Qed.
Lemma lem7159014 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term35 A B t s R k) = (True /\ True).
Proof. exact (MK_COMB (@lem7158987 A s h2) (@lem7159013 A B s R k t h1 h3)). Qed.
Lemma lem7159016 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7159017 : (True /\ True) = True.
Proof. exact (@lem7159016 True). Qed.
Lemma lem7159018 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term35 A B t s R k) = True.
Proof. exact (TRANS (@lem7159014 A B R k s t h1 h2 h3) (@lem7159017)). Qed.
Lemma lem7159019 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : True = (term35 A B t s R k).
Proof. exact (SYM (@lem7159018 A B R k s t h1 h2 h3)). Qed.
Lemma lem7159020 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : term35 A B t s R k.
Proof. exact (EQ_MP (@lem7159019 A B R k s t h1 h2 h3) (@lem0)). Qed.
Lemma lem7159021 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term61 B t k).
Proof. exact (@lem7158972 A B s R t k (@lem7159020 A B R k s t h1 h2 h3)). Qed.
Lemma lem7159022 (m : nat) : term68 m.
Proof. exact (@lem1340396 m). Qed.
Lemma lem7159023 (m : nat) : (term68 m) = (term69 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem7159024 (m : nat) : term69 m.
Proof. exact (EQ_MP (@lem7159023 m) (@lem7159022 m)). Qed.
Lemma lem7159025 (m : nat) (n : nat) : term70 m n.
Proof. exact (@lem7159024 m n). Qed.
Lemma lem7159026 (m : nat) (n : nat) : (term70 m n) = ((term71 m n) = (term72 m n)).
Proof. exact (eq_refl (term70 m n)). Qed.
Lemma lem7159028 {_132484 : Type'} (c : real) : term73 _132484 c.
Proof. exact (@lem7085323 _132484 c). Qed.
Lemma lem7159029 {_132484 : Type'} (c : real) : (term73 _132484 c) = (term74 _132484 c).
Proof. exact (eq_refl (term73 _132484 c)). Qed.
Lemma lem7159030 {_132484 : Type'} (c : real) : term74 _132484 c.
Proof. exact (EQ_MP (@lem7159029 _132484 c) (@lem7159028 _132484 c)). Qed.
Lemma lem7159031 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : term75 _132484 c s.
Proof. exact (@lem7159030 _132484 c s). Qed.
Lemma lem7159032 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term75 _132484 c s) = (term76 _132484 s c).
Proof. exact (eq_refl (term75 _132484 c s)). Qed.
Lemma lem7159033 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term76 _132484 s c.
Proof. exact (EQ_MP (@lem7159032 _132484 s c) (@lem7159031 _132484 c s)). Qed.
Lemma lem7159034 {_132484 : Type'} (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : @FINITE _132484 s.
Proof. exact (h1). Qed.
Lemma lem7159035 {_132484 : Type'} (c : real) (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : (term77 _132484 s c) = (term78 _132484 s c).
Proof. exact (@lem7159033 _132484 s c (@lem7159034 _132484 s h1)). Qed.
Lemma lem7159043 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem7159058 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term76 _132484 s c.
Proof. exact (fun h0 : @FINITE _132484 s => @lem7159035 _132484 c s h0). Qed.
Lemma lem7159059 {B : Type'} (s : B -> Prop) (c : real) : term76 B s c.
Proof. exact (@lem7159058 B s c). Qed.
Lemma lem7159060 {B : Type'} (t : B -> Prop) (k : nat) : term79 B t k.
Proof. exact (@lem7159059 B t (real_of_num k)). Qed.
Lemma lem7159062 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7159043 B t) (@lem7158940 B t h1)). Qed.
Lemma lem7159063 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7159062 B t h1)). Qed.
Lemma lem7159064 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7159063 B t h1) (@lem0)). Qed.
Lemma lem7159065 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : (term61 B t k) = (term80 B t k).
Proof. exact (@lem7159060 B t k (@lem7159064 B t h1)). Qed.
Lemma lem7159067 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (EQ_MP (@lem7159026 m n) (@lem7159025 m n)). Qed.
Lemma lem7159068 {B : Type'} (t : B -> Prop) (k : nat) : (term80 B t k) = (term81 B t k).
Proof. exact (@lem7159067 (@CARD B t) k). Qed.
Lemma lem7159069 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : (term61 B t k) = (term81 B t k).
Proof. exact (TRANS (@lem7159065 B k t h1) (@lem7159068 B t k)). Qed.
Lemma lem7159070 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7159071 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : (term82 B t k) = (term83 B t k).
Proof. exact (MK_COMB (@lem7159070) (@lem7159069 B k t h1)). Qed.
Lemma lem7159072 {B : Type'} (k : nat) (t : B -> Prop) : (term40 B k t) = (term40 B k t).
Proof. exact (eq_refl (term40 B k t)). Qed.
Lemma lem7159073 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : ((term61 B t k) = (term40 B k t)) = ((term81 B t k) = (term40 B k t)).
Proof. exact (MK_COMB (@lem7159071 B k t h1) (@lem7159072 B k t)). Qed.
Lemma lem7159076 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : ((term81 B t k) = (term40 B k t)) = ((term61 B t k) = (term40 B k t)).
Proof. exact (SYM (@lem7159073 B k t h1)). Qed.
Lemma lem7159080 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem7159081 {B : Type'} (k : nat) (t : B -> Prop) : (term84 B t k) = (term85 B k t).
Proof. exact (@lem7159080 k (@CARD B t)). Qed.
Lemma lem7159085 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7159086 {B : Type'} (k : nat) (t : B -> Prop) : (term81 B t k) = (term40 B k t).
Proof. exact (MK_COMB (@lem7159085) (@lem7159081 B k t)). Qed.
Lemma lem7159087 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7159088 {B : Type'} (k : nat) (t : B -> Prop) : (term83 B t k) = (term86 B k t).
Proof. exact (MK_COMB (@lem7159087) (@lem7159086 B k t)). Qed.
Lemma lem7159092 {B : Type'} (k : nat) (t : B -> Prop) : (term40 B k t) = (term40 B k t).
Proof. exact (eq_refl (term40 B k t)). Qed.
Lemma lem7159093 {B : Type'} (k : nat) (t : B -> Prop) : ((term81 B t k) = (term40 B k t)) = ((term40 B k t) = (term40 B k t)).
Proof. exact (MK_COMB (@lem7159088 B k t) (@lem7159092 B k t)). Qed.
Lemma lem7159095 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7159096 (x : real) : (x = x) = True.
Proof. exact (@lem7159095 real x). Qed.
Lemma lem7159097 {B : Type'} (k : nat) (t : B -> Prop) : ((term40 B k t) = (term40 B k t)) = True.
Proof. exact (@lem7159096 (term40 B k t)). Qed.
Lemma lem7159098 {B : Type'} (k : nat) (t : B -> Prop) : ((term81 B t k) = (term40 B k t)) = True.
Proof. exact (TRANS (@lem7159093 B k t) (@lem7159097 B k t)). Qed.
Lemma lem7159099 {B : Type'} (k : nat) (t : B -> Prop) : True = ((term81 B t k) = (term40 B k t)).
Proof. exact (SYM (@lem7159098 B k t)). Qed.
Lemma lem7159100 {B : Type'} (k : nat) (t : B -> Prop) : (term81 B t k) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159099 B k t) (@lem0)). Qed.
Lemma lem7159101 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : (term61 B t k) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159076 B k t h1) (@lem7159100 B k t)). Qed.
Lemma lem7159102 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : term87 A B s R k t.
Proof. exact (conj (@lem7159021 A B R k s t h1 h2 h3) (@lem7159101 B k t h3)). Qed.
Lemma lem7159103 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : term88 A B s R k t.
Proof. exact (ex_intro (term89 A B s R k t) (term61 B t k) (@lem7159102 A B R k s t h1 h2 h3)). Qed.
Lemma lem7159104 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term40 B k t).
Proof. exact (@lem7158944 A B s R k t (@lem7159103 A B R k s t h1 h2 h3)). Qed.
Lemma lem7159105 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : term36 A B t s R k.
Proof. exact (proj2 (@lem7158936 A B t s R k h1)). Qed.
Lemma lem7159106 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : @FINITE A s.
Proof. exact (proj1 (@lem7158936 A B t s R k h1)). Qed.
Lemma lem7159107 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term36 A B t s R k) : term37 A B t s R k.
Proof. exact (proj2 (@lem7158937 A B t s R k h1)). Qed.
Lemma lem7159108 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term36 A B t s R k) : @FINITE B t.
Proof. exact (proj1 (@lem7158937 A B t s R k h1)). Qed.
Lemma lem7159109 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term37 A B t s R k) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h4 : term37 A B t s R k => @lem7159104 A B R k s t h1 h2 h3) (fun h4 : (term10 A B s t R) = (term40 B k t) => @lem7158939 A B t s R k h1)). Qed.
Lemma lem7159110 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159109 A B R k s t h1 h2 h3) (@lem7158939 A B t s R k h1)). Qed.
Lemma lem7159111 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (@FINITE B t) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem7159110 A B R k s t h1 h2 h3) (fun h4 : (term10 A B s t R) = (term40 B k t) => @lem7158940 B t h3)). Qed.
Lemma lem7159112 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159111 A B R k s t h1 h2 h3) (@lem7158940 B t h3)). Qed.
Lemma lem7159113 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term36 A B t s R k) : (term37 A B t s R k) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h4 : term37 A B t s R k => @lem7159112 A B R k s t h4 h1 h2) (fun h4 : (term10 A B s t R) = (term40 B k t) => @lem7159107 A B t s R k h3)). Qed.
Lemma lem7159114 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term36 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159113 A B t s R k h1 h2 h3) (@lem7159107 A B t s R k h3)). Qed.
Lemma lem7159115 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (@FINITE B t) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem7159114 A B t s R k h1 h3 h2) (fun h3 : (term10 A B s t R) = (term40 B k t) => @lem7159108 A B t s R k h2)). Qed.
Lemma lem7159116 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159115 A B t s R k h1 h2) (@lem7159108 A B t s R k h2)). Qed.
Lemma lem7159117 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (@FINITE A s) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7159116 A B t s R k h1 h2) (fun h3 : (term10 A B s t R) = (term40 B k t) => @lem7158938 A s h1)). Qed.
Lemma lem7159118 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159117 A B t s R k h1 h2) (@lem7158938 A s h1)). Qed.
Lemma lem7159119 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term35 A B t s R k) : (term36 A B t s R k) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h3 : term36 A B t s R k => @lem7159118 A B t s R k h1 h3) (fun h3 : (term10 A B s t R) = (term40 B k t) => @lem7159105 A B t s R k h2)). Qed.
Lemma lem7159120 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term35 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159119 A B t s R k h1 h2) (@lem7159105 A B t s R k h2)). Qed.
Lemma lem7159121 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : (@FINITE A s) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7159120 A B t s R k h2 h1) (fun h2 : (term10 A B s t R) = (term40 B k t) => @lem7159106 A B t s R k h1)). Qed.
Lemma lem7159122 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem7159121 A B t s R k h1) (@lem7159106 A B t s R k h1)). Qed.
Lemma lem7159123 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) : term90 A B s R k t.
Proof. exact (fun h0 : term35 A B t s R k => @lem7159122 A B t s R k h0). Qed.
Lemma lem7159128 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term91 A B s R t.
Proof. exact (fun k : nat => @lem7159123 A B s R k t). Qed.
Lemma lem7159133 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term92 A B s R.
Proof. exact (fun t : B -> Prop => @lem7159128 A B s R t). Qed.
Lemma lem7159138 {A B : Type'} (R : type1413 A B) : term93 A B R.
Proof. exact (fun s : A -> Prop => @lem7159133 A B s R). Qed.
Lemma lem7159143 {A B : Type'} : term94 A B.
Proof. exact (fun R : type1413 A B => @lem7159138 A B R). Qed.
