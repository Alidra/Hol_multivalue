Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_MULTICOUNT_term_abbrevs.
Require Import EQ_TRANS_spec.
Require Import MULT_AC_spec.
Require Import NSUM_CONST_spec.
Require Import NSUM_MULTICOUNT_GEN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem6992805 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6992806 {A B : Type'} (R : type1413 A B) (h1 : term0 A B) : term1 A B R.
Proof. exact (@lem6992805 A B h1 R). Qed.
Lemma lem6992807 {A B : Type'} (R : type1413 A B) : (term1 A B R) = (term2 A B R).
Proof. exact (eq_refl (term1 A B R)). Qed.
Lemma lem6992808 {A B : Type'} (R : type1413 A B) (h1 : term0 A B) : term2 A B R.
Proof. exact (EQ_MP (@lem6992807 A B R) (@lem6992806 A B R h1)). Qed.
Lemma lem6992809 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (h1 : term0 A B) : term3 A B R s.
Proof. exact (@lem6992808 A B R h1 s). Qed.
Lemma lem6992810 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term3 A B R s) = (term4 A B s R).
Proof. exact (eq_refl (term3 A B R s)). Qed.
Lemma lem6992811 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (h1 : term0 A B) : term4 A B s R.
Proof. exact (EQ_MP (@lem6992810 A B s R) (@lem6992809 A B R s h1)). Qed.
Lemma lem6992812 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term0 A B) : term5 A B s R t.
Proof. exact (@lem6992811 A B s R h1 t). Qed.
Lemma lem6992813 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term5 A B s R t) = (term6 A B s R t).
Proof. exact (eq_refl (term5 A B s R t)). Qed.
Lemma lem6992814 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term0 A B) : term6 A B s R t.
Proof. exact (EQ_MP (@lem6992813 A B s R t) (@lem6992812 A B s R t h1)). Qed.
Lemma lem6992815 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (h1 : term0 A B) : term7 A B s R t k.
Proof. exact (@lem6992814 A B s R t h1 k). Qed.
Lemma lem6992816 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term7 A B s R t k) = (term8 A B s R t k).
Proof. exact (eq_refl (term7 A B s R t k)). Qed.
Lemma lem6992817 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (h1 : term0 A B) : term8 A B s R t k.
Proof. exact (EQ_MP (@lem6992816 A B s R t k) (@lem6992815 A B s R t k h1)). Qed.
Lemma lem6992818 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term9 A B t s R k) : term9 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem6992819 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term0 A B) (h2 : term9 A B t s R k) : (term10 A B s t R) = (term11 B t k).
Proof. exact (@lem6992817 A B s R t k h1 (@lem6992818 A B t s R k h2)). Qed.
Lemma lem6992820 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term9 A B t s R k) : term12 A B s R t k.
Proof. exact (fun h0 : term0 A B => @lem6992819 A B t s R k h0 h1). Qed.
Lemma lem6992821 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6992822 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term0 A B) (h2 : term9 A B t s R k) : (term10 A B s t R) = (term11 B t k).
Proof. exact (@lem6992820 A B t s R k h2 (@lem6992821 A B h1)). Qed.
Lemma lem6992823 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (h1 : term0 A B) : term8 A B s R t k.
Proof. exact (fun h0 : term9 A B t s R k => @lem6992822 A B t s R k h1 h0). Qed.
Lemma lem6992824 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (h1 : term0 A B) : term6 A B s R t.
Proof. exact (fun k : B -> nat => @lem6992823 A B s R t k h1). Qed.
Lemma lem6992825 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (h1 : term0 A B) : term4 A B s R.
Proof. exact (fun t : B -> Prop => @lem6992824 A B s R t h1). Qed.
Lemma lem6992826 {A B : Type'} (s : A -> Prop) (h1 : term0 A B) : term13 A B s.
Proof. exact (fun R : type1413 A B => @lem6992825 A B s R h1). Qed.
Lemma lem6992827 {A B : Type'} (h1 : term0 A B) : term14 A B.
Proof. exact (fun s : A -> Prop => @lem6992826 A B s h1). Qed.
Lemma lem6992828 {A B : Type'} : term15 A B.
Proof. exact (fun h0 : term0 A B => @lem6992827 A B h0). Qed.
Lemma lem6992829 {A B : Type'} : term14 A B.
Proof. exact (@lem6992828 A B (@lem6992800 A B)). Qed.
Lemma lem6992830 {A B : Type'} (s : A -> Prop) : term16 A B s.
Proof. exact (@lem6992829 A B s). Qed.
Lemma lem6992831 {A B : Type'} (s : A -> Prop) : (term16 A B s) = (term13 A B s).
Proof. exact (eq_refl (term16 A B s)). Qed.
Lemma lem6992832 {A B : Type'} (s : A -> Prop) : term13 A B s.
Proof. exact (EQ_MP (@lem6992831 A B s) (@lem6992830 A B s)). Qed.
Lemma lem6992833 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term17 A B s R.
Proof. exact (@lem6992832 A B s R). Qed.
Lemma lem6992834 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term17 A B s R) = (term4 A B s R).
Proof. exact (eq_refl (term17 A B s R)). Qed.
Lemma lem6992835 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term4 A B s R.
Proof. exact (EQ_MP (@lem6992834 A B s R) (@lem6992833 A B s R)). Qed.
Lemma lem6992836 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term5 A B s R t.
Proof. exact (@lem6992835 A B s R t). Qed.
Lemma lem6992837 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : (term5 A B s R t) = (term6 A B s R t).
Proof. exact (eq_refl (term5 A B s R t)). Qed.
Lemma lem6992838 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term6 A B s R t.
Proof. exact (EQ_MP (@lem6992837 A B s R t) (@lem6992836 A B s R t)). Qed.
Lemma lem6992839 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term7 A B s R t k.
Proof. exact (@lem6992838 A B s R t k). Qed.
Lemma lem6992840 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term7 A B s R t k) = (term8 A B s R t k).
Proof. exact (eq_refl (term7 A B s R t k)). Qed.
Lemma lem6992842 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem6992843 {A : Type'} (x : A) (h1 : term18 A) : term19 A x.
Proof. exact (@lem6992842 A h1 x). Qed.
Lemma lem6992844 {A : Type'} (x : A) : (term19 A x) = (term20 A x).
Proof. exact (eq_refl (term19 A x)). Qed.
Lemma lem6992845 {A : Type'} (x : A) (h1 : term18 A) : term20 A x.
Proof. exact (EQ_MP (@lem6992844 A x) (@lem6992843 A x h1)). Qed.
Lemma lem6992846 {A : Type'} (x : A) (y : A) (h1 : term18 A) : term21 A x y.
Proof. exact (@lem6992845 A x h1 y). Qed.
Lemma lem6992847 {A : Type'} (y : A) (x : A) : (term21 A x y) = (term22 A y x).
Proof. exact (eq_refl (term21 A x y)). Qed.
Lemma lem6992848 {A : Type'} (y : A) (x : A) (h1 : term18 A) : term22 A y x.
Proof. exact (EQ_MP (@lem6992847 A y x) (@lem6992846 A x y h1)). Qed.
Lemma lem6992849 {A : Type'} (y : A) (x : A) (z : A) (h1 : term18 A) : term23 A y x z.
Proof. exact (@lem6992848 A y x h1 z). Qed.
Lemma lem6992850 {A : Type'} (y : A) (x : A) (z : A) : (term23 A y x z) = (term24 A y x z).
Proof. exact (eq_refl (term23 A y x z)). Qed.
Lemma lem6992851 {A : Type'} (y : A) (x : A) (z : A) (h1 : term18 A) : term24 A y x z.
Proof. exact (EQ_MP (@lem6992850 A y x z) (@lem6992849 A y x z h1)). Qed.
Lemma lem6992852 {A : Type'} (x : A) (y : A) (z : A) (h1 : term25 A x y z) : term25 A x y z.
Proof. exact (h1). Qed.
Lemma lem6992853 {A : Type'} (x : A) (y : A) (z : A) (h1 : term18 A) (h2 : term25 A x y z) : x = z.
Proof. exact (@lem6992851 A y x z h1 (@lem6992852 A x y z h2)). Qed.
Lemma lem6992854 {A : Type'} (x : A) (y : A) (z : A) (h1 : term25 A x y z) : term26 A x z.
Proof. exact (fun h0 : term18 A => @lem6992853 A x y z h0 h1). Qed.
Lemma lem6992855 {A : Type'} (x : A) (z : A) (h1 : term27 A x z) : term27 A x z.
Proof. exact (h1). Qed.
Lemma lem6992856 {A : Type'} (x : A) (z : A) (h1 : term27 A x z) : term26 A x z.
Proof. exact (ex_elim (@lem6992855 A x z h1) (fun y : A => fun h0 : term28 A x z y => @lem6992854 A x y z h0)). Qed.
Lemma lem6992857 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem6992858 {A : Type'} (x : A) (z : A) (h1 : term18 A) (h2 : term27 A x z) : x = z.
Proof. exact (@lem6992856 A x z h2 (@lem6992857 A h1)). Qed.
Lemma lem6992859 {A : Type'} (x : A) (z : A) (h1 : term18 A) : term29 A x z.
Proof. exact (fun h0 : term27 A x z => @lem6992858 A x z h1 h0). Qed.
Lemma lem6992860 {A : Type'} (x : A) (h1 : term18 A) : term30 A x.
Proof. exact (fun z : A => @lem6992859 A x z h1). Qed.
Lemma lem6992861 {A : Type'} (h1 : term18 A) : term31 A.
Proof. exact (fun x : A => @lem6992860 A x h1). Qed.
Lemma lem6992862 {A : Type'} : term32 A.
Proof. exact (fun h0 : term18 A => @lem6992861 A h0). Qed.
Lemma lem6992863 {A : Type'} : term31 A.
Proof. exact (@lem6992862 A (@lem403 A)). Qed.
Lemma lem6992864 {A : Type'} (x : A) : term33 A x.
Proof. exact (@lem6992863 A x). Qed.
Lemma lem6992865 {A : Type'} (x : A) : (term33 A x) = (term30 A x).
Proof. exact (eq_refl (term33 A x)). Qed.
Lemma lem6992866 {A : Type'} (x : A) : term30 A x.
Proof. exact (EQ_MP (@lem6992865 A x) (@lem6992864 A x)). Qed.
Lemma lem6992867 {A : Type'} (x : A) (z : A) : term34 A x z.
Proof. exact (@lem6992866 A x z). Qed.
Lemma lem6992868 {A : Type'} (x : A) (z : A) : (term34 A x z) = (term29 A x z).
Proof. exact (eq_refl (term34 A x z)). Qed.
Lemma lem6992870 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : term35 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem6992871 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term36 A B t s R k) : term36 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem6992872 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6992873 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : term37 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem6992874 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem6992876 {A : Type'} (x : A) (z : A) : term29 A x z.
Proof. exact (EQ_MP (@lem6992868 A x z) (@lem6992867 A x z)). Qed.
Lemma lem6992877 (x : nat) (z : nat) : term38 x z.
Proof. exact (@lem6992876 nat x z). Qed.
Lemma lem6992878 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) : term39 A B s R k t.
Proof. exact (@lem6992877 (term10 A B s t R) (term40 B k t)). Qed.
Lemma lem6992880 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term8 A B s R t k.
Proof. exact (EQ_MP (@lem6992840 A B s R t k) (@lem6992839 A B s R t k)). Qed.
Lemma lem6992881 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term8 A B s R t k.
Proof. exact (@lem6992880 A B s R t k). Qed.
Lemma lem6992882 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : term41 A B s R t k.
Proof. exact (@lem6992881 A B s R t (term42 B k)). Qed.
Lemma lem6992883 {B : Type'} (j : B) (k : nat) : (term43 B k j) = k.
Proof. exact (eq_refl (term43 B k j)). Qed.
Lemma lem6992884 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term44 A B s R j) = (term44 A B s R j).
Proof. exact (eq_refl (term44 A B s R j)). Qed.
Lemma lem6992885 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : ((term45 A B s R j) = (term43 B k j)) = ((term45 A B s R j) = k).
Proof. exact (MK_COMB (@lem6992884 A B s R j) (@lem6992883 B j k)). Qed.
Lemma lem6992886 {B : Type'} (j : B) (t : B -> Prop) : (term46 B j t) = (term46 B j t).
Proof. exact (eq_refl (term46 B j t)). Qed.
Lemma lem6992887 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : (term47 A B t s R k j) = (term48 A B t s R j k).
Proof. exact (MK_COMB (@lem6992886 B j t) (@lem6992885 A B s R j k)). Qed.
Lemma lem6992888 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term49 A B t s R k) = (term50 A B t s R k).
Proof. exact (fun_ext (fun j : B => @lem6992887 A B t s R j k)). Qed.
Lemma lem6992889 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6992890 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term51 A B t s R k) = (term37 A B t s R k).
Proof. exact (MK_COMB (@lem6992889 B) (@lem6992888 A B t s R k)). Qed.
Lemma lem6992891 {B : Type'} (t : B -> Prop) : (term52 B t) = (term52 B t).
Proof. exact (eq_refl (term52 B t)). Qed.
Lemma lem6992892 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term53 A B t s R k) = (term36 A B t s R k).
Proof. exact (MK_COMB (@lem6992891 B t) (@lem6992890 A B t s R k)). Qed.
Lemma lem6992893 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem6992894 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term54 A B t s R k) = (term35 A B t s R k).
Proof. exact (MK_COMB (@lem6992893 A s) (@lem6992892 A B t s R k)). Qed.
Lemma lem6992895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6992896 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) : (term55 A B t s R k) = (term56 A B t s R k).
Proof. exact (MK_COMB (@lem6992895) (@lem6992894 A B t s R k)). Qed.
Lemma lem6992897 {B : Type'} (i : B) (k : nat) : (term43 B k i) = k.
Proof. exact (eq_refl (term43 B k i)). Qed.
Lemma lem6992898 {B : Type'} (k : nat) : (term57 B k) = (term42 B k).
Proof. exact (fun_ext (fun i : B => @lem6992897 B i k)). Qed.
Lemma lem6992899 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@nsum B t).
Proof. exact (eq_refl (@nsum B t)). Qed.
Lemma lem6992900 {B : Type'} (t : B -> Prop) (k : nat) : (term58 B t k) = (term59 B t k).
Proof. exact (MK_COMB (@lem6992899 B t) (@lem6992898 B k)). Qed.
Lemma lem6992901 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term60 A B s t R) = (term60 A B s t R).
Proof. exact (eq_refl (term60 A B s t R)). Qed.
Lemma lem6992902 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : ((term10 A B s t R) = (term58 B t k)) = ((term10 A B s t R) = (term59 B t k)).
Proof. exact (MK_COMB (@lem6992901 A B s t R) (@lem6992900 B t k)). Qed.
Lemma lem6992903 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : (term41 A B s R t k) = (term61 A B s R t k).
Proof. exact (MK_COMB (@lem6992896 A B t s R k) (@lem6992902 A B s R t k)). Qed.
Lemma lem6992904 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : nat) : term61 A B s R t k.
Proof. exact (EQ_MP (@lem6992903 A B s R t k) (@lem6992882 A B s R t k)). Qed.
Lemma lem6992905 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6992907 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem6992909 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : term62 A B t s R k j.
Proof. exact (@lem6992873 A B t s R k h1 j). Qed.
Lemma lem6992910 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : (term62 A B t s R k j) = (term48 A B t s R j k).
Proof. exact (eq_refl (term62 A B t s R k j)). Qed.
Lemma lem6992911 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : term48 A B t s R j k.
Proof. exact (EQ_MP (@lem6992910 A B t s R j k) (@lem6992909 A B j t s R k h1)). Qed.
Lemma lem6992912 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (j : B) (k : nat) : (term48 A B t s R j k) = ((term48 A B t s R j k) = True).
Proof. exact (@lem7 (term48 A B t s R j k)). Qed.
Lemma lem6992917 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6992905 A s) (@lem6992872 A s h1)). Qed.
Lemma lem6992918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6992919 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term52 A s) = (and True).
Proof. exact (MK_COMB (@lem6992918) (@lem6992917 A s h1)). Qed.
Lemma lem6992923 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6992907 B t) (@lem6992874 B t h1)). Qed.
Lemma lem6992924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6992925 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (term52 B t) = (and True).
Proof. exact (MK_COMB (@lem6992924) (@lem6992923 B t h1)). Qed.
Lemma lem6992931 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term48 A B t s R j k) = True.
Proof. exact (EQ_MP (@lem6992912 A B t s R j k) (@lem6992911 A B j t s R k h1)). Qed.
Lemma lem6992932 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term48 A B t s R j k) = True.
Proof. exact (@lem6992931 A B j t s R k h1). Qed.
Lemma lem6992933 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term50 A B t s R k) = (term63 B).
Proof. exact (fun_ext (fun j : B => @lem6992932 A B j t s R k h1)). Qed.
Lemma lem6992934 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6992935 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term37 A B t s R k) = (term64 B).
Proof. exact (MK_COMB (@lem6992934 B) (@lem6992933 A B t s R k h1)). Qed.
Lemma lem6992937 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6992938 {B : Type'} (t : Prop) : (term65 B t) = t.
Proof. exact (@lem6992937 B t). Qed.
Lemma lem6992939 {B : Type'} : (term64 B) = True.
Proof. exact (@lem6992938 B True). Qed.
Lemma lem6992940 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term37 A B t s R k) : (term37 A B t s R k) = True.
Proof. exact (TRANS (@lem6992935 A B t s R k h1) (@lem6992939 B)). Qed.
Lemma lem6992941 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE B t) : (term36 A B t s R k) = (True /\ True).
Proof. exact (MK_COMB (@lem6992925 B t h2) (@lem6992940 A B t s R k h1)). Qed.
Lemma lem6992943 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6992944 : (True /\ True) = True.
Proof. exact (@lem6992943 True). Qed.
Lemma lem6992945 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE B t) : (term36 A B t s R k) = True.
Proof. exact (TRANS (@lem6992941 A B s R k t h1 h2) (@lem6992944)). Qed.
Lemma lem6992946 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term35 A B t s R k) = (True /\ True).
Proof. exact (MK_COMB (@lem6992919 A s h2) (@lem6992945 A B s R k t h1 h3)). Qed.
Lemma lem6992948 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6992949 : (True /\ True) = True.
Proof. exact (@lem6992948 True). Qed.
Lemma lem6992950 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term35 A B t s R k) = True.
Proof. exact (TRANS (@lem6992946 A B R k s t h1 h2 h3) (@lem6992949)). Qed.
Lemma lem6992951 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : True = (term35 A B t s R k).
Proof. exact (SYM (@lem6992950 A B R k s t h1 h2 h3)). Qed.
Lemma lem6992952 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : term35 A B t s R k.
Proof. exact (EQ_MP (@lem6992951 A B R k s t h1 h2 h3) (@lem0)). Qed.
Lemma lem6992953 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term59 B t k).
Proof. exact (@lem6992904 A B s R t k (@lem6992952 A B R k s t h1 h2 h3)). Qed.
Lemma lem6992954 {_127196 : Type'} (c : nat) : term66 _127196 c.
Proof. exact (@lem6940531 _127196 c). Qed.
Lemma lem6992955 {_127196 : Type'} (c : nat) : (term66 _127196 c) = (term67 _127196 c).
Proof. exact (eq_refl (term66 _127196 c)). Qed.
Lemma lem6992956 {_127196 : Type'} (c : nat) : term67 _127196 c.
Proof. exact (EQ_MP (@lem6992955 _127196 c) (@lem6992954 _127196 c)). Qed.
Lemma lem6992957 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term68 _127196 c s.
Proof. exact (@lem6992956 _127196 c s). Qed.
Lemma lem6992958 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term68 _127196 c s) = (term69 _127196 s c).
Proof. exact (eq_refl (term68 _127196 c s)). Qed.
Lemma lem6992959 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term69 _127196 s c.
Proof. exact (EQ_MP (@lem6992958 _127196 s c) (@lem6992957 _127196 c s)). Qed.
Lemma lem6992960 {_127196 : Type'} (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : @FINITE _127196 s.
Proof. exact (h1). Qed.
Lemma lem6992961 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : (term59 _127196 s c) = (term70 _127196 s c).
Proof. exact (@lem6992959 _127196 s c (@lem6992960 _127196 s h1)). Qed.
Lemma lem6992969 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem6992984 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term69 _127196 s c.
Proof. exact (fun h0 : @FINITE _127196 s => @lem6992961 _127196 c s h0). Qed.
Lemma lem6992985 {B : Type'} (s : B -> Prop) (c : nat) : term69 B s c.
Proof. exact (@lem6992984 B s c). Qed.
Lemma lem6992986 {B : Type'} (t : B -> Prop) (k : nat) : term69 B t k.
Proof. exact (@lem6992985 B t k). Qed.
Lemma lem6992988 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6992969 B t) (@lem6992874 B t h1)). Qed.
Lemma lem6992989 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem6992988 B t h1)). Qed.
Lemma lem6992990 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem6992989 B t h1) (@lem0)). Qed.
Lemma lem6992991 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : (term59 B t k) = (term70 B t k).
Proof. exact (@lem6992986 B t k (@lem6992990 B t h1)). Qed.
Lemma lem6992992 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992993 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : (term71 B t k) = (term72 B t k).
Proof. exact (MK_COMB (@lem6992992) (@lem6992991 B k t h1)). Qed.
Lemma lem6992994 {B : Type'} (k : nat) (t : B -> Prop) : (term40 B k t) = (term40 B k t).
Proof. exact (eq_refl (term40 B k t)). Qed.
Lemma lem6992995 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : ((term59 B t k) = (term40 B k t)) = ((term70 B t k) = (term40 B k t)).
Proof. exact (MK_COMB (@lem6992993 B k t h1) (@lem6992994 B k t)). Qed.
Lemma lem6992998 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : ((term70 B t k) = (term40 B k t)) = ((term59 B t k) = (term40 B k t)).
Proof. exact (SYM (@lem6992995 B k t h1)). Qed.
Lemma lem6993002 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem6993003 {B : Type'} (k : nat) (t : B -> Prop) : (term70 B t k) = (term40 B k t).
Proof. exact (@lem6993002 k (@CARD B t)). Qed.
Lemma lem6993007 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6993008 {B : Type'} (k : nat) (t : B -> Prop) : (term72 B t k) = (term73 B k t).
Proof. exact (MK_COMB (@lem6993007) (@lem6993003 B k t)). Qed.
Lemma lem6993012 {B : Type'} (k : nat) (t : B -> Prop) : (term40 B k t) = (term40 B k t).
Proof. exact (eq_refl (term40 B k t)). Qed.
Lemma lem6993013 {B : Type'} (k : nat) (t : B -> Prop) : ((term70 B t k) = (term40 B k t)) = ((term40 B k t) = (term40 B k t)).
Proof. exact (MK_COMB (@lem6993008 B k t) (@lem6993012 B k t)). Qed.
Lemma lem6993015 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6993016 (x : nat) : (x = x) = True.
Proof. exact (@lem6993015 nat x). Qed.
Lemma lem6993017 {B : Type'} (k : nat) (t : B -> Prop) : ((term40 B k t) = (term40 B k t)) = True.
Proof. exact (@lem6993016 (term40 B k t)). Qed.
Lemma lem6993018 {B : Type'} (k : nat) (t : B -> Prop) : ((term70 B t k) = (term40 B k t)) = True.
Proof. exact (TRANS (@lem6993013 B k t) (@lem6993017 B k t)). Qed.
Lemma lem6993019 {B : Type'} (k : nat) (t : B -> Prop) : True = ((term70 B t k) = (term40 B k t)).
Proof. exact (SYM (@lem6993018 B k t)). Qed.
Lemma lem6993020 {B : Type'} (k : nat) (t : B -> Prop) : (term70 B t k) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993019 B k t) (@lem0)). Qed.
Lemma lem6993021 {B : Type'} (k : nat) (t : B -> Prop) (h1 : @FINITE B t) : (term59 B t k) = (term40 B k t).
Proof. exact (EQ_MP (@lem6992998 B k t h1) (@lem6993020 B k t)). Qed.
Lemma lem6993022 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : term74 A B s R k t.
Proof. exact (conj (@lem6992953 A B R k s t h1 h2 h3) (@lem6993021 B k t h3)). Qed.
Lemma lem6993023 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : term75 A B s R k t.
Proof. exact (ex_intro (term76 A B s R k t) (term59 B t k) (@lem6993022 A B R k s t h1 h2 h3)). Qed.
Lemma lem6993024 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term40 B k t).
Proof. exact (@lem6992878 A B s R k t (@lem6993023 A B R k s t h1 h2 h3)). Qed.
Lemma lem6993025 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : term36 A B t s R k.
Proof. exact (proj2 (@lem6992870 A B t s R k h1)). Qed.
Lemma lem6993026 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : @FINITE A s.
Proof. exact (proj1 (@lem6992870 A B t s R k h1)). Qed.
Lemma lem6993027 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term36 A B t s R k) : term37 A B t s R k.
Proof. exact (proj2 (@lem6992871 A B t s R k h1)). Qed.
Lemma lem6993028 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term36 A B t s R k) : @FINITE B t.
Proof. exact (proj1 (@lem6992871 A B t s R k h1)). Qed.
Lemma lem6993029 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term37 A B t s R k) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h4 : term37 A B t s R k => @lem6993024 A B R k s t h1 h2 h3) (fun h4 : (term10 A B s t R) = (term40 B k t) => @lem6992873 A B t s R k h1)). Qed.
Lemma lem6993030 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993029 A B R k s t h1 h2 h3) (@lem6992873 A B t s R k h1)). Qed.
Lemma lem6993031 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (@FINITE B t) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem6993030 A B R k s t h1 h2 h3) (fun h4 : (term10 A B s t R) = (term40 B k t) => @lem6992874 B t h3)). Qed.
Lemma lem6993032 {A B : Type'} (R : type1413 A B) (k : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B t s R k) (h2 : @FINITE A s) (h3 : @FINITE B t) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993031 A B R k s t h1 h2 h3) (@lem6992874 B t h3)). Qed.
Lemma lem6993033 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term36 A B t s R k) : (term37 A B t s R k) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h4 : term37 A B t s R k => @lem6993032 A B R k s t h4 h1 h2) (fun h4 : (term10 A B s t R) = (term40 B k t) => @lem6993027 A B t s R k h3)). Qed.
Lemma lem6993034 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term36 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993033 A B t s R k h1 h2 h3) (@lem6993027 A B t s R k h3)). Qed.
Lemma lem6993035 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (@FINITE B t) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem6993034 A B t s R k h1 h3 h2) (fun h3 : (term10 A B s t R) = (term40 B k t) => @lem6993028 A B t s R k h2)). Qed.
Lemma lem6993036 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993035 A B t s R k h1 h2) (@lem6993028 A B t s R k h2)). Qed.
Lemma lem6993037 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (@FINITE A s) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6993036 A B t s R k h1 h2) (fun h3 : (term10 A B s t R) = (term40 B k t) => @lem6992872 A s h1)). Qed.
Lemma lem6993038 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term36 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993037 A B t s R k h1 h2) (@lem6992872 A s h1)). Qed.
Lemma lem6993039 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term35 A B t s R k) : (term36 A B t s R k) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h3 : term36 A B t s R k => @lem6993038 A B t s R k h1 h3) (fun h3 : (term10 A B s t R) = (term40 B k t) => @lem6993025 A B t s R k h2)). Qed.
Lemma lem6993040 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : @FINITE A s) (h2 : term35 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993039 A B t s R k h1 h2) (@lem6993025 A B t s R k h2)). Qed.
Lemma lem6993041 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : (@FINITE A s) = ((term10 A B s t R) = (term40 B k t)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem6993040 A B t s R k h2 h1) (fun h2 : (term10 A B s t R) = (term40 B k t) => @lem6993026 A B t s R k h1)). Qed.
Lemma lem6993042 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : nat) (h1 : term35 A B t s R k) : (term10 A B s t R) = (term40 B k t).
Proof. exact (EQ_MP (@lem6993041 A B t s R k h1) (@lem6993026 A B t s R k h1)). Qed.
Lemma lem6993043 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : nat) (t : B -> Prop) : term77 A B s R k t.
Proof. exact (fun h0 : term35 A B t s R k => @lem6993042 A B t s R k h0). Qed.
Lemma lem6993048 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term78 A B s R t.
Proof. exact (fun k : nat => @lem6993043 A B s R k t). Qed.
Lemma lem6993053 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term79 A B s R.
Proof. exact (fun t : B -> Prop => @lem6993048 A B s R t). Qed.
Lemma lem6993058 {A B : Type'} (R : type1413 A B) : term80 A B R.
Proof. exact (fun s : A -> Prop => @lem6993053 A B s R). Qed.
Lemma lem6993063 {A B : Type'} : term81 A B.
Proof. exact (fun R : type1413 A B => @lem6993058 A B R). Qed.
