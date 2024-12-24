Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_UNION_term_abbrevs.
Require Import UNION_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3204819 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3188344 A s). Qed.
Lemma lem3204820 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3204821 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3204820 A s) (@lem3204819 A s)). Qed.
Lemma lem3204822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3204821 A s t). Qed.
Lemma lem3204823 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((@UNION A s t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3204849 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3204850 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem3204849 _83095 p). Qed.
Lemma lem3204851 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem3204852 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem3204851 _83095 p) (@lem3204850 _83095 p)). Qed.
Lemma lem3204853 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem3204852 _83095 p x). Qed.
Lemma lem3204854 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem3204878 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3204823 A s t) (@lem3204822 A s t)). Qed.
Lemma lem3204879 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term3 A s t).
Proof. exact (@lem3204878 A s t). Qed.
Lemma lem3204886 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3204887 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term9 A x s t) = (term10 A x s t).
Proof. exact (MK_COMB (@lem3204886 A x) (@lem3204879 A s t)). Qed.
Lemma lem3204889 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3204854 _83095 p x) (@lem3204853 _83095 p x)). Qed.
Lemma lem3204890 {A : Type'} (p : A -> Prop) (x : A) : (term8 A x p) = (p x).
Proof. exact (@lem3204889 A p x). Qed.
Lemma lem3204891 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A x s t) = (term12 A s t x).
Proof. exact (@lem3204890 A (term13 A s t) x). Qed.
Lemma lem3204892 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s t x) = (term14 A s x t).
Proof. exact (eq_refl (term12 A s t x)). Qed.
Lemma lem3204893 {A : Type'} (GEN_PVAR_0 : A) : (@SETSPEC A GEN_PVAR_0) = (@SETSPEC A GEN_PVAR_0).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_0)). Qed.
Lemma lem3204894 {A : Type'} (GEN_PVAR_0 : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A GEN_PVAR_0 s t x) = (term16 A GEN_PVAR_0 s x t).
Proof. exact (MK_COMB (@lem3204893 A GEN_PVAR_0) (@lem3204892 A s x t)). Qed.
Lemma lem3204895 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3204896 {A : Type'} (GEN_PVAR_0 : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A GEN_PVAR_0 s t x) = (term18 A GEN_PVAR_0 s t x).
Proof. exact (MK_COMB (@lem3204894 A GEN_PVAR_0 s x t) (@lem3204895 A x)). Qed.
Lemma lem3204897 {A : Type'} (GEN_PVAR_0 : A) (s : A -> Prop) (t : A -> Prop) : (term19 A GEN_PVAR_0 s t) = (term20 A GEN_PVAR_0 s t).
Proof. exact (fun_ext (fun x : A => @lem3204896 A GEN_PVAR_0 s t x)). Qed.
Lemma lem3204898 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3204899 {A : Type'} (GEN_PVAR_0 : A) (s : A -> Prop) (t : A -> Prop) : (term21 A GEN_PVAR_0 s t) = (term22 A GEN_PVAR_0 s t).
Proof. exact (MK_COMB (@lem3204898 A) (@lem3204897 A GEN_PVAR_0 s t)). Qed.
Lemma lem3204900 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term24 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_0 : A => @lem3204899 A GEN_PVAR_0 s t)). Qed.
Lemma lem3204901 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3204902 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3204901 A) (@lem3204900 A s t)). Qed.
Lemma lem3204903 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3204904 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term11 A x s t) = (term10 A x s t).
Proof. exact (MK_COMB (@lem3204903 A x) (@lem3204902 A s t)). Qed.
Lemma lem3204905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3204906 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term27 A x s t).
Proof. exact (MK_COMB (@lem3204905) (@lem3204904 A x s t)). Qed.
Lemma lem3204907 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s t x) = (term14 A s x t).
Proof. exact (eq_refl (term12 A s t x)). Qed.
Lemma lem3204908 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term11 A x s t) = (term12 A s t x)) = ((term10 A x s t) = (term14 A s x t)).
Proof. exact (MK_COMB (@lem3204906 A x s t) (@lem3204907 A s x t)). Qed.
Lemma lem3204909 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term14 A s x t).
Proof. exact (EQ_MP (@lem3204908 A s x t) (@lem3204891 A s t x)). Qed.
Lemma lem3204912 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term9 A x s t) = (term14 A s x t).
Proof. exact (TRANS (@lem3204887 A x s t) (@lem3204909 A s x t)). Qed.
Lemma lem3204913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3204914 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (MK_COMB (@lem3204913) (@lem3204912 A s x t)). Qed.
Lemma lem3204917 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A s x t) = (term14 A s x t).
Proof. exact (eq_refl (term14 A s x t)). Qed.
Lemma lem3204918 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term9 A x s t) = (term14 A s x t)) = ((term14 A s x t) = (term14 A s x t)).
Proof. exact (MK_COMB (@lem3204914 A s x t) (@lem3204917 A s x t)). Qed.
Lemma lem3204920 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3204921 (x : Prop) : (x = x) = True.
Proof. exact (@lem3204920 Prop x). Qed.
Lemma lem3204922 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term14 A s x t) = (term14 A s x t)) = True.
Proof. exact (@lem3204921 (term14 A s x t)). Qed.
Lemma lem3204923 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term9 A x s t) = (term14 A s x t)) = True.
Proof. exact (TRANS (@lem3204918 A s x t) (@lem3204922 A s x t)). Qed.
Lemma lem3204924 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term31 A).
Proof. exact (fun_ext (fun x : A => @lem3204923 A s x t)). Qed.
Lemma lem3204925 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3204926 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A).
Proof. exact (MK_COMB (@lem3204925 A) (@lem3204924 A s t)). Qed.
Lemma lem3204928 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3204929 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (@lem3204928 A t). Qed.
Lemma lem3204930 {A : Type'} : (term33 A) = True.
Proof. exact (@lem3204929 A True). Qed.
Lemma lem3204931 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = True.
Proof. exact (TRANS (@lem3204926 A s t) (@lem3204930 A)). Qed.
Lemma lem3204932 {A : Type'} (s : A -> Prop) : (term35 A s) = (term36 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3204931 A s t)). Qed.
Lemma lem3204933 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3204934 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A).
Proof. exact (MK_COMB (@lem3204933 A) (@lem3204932 A s)). Qed.
Lemma lem3204936 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3204937 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem3204936 (A -> Prop) t). Qed.
Lemma lem3204938 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3204937 A True). Qed.
Lemma lem3204939 {A : Type'} (s : A -> Prop) : (term37 A s) = True.
Proof. exact (TRANS (@lem3204934 A s) (@lem3204938 A)). Qed.
Lemma lem3204940 {A : Type'} : (term40 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3204939 A s)). Qed.
Lemma lem3204941 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3204942 {A : Type'} : (term41 A) = (term38 A).
Proof. exact (MK_COMB (@lem3204941 A) (@lem3204940 A)). Qed.
Lemma lem3204944 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3204945 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem3204944 (A -> Prop) t). Qed.
Lemma lem3204946 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3204945 A True). Qed.
Lemma lem3204947 {A : Type'} : (term41 A) = True.
Proof. exact (TRANS (@lem3204942 A) (@lem3204946 A)). Qed.
Lemma lem3204948 {A : Type'} : True = (term41 A).
Proof. exact (SYM (@lem3204947 A)). Qed.
Lemma lem3204949 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3204948 A) (@lem0)). Qed.
