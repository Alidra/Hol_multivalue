Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_RAND_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem12861 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem12862 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem12863 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem12862 b) (@lem12861 b)). Qed.
Lemma lem12864 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem12865 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem12866 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term2 A B x f y) = (term2 A B x f y).
Proof. exact (eq_refl (term2 A B x f y)). Qed.
Lemma lem12867 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = True) : (term3 A B x f y b) = (term4 A B x f y).
Proof. exact (MK_COMB (@lem12866 A B x f y) (@lem12864 b h1)). Qed.
Lemma lem12868 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term4 A B x f y) = ((term5 A B f x y) = (term6 A B x f y)).
Proof. exact (eq_refl (term4 A B x f y)). Qed.
Lemma lem12869 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) : (term7 A B x f y b) = (term7 A B x f y b).
Proof. exact (eq_refl (term7 A B x f y b)). Qed.
Lemma lem12870 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : ((term3 A B x f y b) = (term4 A B x f y)) = ((term3 A B x f y b) = ((term5 A B f x y) = (term6 A B x f y))).
Proof. exact (MK_COMB (@lem12869 A B x f y b) (@lem12868 A B x f y)). Qed.
Lemma lem12871 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term3 A B x f y b) = ((term8 A B f b x y) = (term9 A B b x f y)).
Proof. exact (eq_refl (term3 A B x f y b)). Qed.
Lemma lem12872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12873 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term7 A B x f y b) = (term10 A B b x f y).
Proof. exact (MK_COMB (@lem12872) (@lem12871 A B b x f y)). Qed.
Lemma lem12874 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term5 A B f x y) = (term6 A B x f y)) = ((term5 A B f x y) = (term6 A B x f y)).
Proof. exact (eq_refl ((term5 A B f x y) = (term6 A B x f y))). Qed.
Lemma lem12875 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : ((term3 A B x f y b) = ((term5 A B f x y) = (term6 A B x f y))) = (((term8 A B f b x y) = (term9 A B b x f y)) = ((term5 A B f x y) = (term6 A B x f y))).
Proof. exact (MK_COMB (@lem12873 A B b x f y) (@lem12874 A B x f y)). Qed.
Lemma lem12876 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : ((term3 A B x f y b) = (term4 A B x f y)) = (((term8 A B f b x y) = (term9 A B b x f y)) = ((term5 A B f x y) = (term6 A B x f y))).
Proof. exact (TRANS (@lem12870 A B b x f y) (@lem12875 A B b x f y)). Qed.
Lemma lem12877 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = True) : ((term8 A B f b x y) = (term9 A B b x f y)) = ((term5 A B f x y) = (term6 A B x f y)).
Proof. exact (EQ_MP (@lem12876 A B b x f y) (@lem12867 A B x f y b h1)). Qed.
Lemma lem12878 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = True) : ((term5 A B f x y) = (term6 A B x f y)) = ((term8 A B f b x y) = (term9 A B b x f y)).
Proof. exact (SYM (@lem12877 A B x f y b h1)). Qed.
Lemma lem12879 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term2 A B x f y) = (term2 A B x f y).
Proof. exact (eq_refl (term2 A B x f y)). Qed.
Lemma lem12880 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = False) : (term3 A B x f y b) = (term11 A B x f y).
Proof. exact (MK_COMB (@lem12879 A B x f y) (@lem12865 b h1)). Qed.
Lemma lem12881 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term11 A B x f y) = ((term12 A B f x y) = (term13 A B x f y)).
Proof. exact (eq_refl (term11 A B x f y)). Qed.
Lemma lem12882 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) : (term7 A B x f y b) = (term7 A B x f y b).
Proof. exact (eq_refl (term7 A B x f y b)). Qed.
Lemma lem12883 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : ((term3 A B x f y b) = (term11 A B x f y)) = ((term3 A B x f y b) = ((term12 A B f x y) = (term13 A B x f y))).
Proof. exact (MK_COMB (@lem12882 A B x f y b) (@lem12881 A B x f y)). Qed.
Lemma lem12884 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term3 A B x f y b) = ((term8 A B f b x y) = (term9 A B b x f y)).
Proof. exact (eq_refl (term3 A B x f y b)). Qed.
Lemma lem12885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem12886 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term7 A B x f y b) = (term10 A B b x f y).
Proof. exact (MK_COMB (@lem12885) (@lem12884 A B b x f y)). Qed.
Lemma lem12887 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term12 A B f x y) = (term13 A B x f y)) = ((term12 A B f x y) = (term13 A B x f y)).
Proof. exact (eq_refl ((term12 A B f x y) = (term13 A B x f y))). Qed.
Lemma lem12888 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : ((term3 A B x f y b) = ((term12 A B f x y) = (term13 A B x f y))) = (((term8 A B f b x y) = (term9 A B b x f y)) = ((term12 A B f x y) = (term13 A B x f y))).
Proof. exact (MK_COMB (@lem12886 A B b x f y) (@lem12887 A B x f y)). Qed.
Lemma lem12889 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : ((term3 A B x f y b) = (term11 A B x f y)) = (((term8 A B f b x y) = (term9 A B b x f y)) = ((term12 A B f x y) = (term13 A B x f y))).
Proof. exact (TRANS (@lem12883 A B b x f y) (@lem12888 A B b x f y)). Qed.
Lemma lem12890 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = False) : ((term8 A B f b x y) = (term9 A B b x f y)) = ((term12 A B f x y) = (term13 A B x f y)).
Proof. exact (EQ_MP (@lem12889 A B b x f y) (@lem12880 A B x f y b h1)). Qed.
Lemma lem12891 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = False) : ((term12 A B f x y) = (term13 A B x f y)) = ((term8 A B f b x y) = (term9 A B b x f y)).
Proof. exact (SYM (@lem12890 A B x f y b h1)). Qed.
Lemma lem12895 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem12896 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem12895 A t2 t1). Qed.
Lemma lem12897 {A : Type'} (y : A) (x : A) : (@COND A True x y) = x.
Proof. exact (@lem12896 A y x). Qed.
Lemma lem12898 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem12899 {A B : Type'} (y : A) (f : A -> B) (x : A) : (term5 A B f x y) = (f x).
Proof. exact (MK_COMB (@lem12898 A B f) (@lem12897 A y x)). Qed.
Lemma lem12900 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem12901 {A B : Type'} (y : A) (f : A -> B) (x : A) : (term14 A B f x y) = (term15 A B f x).
Proof. exact (MK_COMB (@lem12900 B) (@lem12899 A B y f x)). Qed.
Lemma lem12903 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem12904 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem12903 B t2 t1). Qed.
Lemma lem12905 {A B : Type'} (y : A) (f : A -> B) (x : A) : (term6 A B x f y) = (f x).
Proof. exact (@lem12904 B (f y) (f x)). Qed.
Lemma lem12906 {A B : Type'} (y : A) (f : A -> B) (x : A) : ((term5 A B f x y) = (term6 A B x f y)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem12901 A B y f x) (@lem12905 A B y f x)). Qed.
Lemma lem12908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12909 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem12908 B x). Qed.
Lemma lem12910 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem12909 B (f x)). Qed.
Lemma lem12911 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term5 A B f x y) = (term6 A B x f y)) = True.
Proof. exact (TRANS (@lem12906 A B y f x) (@lem12910 A B f x)). Qed.
Lemma lem12912 {A B : Type'} (x : A) (f : A -> B) (y : A) : True = ((term5 A B f x y) = (term6 A B x f y)).
Proof. exact (SYM (@lem12911 A B x f y)). Qed.
Lemma lem12913 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term5 A B f x y) = (term6 A B x f y).
Proof. exact (EQ_MP (@lem12912 A B x f y) (@lem0)). Qed.
Lemma lem12917 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem12918 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem12917 A t1 t2). Qed.
Lemma lem12919 {A : Type'} (x : A) (y : A) : (@COND A False x y) = y.
Proof. exact (@lem12918 A x y). Qed.
Lemma lem12920 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem12921 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term12 A B f x y) = (f y).
Proof. exact (MK_COMB (@lem12920 A B f) (@lem12919 A x y)). Qed.
Lemma lem12922 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem12923 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term16 A B f x y) = (term15 A B f y).
Proof. exact (MK_COMB (@lem12922 B) (@lem12921 A B x f y)). Qed.
Lemma lem12925 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem12926 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem12925 B t1 t2). Qed.
Lemma lem12927 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term13 A B x f y) = (f y).
Proof. exact (@lem12926 B (f x) (f y)). Qed.
Lemma lem12928 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term12 A B f x y) = (term13 A B x f y)) = ((f y) = (f y)).
Proof. exact (MK_COMB (@lem12923 A B x f y) (@lem12927 A B x f y)). Qed.
Lemma lem12930 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem12931 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem12930 B x). Qed.
Lemma lem12932 {A B : Type'} (f : A -> B) (y : A) : ((f y) = (f y)) = True.
Proof. exact (@lem12931 B (f y)). Qed.
Lemma lem12933 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((term12 A B f x y) = (term13 A B x f y)) = True.
Proof. exact (TRANS (@lem12928 A B x f y) (@lem12932 A B f y)). Qed.
Lemma lem12934 {A B : Type'} (x : A) (f : A -> B) (y : A) : True = ((term12 A B f x y) = (term13 A B x f y)).
Proof. exact (SYM (@lem12933 A B x f y)). Qed.
Lemma lem12935 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term12 A B f x y) = (term13 A B x f y).
Proof. exact (EQ_MP (@lem12934 A B x f y) (@lem0)). Qed.
Lemma lem12936 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = False) : (term8 A B f b x y) = (term9 A B b x f y).
Proof. exact (EQ_MP (@lem12891 A B x f y b h1) (@lem12935 A B x f y)). Qed.
Lemma lem12937 {A B : Type'} (x : A) (f : A -> B) (y : A) (b : Prop) (h1 : b = True) : (term8 A B f b x y) = (term9 A B b x f y).
Proof. exact (EQ_MP (@lem12878 A B x f y b h1) (@lem12913 A B x f y)). Qed.
Lemma lem12938 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term8 A B f b x y) = (term9 A B b x f y).
Proof. exact (or_elim (@lem12863 b) (fun h0 : b = True => @lem12937 A B x f y b h0) (fun h0 : b = False => @lem12936 A B x f y b h0)). Qed.
Lemma lem12943 {A B : Type'} (b : Prop) (x : A) (f : A -> B) : term17 A B b x f.
Proof. exact (fun y : A => @lem12938 A B b x f y). Qed.
Lemma lem12948 {A B : Type'} (b : Prop) (f : A -> B) : term18 A B b f.
Proof. exact (fun x : A => @lem12943 A B b x f). Qed.
Lemma lem12953 {A B : Type'} (b : Prop) : term19 A B b.
Proof. exact (fun f : A -> B => @lem12948 A B b f). Qed.
Lemma lem12958 {A B : Type'} : term20 A B.
Proof. exact (fun b : Prop => @lem12953 A B b). Qed.
