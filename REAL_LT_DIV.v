Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_DIV_term_abbrevs.
Require Import REAL_LT_INV_EQ_spec.
Require Import REAL_LT_MUL_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1640852 (x : real) : term0 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1640853 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1640854 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1640853 x) (@lem1640852 x)). Qed.
Lemma lem1640855 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1640854 x y). Qed.
Lemma lem1640856 (x : real) (y : real) : (term2 x y) = ((real_div x y) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1640858 (x : real) : term4 x.
Proof. exact (@lem1590037 x). Qed.
Lemma lem1640859 (x : real) : (term4 x) = ((term5 x) = (term6 x)).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1640861 (x : real) : term7 x.
Proof. exact (@lem1487565 x). Qed.
Lemma lem1640862 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1640863 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1640862 x) (@lem1640861 x)). Qed.
Lemma lem1640864 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1640863 x y). Qed.
Lemma lem1640865 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1640866 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1640865 x y) (@lem1640864 x y)). Qed.
Lemma lem1640867 (x : real) (y : real) (h1 : term11 x y) : term11 x y.
Proof. exact (h1). Qed.
Lemma lem1640868 (x : real) (y : real) (h1 : term11 x y) : term12 x y.
Proof. exact (@lem1640866 x y (@lem1640867 x y h1)). Qed.
Lemma lem1640869 (x : real) (y : real) : (term12 x y) = ((term12 x y) = True).
Proof. exact (@lem7 (term12 x y)). Qed.
Lemma lem1640870 (x : real) (y : real) (h1 : term11 x y) : (term12 x y) = True.
Proof. exact (EQ_MP (@lem1640869 x y) (@lem1640868 x y h1)). Qed.
Lemma lem1640887 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1640888 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem1640887 p q p' q'). Qed.
Lemma lem1640889 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem1640888 p q p'). Qed.
Lemma lem1640890 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1640889 (term11 x y) (term17 x y)). Qed.
Lemma lem1640891 (x : real) (y : real) (p' : Prop) : term18 x y p'.
Proof. exact (@lem1640890 x y p'). Qed.
Lemma lem1640892 (x : real) (y : real) (p' : Prop) : (term18 x y p') = (term19 x y p').
Proof. exact (eq_refl (term18 x y p')). Qed.
Lemma lem1640893 (x : real) (y : real) (p' : Prop) : term19 x y p'.
Proof. exact (EQ_MP (@lem1640892 x y p') (@lem1640891 x y p')). Qed.
Lemma lem1640894 (x : real) (y : real) (p' : Prop) (q' : Prop) : term20 x y p' q'.
Proof. exact (@lem1640893 x y p' q'). Qed.
Lemma lem1640895 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term20 x y p' q') = (term21 x y p' q').
Proof. exact (eq_refl (term20 x y p' q')). Qed.
Lemma lem1640896 (x : real) (y : real) (p' : Prop) (q' : Prop) : term21 x y p' q'.
Proof. exact (EQ_MP (@lem1640895 x y p' q') (@lem1640894 x y p' q')). Qed.
Lemma lem1640899 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1640900 (x : real) (y : real) (q' : Prop) : term22 x y q'.
Proof. exact (@lem1640896 x y (term11 x y) q'). Qed.
Lemma lem1640901 (x : real) (y : real) (q' : Prop) : term23 x y q'.
Proof. exact (@lem1640900 x y q' (@lem1640899 x y)). Qed.
Lemma lem1640902 (x : real) (y : real) (h1 : term11 x y) : term11 x y.
Proof. exact (h1). Qed.
Lemma lem1640903 (x : real) (y : real) (h1 : term11 x y) : term6 y.
Proof. exact (proj2 (@lem1640902 x y h1)). Qed.
Lemma lem1640904 (y : real) : (term6 y) = ((term6 y) = True).
Proof. exact (@lem7 (term6 y)). Qed.
Lemma lem1640906 (x : real) (y : real) (h1 : term11 x y) : term6 x.
Proof. exact (proj1 (@lem1640902 x y h1)). Qed.
Lemma lem1640907 (x : real) : (term6 x) = ((term6 x) = True).
Proof. exact (@lem7 (term6 x)). Qed.
Lemma lem1640910 (x : real) (y : real) : (real_div x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1640856 x y) (@lem1640855 x y)). Qed.
Lemma lem1640911 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1640912 (x : real) (y : real) : (term17 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1640911) (@lem1640910 x y)). Qed.
Lemma lem1640914 (x : real) (y : real) : term26 x y.
Proof. exact (fun h0 : term11 x y => @lem1640870 x y h0). Qed.
Lemma lem1640915 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1640914 x (real_inv y)). Qed.
Lemma lem1640919 (x : real) (y : real) (h1 : term11 x y) : (term6 x) = True.
Proof. exact (EQ_MP (@lem1640907 x) (@lem1640906 x y h1)). Qed.
Lemma lem1640920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640921 (x : real) (y : real) (h1 : term11 x y) : (term28 x) = (and True).
Proof. exact (MK_COMB (@lem1640920) (@lem1640919 x y h1)). Qed.
Lemma lem1640923 (x : real) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem1640859 x) (@lem1640858 x)). Qed.
Lemma lem1640924 (y : real) : (term5 y) = (term6 y).
Proof. exact (@lem1640923 y). Qed.
Lemma lem1640926 (x : real) (y : real) (h1 : term11 x y) : (term6 y) = True.
Proof. exact (EQ_MP (@lem1640904 y) (@lem1640903 x y h1)). Qed.
Lemma lem1640927 (x : real) (y : real) (h1 : term11 x y) : (term5 y) = True.
Proof. exact (TRANS (@lem1640924 y) (@lem1640926 x y h1)). Qed.
Lemma lem1640928 (x : real) (y : real) (h1 : term11 x y) : (term29 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1640921 x y h1) (@lem1640927 x y h1)). Qed.
Lemma lem1640930 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1640931 : (True /\ True) = True.
Proof. exact (@lem1640930 True). Qed.
Lemma lem1640932 (x : real) (y : real) (h1 : term11 x y) : (term29 x y) = True.
Proof. exact (TRANS (@lem1640928 x y h1) (@lem1640931)). Qed.
Lemma lem1640933 (x : real) (y : real) (h1 : term11 x y) : True = (term29 x y).
Proof. exact (SYM (@lem1640932 x y h1)). Qed.
Lemma lem1640934 (x : real) (y : real) (h1 : term11 x y) : term29 x y.
Proof. exact (EQ_MP (@lem1640933 x y h1) (@lem0)). Qed.
Lemma lem1640935 (x : real) (y : real) (h1 : term11 x y) : (term25 x y) = True.
Proof. exact (@lem1640915 x y (@lem1640934 x y h1)). Qed.
Lemma lem1640936 (x : real) (y : real) (h1 : term11 x y) : (term17 x y) = True.
Proof. exact (TRANS (@lem1640912 x y) (@lem1640935 x y h1)). Qed.
Lemma lem1640937 (x : real) (y : real) : term30 x y.
Proof. exact (fun h0 : term11 x y => @lem1640936 x y h0). Qed.
Lemma lem1640938 (x : real) (y : real) : term31 x y.
Proof. exact (@lem1640901 x y True). Qed.
Lemma lem1640939 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (@lem1640938 x y (@lem1640937 x y)). Qed.
Lemma lem1640941 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1640942 (x : real) (y : real) : (term33 x y) = True.
Proof. exact (@lem1640941 (term11 x y)). Qed.
Lemma lem1640943 (x : real) (y : real) : (term32 x y) = True.
Proof. exact (TRANS (@lem1640939 x y) (@lem1640942 x y)). Qed.
Lemma lem1640944 (x : real) : (term34 x) = term35.
Proof. exact (fun_ext (fun y : real => @lem1640943 x y)). Qed.
Lemma lem1640945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640946 (x : real) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1640945) (@lem1640944 x)). Qed.
Lemma lem1640948 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1640949 (t : Prop) : (term39 t) = t.
Proof. exact (@lem1640948 real t). Qed.
Lemma lem1640950 : term37 = True.
Proof. exact (@lem1640949 True). Qed.
Lemma lem1640951 (x : real) : (term36 x) = True.
Proof. exact (TRANS (@lem1640946 x) (@lem1640950)). Qed.
Lemma lem1640952 : term40 = term35.
Proof. exact (fun_ext (fun x : real => @lem1640951 x)). Qed.
Lemma lem1640953 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640954 : term41 = term37.
Proof. exact (MK_COMB (@lem1640953) (@lem1640952)). Qed.
Lemma lem1640956 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1640957 (t : Prop) : (term39 t) = t.
Proof. exact (@lem1640956 real t). Qed.
Lemma lem1640958 : term37 = True.
Proof. exact (@lem1640957 True). Qed.
Lemma lem1640959 : term41 = True.
Proof. exact (TRANS (@lem1640954) (@lem1640958)). Qed.
Lemma lem1640960 : True = term41.
Proof. exact (SYM (@lem1640959)). Qed.
Lemma lem1640961 : term41.
Proof. exact (EQ_MP (@lem1640960) (@lem0)). Qed.
