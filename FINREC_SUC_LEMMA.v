Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINREC_SUC_LEMMA_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINREC_1_LEMMA_spec.
Require Import IN_DELETE_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1820_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3791009_spec.
Require Import thm3791010_spec.
Require Import thm3791024_spec.
Require Import thm3791025_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem3794822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3794823 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3794822 A s t). Qed.
Lemma lem3794824 {A : Type'} (s : A -> Prop) (y : A) (x : A) : ((term1 A s x y) = (term1 A s y x)) = (term2 A s y x).
Proof. exact (@lem3794823 A (term1 A s x y) (term1 A s y x)). Qed.
Lemma lem3794833 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term2 A s y x) = ((term1 A s x y) = (term1 A s y x)).
Proof. exact (SYM (@lem3794824 A s y x)). Qed.
Lemma lem3794841 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3794842 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (@lem3794841 A s x y). Qed.
Lemma lem3794843 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term5 A x' s x y) = (term6 A s x x' y).
Proof. exact (@lem3794842 A (@DELETE A s x) x' y). Qed.
Lemma lem3794847 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3794848 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (@lem3794847 A s x y). Qed.
Lemma lem3794849 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term3 A x' s x) = (term4 A s x' x).
Proof. exact (@lem3794848 A s x' x). Qed.
Lemma lem3794853 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3794854 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3794853 A P x). Qed.
Lemma lem3794855 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3794854 A s x'). Qed.
Lemma lem3794856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3794857 {A : Type'} (s : A -> Prop) (x' : A) : (term7 A x' s) = (term8 A s x').
Proof. exact (MK_COMB (@lem3794856) (@lem3794855 A s x')). Qed.
Lemma lem3794860 {A : Type'} (x' : A) (x : A) : (term9 A x' x) = (term9 A x' x).
Proof. exact (eq_refl (term9 A x' x)). Qed.
Lemma lem3794861 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term4 A s x' x) = (term10 A s x' x).
Proof. exact (MK_COMB (@lem3794857 A s x') (@lem3794860 A x' x)). Qed.
Lemma lem3794864 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term3 A x' s x) = (term10 A s x' x).
Proof. exact (TRANS (@lem3794849 A s x' x) (@lem3794861 A s x' x)). Qed.
Lemma lem3794865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3794866 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term12 A s x' x).
Proof. exact (MK_COMB (@lem3794865) (@lem3794864 A s x' x)). Qed.
Lemma lem3794869 {A : Type'} (x' : A) (y : A) : (term9 A x' y) = (term9 A x' y).
Proof. exact (eq_refl (term9 A x' y)). Qed.
Lemma lem3794870 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term6 A s x x' y) = (term13 A s x x' y).
Proof. exact (MK_COMB (@lem3794866 A s x' x) (@lem3794869 A x' y)). Qed.
Lemma lem3794873 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term5 A x' s x y) = (term13 A s x x' y).
Proof. exact (TRANS (@lem3794843 A s x x' y) (@lem3794870 A s x x' y)). Qed.
Lemma lem3794874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3794875 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term14 A x' s x y) = (term15 A s x x' y).
Proof. exact (MK_COMB (@lem3794874) (@lem3794873 A s x x' y)). Qed.
Lemma lem3794877 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3794878 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (@lem3794877 A s x y). Qed.
Lemma lem3794879 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term5 A x' s y x) = (term6 A s y x' x).
Proof. exact (@lem3794878 A (@DELETE A s y) x' x). Qed.
Lemma lem3794883 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3794884 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (@lem3794883 A s x y). Qed.
Lemma lem3794885 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term3 A x' s y) = (term4 A s x' y).
Proof. exact (@lem3794884 A s x' y). Qed.
Lemma lem3794889 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3794890 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3794889 A P x). Qed.
Lemma lem3794891 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3794890 A s x'). Qed.
Lemma lem3794892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3794893 {A : Type'} (s : A -> Prop) (x' : A) : (term7 A x' s) = (term8 A s x').
Proof. exact (MK_COMB (@lem3794892) (@lem3794891 A s x')). Qed.
Lemma lem3794896 {A : Type'} (x' : A) (y : A) : (term9 A x' y) = (term9 A x' y).
Proof. exact (eq_refl (term9 A x' y)). Qed.
Lemma lem3794897 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term4 A s x' y) = (term10 A s x' y).
Proof. exact (MK_COMB (@lem3794893 A s x') (@lem3794896 A x' y)). Qed.
Lemma lem3794900 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term3 A x' s y) = (term10 A s x' y).
Proof. exact (TRANS (@lem3794885 A s x' y) (@lem3794897 A s x' y)). Qed.
Lemma lem3794901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3794902 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term11 A x' s y) = (term12 A s x' y).
Proof. exact (MK_COMB (@lem3794901) (@lem3794900 A s x' y)). Qed.
Lemma lem3794905 {A : Type'} (x' : A) (x : A) : (term9 A x' x) = (term9 A x' x).
Proof. exact (eq_refl (term9 A x' x)). Qed.
Lemma lem3794906 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term6 A s y x' x) = (term13 A s y x' x).
Proof. exact (MK_COMB (@lem3794902 A s x' y) (@lem3794905 A x' x)). Qed.
Lemma lem3794909 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term5 A x' s y x) = (term13 A s y x' x).
Proof. exact (TRANS (@lem3794879 A s y x' x) (@lem3794906 A s y x' x)). Qed.
Lemma lem3794910 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : ((term5 A x' s x y) = (term5 A x' s y x)) = ((term13 A s x x' y) = (term13 A s y x' x)).
Proof. exact (MK_COMB (@lem3794875 A s x x' y) (@lem3794909 A s y x' x)). Qed.
Lemma lem3794913 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term16 A s y x) = (term17 A s y x).
Proof. exact (fun_ext (fun x' : A => @lem3794910 A s y x' x)). Qed.
Lemma lem3794914 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3794915 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term2 A s y x) = (term18 A s y x).
Proof. exact (MK_COMB (@lem3794914 A) (@lem3794913 A s y x)). Qed.
Lemma lem3794920 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term18 A s y x) = (term2 A s y x).
Proof. exact (SYM (@lem3794915 A s y x)). Qed.
Lemma lem3794922 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3794923 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term18 A s y x) = (term20 A s y x).
Proof. exact (@lem3794922 (term18 A s y x)). Qed.
Lemma lem3794924 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term20 A s y x) = (term18 A s y x).
Proof. exact (SYM (@lem3794923 A s y x)). Qed.
Lemma lem3794925 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term21 A s y x) : term21 A s y x.
Proof. exact (h1). Qed.
Lemma lem3794928 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term20 A s y x) : term20 A s y x.
Proof. exact (h1). Qed.
Lemma lem3794929 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term22 A s y x.
Proof. exact (fun h0 : term20 A s y x => @lem3794928 A s y x h0). Qed.
Lemma lem3794930 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term22 A s y x) : term22 A s y x.
Proof. exact (h1). Qed.
Lemma lem3794931 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term20 A s y x) : term20 A s y x.
Proof. exact (h1). Qed.
Lemma lem3794932 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term20 A s y x) (h2 : term22 A s y x) : term20 A s y x.
Proof. exact (@lem3794930 A s y x h2 (@lem3794931 A s y x h1)). Qed.
Lemma lem3794933 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term20 A s y x) : term23 A s y x.
Proof. exact (fun h0 : term22 A s y x => @lem3794932 A s y x h1 h0). Qed.
Lemma lem3794934 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term22 A s y x) : term22 A s y x.
Proof. exact (h1). Qed.
Lemma lem3794935 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term20 A s y x) (h2 : term22 A s y x) : term20 A s y x.
Proof. exact (@lem3794933 A s y x h1 (@lem3794934 A s y x h2)). Qed.
Lemma lem3794936 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term22 A s y x) : term22 A s y x.
Proof. exact (fun h0 : term20 A s y x => @lem3794935 A s y x h0 h1). Qed.
Lemma lem3794937 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term24 A s y x.
Proof. exact (fun h0 : term22 A s y x => @lem3794936 A s y x h0). Qed.
Lemma lem3794940 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term22 A s y x.
Proof. exact (@lem3794937 A s y x (@lem3794929 A s y x)). Qed.
Lemma lem3794941 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term22 A s y x.
Proof. exact (@lem3794940 A s y x). Qed.
Lemma lem3794955 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3794956 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term20 A s y x) = (term25 A s y x).
Proof. exact (@lem3794955 (term21 A s y x)). Qed.
Lemma lem3794958 (t : Prop) : (term26 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3794959 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term25 A s y x) = (term18 A s y x).
Proof. exact (@lem3794958 (term18 A s y x)). Qed.
Lemma lem3794964 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term20 A s y x) = (term18 A s y x).
Proof. exact (TRANS (@lem3794956 A s y x) (@lem3794959 A s y x)). Qed.
Lemma lem3794973 {A : Type'} (y : A) (x : A) : (term27 A y x) = (term28 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3794964 A s y x)). Qed.
Lemma lem3794974 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3794975 {A : Type'} (y : A) (x : A) : (term29 A y x) = (term30 A y x).
Proof. exact (MK_COMB (@lem3794974 A) (@lem3794973 A y x)). Qed.
Lemma lem3794980 {A : Type'} (x : A) : (term31 A x) = (term32 A x).
Proof. exact (fun_ext (fun y : A => @lem3794975 A y x)). Qed.
Lemma lem3794981 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3794982 {A : Type'} (x : A) : (term33 A x) = (term34 A x).
Proof. exact (MK_COMB (@lem3794981 A) (@lem3794980 A x)). Qed.
Lemma lem3794987 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (fun_ext (fun x : A => @lem3794982 A x)). Qed.
Lemma lem3794988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3794997 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (MK_COMB (@lem3794988 A) (@lem3794987 A)). Qed.
Lemma lem3795026 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : ((term13 A s x x' y) = (term13 A s y x' x)) = ((term13 A s x x' y) = (term13 A s y x' x)).
Proof. exact (eq_refl ((term13 A s x x' y) = (term13 A s y x' x))). Qed.
Lemma lem3795027 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term17 A s y x) = (term17 A s y x).
Proof. exact (fun_ext (fun x' : A => @lem3795026 A s y x' x)). Qed.
Lemma lem3795028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3795029 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term18 A s y x) = (term18 A s y x).
Proof. exact (MK_COMB (@lem3795028 A) (@lem3795027 A s y x)). Qed.
Lemma lem3795030 {A : Type'} (y : A) (x : A) : (term28 A y x) = (term28 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3795029 A s y x)). Qed.
Lemma lem3795031 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3795032 {A : Type'} (y : A) (x : A) : (term30 A y x) = (term30 A y x).
Proof. exact (MK_COMB (@lem3795031 A) (@lem3795030 A y x)). Qed.
Lemma lem3795033 {A : Type'} (x : A) : (term32 A x) = (term32 A x).
Proof. exact (fun_ext (fun y : A => @lem3795032 A y x)). Qed.
Lemma lem3795034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3795035 {A : Type'} (x : A) : (term34 A x) = (term34 A x).
Proof. exact (MK_COMB (@lem3795034 A) (@lem3795033 A x)). Qed.
Lemma lem3795036 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (fun_ext (fun x : A => @lem3795035 A x)). Qed.
Lemma lem3795037 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3795038 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (MK_COMB (@lem3795037 A) (@lem3795036 A)). Qed.
Lemma lem3795073 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (TRANS (@lem3794997 A) (@lem3795038 A)). Qed.
Lemma lem3795074 {A : Type'} : (term38 A) = (term37 A).
Proof. exact (SYM (@lem3795073 A)). Qed.
Lemma lem3795076 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3795077 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : ((term13 A s x x' y) = (term13 A s y x' x)) = (term39 A s y x' x).
Proof. exact (@lem3795076 ((term13 A s x x' y) = (term13 A s y x' x))). Qed.
Lemma lem3795078 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term39 A s y x' x) = ((term13 A s x x' y) = (term13 A s y x' x)).
Proof. exact (SYM (@lem3795077 A s y x' x)). Qed.
Lemma lem3795079 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term40 A s y x' x) : term40 A s y x' x.
Proof. exact (h1). Qed.
Lemma lem3795085 {A : Type'} (x' : A) (x : A) : (term41 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3795087 {A : Type'} (s : A -> Prop) (x' : A) : (term42 A s x') = (term42 A s x').
Proof. exact (eq_refl (term42 A s x')). Qed.
Lemma lem3795088 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term43 A s x' x) = (term44 A s x' x).
Proof. exact (MK_COMB (@lem3795087 A s x') (@lem3795085 A x' x)). Qed.
Lemma lem3795089 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term43 A s x' x).
Proof. exact (@lem17045 (s x') (term9 A x' x)). Qed.
Lemma lem3795090 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term45 A s x' x) = (term44 A s x' x).
Proof. exact (TRANS (@lem3795089 A s x' x) (@lem3795088 A s x' x)). Qed.
Lemma lem3795097 {A : Type'} (x' : A) (y : A) : (term41 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3795098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3795099 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term46 A s x' x) = (term47 A s x' x).
Proof. exact (MK_COMB (@lem3795098) (@lem3795090 A s x' x)). Qed.
Lemma lem3795100 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term48 A s x x' y) = (term49 A s x x' y).
Proof. exact (MK_COMB (@lem3795099 A s x' x) (@lem3795097 A x' y)). Qed.
Lemma lem3795101 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term50 A s x x' y) = (term48 A s x x' y).
Proof. exact (@lem17045 (term10 A s x' x) (term9 A x' y)). Qed.
Lemma lem3795102 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term50 A s x x' y) = (term49 A s x x' y).
Proof. exact (TRANS (@lem3795101 A s x x' y) (@lem3795100 A s x x' y)). Qed.
Lemma lem3795111 {A : Type'} (x' : A) (y : A) : (term41 A x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem3795113 {A : Type'} (s : A -> Prop) (x' : A) : (term42 A s x') = (term42 A s x').
Proof. exact (eq_refl (term42 A s x')). Qed.
Lemma lem3795114 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term43 A s x' y) = (term44 A s x' y).
Proof. exact (MK_COMB (@lem3795113 A s x') (@lem3795111 A x' y)). Qed.
Lemma lem3795115 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term45 A s x' y) = (term43 A s x' y).
Proof. exact (@lem17045 (s x') (term9 A x' y)). Qed.
Lemma lem3795116 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term45 A s x' y) = (term44 A s x' y).
Proof. exact (TRANS (@lem3795115 A s x' y) (@lem3795114 A s x' y)). Qed.
Lemma lem3795123 {A : Type'} (x' : A) (x : A) : (term41 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3795124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3795125 {A : Type'} (s : A -> Prop) (x' : A) (y : A) : (term46 A s x' y) = (term47 A s x' y).
Proof. exact (MK_COMB (@lem3795124) (@lem3795116 A s x' y)). Qed.
Lemma lem3795126 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term48 A s y x' x) = (term49 A s y x' x).
Proof. exact (MK_COMB (@lem3795125 A s x' y) (@lem3795123 A x' x)). Qed.
Lemma lem3795127 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term50 A s y x' x) = (term48 A s y x' x).
Proof. exact (@lem17045 (term10 A s x' y) (term9 A x' x)). Qed.
Lemma lem3795128 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term50 A s y x' x) = (term49 A s y x' x).
Proof. exact (TRANS (@lem3795127 A s y x' x) (@lem3795126 A s y x' x)). Qed.
Lemma lem3795131 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term13 A s y x' x) = (term13 A s y x' x).
Proof. exact (eq_refl (term13 A s y x' x)). Qed.
Lemma lem3795132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3795133 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term51 A s x x' y) = (term52 A s x x' y).
Proof. exact (MK_COMB (@lem3795132) (@lem3795102 A s x x' y)). Qed.
Lemma lem3795134 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term53 A s y x' x) = (term54 A s y x' x).
Proof. exact (MK_COMB (@lem3795133 A s x x' y) (@lem3795131 A s y x' x)). Qed.
Lemma lem3795136 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) : (term55 A s x x' y) = (term55 A s x x' y).
Proof. exact (eq_refl (term55 A s x x' y)). Qed.
Lemma lem3795137 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term56 A s y x' x) = (term57 A s y x' x).
Proof. exact (MK_COMB (@lem3795136 A s x x' y) (@lem3795128 A s y x' x)). Qed.
Lemma lem3795138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3795139 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term58 A s y x' x) = (term59 A s y x' x).
Proof. exact (MK_COMB (@lem3795138) (@lem3795137 A s y x' x)). Qed.
Lemma lem3795140 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term60 A s y x' x) = (term61 A s y x' x).
Proof. exact (MK_COMB (@lem3795139 A s y x' x) (@lem3795134 A s y x' x)). Qed.
Lemma lem3795141 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term40 A s y x' x) = (term60 A s y x' x).
Proof. exact (@lem17646 (term13 A s x x' y) (term13 A s y x' x)). Qed.
Lemma lem3795146 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term40 A s y x' x) = (term61 A s y x' x).
Proof. exact (TRANS (@lem3795141 A s y x' x) (@lem3795140 A s y x' x)). Qed.
Lemma lem3795245 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term40 A s y x' x) : term61 A s y x' x.
Proof. exact (EQ_MP (@lem3795146 A s y x' x) (@lem3795079 A s y x' x h1)). Qed.
Lemma lem3795246 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : term57 A s y x' x.
Proof. exact (h1). Qed.
Lemma lem3795247 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : term54 A s y x' x.
Proof. exact (h1). Qed.
Lemma lem3795248 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : term49 A s y x' x.
Proof. exact (proj2 (@lem3795246 A s y x' x h1)). Qed.
Lemma lem3795249 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : term13 A s x x' y.
Proof. exact (proj1 (@lem3795246 A s y x' x h1)). Qed.
Lemma lem3795251 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : term10 A s x' x.
Proof. exact (proj1 (@lem3795249 A s y x' x h1)). Qed.
Lemma lem3795254 {A : Type'} (s : A -> Prop) (x' : A) (y : A) (h1 : term44 A s x' y) : term44 A s x' y.
Proof. exact (h1). Qed.
Lemma lem3795258 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : term13 A s y x' x.
Proof. exact (proj2 (@lem3795247 A s y x' x h1)). Qed.
Lemma lem3795259 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : term49 A s x x' y.
Proof. exact (proj1 (@lem3795247 A s y x' x h1)). Qed.
Lemma lem3795261 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : term10 A s x' y.
Proof. exact (proj1 (@lem3795258 A s y x' x h1)). Qed.
Lemma lem3795264 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term44 A s x' x) : term44 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3795283 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3795299 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3795315 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3795331 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3795347 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3795363 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3795371 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3795373 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : term9 A x' y.
Proof. exact (proj2 (@lem3795249 A s y x' x h1)). Qed.
Lemma lem3795379 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3795385 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : term9 A x' x.
Proof. exact (proj2 (@lem3795251 A s y x' x h1)). Qed.
Lemma lem3795387 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3795395 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term62 A s x'.
Proof. exact (h1). Qed.
Lemma lem3795397 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : term9 A x' x.
Proof. exact (proj2 (@lem3795258 A s y x' x h1)). Qed.
Lemma lem3795403 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3795409 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : term9 A x' y.
Proof. exact (proj2 (@lem3795261 A s y x' x h1)). Qed.
Lemma lem3795411 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3795426 {A : Type'} (y : A) : (term63 A y) = (term63 A y).
Proof. exact (eq_refl (term63 A y)). Qed.
Lemma lem3795427 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term64 A y x') = (term65 A y).
Proof. exact (MK_COMB (@lem3795426 A y) (@lem3795379 A x' y h1)). Qed.
Lemma lem3795428 {A : Type'} (y : A) : (term65 A y) = (term66 A y).
Proof. exact (eq_refl (term65 A y)). Qed.
Lemma lem3795429 {A : Type'} (y : A) (x' : A) : (term67 A y x') = (term67 A y x').
Proof. exact (eq_refl (term67 A y x')). Qed.
Lemma lem3795430 {A : Type'} (x' : A) (y : A) : ((term64 A y x') = (term65 A y)) = ((term64 A y x') = (term66 A y)).
Proof. exact (MK_COMB (@lem3795429 A y x') (@lem3795428 A y)). Qed.
Lemma lem3795431 {A : Type'} (x' : A) (y : A) : (term64 A y x') = (term9 A x' y).
Proof. exact (eq_refl (term64 A y x')). Qed.
Lemma lem3795432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3795433 {A : Type'} (x' : A) (y : A) : (term67 A y x') = (term68 A x' y).
Proof. exact (MK_COMB (@lem3795432) (@lem3795431 A x' y)). Qed.
Lemma lem3795434 {A : Type'} (y : A) : (term66 A y) = (term66 A y).
Proof. exact (eq_refl (term66 A y)). Qed.
Lemma lem3795435 {A : Type'} (x' : A) (y : A) : ((term64 A y x') = (term66 A y)) = ((term9 A x' y) = (term66 A y)).
Proof. exact (MK_COMB (@lem3795433 A x' y) (@lem3795434 A y)). Qed.
Lemma lem3795436 {A : Type'} (x' : A) (y : A) : ((term64 A y x') = (term65 A y)) = ((term9 A x' y) = (term66 A y)).
Proof. exact (TRANS (@lem3795430 A x' y) (@lem3795435 A x' y)). Qed.
Lemma lem3795437 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term9 A x' y) = (term66 A y).
Proof. exact (EQ_MP (@lem3795436 A x' y) (@lem3795427 A x' y h1)). Qed.
Lemma lem3795438 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : term66 A y.
Proof. exact (EQ_MP (@lem3795437 A x' y h2) (@lem3795373 A s y x' x h1)). Qed.
Lemma lem3795505 {A : Type'} (x : A) : (term63 A x) = (term63 A x).
Proof. exact (eq_refl (term63 A x)). Qed.
Lemma lem3795506 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term64 A x x') = (term65 A x).
Proof. exact (MK_COMB (@lem3795505 A x) (@lem3795387 A x' x h1)). Qed.
Lemma lem3795507 {A : Type'} (x : A) : (term65 A x) = (term66 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3795508 {A : Type'} (x : A) (x' : A) : (term67 A x x') = (term67 A x x').
Proof. exact (eq_refl (term67 A x x')). Qed.
Lemma lem3795509 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term64 A x x') = (term66 A x)).
Proof. exact (MK_COMB (@lem3795508 A x x') (@lem3795507 A x)). Qed.
Lemma lem3795510 {A : Type'} (x' : A) (x : A) : (term64 A x x') = (term9 A x' x).
Proof. exact (eq_refl (term64 A x x')). Qed.
Lemma lem3795511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3795512 {A : Type'} (x' : A) (x : A) : (term67 A x x') = (term68 A x' x).
Proof. exact (MK_COMB (@lem3795511) (@lem3795510 A x' x)). Qed.
Lemma lem3795513 {A : Type'} (x : A) : (term66 A x) = (term66 A x).
Proof. exact (eq_refl (term66 A x)). Qed.
Lemma lem3795514 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term66 A x)) = ((term9 A x' x) = (term66 A x)).
Proof. exact (MK_COMB (@lem3795512 A x' x) (@lem3795513 A x)). Qed.
Lemma lem3795515 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term9 A x' x) = (term66 A x)).
Proof. exact (TRANS (@lem3795509 A x' x) (@lem3795514 A x' x)). Qed.
Lemma lem3795516 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term9 A x' x) = (term66 A x).
Proof. exact (EQ_MP (@lem3795515 A x' x) (@lem3795506 A x' x h1)). Qed.
Lemma lem3795517 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : term66 A x.
Proof. exact (EQ_MP (@lem3795516 A x' x h2) (@lem3795385 A s y x' x h1)). Qed.
Lemma lem3795532 {A : Type'} (x : A) : (term63 A x) = (term63 A x).
Proof. exact (eq_refl (term63 A x)). Qed.
Lemma lem3795533 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term64 A x x') = (term65 A x).
Proof. exact (MK_COMB (@lem3795532 A x) (@lem3795403 A x' x h1)). Qed.
Lemma lem3795534 {A : Type'} (x : A) : (term65 A x) = (term66 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3795535 {A : Type'} (x : A) (x' : A) : (term67 A x x') = (term67 A x x').
Proof. exact (eq_refl (term67 A x x')). Qed.
Lemma lem3795536 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term64 A x x') = (term66 A x)).
Proof. exact (MK_COMB (@lem3795535 A x x') (@lem3795534 A x)). Qed.
Lemma lem3795537 {A : Type'} (x' : A) (x : A) : (term64 A x x') = (term9 A x' x).
Proof. exact (eq_refl (term64 A x x')). Qed.
Lemma lem3795538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3795539 {A : Type'} (x' : A) (x : A) : (term67 A x x') = (term68 A x' x).
Proof. exact (MK_COMB (@lem3795538) (@lem3795537 A x' x)). Qed.
Lemma lem3795540 {A : Type'} (x : A) : (term66 A x) = (term66 A x).
Proof. exact (eq_refl (term66 A x)). Qed.
Lemma lem3795541 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term66 A x)) = ((term9 A x' x) = (term66 A x)).
Proof. exact (MK_COMB (@lem3795539 A x' x) (@lem3795540 A x)). Qed.
Lemma lem3795542 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term9 A x' x) = (term66 A x)).
Proof. exact (TRANS (@lem3795536 A x' x) (@lem3795541 A x' x)). Qed.
Lemma lem3795543 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term9 A x' x) = (term66 A x).
Proof. exact (EQ_MP (@lem3795542 A x' x) (@lem3795533 A x' x h1)). Qed.
Lemma lem3795544 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : term66 A x.
Proof. exact (EQ_MP (@lem3795543 A x' x h2) (@lem3795397 A s y x' x h1)). Qed.
Lemma lem3795611 {A : Type'} (y : A) : (term63 A y) = (term63 A y).
Proof. exact (eq_refl (term63 A y)). Qed.
Lemma lem3795612 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term64 A y x') = (term65 A y).
Proof. exact (MK_COMB (@lem3795611 A y) (@lem3795411 A x' y h1)). Qed.
Lemma lem3795613 {A : Type'} (y : A) : (term65 A y) = (term66 A y).
Proof. exact (eq_refl (term65 A y)). Qed.
Lemma lem3795614 {A : Type'} (y : A) (x' : A) : (term67 A y x') = (term67 A y x').
Proof. exact (eq_refl (term67 A y x')). Qed.
Lemma lem3795615 {A : Type'} (x' : A) (y : A) : ((term64 A y x') = (term65 A y)) = ((term64 A y x') = (term66 A y)).
Proof. exact (MK_COMB (@lem3795614 A y x') (@lem3795613 A y)). Qed.
Lemma lem3795616 {A : Type'} (x' : A) (y : A) : (term64 A y x') = (term9 A x' y).
Proof. exact (eq_refl (term64 A y x')). Qed.
Lemma lem3795617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3795618 {A : Type'} (x' : A) (y : A) : (term67 A y x') = (term68 A x' y).
Proof. exact (MK_COMB (@lem3795617) (@lem3795616 A x' y)). Qed.
Lemma lem3795619 {A : Type'} (y : A) : (term66 A y) = (term66 A y).
Proof. exact (eq_refl (term66 A y)). Qed.
Lemma lem3795620 {A : Type'} (x' : A) (y : A) : ((term64 A y x') = (term66 A y)) = ((term9 A x' y) = (term66 A y)).
Proof. exact (MK_COMB (@lem3795618 A x' y) (@lem3795619 A y)). Qed.
Lemma lem3795621 {A : Type'} (x' : A) (y : A) : ((term64 A y x') = (term65 A y)) = ((term9 A x' y) = (term66 A y)).
Proof. exact (TRANS (@lem3795615 A x' y) (@lem3795620 A x' y)). Qed.
Lemma lem3795622 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term9 A x' y) = (term66 A y).
Proof. exact (EQ_MP (@lem3795621 A x' y) (@lem3795612 A x' y h1)). Qed.
Lemma lem3795623 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : term66 A y.
Proof. exact (EQ_MP (@lem3795622 A x' y h2) (@lem3795409 A s y x' x h1)). Qed.
Lemma lem3795639 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : s x'.
Proof. exact (proj1 (@lem3795251 A s y x' x h1)). Qed.
Lemma lem3795640 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : term69 A s x'.
Proof. exact (fun h0 : term62 A s x' => @lem3795639 A s y x' x h1). Qed.
Lemma lem3795642 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795643 {A : Type'} (s : A -> Prop) (x' : A) : (term69 A s x') = (s x').
Proof. exact (@lem3795642 (s x')). Qed.
Lemma lem3795644 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : s x'.
Proof. exact (EQ_MP (@lem3795643 A s x') (@lem3795640 A s y x' x h1)). Qed.
Lemma lem3795647 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3795649 {A : Type'} (s : A -> Prop) (x' : A) : (term62 A s x') = (term71 A s x').
Proof. exact (@lem3795647 (s x')). Qed.
Lemma lem3795652 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term71 A s x'.
Proof. exact (EQ_MP (@lem3795649 A s x') (@lem3795371 A s x' h1)). Qed.
Lemma lem3795655 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : False.
Proof. exact (@lem3795652 A s x' h1 (@lem3795644 A s y x' x h2)). Qed.
Lemma lem3795656 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : term72.
Proof. exact (fun h0 : ~ False => @lem3795655 A s y x' x h1 h2). Qed.
Lemma lem3795658 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795659 : term72 = False.
Proof. exact (@lem3795658 False). Qed.
Lemma lem3795660 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795659) (@lem3795656 A s y x' x h1 h2)). Qed.
Lemma lem3795676 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3795677 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3795676 A x). Qed.
Lemma lem3795678 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3795677 A y). Qed.
Lemma lem3795679 {A : Type'} (y : A) : term73 A y.
Proof. exact (fun h0 : term66 A y => @lem3795678 A y). Qed.
Lemma lem3795681 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795682 {A : Type'} (y : A) : (term73 A y) = (y = y).
Proof. exact (@lem3795681 (y = y)). Qed.
Lemma lem3795683 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3795682 A y) (@lem3795679 A y)). Qed.
Lemma lem3795686 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3795688 {A : Type'} (y : A) : (term66 A y) = (term74 A y).
Proof. exact (@lem3795686 (y = y)). Qed.
Lemma lem3795691 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : term74 A y.
Proof. exact (EQ_MP (@lem3795688 A y) (@lem3795438 A s x x' y h1 h2)). Qed.
Lemma lem3795694 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : False.
Proof. exact (@lem3795691 A s x x' y h1 h2 (@lem3795683 A y)). Qed.
Lemma lem3795695 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : term72.
Proof. exact (fun h0 : ~ False => @lem3795694 A s x x' y h1 h2). Qed.
Lemma lem3795697 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795698 : term72 = False.
Proof. exact (@lem3795697 False). Qed.
Lemma lem3795715 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3795716 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3795715 A x). Qed.
Lemma lem3795717 {A : Type'} (x : A) : term73 A x.
Proof. exact (fun h0 : term66 A x => @lem3795716 A x). Qed.
Lemma lem3795719 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795720 {A : Type'} (x : A) : (term73 A x) = (x = x).
Proof. exact (@lem3795719 (x = x)). Qed.
Lemma lem3795721 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3795720 A x) (@lem3795717 A x)). Qed.
Lemma lem3795724 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3795726 {A : Type'} (x : A) : (term66 A x) = (term74 A x).
Proof. exact (@lem3795724 (x = x)). Qed.
Lemma lem3795729 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : term74 A x.
Proof. exact (EQ_MP (@lem3795726 A x) (@lem3795517 A s y x' x h1 h2)). Qed.
Lemma lem3795732 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : False.
Proof. exact (@lem3795729 A s y x' x h1 h2 (@lem3795721 A x)). Qed.
Lemma lem3795733 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : term72.
Proof. exact (fun h0 : ~ False => @lem3795732 A s y x' x h1 h2). Qed.
Lemma lem3795735 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795736 : term72 = False.
Proof. exact (@lem3795735 False). Qed.
Lemma lem3795753 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : s x'.
Proof. exact (proj1 (@lem3795261 A s y x' x h1)). Qed.
Lemma lem3795754 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : term69 A s x'.
Proof. exact (fun h0 : term62 A s x' => @lem3795753 A s y x' x h1). Qed.
Lemma lem3795756 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795757 {A : Type'} (s : A -> Prop) (x' : A) : (term69 A s x') = (s x').
Proof. exact (@lem3795756 (s x')). Qed.
Lemma lem3795758 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : s x'.
Proof. exact (EQ_MP (@lem3795757 A s x') (@lem3795754 A s y x' x h1)). Qed.
Lemma lem3795761 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3795763 {A : Type'} (s : A -> Prop) (x' : A) : (term62 A s x') = (term71 A s x').
Proof. exact (@lem3795761 (s x')). Qed.
Lemma lem3795766 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term62 A s x') : term71 A s x'.
Proof. exact (EQ_MP (@lem3795763 A s x') (@lem3795395 A s x' h1)). Qed.
Lemma lem3795769 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : False.
Proof. exact (@lem3795766 A s x' h1 (@lem3795758 A s y x' x h2)). Qed.
Lemma lem3795770 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : term72.
Proof. exact (fun h0 : ~ False => @lem3795769 A s y x' x h1 h2). Qed.
Lemma lem3795772 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795773 : term72 = False.
Proof. exact (@lem3795772 False). Qed.
Lemma lem3795774 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795773) (@lem3795770 A s y x' x h1 h2)). Qed.
Lemma lem3795790 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3795791 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3795790 A x). Qed.
Lemma lem3795792 {A : Type'} (x : A) : term73 A x.
Proof. exact (fun h0 : term66 A x => @lem3795791 A x). Qed.
Lemma lem3795794 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795795 {A : Type'} (x : A) : (term73 A x) = (x = x).
Proof. exact (@lem3795794 (x = x)). Qed.
Lemma lem3795796 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3795795 A x) (@lem3795792 A x)). Qed.
Lemma lem3795799 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3795801 {A : Type'} (x : A) : (term66 A x) = (term74 A x).
Proof. exact (@lem3795799 (x = x)). Qed.
Lemma lem3795804 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : term74 A x.
Proof. exact (EQ_MP (@lem3795801 A x) (@lem3795544 A s y x' x h1 h2)). Qed.
Lemma lem3795807 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : False.
Proof. exact (@lem3795804 A s y x' x h1 h2 (@lem3795796 A x)). Qed.
Lemma lem3795808 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : term72.
Proof. exact (fun h0 : ~ False => @lem3795807 A s y x' x h1 h2). Qed.
Lemma lem3795810 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795811 : term72 = False.
Proof. exact (@lem3795810 False). Qed.
Lemma lem3795828 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3795829 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3795828 A x). Qed.
Lemma lem3795830 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3795829 A y). Qed.
Lemma lem3795831 {A : Type'} (y : A) : term73 A y.
Proof. exact (fun h0 : term66 A y => @lem3795830 A y). Qed.
Lemma lem3795833 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795834 {A : Type'} (y : A) : (term73 A y) = (y = y).
Proof. exact (@lem3795833 (y = y)). Qed.
Lemma lem3795835 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3795834 A y) (@lem3795831 A y)). Qed.
Lemma lem3795838 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3795840 {A : Type'} (y : A) : (term66 A y) = (term74 A y).
Proof. exact (@lem3795838 (y = y)). Qed.
Lemma lem3795843 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : term74 A y.
Proof. exact (EQ_MP (@lem3795840 A y) (@lem3795623 A s x x' y h1 h2)). Qed.
Lemma lem3795846 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : False.
Proof. exact (@lem3795843 A s x x' y h1 h2 (@lem3795835 A y)). Qed.
Lemma lem3795847 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : term72.
Proof. exact (fun h0 : ~ False => @lem3795846 A s x x' y h1 h2). Qed.
Lemma lem3795849 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3795850 : term72 = False.
Proof. exact (@lem3795849 False). Qed.
Lemma lem3795852 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795850) (@lem3795847 A s x x' y h1 h2)). Qed.
Lemma lem3795853 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795811) (@lem3795808 A s y x' x h1 h2)). Qed.
Lemma lem3795854 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795736) (@lem3795733 A s y x' x h1 h2)). Qed.
Lemma lem3795855 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795698) (@lem3795695 A s x x' y h1 h2)). Qed.
Lemma lem3795856 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3795852 A s x x' y h1 h2) (fun h3 : False => @lem3795411 A x' y h2)). Qed.
Lemma lem3795857 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795856 A s x x' y h1 h2) (@lem3795411 A x' y h2)). Qed.
Lemma lem3795858 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3795853 A s y x' x h1 h2) (fun h3 : False => @lem3795403 A x' x h2)). Qed.
Lemma lem3795859 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795858 A s y x' x h1 h2) (@lem3795403 A x' x h2)). Qed.
Lemma lem3795860 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3795774 A s y x' x h1 h2) (fun h3 : False => @lem3795395 A s x' h1)). Qed.
Lemma lem3795861 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795860 A s y x' x h1 h2) (@lem3795395 A s x' h1)). Qed.
Lemma lem3795862 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3795854 A s y x' x h1 h2) (fun h3 : False => @lem3795387 A x' x h2)). Qed.
Lemma lem3795863 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795862 A s y x' x h1 h2) (@lem3795387 A x' x h2)). Qed.
Lemma lem3795864 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3795855 A s x x' y h1 h2) (fun h3 : False => @lem3795379 A x' y h2)). Qed.
Lemma lem3795865 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795864 A s x x' y h1 h2) (@lem3795379 A x' y h2)). Qed.
Lemma lem3795866 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3795660 A s y x' x h1 h2) (fun h3 : False => @lem3795371 A s x' h1)). Qed.
Lemma lem3795867 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795866 A s y x' x h1 h2) (@lem3795371 A s x' h1)). Qed.
Lemma lem3795868 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3795857 A s x x' y h1 h2) (fun h3 : False => @lem3795363 A x' y h2)). Qed.
Lemma lem3795869 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795868 A s x x' y h1 h2) (@lem3795363 A x' y h2)). Qed.
Lemma lem3795870 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3795859 A s y x' x h1 h2) (fun h3 : False => @lem3795347 A x' x h2)). Qed.
Lemma lem3795871 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795870 A s y x' x h1 h2) (@lem3795347 A x' x h2)). Qed.
Lemma lem3795872 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3795861 A s y x' x h1 h2) (fun h3 : False => @lem3795331 A s x' h1)). Qed.
Lemma lem3795873 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795872 A s y x' x h1 h2) (@lem3795331 A s x' h1)). Qed.
Lemma lem3795874 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3795863 A s y x' x h1 h2) (fun h3 : False => @lem3795315 A x' x h2)). Qed.
Lemma lem3795875 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795874 A s y x' x h1 h2) (@lem3795315 A x' x h2)). Qed.
Lemma lem3795876 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3795865 A s x x' y h1 h2) (fun h3 : False => @lem3795299 A x' y h2)). Qed.
Lemma lem3795877 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795876 A s x x' y h1 h2) (@lem3795299 A x' y h2)). Qed.
Lemma lem3795878 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3795867 A s y x' x h1 h2) (fun h3 : False => @lem3795283 A s x' h1)). Qed.
Lemma lem3795879 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795878 A s y x' x h1 h2) (@lem3795283 A s x' h1)). Qed.
Lemma lem3795880 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3795869 A s x x' y h1 h2) (fun h3 : False => @lem3795363 A x' y h2)). Qed.
Lemma lem3795881 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term54 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795880 A s x x' y h1 h2) (@lem3795363 A x' y h2)). Qed.
Lemma lem3795882 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3795871 A s y x' x h1 h2) (fun h3 : False => @lem3795347 A x' x h2)). Qed.
Lemma lem3795883 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795882 A s y x' x h1 h2) (@lem3795347 A x' x h2)). Qed.
Lemma lem3795884 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3795873 A s y x' x h1 h2) (fun h3 : False => @lem3795331 A s x' h1)). Qed.
Lemma lem3795885 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term54 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795884 A s y x' x h1 h2) (@lem3795331 A s x' h1)). Qed.
Lemma lem3795886 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3795875 A s y x' x h1 h2) (fun h3 : False => @lem3795315 A x' x h2)). Qed.
Lemma lem3795887 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3795886 A s y x' x h1 h2) (@lem3795315 A x' x h2)). Qed.
Lemma lem3795888 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3795877 A s x x' y h1 h2) (fun h3 : False => @lem3795299 A x' y h2)). Qed.
Lemma lem3795889 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3795888 A s x x' y h1 h2) (@lem3795299 A x' y h2)). Qed.
Lemma lem3795890 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : (term62 A s x') = False.
Proof. exact (prop_ext (fun h3 : term62 A s x' => @lem3795879 A s y x' x h1 h2) (fun h3 : False => @lem3795283 A s x' h1)). Qed.
Lemma lem3795891 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term62 A s x') (h2 : term57 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795890 A s y x' x h1 h2) (@lem3795283 A s x' h1)). Qed.
Lemma lem3795892 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term54 A s y x' x) (h2 : term44 A s x' x) : False.
Proof. exact (or_elim (@lem3795264 A s x' x h2) (fun h0 : term62 A s x' => @lem3795885 A s y x' x h0 h1) (fun h0 : x' = x => @lem3795883 A s y x' x h1 h0)). Qed.
Lemma lem3795893 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term54 A s y x' x) : False.
Proof. exact (or_elim (@lem3795259 A s y x' x h1) (fun h0 : term44 A s x' x => @lem3795892 A y s x' x h1 h0) (fun h0 : x' = y => @lem3795881 A s x x' y h1 h0)). Qed.
Lemma lem3795894 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term57 A s y x' x) (h2 : term44 A s x' y) : False.
Proof. exact (or_elim (@lem3795254 A s x' y h2) (fun h0 : term62 A s x' => @lem3795891 A s y x' x h0 h1) (fun h0 : x' = y => @lem3795889 A s x x' y h1 h0)). Qed.
Lemma lem3795895 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term57 A s y x' x) : False.
Proof. exact (or_elim (@lem3795248 A s y x' x h1) (fun h0 : term44 A s x' y => @lem3795894 A x s x' y h1 h0) (fun h0 : x' = x => @lem3795887 A s y x' x h1 h0)). Qed.
Lemma lem3795896 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term40 A s y x' x) : False.
Proof. exact (or_elim (@lem3795245 A s y x' x h1) (fun h0 : term57 A s y x' x => @lem3795895 A s y x' x h0) (fun h0 : term54 A s y x' x => @lem3795893 A s y x' x h0)). Qed.
Lemma lem3795897 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term40 A s y x' x) : (term40 A s y x' x) = False.
Proof. exact (prop_ext (fun h2 : term40 A s y x' x => @lem3795896 A s y x' x h1) (fun h2 : False => @lem3795079 A s y x' x h1)). Qed.
Lemma lem3795898 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) (h1 : term40 A s y x' x) : False.
Proof. exact (EQ_MP (@lem3795897 A s y x' x h1) (@lem3795079 A s y x' x h1)). Qed.
Lemma lem3795899 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : term39 A s y x' x.
Proof. exact (fun h0 : term40 A s y x' x => @lem3795898 A s y x' x h0). Qed.
Lemma lem3795900 {A : Type'} (s : A -> Prop) (y : A) (x' : A) (x : A) : (term13 A s x x' y) = (term13 A s y x' x).
Proof. exact (EQ_MP (@lem3795078 A s y x' x) (@lem3795899 A s y x' x)). Qed.
Lemma lem3795905 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term18 A s y x.
Proof. exact (fun x' : A => @lem3795900 A s y x' x). Qed.
Lemma lem3795910 {A : Type'} (y : A) (x : A) : term30 A y x.
Proof. exact (fun s : A -> Prop => @lem3795905 A s y x). Qed.
Lemma lem3795915 {A : Type'} (x : A) : term34 A x.
Proof. exact (fun y : A => @lem3795910 A y x). Qed.
Lemma lem3795920 {A : Type'} : term38 A.
Proof. exact (fun x : A => @lem3795915 A x). Qed.
Lemma lem3795921 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem3795074 A) (@lem3795920 A)). Qed.
Lemma lem3795922 {A : Type'} (x : A) : term75 A x.
Proof. exact (@lem3795921 A x). Qed.
Lemma lem3795923 {A : Type'} (x : A) : (term75 A x) = (term33 A x).
Proof. exact (eq_refl (term75 A x)). Qed.
Lemma lem3795924 {A : Type'} (x : A) : term33 A x.
Proof. exact (EQ_MP (@lem3795923 A x) (@lem3795922 A x)). Qed.
Lemma lem3795925 {A : Type'} (x : A) (y : A) : term76 A x y.
Proof. exact (@lem3795924 A x y). Qed.
Lemma lem3795926 {A : Type'} (y : A) (x : A) : (term76 A x y) = (term29 A y x).
Proof. exact (eq_refl (term76 A x y)). Qed.
Lemma lem3795927 {A : Type'} (y : A) (x : A) : term29 A y x.
Proof. exact (EQ_MP (@lem3795926 A y x) (@lem3795925 A x y)). Qed.
Lemma lem3795928 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term77 A y x s.
Proof. exact (@lem3795927 A y x s). Qed.
Lemma lem3795929 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term77 A y x s) = (term20 A s y x).
Proof. exact (eq_refl (term77 A y x s)). Qed.
Lemma lem3795930 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term20 A s y x.
Proof. exact (EQ_MP (@lem3795929 A s y x) (@lem3795928 A y x s)). Qed.
Lemma lem3795932 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term20 A s y x.
Proof. exact (@lem3794941 A s y x (@lem3795930 A s y x)). Qed.
Lemma lem3795933 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term21 A s y x) : False.
Proof. exact (@lem3795932 A s y x (@lem3794925 A s y x h1)). Qed.
Lemma lem3795934 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term21 A s y x) : (term21 A s y x) = False.
Proof. exact (prop_ext (fun h2 : term21 A s y x => @lem3795933 A s y x h1) (fun h2 : False => @lem3794925 A s y x h1)). Qed.
Lemma lem3795935 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : term21 A s y x) : False.
Proof. exact (EQ_MP (@lem3795934 A s y x h1) (@lem3794925 A s y x h1)). Qed.
Lemma lem3795936 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term20 A s y x.
Proof. exact (fun h0 : term21 A s y x => @lem3795935 A s y x h0). Qed.
Lemma lem3795937 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term18 A s y x.
Proof. exact (EQ_MP (@lem3794924 A s y x) (@lem3795936 A s y x)). Qed.
Lemma lem3795938 {A : Type'} (s : A -> Prop) (y : A) (x : A) : term2 A s y x.
Proof. exact (EQ_MP (@lem3794920 A s y x) (@lem3795937 A s y x)). Qed.
Lemma lem3795940 {A : Type'} (x : A) (y : A) : term78 A x y.
Proof. exact (@lem9784 (x = y)). Qed.
Lemma lem3795941 {A : Type'} (x : A) (y : A) : (term78 A x y) = (term79 A x y).
Proof. exact (eq_refl (term78 A x y)). Qed.
Lemma lem3795942 {A : Type'} (x : A) (y : A) : term79 A x y.
Proof. exact (EQ_MP (@lem3795941 A x y) (@lem3795940 A x y)). Qed.
Lemma lem3795944 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : term9 A x y.
Proof. exact (h1). Qed.
Lemma lem3795959 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) : term80 _98584 _98585 f.
Proof. exact (@lem3794808 _98584 _98585 f). Qed.
Lemma lem3795960 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) : (term80 _98584 _98585 f) = (term81 _98584 _98585 f).
Proof. exact (eq_refl (term80 _98584 _98585 f)). Qed.
Lemma lem3795961 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) : term81 _98584 _98585 f.
Proof. exact (EQ_MP (@lem3795960 _98584 _98585 f) (@lem3795959 _98584 _98585 f)). Qed.
Lemma lem3795962 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (b : _98584) : term82 _98584 _98585 f b.
Proof. exact (@lem3795961 _98584 _98585 f b). Qed.
Lemma lem3795963 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (b : _98584) : (term82 _98584 _98585 f b) = (term83 _98584 _98585 f b).
Proof. exact (eq_refl (term82 _98584 _98585 f b)). Qed.
Lemma lem3795964 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (b : _98584) : term83 _98584 _98585 f b.
Proof. exact (EQ_MP (@lem3795963 _98584 _98585 f b) (@lem3795962 _98584 _98585 f b)). Qed.
Lemma lem3795965 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (b : _98584) (s : _98585 -> Prop) : term84 _98584 _98585 f b s.
Proof. exact (@lem3795964 _98584 _98585 f b s). Qed.
Lemma lem3795966 {_98584 _98585 : Type'} (s : _98585 -> Prop) (f : type1467 _98584 _98585) (b : _98584) : (term84 _98584 _98585 f b s) = (term85 _98584 _98585 s f b).
Proof. exact (eq_refl (term84 _98584 _98585 f b s)). Qed.
Lemma lem3795967 {_98584 _98585 : Type'} (s : _98585 -> Prop) (f : type1467 _98584 _98585) (b : _98584) : term85 _98584 _98585 s f b.
Proof. exact (EQ_MP (@lem3795966 _98584 _98585 s f b) (@lem3795965 _98584 _98585 f b s)). Qed.
Lemma lem3795968 {_98584 _98585 : Type'} (s : _98585 -> Prop) (f : type1467 _98584 _98585) (b : _98584) (a : _98584) : term86 _98584 _98585 s f b a.
Proof. exact (@lem3795967 _98584 _98585 s f b a). Qed.
Lemma lem3795969 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) : (term86 _98584 _98585 s f b a) = ((term87 _98584 _98585 f b s a) = (term88 _98584 _98585 s a f b)).
Proof. exact (eq_refl (term86 _98584 _98585 s f b a)). Qed.
Lemma lem3795971 {A B : Type'} (f : type1411 A B) (h1 : term89 A B f) : term89 A B f.
Proof. exact (h1). Qed.
Lemma lem3795973 (P : nat -> Prop) : term90 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem3795974 {A B : Type'} (b : B) (f : type1411 A B) : term91 A B b f.
Proof. exact (@lem3795973 (term92 A B b f)). Qed.
Lemma lem3795975 {A B : Type'} (b : B) (f : type1411 A B) : (term93 A B b f) = (term94 A B b f).
Proof. exact (eq_refl (term93 A B b f)). Qed.
Lemma lem3795976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3795977 {A B : Type'} (b : B) (f : type1411 A B) : (term95 A B b f) = (term96 A B b f).
Proof. exact (MK_COMB (@lem3795976) (@lem3795975 A B b f)). Qed.
Lemma lem3795978 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term97 A B b f n) = (term98 A B b n f).
Proof. exact (eq_refl (term97 A B b f n)). Qed.
Lemma lem3795979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3795980 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term99 A B b f n) = (term100 A B b n f).
Proof. exact (MK_COMB (@lem3795979) (@lem3795978 A B b n f)). Qed.
Lemma lem3795981 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term101 A B b f n) = (term102 A B b n f).
Proof. exact (eq_refl (term101 A B b f n)). Qed.
Lemma lem3795982 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term103 A B b f n) = (term104 A B b n f).
Proof. exact (MK_COMB (@lem3795980 A B b n f) (@lem3795981 A B b n f)). Qed.
Lemma lem3795983 {A B : Type'} (b : B) (f : type1411 A B) : (term105 A B b f) = (term106 A B b f).
Proof. exact (fun_ext (fun n : nat => @lem3795982 A B b n f)). Qed.
Lemma lem3795984 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3795985 {A B : Type'} (b : B) (f : type1411 A B) : (term107 A B b f) = (term108 A B b f).
Proof. exact (MK_COMB (@lem3795984) (@lem3795983 A B b f)). Qed.
Lemma lem3795986 {A B : Type'} (b : B) (f : type1411 A B) : (term109 A B b f) = (term110 A B b f).
Proof. exact (MK_COMB (@lem3795977 A B b f) (@lem3795985 A B b f)). Qed.
Lemma lem3795987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3795988 {A B : Type'} (b : B) (f : type1411 A B) : (term111 A B b f) = (term112 A B b f).
Proof. exact (MK_COMB (@lem3795987) (@lem3795986 A B b f)). Qed.
Lemma lem3795989 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term97 A B b f n) = (term98 A B b n f).
Proof. exact (eq_refl (term97 A B b f n)). Qed.
Lemma lem3795990 {A B : Type'} (b : B) (f : type1411 A B) : (term113 A B b f) = (term92 A B b f).
Proof. exact (fun_ext (fun n : nat => @lem3795989 A B b n f)). Qed.
Lemma lem3795991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3795992 {A B : Type'} (b : B) (f : type1411 A B) : (term114 A B b f) = (term115 A B b f).
Proof. exact (MK_COMB (@lem3795991) (@lem3795990 A B b f)). Qed.
Lemma lem3795993 {A B : Type'} (b : B) (f : type1411 A B) : (term91 A B b f) = (term116 A B b f).
Proof. exact (MK_COMB (@lem3795988 A B b f) (@lem3795992 A B b f)). Qed.
Lemma lem3795994 {A B : Type'} (b : B) (f : type1411 A B) : term116 A B b f.
Proof. exact (EQ_MP (@lem3795993 A B b f) (@lem3795974 A B b f)). Qed.
Lemma lem3795995 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term98 A B b n f) : term98 A B b n f.
Proof. exact (h1). Qed.
Lemma lem3796007 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) : (term87 _98584 _98585 f b s a) = (term88 _98584 _98585 s a f b).
Proof. exact (EQ_MP (@lem3795969 _98584 _98585 s a f b) (@lem3795968 _98584 _98585 s f b a)). Qed.
Lemma lem3796008 {A B : Type'} (s : A -> Prop) (a : B) (f : type1411 A B) (b : B) : (term117 A B f b s a) = (term118 A B s a f b).
Proof. exact (@lem3796007 B A s a f b). Qed.
Lemma lem3796009 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (b : B) : (term117 A B f b s z) = (term118 A B s z f b).
Proof. exact (@lem3796008 A B s z f b). Qed.
Lemma lem3796020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3796021 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (b : B) : (term119 A B f b s z) = (term120 A B s z f b).
Proof. exact (MK_COMB (@lem3796020) (@lem3796009 A B s z f b)). Qed.
Lemma lem3796036 {A B : Type'} (b : B) (s : A -> Prop) (z : B) (f : type1411 A B) : (term121 A B b s z f) = (term121 A B b s z f).
Proof. exact (eq_refl (term121 A B b s z f)). Qed.
Lemma lem3796037 {A B : Type'} (b : B) (s : A -> Prop) (z : B) (f : type1411 A B) : (term122 A B b s z f) = (term123 A B b s z f).
Proof. exact (MK_COMB (@lem3796021 A B s z f b) (@lem3796036 A B b s z f)). Qed.
Lemma lem3796040 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) : (term124 A B b s f) = (term125 A B b s f).
Proof. exact (fun_ext (fun z : B => @lem3796037 A B b s z f)). Qed.
Lemma lem3796041 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3796042 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) : (term126 A B b s f) = (term127 A B b s f).
Proof. exact (MK_COMB (@lem3796041 B) (@lem3796040 A B b s f)). Qed.
Lemma lem3796047 {A B : Type'} (b : B) (f : type1411 A B) : (term128 A B b f) = (term129 A B b f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3796042 A B b s f)). Qed.
Lemma lem3796048 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3796049 {A B : Type'} (b : B) (f : type1411 A B) : (term94 A B b f) = (term130 A B b f).
Proof. exact (MK_COMB (@lem3796048 A) (@lem3796047 A B b f)). Qed.
Lemma lem3796054 {A B : Type'} (b : B) (f : type1411 A B) : (term130 A B b f) = (term94 A B b f).
Proof. exact (SYM (@lem3796049 A B b f)). Qed.
Lemma lem3796088 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term131 A B f b s a) = (term132 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3796089 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term131 A B f b s a) = (term132 A B s a b).
Proof. exact (@lem3796088 A B f s a b). Qed.
Lemma lem3796090 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (w : B) (b : B) : (term133 A B f b s x w) = (term134 A B s x w b).
Proof. exact (@lem3796089 A B f (@DELETE A s x) w b). Qed.
Lemma lem3796097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796098 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (x : A) (w : B) (b : B) : (term135 A B f b s x w) = (term136 A B s x w b).
Proof. exact (MK_COMB (@lem3796097) (@lem3796090 A B f s x w b)). Qed.
Lemma lem3796101 {A B : Type'} (z : B) (f : type1411 A B) (x : A) (w : B) : (z = (f x w)) = (z = (f x w)).
Proof. exact (eq_refl (z = (f x w))). Qed.
Lemma lem3796102 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) (x : A) (w : B) : (term137 A B b s z f x w) = (term138 A B s b z f x w).
Proof. exact (MK_COMB (@lem3796098 A B f s x w b) (@lem3796101 A B z f x w)). Qed.
Lemma lem3796105 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) (x : A) : (term139 A B b s z f x) = (term140 A B s b z f x).
Proof. exact (fun_ext (fun w : B => @lem3796102 A B s b z f x w)). Qed.
Lemma lem3796106 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3796107 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) (x : A) : (term141 A B b s z f x) = (term142 A B s b z f x).
Proof. exact (MK_COMB (@lem3796106 B) (@lem3796105 A B s b z f x)). Qed.
Lemma lem3796112 {A : Type'} (x : A) (s : A -> Prop) : (term143 A x s) = (term143 A x s).
Proof. exact (eq_refl (term143 A x s)). Qed.
Lemma lem3796113 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) (x : A) : (term144 A B b s z f x) = (term145 A B s b z f x).
Proof. exact (MK_COMB (@lem3796112 A x s) (@lem3796107 A B s b z f x)). Qed.
Lemma lem3796116 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) : (term146 A B b s z f) = (term147 A B s b z f).
Proof. exact (fun_ext (fun x : A => @lem3796113 A B s b z f x)). Qed.
Lemma lem3796117 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3796118 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) : (term121 A B b s z f) = (term148 A B s b z f).
Proof. exact (MK_COMB (@lem3796117 A) (@lem3796116 A B s b z f)). Qed.
Lemma lem3796123 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (b : B) : (term120 A B s z f b) = (term120 A B s z f b).
Proof. exact (eq_refl (term120 A B s z f b)). Qed.
Lemma lem3796124 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) : (term123 A B b s z f) = (term149 A B s b z f).
Proof. exact (MK_COMB (@lem3796123 A B s z f b) (@lem3796118 A B s b z f)). Qed.
Lemma lem3796127 {A B : Type'} (s : A -> Prop) (b : B) (f : type1411 A B) : (term125 A B b s f) = (term150 A B s b f).
Proof. exact (fun_ext (fun z : B => @lem3796124 A B s b z f)). Qed.
Lemma lem3796128 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3796129 {A B : Type'} (s : A -> Prop) (b : B) (f : type1411 A B) : (term127 A B b s f) = (term151 A B s b f).
Proof. exact (MK_COMB (@lem3796128 B) (@lem3796127 A B s b f)). Qed.
Lemma lem3796134 {A B : Type'} (b : B) (f : type1411 A B) : (term129 A B b f) = (term152 A B b f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3796129 A B s b f)). Qed.
Lemma lem3796135 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3796136 {A B : Type'} (b : B) (f : type1411 A B) : (term130 A B b f) = (term153 A B b f).
Proof. exact (MK_COMB (@lem3796135 A) (@lem3796134 A B b f)). Qed.
Lemma lem3796141 {A B : Type'} (b : B) (f : type1411 A B) : (term153 A B b f) = (term130 A B b f).
Proof. exact (SYM (@lem3796136 A B b f)). Qed.
Lemma lem3796142 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (b : B) (h1 : term118 A B s z f b) : term118 A B s z f b.
Proof. exact (h1). Qed.
Lemma lem3796143 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : term154 A B s z f x b) : term154 A B s z f x b.
Proof. exact (h1). Qed.
Lemma lem3796144 {A B : Type'} (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : z = (f x b)) : z = (f x b).
Proof. exact (h1). Qed.
Lemma lem3796145 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : s = (@INSERT A x (@EMPTY A)).
Proof. exact (h1). Qed.
Lemma lem3796146 {A : Type'} (x : A) : term155 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3796147 {A : Type'} (x : A) : (term155 A x) = (term156 A x).
Proof. exact (eq_refl (term155 A x)). Qed.
Lemma lem3796148 {A : Type'} (x : A) : term156 A x.
Proof. exact (EQ_MP (@lem3796147 A x) (@lem3796146 A x)). Qed.
Lemma lem3796149 {A : Type'} (x : A) : term157 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3796151 {A : Type'} (x : A) : term158 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3796152 {A : Type'} (x : A) : (term158 A x) = (term159 A x).
Proof. exact (eq_refl (term158 A x)). Qed.
Lemma lem3796153 {A : Type'} (x : A) : term159 A x.
Proof. exact (EQ_MP (@lem3796152 A x) (@lem3796151 A x)). Qed.
Lemma lem3796154 {A : Type'} (x : A) (y : A) : term160 A x y.
Proof. exact (@lem3796153 A x y). Qed.
Lemma lem3796155 {A : Type'} (y : A) (x : A) : (term160 A x y) = (term161 A y x).
Proof. exact (eq_refl (term160 A x y)). Qed.
Lemma lem3796156 {A : Type'} (y : A) (x : A) : term161 A y x.
Proof. exact (EQ_MP (@lem3796155 A y x) (@lem3796154 A x y)). Qed.
Lemma lem3796157 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term162 A y x s.
Proof. exact (@lem3796156 A y x s). Qed.
Lemma lem3796158 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term162 A y x s) = ((term163 A x y s) = (term164 A y x s)).
Proof. exact (eq_refl (term162 A y x s)). Qed.
Lemma lem3796174 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : s = (@INSERT A x (@EMPTY A)).
Proof. exact (h1). Qed.
Lemma lem3796175 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem3796176 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (@IN A x' s) = (term165 A x' x).
Proof. exact (MK_COMB (@lem3796175 A x') (@lem3796174 A s x h1)). Qed.
Lemma lem3796178 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term163 A x y s) = (term164 A y x s).
Proof. exact (EQ_MP (@lem3796158 A y x s) (@lem3796157 A y x s)). Qed.
Lemma lem3796179 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term163 A x y s) = (term164 A y x s).
Proof. exact (@lem3796178 A y x s). Qed.
Lemma lem3796180 {A : Type'} (x : A) (x' : A) : (term165 A x' x) = (term166 A x x').
Proof. exact (@lem3796179 A x x' (@EMPTY A)). Qed.
Lemma lem3796186 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3796149 A x (@lem3796148 A x)). Qed.
Lemma lem3796187 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3796186 A x). Qed.
Lemma lem3796188 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3796187 A x'). Qed.
Lemma lem3796189 {A : Type'} (x' : A) (x : A) : (term167 A x' x) = (term167 A x' x).
Proof. exact (eq_refl (term167 A x' x)). Qed.
Lemma lem3796190 {A : Type'} (x' : A) (x : A) : (term166 A x x') = (term168 A x' x).
Proof. exact (MK_COMB (@lem3796189 A x' x) (@lem3796188 A x')). Qed.
Lemma lem3796192 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3796193 {A : Type'} (x' : A) (x : A) : (term168 A x' x) = (x' = x).
Proof. exact (@lem3796192 (x' = x)). Qed.
Lemma lem3796196 {A : Type'} (x' : A) (x : A) : (term166 A x x') = (x' = x).
Proof. exact (TRANS (@lem3796190 A x' x) (@lem3796193 A x' x)). Qed.
Lemma lem3796197 {A : Type'} (x' : A) (x : A) : (term165 A x' x) = (x' = x).
Proof. exact (TRANS (@lem3796180 A x x') (@lem3796196 A x' x)). Qed.
Lemma lem3796198 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (@IN A x' s) = (x' = x).
Proof. exact (TRANS (@lem3796176 A x' s x h1) (@lem3796197 A x' x)). Qed.
Lemma lem3796199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3796200 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (term143 A x' s) = (term169 A x' x).
Proof. exact (MK_COMB (@lem3796199) (@lem3796198 A x' s x h1)). Qed.
Lemma lem3796212 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : s = (@INSERT A x (@EMPTY A)).
Proof. exact (h1). Qed.
Lemma lem3796213 {A : Type'} : (@DELETE A) = (@DELETE A).
Proof. exact (eq_refl (@DELETE A)). Qed.
Lemma lem3796214 {A : Type'} (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (@DELETE A s) = (term170 A x).
Proof. exact (MK_COMB (@lem3796213 A) (@lem3796212 A s x h1)). Qed.
Lemma lem3796215 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3796216 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (@DELETE A s x') = (term171 A x x').
Proof. exact (MK_COMB (@lem3796214 A s x h1) (@lem3796215 A x')). Qed.
Lemma lem3796217 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3796218 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (term172 A s x') = (term173 A x x').
Proof. exact (MK_COMB (@lem3796217 A) (@lem3796216 A x' s x h1)). Qed.
Lemma lem3796219 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem3796220 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : ((@DELETE A s x') = (@EMPTY A)) = ((term171 A x x') = (@EMPTY A)).
Proof. exact (MK_COMB (@lem3796218 A x' s x h1) (@lem3796219 A)). Qed.
Lemma lem3796223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796224 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (term174 A s x') = (term175 A x x').
Proof. exact (MK_COMB (@lem3796223) (@lem3796220 A x' s x h1)). Qed.
Lemma lem3796227 {B : Type'} (w : B) (b : B) : (w = b) = (w = b).
Proof. exact (eq_refl (w = b)). Qed.
Lemma lem3796228 {A B : Type'} (x' : A) (w : B) (b : B) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (term134 A B s x' w b) = (term176 A B x x' w b).
Proof. exact (MK_COMB (@lem3796224 A x' s x h1) (@lem3796227 B w b)). Qed.
Lemma lem3796231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796232 {A B : Type'} (x' : A) (w : B) (b : B) (s : A -> Prop) (x : A) (h1 : s = (@INSERT A x (@EMPTY A))) : (term136 A B s x' w b) = (term177 A B x x' w b).
Proof. exact (MK_COMB (@lem3796231) (@lem3796228 A B x' w b s x h1)). Qed.
Lemma lem3796236 {A B : Type'} (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : z = (f x b)) : z = (f x b).
Proof. exact (h1). Qed.
Lemma lem3796237 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3796238 {A B : Type'} (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : z = (f x b)) : (@eq B z) = (term178 A B f x b).
Proof. exact (MK_COMB (@lem3796237 B) (@lem3796236 A B z f x b h1)). Qed.
Lemma lem3796239 {A B : Type'} (f : type1411 A B) (x' : A) (w : B) : (f x' w) = (f x' w).
Proof. exact (eq_refl (f x' w)). Qed.
Lemma lem3796240 {A B : Type'} (x' : A) (w : B) (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : z = (f x b)) : (z = (f x' w)) = ((f x b) = (f x' w)).
Proof. exact (MK_COMB (@lem3796238 A B z f x b h1) (@lem3796239 A B f x' w)). Qed.
Lemma lem3796243 {A B : Type'} (x' : A) (w : B) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : (term138 A B s b z f x' w) = (term179 A B x b f x' w).
Proof. exact (MK_COMB (@lem3796232 A B x' w b s x h2) (@lem3796240 A B x' w z f x b h1)). Qed.
Lemma lem3796246 {A B : Type'} (x' : A) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : (term140 A B s b z f x') = (term180 A B x b f x').
Proof. exact (fun_ext (fun w : B => @lem3796243 A B x' w z f b s x h1 h2)). Qed.
Lemma lem3796247 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3796248 {A B : Type'} (x' : A) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : (term142 A B s b z f x') = (term181 A B x b f x').
Proof. exact (MK_COMB (@lem3796247 B) (@lem3796246 A B x' z f b s x h1 h2)). Qed.
Lemma lem3796253 {A B : Type'} (x' : A) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : (term145 A B s b z f x') = (term182 A B x b f x').
Proof. exact (MK_COMB (@lem3796200 A x' s x h2) (@lem3796248 A B x' z f b s x h1 h2)). Qed.
Lemma lem3796258 {A B : Type'} (x' : A) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : (term182 A B x b f x') = (term145 A B s b z f x').
Proof. exact (SYM (@lem3796253 A B x' z f b s x h1 h2)). Qed.
Lemma lem3796259 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3796260 {A B : Type'} (x : A) (b : B) (f : type1411 A B) : (term183 A B x b f) = (term183 A B x b f).
Proof. exact (eq_refl (term183 A B x b f)). Qed.
Lemma lem3796261 {A B : Type'} (b : B) (f : type1411 A B) (x' : A) (x : A) (h1 : x' = x) : (term184 A B x b f x') = (term185 A B b f x).
Proof. exact (MK_COMB (@lem3796260 A B x b f) (@lem3796259 A x' x h1)). Qed.
Lemma lem3796262 {A B : Type'} (b : B) (f : type1411 A B) (x : A) : (term185 A B b f x) = (term186 A B b f x).
Proof. exact (eq_refl (term185 A B b f x)). Qed.
Lemma lem3796263 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (x' : A) : (term187 A B x b f x') = (term187 A B x b f x').
Proof. exact (eq_refl (term187 A B x b f x')). Qed.
Lemma lem3796264 {A B : Type'} (x' : A) (b : B) (f : type1411 A B) (x : A) : ((term184 A B x b f x') = (term185 A B b f x)) = ((term184 A B x b f x') = (term186 A B b f x)).
Proof. exact (MK_COMB (@lem3796263 A B x b f x') (@lem3796262 A B b f x)). Qed.
Lemma lem3796265 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (x' : A) : (term184 A B x b f x') = (term181 A B x b f x').
Proof. exact (eq_refl (term184 A B x b f x')). Qed.
Lemma lem3796266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3796267 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (x' : A) : (term187 A B x b f x') = (term188 A B x b f x').
Proof. exact (MK_COMB (@lem3796266) (@lem3796265 A B x b f x')). Qed.
Lemma lem3796268 {A B : Type'} (b : B) (f : type1411 A B) (x : A) : (term186 A B b f x) = (term186 A B b f x).
Proof. exact (eq_refl (term186 A B b f x)). Qed.
Lemma lem3796269 {A B : Type'} (x' : A) (b : B) (f : type1411 A B) (x : A) : ((term184 A B x b f x') = (term186 A B b f x)) = ((term181 A B x b f x') = (term186 A B b f x)).
Proof. exact (MK_COMB (@lem3796267 A B x b f x') (@lem3796268 A B b f x)). Qed.
Lemma lem3796270 {A B : Type'} (x' : A) (b : B) (f : type1411 A B) (x : A) : ((term184 A B x b f x') = (term185 A B b f x)) = ((term181 A B x b f x') = (term186 A B b f x)).
Proof. exact (TRANS (@lem3796264 A B x' b f x) (@lem3796269 A B x' b f x)). Qed.
Lemma lem3796271 {A B : Type'} (b : B) (f : type1411 A B) (x' : A) (x : A) (h1 : x' = x) : (term181 A B x b f x') = (term186 A B b f x).
Proof. exact (EQ_MP (@lem3796270 A B x' b f x) (@lem3796261 A B b f x' x h1)). Qed.
Lemma lem3796272 {A B : Type'} (b : B) (f : type1411 A B) (x' : A) (x : A) (h1 : x' = x) : (term186 A B b f x) = (term181 A B x b f x').
Proof. exact (SYM (@lem3796271 A B b f x' x h1)). Qed.
Lemma lem3796291 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3796292 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3796291 B x). Qed.
Lemma lem3796293 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem3796292 B b). Qed.
Lemma lem3796294 {A : Type'} (x : A) : (term189 A x) = (term189 A x).
Proof. exact (eq_refl (term189 A x)). Qed.
Lemma lem3796295 {A B : Type'} (b : B) (x : A) : (term190 A B x b) = (term191 A x).
Proof. exact (MK_COMB (@lem3796294 A x) (@lem3796293 B b)). Qed.
Lemma lem3796297 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3796298 {A : Type'} (x : A) : (term191 A x) = ((term192 A x) = (@EMPTY A)).
Proof. exact (@lem3796297 ((term192 A x) = (@EMPTY A))). Qed.
Lemma lem3796301 {A B : Type'} (b : B) (x : A) : (term190 A B x b) = ((term192 A x) = (@EMPTY A)).
Proof. exact (TRANS (@lem3796295 A B b x) (@lem3796298 A x)). Qed.
Lemma lem3796302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796303 {A B : Type'} (b : B) (x : A) : (term193 A B x b) = (term189 A x).
Proof. exact (MK_COMB (@lem3796302) (@lem3796301 A B b x)). Qed.
Lemma lem3796305 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3796306 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3796305 B x). Qed.
Lemma lem3796307 {A B : Type'} (f : type1411 A B) (x : A) (b : B) : ((f x b) = (f x b)) = True.
Proof. exact (@lem3796306 B (f x b)). Qed.
Lemma lem3796308 {A B : Type'} (f : type1411 A B) (b : B) (x : A) : (term194 A B f x b) = (term191 A x).
Proof. exact (MK_COMB (@lem3796303 A B b x) (@lem3796307 A B f x b)). Qed.
Lemma lem3796310 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3796311 {A : Type'} (x : A) : (term191 A x) = ((term192 A x) = (@EMPTY A)).
Proof. exact (@lem3796310 ((term192 A x) = (@EMPTY A))). Qed.
Lemma lem3796314 {A B : Type'} (f : type1411 A B) (b : B) (x : A) : (term194 A B f x b) = ((term192 A x) = (@EMPTY A)).
Proof. exact (TRANS (@lem3796308 A B f b x) (@lem3796311 A x)). Qed.
Lemma lem3796315 {A B : Type'} (f : type1411 A B) (x : A) (b : B) : ((term192 A x) = (@EMPTY A)) = (term194 A B f x b).
Proof. exact (SYM (@lem3796314 A B f b x)). Qed.
Lemma lem3796319 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3796320 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3796319 A s t). Qed.
Lemma lem3796321 {A : Type'} (x : A) : ((term192 A x) = (@EMPTY A)) = (term195 A x).
Proof. exact (@lem3796320 A (term192 A x) (@EMPTY A)). Qed.
Lemma lem3796330 {A : Type'} (x : A) : (term195 A x) = ((term192 A x) = (@EMPTY A)).
Proof. exact (SYM (@lem3796321 A x)). Qed.
Lemma lem3796338 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3796339 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (@lem3796338 A s x y). Qed.
Lemma lem3796340 {A : Type'} (x' : A) (x : A) : (term196 A x' x) = (term197 A x' x).
Proof. exact (@lem3796339 A (@INSERT A x (@EMPTY A)) x' x). Qed.
Lemma lem3796344 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term163 A x y s) = (term164 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3796345 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term163 A x y s) = (term164 A y x s).
Proof. exact (@lem3796344 A y x s). Qed.
Lemma lem3796346 {A : Type'} (x : A) (x' : A) : (term165 A x' x) = (term166 A x x').
Proof. exact (@lem3796345 A x x' (@EMPTY A)). Qed.
Lemma lem3796352 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3796353 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3796352 A x). Qed.
Lemma lem3796354 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3796353 A x'). Qed.
Lemma lem3796355 {A : Type'} (x' : A) (x : A) : (term167 A x' x) = (term167 A x' x).
Proof. exact (eq_refl (term167 A x' x)). Qed.
Lemma lem3796356 {A : Type'} (x' : A) (x : A) : (term166 A x x') = (term168 A x' x).
Proof. exact (MK_COMB (@lem3796355 A x' x) (@lem3796354 A x')). Qed.
Lemma lem3796358 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3796359 {A : Type'} (x' : A) (x : A) : (term168 A x' x) = (x' = x).
Proof. exact (@lem3796358 (x' = x)). Qed.
Lemma lem3796362 {A : Type'} (x' : A) (x : A) : (term166 A x x') = (x' = x).
Proof. exact (TRANS (@lem3796356 A x' x) (@lem3796359 A x' x)). Qed.
Lemma lem3796363 {A : Type'} (x' : A) (x : A) : (term165 A x' x) = (x' = x).
Proof. exact (TRANS (@lem3796346 A x x') (@lem3796362 A x' x)). Qed.
Lemma lem3796364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796365 {A : Type'} (x' : A) (x : A) : (term198 A x' x) = (term199 A x' x).
Proof. exact (MK_COMB (@lem3796364) (@lem3796363 A x' x)). Qed.
Lemma lem3796368 {A : Type'} (x' : A) (x : A) : (term9 A x' x) = (term9 A x' x).
Proof. exact (eq_refl (term9 A x' x)). Qed.
Lemma lem3796369 {A : Type'} (x' : A) (x : A) : (term197 A x' x) = (term200 A x' x).
Proof. exact (MK_COMB (@lem3796365 A x' x) (@lem3796368 A x' x)). Qed.
Lemma lem3796372 {A : Type'} (x' : A) (x : A) : (term196 A x' x) = (term200 A x' x).
Proof. exact (TRANS (@lem3796340 A x' x) (@lem3796369 A x' x)). Qed.
Lemma lem3796373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3796374 {A : Type'} (x' : A) (x : A) : (term201 A x' x) = (term202 A x' x).
Proof. exact (MK_COMB (@lem3796373) (@lem3796372 A x' x)). Qed.
Lemma lem3796376 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3796377 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3796376 A x). Qed.
Lemma lem3796378 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3796377 A x'). Qed.
Lemma lem3796379 {A : Type'} (x' : A) (x : A) : ((term196 A x' x) = (@IN A x' (@EMPTY A))) = ((term200 A x' x) = False).
Proof. exact (MK_COMB (@lem3796374 A x' x) (@lem3796378 A x')). Qed.
Lemma lem3796381 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3796382 {A : Type'} (x' : A) (x : A) : ((term200 A x' x) = False) = (term203 A x' x).
Proof. exact (@lem3796381 (term200 A x' x)). Qed.
Lemma lem3796389 {A : Type'} (x' : A) (x : A) : ((term196 A x' x) = (@IN A x' (@EMPTY A))) = (term203 A x' x).
Proof. exact (TRANS (@lem3796379 A x' x) (@lem3796382 A x' x)). Qed.
Lemma lem3796390 {A : Type'} (x : A) : (term204 A x) = (term205 A x).
Proof. exact (fun_ext (fun x' : A => @lem3796389 A x' x)). Qed.
Lemma lem3796391 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3796392 {A : Type'} (x : A) : (term195 A x) = (term206 A x).
Proof. exact (MK_COMB (@lem3796391 A) (@lem3796390 A x)). Qed.
Lemma lem3796397 {A : Type'} (x : A) : (term206 A x) = (term195 A x).
Proof. exact (SYM (@lem3796392 A x)). Qed.
Lemma lem3796399 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3796400 {A : Type'} (x : A) : (term206 A x) = (term207 A x).
Proof. exact (@lem3796399 (term206 A x)). Qed.
Lemma lem3796401 {A : Type'} (x : A) : (term207 A x) = (term206 A x).
Proof. exact (SYM (@lem3796400 A x)). Qed.
Lemma lem3796402 {A : Type'} (x : A) (h1 : term208 A x) : term208 A x.
Proof. exact (h1). Qed.
Lemma lem3796405 {A : Type'} (x : A) (h1 : term207 A x) : term207 A x.
Proof. exact (h1). Qed.
Lemma lem3796406 {A : Type'} (x : A) : term209 A x.
Proof. exact (fun h0 : term207 A x => @lem3796405 A x h0). Qed.
Lemma lem3796407 {A : Type'} (x : A) (h1 : term209 A x) : term209 A x.
Proof. exact (h1). Qed.
Lemma lem3796408 {A : Type'} (x : A) (h1 : term207 A x) : term207 A x.
Proof. exact (h1). Qed.
Lemma lem3796409 {A : Type'} (x : A) (h1 : term207 A x) (h2 : term209 A x) : term207 A x.
Proof. exact (@lem3796407 A x h2 (@lem3796408 A x h1)). Qed.
Lemma lem3796410 {A : Type'} (x : A) (h1 : term207 A x) : term210 A x.
Proof. exact (fun h0 : term209 A x => @lem3796409 A x h1 h0). Qed.
Lemma lem3796411 {A : Type'} (x : A) (h1 : term209 A x) : term209 A x.
Proof. exact (h1). Qed.
Lemma lem3796412 {A : Type'} (x : A) (h1 : term207 A x) (h2 : term209 A x) : term207 A x.
Proof. exact (@lem3796410 A x h1 (@lem3796411 A x h2)). Qed.
Lemma lem3796413 {A : Type'} (x : A) (h1 : term209 A x) : term209 A x.
Proof. exact (fun h0 : term207 A x => @lem3796412 A x h0 h1). Qed.
Lemma lem3796414 {A : Type'} (x : A) : term211 A x.
Proof. exact (fun h0 : term209 A x => @lem3796413 A x h0). Qed.
Lemma lem3796417 {A : Type'} (x : A) : term209 A x.
Proof. exact (@lem3796414 A x (@lem3796406 A x)). Qed.
Lemma lem3796418 {A : Type'} (x : A) : term209 A x.
Proof. exact (@lem3796417 A x). Qed.
Lemma lem3796424 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3796425 {A : Type'} (x : A) : (term207 A x) = (term212 A x).
Proof. exact (@lem3796424 (term208 A x)). Qed.
Lemma lem3796427 (t : Prop) : (term26 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3796428 {A : Type'} (x : A) : (term212 A x) = (term206 A x).
Proof. exact (@lem3796427 (term206 A x)). Qed.
Lemma lem3796433 {A : Type'} (x : A) : (term207 A x) = (term206 A x).
Proof. exact (TRANS (@lem3796425 A x) (@lem3796428 A x)). Qed.
Lemma lem3796436 {A : Type'} : (term213 A) = (term214 A).
Proof. exact (fun_ext (fun x : A => @lem3796433 A x)). Qed.
Lemma lem3796437 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3796446 {A : Type'} : (term215 A) = (term216 A).
Proof. exact (MK_COMB (@lem3796437 A) (@lem3796436 A)). Qed.
Lemma lem3796455 {A : Type'} (x' : A) (x : A) : (term203 A x' x) = (term203 A x' x).
Proof. exact (eq_refl (term203 A x' x)). Qed.
Lemma lem3796456 {A : Type'} (x : A) : (term205 A x) = (term205 A x).
Proof. exact (fun_ext (fun x' : A => @lem3796455 A x' x)). Qed.
Lemma lem3796457 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3796458 {A : Type'} (x : A) : (term206 A x) = (term206 A x).
Proof. exact (MK_COMB (@lem3796457 A) (@lem3796456 A x)). Qed.
Lemma lem3796459 {A : Type'} : (term214 A) = (term214 A).
Proof. exact (fun_ext (fun x : A => @lem3796458 A x)). Qed.
Lemma lem3796460 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3796461 {A : Type'} : (term216 A) = (term216 A).
Proof. exact (MK_COMB (@lem3796460 A) (@lem3796459 A)). Qed.
Lemma lem3796478 {A : Type'} : (term215 A) = (term216 A).
Proof. exact (TRANS (@lem3796446 A) (@lem3796461 A)). Qed.
Lemma lem3796479 {A : Type'} : (term216 A) = (term215 A).
Proof. exact (SYM (@lem3796478 A)). Qed.
Lemma lem3796490 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : term200 A x' x.
Proof. exact (h1). Qed.
Lemma lem3796506 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : term200 A x' x.
Proof. exact (h1). Qed.
Lemma lem3796518 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : x' = x.
Proof. exact (proj1 (@lem3796506 A x' x h1)). Qed.
Lemma lem3796520 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : term9 A x' x.
Proof. exact (proj2 (@lem3796506 A x' x h1)). Qed.
Lemma lem3796535 {A : Type'} (x : A) : (term63 A x) = (term63 A x).
Proof. exact (eq_refl (term63 A x)). Qed.
Lemma lem3796536 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : (term64 A x x') = (term65 A x).
Proof. exact (MK_COMB (@lem3796535 A x) (@lem3796518 A x' x h1)). Qed.
Lemma lem3796537 {A : Type'} (x : A) : (term65 A x) = (term66 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3796538 {A : Type'} (x : A) (x' : A) : (term67 A x x') = (term67 A x x').
Proof. exact (eq_refl (term67 A x x')). Qed.
Lemma lem3796539 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term64 A x x') = (term66 A x)).
Proof. exact (MK_COMB (@lem3796538 A x x') (@lem3796537 A x)). Qed.
Lemma lem3796540 {A : Type'} (x' : A) (x : A) : (term64 A x x') = (term9 A x' x).
Proof. exact (eq_refl (term64 A x x')). Qed.
Lemma lem3796541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3796542 {A : Type'} (x' : A) (x : A) : (term67 A x x') = (term68 A x' x).
Proof. exact (MK_COMB (@lem3796541) (@lem3796540 A x' x)). Qed.
Lemma lem3796543 {A : Type'} (x : A) : (term66 A x) = (term66 A x).
Proof. exact (eq_refl (term66 A x)). Qed.
Lemma lem3796544 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term66 A x)) = ((term9 A x' x) = (term66 A x)).
Proof. exact (MK_COMB (@lem3796542 A x' x) (@lem3796543 A x)). Qed.
Lemma lem3796545 {A : Type'} (x' : A) (x : A) : ((term64 A x x') = (term65 A x)) = ((term9 A x' x) = (term66 A x)).
Proof. exact (TRANS (@lem3796539 A x' x) (@lem3796544 A x' x)). Qed.
Lemma lem3796546 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : (term9 A x' x) = (term66 A x).
Proof. exact (EQ_MP (@lem3796545 A x' x) (@lem3796536 A x' x h1)). Qed.
Lemma lem3796547 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : term66 A x.
Proof. exact (EQ_MP (@lem3796546 A x' x h1) (@lem3796520 A x' x h1)). Qed.
Lemma lem3796551 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3796552 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3796551 A x). Qed.
Lemma lem3796553 {A : Type'} (x : A) : term73 A x.
Proof. exact (fun h0 : term66 A x => @lem3796552 A x). Qed.
Lemma lem3796555 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3796556 {A : Type'} (x : A) : (term73 A x) = (x = x).
Proof. exact (@lem3796555 (x = x)). Qed.
Lemma lem3796557 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3796556 A x) (@lem3796553 A x)). Qed.
Lemma lem3796560 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3796562 {A : Type'} (x : A) : (term66 A x) = (term74 A x).
Proof. exact (@lem3796560 (x = x)). Qed.
Lemma lem3796565 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : term74 A x.
Proof. exact (EQ_MP (@lem3796562 A x) (@lem3796547 A x' x h1)). Qed.
Lemma lem3796568 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : False.
Proof. exact (@lem3796565 A x' x h1 (@lem3796557 A x)). Qed.
Lemma lem3796569 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : term72.
Proof. exact (fun h0 : ~ False => @lem3796568 A x' x h1). Qed.
Lemma lem3796571 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3796572 : term72 = False.
Proof. exact (@lem3796571 False). Qed.
Lemma lem3796574 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : False.
Proof. exact (EQ_MP (@lem3796572) (@lem3796569 A x' x h1)). Qed.
Lemma lem3796575 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : (term200 A x' x) = False.
Proof. exact (prop_ext (fun h2 : term200 A x' x => @lem3796574 A x' x h1) (fun h2 : False => @lem3796506 A x' x h1)). Qed.
Lemma lem3796576 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : False.
Proof. exact (EQ_MP (@lem3796575 A x' x h1) (@lem3796506 A x' x h1)). Qed.
Lemma lem3796577 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : (term200 A x' x) = False.
Proof. exact (prop_ext (fun h2 : term200 A x' x => @lem3796576 A x' x h1) (fun h2 : False => @lem3796490 A x' x h1)). Qed.
Lemma lem3796578 {A : Type'} (x' : A) (x : A) (h1 : term200 A x' x) : False.
Proof. exact (EQ_MP (@lem3796577 A x' x h1) (@lem3796490 A x' x h1)). Qed.
Lemma lem3796579 {A : Type'} (x' : A) (x : A) : term217 A x' x.
Proof. exact (fun h0 : term200 A x' x => @lem3796578 A x' x h0). Qed.
Lemma lem3796580 {A : Type'} (x' : A) (x : A) : (term217 A x' x) = (term203 A x' x).
Proof. exact (@lem69 (term200 A x' x)). Qed.
Lemma lem3796581 {A : Type'} (x' : A) (x : A) : term203 A x' x.
Proof. exact (EQ_MP (@lem3796580 A x' x) (@lem3796579 A x' x)). Qed.
Lemma lem3796586 {A : Type'} (x : A) : term206 A x.
Proof. exact (fun x' : A => @lem3796581 A x' x). Qed.
Lemma lem3796591 {A : Type'} : term216 A.
Proof. exact (fun x : A => @lem3796586 A x). Qed.
Lemma lem3796592 {A : Type'} : term215 A.
Proof. exact (EQ_MP (@lem3796479 A) (@lem3796591 A)). Qed.
Lemma lem3796593 {A : Type'} (x : A) : term218 A x.
Proof. exact (@lem3796592 A x). Qed.
Lemma lem3796594 {A : Type'} (x : A) : (term218 A x) = (term207 A x).
Proof. exact (eq_refl (term218 A x)). Qed.
Lemma lem3796595 {A : Type'} (x : A) : term207 A x.
Proof. exact (EQ_MP (@lem3796594 A x) (@lem3796593 A x)). Qed.
Lemma lem3796597 {A : Type'} (x : A) : term207 A x.
Proof. exact (@lem3796418 A x (@lem3796595 A x)). Qed.
Lemma lem3796598 {A : Type'} (x : A) (h1 : term208 A x) : False.
Proof. exact (@lem3796597 A x (@lem3796402 A x h1)). Qed.
Lemma lem3796599 {A : Type'} (x : A) (h1 : term208 A x) : (term208 A x) = False.
Proof. exact (prop_ext (fun h2 : term208 A x => @lem3796598 A x h1) (fun h2 : False => @lem3796402 A x h1)). Qed.
Lemma lem3796600 {A : Type'} (x : A) (h1 : term208 A x) : False.
Proof. exact (EQ_MP (@lem3796599 A x h1) (@lem3796402 A x h1)). Qed.
Lemma lem3796601 {A : Type'} (x : A) : term207 A x.
Proof. exact (fun h0 : term208 A x => @lem3796600 A x h0). Qed.
Lemma lem3796602 {A : Type'} (x : A) : term206 A x.
Proof. exact (EQ_MP (@lem3796401 A x) (@lem3796601 A x)). Qed.
Lemma lem3796603 {A : Type'} (x : A) : term195 A x.
Proof. exact (EQ_MP (@lem3796397 A x) (@lem3796602 A x)). Qed.
Lemma lem3796604 {A : Type'} (x : A) : (term192 A x) = (@EMPTY A).
Proof. exact (EQ_MP (@lem3796330 A x) (@lem3796603 A x)). Qed.
Lemma lem3796605 {A B : Type'} (f : type1411 A B) (x : A) (b : B) : term194 A B f x b.
Proof. exact (EQ_MP (@lem3796315 A B f x b) (@lem3796604 A x)). Qed.
Lemma lem3796606 {A B : Type'} (b : B) (f : type1411 A B) (x : A) : term186 A B b f x.
Proof. exact (ex_intro (term219 A B b f x) b (@lem3796605 A B f x b)). Qed.
Lemma lem3796607 {A B : Type'} (b : B) (f : type1411 A B) (x' : A) (x : A) (h1 : x' = x) : term181 A B x b f x'.
Proof. exact (EQ_MP (@lem3796272 A B b f x' x h1) (@lem3796606 A B b f x)). Qed.
Lemma lem3796608 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (x' : A) : term182 A B x b f x'.
Proof. exact (fun h0 : x' = x => @lem3796607 A B b f x' x h0). Qed.
Lemma lem3796609 {A B : Type'} (x' : A) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : term145 A B s b z f x'.
Proof. exact (EQ_MP (@lem3796258 A B x' z f b s x h1 h2) (@lem3796608 A B x b f x')). Qed.
Lemma lem3796614 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : term148 A B s b z f.
Proof. exact (fun x' : A => @lem3796609 A B x' z f b s x h1 h2). Qed.
Lemma lem3796615 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : term154 A B s z f x b) : z = (f x b).
Proof. exact (proj2 (@lem3796143 A B s z f x b h1)). Qed.
Lemma lem3796616 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : term154 A B s z f x b) : s = (@INSERT A x (@EMPTY A)).
Proof. exact (proj1 (@lem3796143 A B s z f x b h1)). Qed.
Lemma lem3796617 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : (z = (f x b)) = (term148 A B s b z f).
Proof. exact (prop_ext (fun h3 : z = (f x b) => @lem3796614 A B z f b s x h1 h2) (fun h3 : term148 A B s b z f => @lem3796144 A B z f x b h1)). Qed.
Lemma lem3796618 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : term148 A B s b z f.
Proof. exact (EQ_MP (@lem3796617 A B z f b s x h1 h2) (@lem3796144 A B z f x b h1)). Qed.
Lemma lem3796619 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : (s = (@INSERT A x (@EMPTY A))) = (term148 A B s b z f).
Proof. exact (prop_ext (fun h3 : s = (@INSERT A x (@EMPTY A)) => @lem3796618 A B z f b s x h1 h2) (fun h3 : term148 A B s b z f => @lem3796145 A s x h2)). Qed.
Lemma lem3796620 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : z = (f x b)) (h2 : s = (@INSERT A x (@EMPTY A))) : term148 A B s b z f.
Proof. exact (EQ_MP (@lem3796619 A B z f b s x h1 h2) (@lem3796145 A s x h2)). Qed.
Lemma lem3796621 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term154 A B s z f x b) (h2 : s = (@INSERT A x (@EMPTY A))) : (z = (f x b)) = (term148 A B s b z f).
Proof. exact (prop_ext (fun h3 : z = (f x b) => @lem3796620 A B z f b s x h3 h2) (fun h3 : term148 A B s b z f => @lem3796615 A B s z f x b h1)). Qed.
Lemma lem3796622 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (h1 : term154 A B s z f x b) (h2 : s = (@INSERT A x (@EMPTY A))) : term148 A B s b z f.
Proof. exact (EQ_MP (@lem3796621 A B z f b s x h1 h2) (@lem3796615 A B s z f x b h1)). Qed.
Lemma lem3796623 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : term154 A B s z f x b) : (s = (@INSERT A x (@EMPTY A))) = (term148 A B s b z f).
Proof. exact (prop_ext (fun h2 : s = (@INSERT A x (@EMPTY A)) => @lem3796622 A B z f b s x h1 h2) (fun h2 : term148 A B s b z f => @lem3796616 A B s z f x b h1)). Qed.
Lemma lem3796624 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (x : A) (b : B) (h1 : term154 A B s z f x b) : term148 A B s b z f.
Proof. exact (EQ_MP (@lem3796623 A B s z f x b h1) (@lem3796616 A B s z f x b h1)). Qed.
Lemma lem3796625 {A B : Type'} (s : A -> Prop) (z : B) (f : type1411 A B) (b : B) (h1 : term118 A B s z f b) : term148 A B s b z f.
Proof. exact (ex_elim (@lem3796142 A B s z f b h1) (fun x : A => fun h0 : term220 A B s z f b x => @lem3796624 A B s z f x b h0)). Qed.
Lemma lem3796626 {A B : Type'} (s : A -> Prop) (b : B) (z : B) (f : type1411 A B) : term149 A B s b z f.
Proof. exact (fun h0 : term118 A B s z f b => @lem3796625 A B s z f b h0). Qed.
Lemma lem3796631 {A B : Type'} (s : A -> Prop) (b : B) (f : type1411 A B) : term151 A B s b f.
Proof. exact (fun z : B => @lem3796626 A B s b z f). Qed.
Lemma lem3796636 {A B : Type'} (b : B) (f : type1411 A B) : term153 A B b f.
Proof. exact (fun s : A -> Prop => @lem3796631 A B s b f). Qed.
Lemma lem3796637 {A B : Type'} (b : B) (f : type1411 A B) : term130 A B b f.
Proof. exact (EQ_MP (@lem3796141 A B b f) (@lem3796636 A B b f)). Qed.
Lemma lem3796638 {A B : Type'} (b : B) (f : type1411 A B) : term94 A B b f.
Proof. exact (EQ_MP (@lem3796054 A B b f) (@lem3796637 A B b f)). Qed.
Lemma lem3796640 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term221 A B f b s a n) = (term222 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3796641 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term221 A B f b s a n) = (term222 A B b s n a f).
Proof. exact (@lem3796640 A B b s n a f). Qed.
Lemma lem3796642 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term223 A B f b s z n) = (term224 A B b s n z f).
Proof. exact (@lem3796641 A B b s (S n) z f). Qed.
Lemma lem3796643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3796644 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term225 A B f b s z n) = (term226 A B b s n z f).
Proof. exact (MK_COMB (@lem3796643) (@lem3796642 A B b s n z f)). Qed.
Lemma lem3796645 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term227 A B b s n z f) = (term227 A B b s n z f).
Proof. exact (eq_refl (term227 A B b s n z f)). Qed.
Lemma lem3796646 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term228 A B b s n z f) = (term229 A B b s n z f).
Proof. exact (MK_COMB (@lem3796644 A B b s n z f) (@lem3796645 A B b s n z f)). Qed.
Lemma lem3796647 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term229 A B b s n z f) = (term228 A B b s n z f).
Proof. exact (SYM (@lem3796646 A B b s n z f)). Qed.
Lemma lem3796648 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term224 A B b s n z f) : term224 A B b s n z f.
Proof. exact (h1). Qed.
Lemma lem3796649 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (h1 : term230 A B b s n z f y) : term230 A B b s n z f y.
Proof. exact (h1). Qed.
Lemma lem3796650 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (h1 : term230 A B b s n z f y) : term230 A B b s n z f y.
Proof. exact (h1). Qed.
Lemma lem3796651 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term231 A B b s n z f y c) : term231 A B b s n z f y c.
Proof. exact (h1). Qed.
Lemma lem3796652 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term232 A B b s n z f y c) : term232 A B b s n z f y c.
Proof. exact (h1). Qed.
Lemma lem3796653 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem3796654 {A B : Type'} (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : z = (f y c).
Proof. exact (h1). Qed.
Lemma lem3796655 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : term233 A B f b s y c n.
Proof. exact (h1). Qed.
Lemma lem3796656 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3796689 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3796690 {A : Type'} (s : A -> Prop) : (@DELETE A s) = (@DELETE A s).
Proof. exact (eq_refl (@DELETE A s)). Qed.
Lemma lem3796691 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : x = y) : (@DELETE A s x) = (@DELETE A s y).
Proof. exact (MK_COMB (@lem3796690 A s) (@lem3796689 A x y h1)). Qed.
Lemma lem3796692 {A B : Type'} (f : type1411 A B) (b : B) : (@FINREC A B f b) = (@FINREC A B f b).
Proof. exact (eq_refl (@FINREC A B f b)). Qed.
Lemma lem3796693 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (y : A) (h1 : x = y) : (term234 A B f b s x) = (term234 A B f b s y).
Proof. exact (MK_COMB (@lem3796692 A B f b) (@lem3796691 A s x y h1)). Qed.
Lemma lem3796694 {B : Type'} (w : B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3796695 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : B) (x : A) (y : A) (h1 : x = y) : (term235 A B f b s x w) = (term235 A B f b s y w).
Proof. exact (MK_COMB (@lem3796693 A B f b s x y h1) (@lem3796694 B w)). Qed.
Lemma lem3796696 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem3796697 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : B) (n : nat) (x : A) (y : A) (h1 : x = y) : (term233 A B f b s x w n) = (term233 A B f b s y w n).
Proof. exact (MK_COMB (@lem3796695 A B f b s w x y h1) (@lem3796696 n)). Qed.
Lemma lem3796698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796699 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : B) (n : nat) (x : A) (y : A) (h1 : x = y) : (term236 A B f b s x w n) = (term236 A B f b s y w n).
Proof. exact (MK_COMB (@lem3796698) (@lem3796697 A B f b s w n x y h1)). Qed.
Lemma lem3796703 {A B : Type'} (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : z = (f y c).
Proof. exact (h1). Qed.
Lemma lem3796704 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3796705 {A B : Type'} (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : (@eq B z) = (term178 A B f y c).
Proof. exact (MK_COMB (@lem3796704 B) (@lem3796703 A B z f y c h1)). Qed.
Lemma lem3796707 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3796708 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3796709 {A B : Type'} (f : type1411 A B) (x : A) (y : A) (h1 : x = y) : (f x) = (f y).
Proof. exact (MK_COMB (@lem3796708 A B f) (@lem3796707 A x y h1)). Qed.
Lemma lem3796710 {B : Type'} (w : B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3796711 {A B : Type'} (f : type1411 A B) (w : B) (x : A) (y : A) (h1 : x = y) : (f x w) = (f y w).
Proof. exact (MK_COMB (@lem3796709 A B f x y h1) (@lem3796710 B w)). Qed.
Lemma lem3796712 {A B : Type'} (w : B) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : x = y) (h2 : z = (f y c)) : (z = (f x w)) = ((f y c) = (f y w)).
Proof. exact (MK_COMB (@lem3796705 A B z f y c h2) (@lem3796711 A B f w x y h1)). Qed.
Lemma lem3796715 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (w : B) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : x = y) (h2 : z = (f y c)) : (term232 A B b s n z f x w) = (term237 A B b s n c f y w).
Proof. exact (MK_COMB (@lem3796699 A B f b s w n x y h1) (@lem3796712 A B w x z f y c h1 h2)). Qed.
Lemma lem3796718 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : x = y) (h2 : z = (f y c)) : (term238 A B b s n z f x) = (term239 A B b s n c f y).
Proof. exact (fun_ext (fun w : B => @lem3796715 A B b s n w x z f y c h1 h2)). Qed.
Lemma lem3796719 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3796720 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : x = y) (h2 : z = (f y c)) : (term240 A B b s n z f x) = (term241 A B b s n c f y).
Proof. exact (MK_COMB (@lem3796719 B) (@lem3796718 A B b s n x z f y c h1 h2)). Qed.
Lemma lem3796725 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : x = y) (h2 : z = (f y c)) : (term241 A B b s n c f y) = (term240 A B b s n z f x).
Proof. exact (SYM (@lem3796720 A B b s n x z f y c h1 h2)). Qed.
Lemma lem3796773 {A B : Type'} (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : z = (f y c).
Proof. exact (h1). Qed.
Lemma lem3796774 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3796775 {A B : Type'} (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : (@eq B z) = (term178 A B f y c).
Proof. exact (MK_COMB (@lem3796774 B) (@lem3796773 A B z f y c h1)). Qed.
Lemma lem3796776 {A B : Type'} (f : type1411 A B) (x : A) (w : B) : (f x w) = (f x w).
Proof. exact (eq_refl (f x w)). Qed.
Lemma lem3796777 {A B : Type'} (x : A) (w : B) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : (z = (f x w)) = ((f y c) = (f x w)).
Proof. exact (MK_COMB (@lem3796775 A B z f y c h1) (@lem3796776 A B f x w)). Qed.
Lemma lem3796780 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (w : B) (n : nat) : (term236 A B f b s x w n) = (term236 A B f b s x w n).
Proof. exact (eq_refl (term236 A B f b s x w n)). Qed.
Lemma lem3796781 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (w : B) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : (term232 A B b s n z f x w) = (term242 A B b s n y c f x w).
Proof. exact (MK_COMB (@lem3796780 A B f b s x w n) (@lem3796777 A B x w z f y c h1)). Qed.
Lemma lem3796784 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : (term238 A B b s n z f x) = (term243 A B b s n y c f x).
Proof. exact (fun_ext (fun w : B => @lem3796781 A B b s n x w z f y c h1)). Qed.
Lemma lem3796785 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3796786 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : (term240 A B b s n z f x) = (term244 A B b s n y c f x).
Proof. exact (MK_COMB (@lem3796785 B) (@lem3796784 A B b s n x z f y c h1)). Qed.
Lemma lem3796791 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : z = (f y c)) : (term244 A B b s n y c f x) = (term240 A B b s n z f x).
Proof. exact (SYM (@lem3796786 A B b s n x z f y c h1)). Qed.
Lemma lem3796813 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) : (term233 A B f b s y c n) = ((term233 A B f b s y c n) = True).
Proof. exact (@lem7 (term233 A B f b s y c n)). Qed.
Lemma lem3796820 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : (term233 A B f b s y c n) = True.
Proof. exact (EQ_MP (@lem3796813 A B f b s y c n) (@lem3796655 A B f b s y c n h1)). Qed.
Lemma lem3796821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796822 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : (term236 A B f b s y c n) = (and True).
Proof. exact (MK_COMB (@lem3796821) (@lem3796820 A B f b s y c n h1)). Qed.
Lemma lem3796824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3796825 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3796824 B x). Qed.
Lemma lem3796826 {A B : Type'} (f : type1411 A B) (y : A) (c : B) : ((f y c) = (f y c)) = True.
Proof. exact (@lem3796825 B (f y c)). Qed.
Lemma lem3796827 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : (term245 A B b s n f y c) = (True /\ True).
Proof. exact (MK_COMB (@lem3796822 A B f b s y c n h1) (@lem3796826 A B f y c)). Qed.
Lemma lem3796829 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3796830 : (True /\ True) = True.
Proof. exact (@lem3796829 True). Qed.
Lemma lem3796831 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : (term245 A B b s n f y c) = True.
Proof. exact (TRANS (@lem3796827 A B f b s y c n h1) (@lem3796830)). Qed.
Lemma lem3796832 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : True = (term245 A B b s n f y c).
Proof. exact (SYM (@lem3796831 A B f b s y c n h1)). Qed.
Lemma lem3796833 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : term245 A B b s n f y c.
Proof. exact (EQ_MP (@lem3796832 A B f b s y c n h1) (@lem0)). Qed.
Lemma lem3796834 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : term241 A B b s n c f y.
Proof. exact (ex_intro (term239 A B b s n c f y) c (@lem3796833 A B f b s y c n h1)). Qed.
Lemma lem3796835 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term233 A B f b s y c n) : term233 A B f b s y c n.
Proof. exact (h1). Qed.
Lemma lem3796862 {A B : Type'} (s : A -> Prop) (b : B) (n : nat) (f : type1411 A B) (h1 : term98 A B b n f) : term246 A B b n f s.
Proof. exact (@lem3795995 A B b n f h1 s). Qed.
Lemma lem3796863 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term246 A B b n f s) = (term247 A B b s n f).
Proof. exact (eq_refl (term246 A B b n f s)). Qed.
Lemma lem3796864 {A B : Type'} (s : A -> Prop) (b : B) (n : nat) (f : type1411 A B) (h1 : term98 A B b n f) : term247 A B b s n f.
Proof. exact (EQ_MP (@lem3796863 A B b s n f) (@lem3796862 A B s b n f h1)). Qed.
Lemma lem3796865 {A B : Type'} (s : A -> Prop) (z : B) (b : B) (n : nat) (f : type1411 A B) (h1 : term98 A B b n f) : term248 A B b s n f z.
Proof. exact (@lem3796864 A B s b n f h1 z). Qed.
Lemma lem3796866 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term248 A B b s n f z) = (term249 A B b s n z f).
Proof. exact (eq_refl (term248 A B b s n f z)). Qed.
Lemma lem3796869 {A B : Type'} (s : A -> Prop) (z : B) (b : B) (n : nat) (f : type1411 A B) (h1 : term98 A B b n f) : term249 A B b s n z f.
Proof. exact (EQ_MP (@lem3796866 A B b s n z f) (@lem3796865 A B s z b n f h1)). Qed.
Lemma lem3796870 {A B : Type'} (s : A -> Prop) (z : B) (b : B) (n : nat) (f : type1411 A B) (h1 : term98 A B b n f) : term249 A B b s n z f.
Proof. exact (@lem3796869 A B s z b n f h1). Qed.
Lemma lem3796871 {A B : Type'} (s : A -> Prop) (y : A) (c : B) (b : B) (n : nat) (f : type1411 A B) (h1 : term98 A B b n f) : term250 A B b s y n c f.
Proof. exact (@lem3796870 A B (@DELETE A s y) c b n f h1). Qed.
Lemma lem3796872 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term98 A B b n f) (h2 : term233 A B f b s y c n) : term251 A B b s y n c f.
Proof. exact (@lem3796871 A B s y c b n f h1 (@lem3796835 A B f b s y c n h2)). Qed.
Lemma lem3796873 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term98 A B b n f) (h2 : term233 A B f b s y c n) : term252 A B b s y n c f x.
Proof. exact (@lem3796872 A B f b s y c n h1 h2 x). Qed.
Lemma lem3796874 {A B : Type'} (b : B) (s : A -> Prop) (y : A) (n : nat) (c : B) (f : type1411 A B) (x : A) : (term252 A B b s y n c f x) = (term253 A B b s y n c f x).
Proof. exact (eq_refl (term252 A B b s y n c f x)). Qed.
Lemma lem3796875 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term98 A B b n f) (h2 : term233 A B f b s y c n) : term253 A B b s y n c f x.
Proof. exact (EQ_MP (@lem3796874 A B b s y n c f x) (@lem3796873 A B x f b s y c n h1 h2)). Qed.
Lemma lem3796876 {A : Type'} (s : A -> Prop) : term254 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3796877 {A : Type'} (s : A -> Prop) : (term254 A s) = (term255 A s).
Proof. exact (eq_refl (term254 A s)). Qed.
Lemma lem3796878 {A : Type'} (s : A -> Prop) : term255 A s.
Proof. exact (EQ_MP (@lem3796877 A s) (@lem3796876 A s)). Qed.
Lemma lem3796879 {A : Type'} (s : A -> Prop) (x : A) : term256 A s x.
Proof. exact (@lem3796878 A s x). Qed.
Lemma lem3796880 {A : Type'} (s : A -> Prop) (x : A) : (term256 A s x) = (term257 A s x).
Proof. exact (eq_refl (term256 A s x)). Qed.
Lemma lem3796881 {A : Type'} (s : A -> Prop) (x : A) : term257 A s x.
Proof. exact (EQ_MP (@lem3796880 A s x) (@lem3796879 A s x)). Qed.
Lemma lem3796882 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term258 A s x y.
Proof. exact (@lem3796881 A s x y). Qed.
Lemma lem3796883 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term258 A s x y) = ((term3 A x s y) = (term4 A s x y)).
Proof. exact (eq_refl (term258 A s x y)). Qed.
Lemma lem3796906 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem3796908 {A : Type'} (x : A) (y : A) : term259 A x y.
Proof. exact (@lem82 (x = y)). Qed.
Lemma lem3796926 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (EQ_MP (@lem3796883 A s x y) (@lem3796882 A s x y)). Qed.
Lemma lem3796927 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (@lem3796926 A s x y). Qed.
Lemma lem3796931 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem3796906 A x s) (@lem3796656 A x s h1)). Qed.
Lemma lem3796932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3796933 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term7 A x s) = (and True).
Proof. exact (MK_COMB (@lem3796932) (@lem3796931 A x s h1)). Qed.
Lemma lem3796935 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (x = y) = False.
Proof. exact (@lem3796908 A x y (@lem3795944 A x y h1)). Qed.
Lemma lem3796936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3796937 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (term9 A x y) = (~ False).
Proof. exact (MK_COMB (@lem3796936) (@lem3796935 A x y h1)). Qed.
Lemma lem3796939 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3796940 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (term9 A x y) = True.
Proof. exact (TRANS (@lem3796937 A x y h1) (@lem3796939)). Qed.
Lemma lem3796941 {A : Type'} (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term4 A s x y) = (True /\ True).
Proof. exact (MK_COMB (@lem3796933 A x s h2) (@lem3796940 A x y h1)). Qed.
Lemma lem3796943 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3796944 : (True /\ True) = True.
Proof. exact (@lem3796943 True). Qed.
Lemma lem3796945 {A : Type'} (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term4 A s x y) = True.
Proof. exact (TRANS (@lem3796941 A y x s h1 h2) (@lem3796944)). Qed.
Lemma lem3796946 {A : Type'} (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term3 A x s y) = True.
Proof. exact (TRANS (@lem3796927 A s x y) (@lem3796945 A y x s h1 h2)). Qed.
Lemma lem3796947 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3796948 {A : Type'} (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term260 A x s y) = (imp True).
Proof. exact (MK_COMB (@lem3796947) (@lem3796946 A y x s h1 h2)). Qed.
Lemma lem3796957 {A B : Type'} (b : B) (s : A -> Prop) (y : A) (n : nat) (c : B) (f : type1411 A B) (x : A) : (term261 A B b s y n c f x) = (term261 A B b s y n c f x).
Proof. exact (eq_refl (term261 A B b s y n c f x)). Qed.
Lemma lem3796958 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term253 A B b s y n c f x) = (term262 A B b s y n c f x).
Proof. exact (MK_COMB (@lem3796948 A y x s h1 h2) (@lem3796957 A B b s y n c f x)). Qed.
Lemma lem3796960 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3796961 {A B : Type'} (b : B) (s : A -> Prop) (y : A) (n : nat) (c : B) (f : type1411 A B) (x : A) : (term262 A B b s y n c f x) = (term261 A B b s y n c f x).
Proof. exact (@lem3796960 (term261 A B b s y n c f x)). Qed.
Lemma lem3796970 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term253 A B b s y n c f x) = (term261 A B b s y n c f x).
Proof. exact (TRANS (@lem3796958 A B b n c f y x s h1 h2) (@lem3796961 A B b s y n c f x)). Qed.
Lemma lem3796971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3796972 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term263 A B b s y n c f x) = (term264 A B b s y n c f x).
Proof. exact (MK_COMB (@lem3796971) (@lem3796970 A B b n c f y x s h1 h2)). Qed.
Lemma lem3796981 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (y : A) (c : B) (f : type1411 A B) (x : A) : (term244 A B b s n y c f x) = (term244 A B b s n y c f x).
Proof. exact (eq_refl (term244 A B b s n y c f x)). Qed.
Lemma lem3796982 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term265 A B b s n y c f x) = (term266 A B b s n y c f x).
Proof. exact (MK_COMB (@lem3796972 A B b n c f y x s h1 h2) (@lem3796981 A B b s n y c f x)). Qed.
Lemma lem3796985 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (y : A) (x : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A x s) : (term266 A B b s n y c f x) = (term265 A B b s n y c f x).
Proof. exact (SYM (@lem3796982 A B b n c f y x s h1 h2)). Qed.
Lemma lem3796986 {A B : Type'} (b : B) (s : A -> Prop) (y : A) (n : nat) (c : B) (f : type1411 A B) (x : A) (h1 : term261 A B b s y n c f x) : term261 A B b s y n c f x.
Proof. exact (h1). Qed.
Lemma lem3796987 {A B : Type'} (b : B) (s : A -> Prop) (y : A) (n : nat) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : term267 A B b s y n c f x v) : term267 A B b s y n c f x v.
Proof. exact (h1). Qed.
Lemma lem3796988 {A B : Type'} (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : c = (f x v)) : c = (f x v).
Proof. exact (h1). Qed.
Lemma lem3796989 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term268 A B f b s y x v n) : term268 A B f b s y x v n.
Proof. exact (h1). Qed.
Lemma lem3797033 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term221 A B f b s a n) = (term222 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3797034 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term221 A B f b s a n) = (term222 A B b s n a f).
Proof. exact (@lem3797033 A B b s n a f). Qed.
Lemma lem3797035 {A B : Type'} (b : B) (s : A -> Prop) (x : A) (n : nat) (y : A) (v : B) (f : type1411 A B) : (term269 A B b s x f y v n) = (term270 A B b s x n y v f).
Proof. exact (@lem3797034 A B b (@DELETE A s x) n (f y v) f). Qed.
Lemma lem3797079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797080 {A B : Type'} (b : B) (s : A -> Prop) (x : A) (n : nat) (y : A) (v : B) (f : type1411 A B) : (term271 A B b s x f y v n) = (term272 A B b s x n y v f).
Proof. exact (MK_COMB (@lem3797079) (@lem3797035 A B b s x n y v f)). Qed.
Lemma lem3797084 {A B : Type'} (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : c = (f x v)) : c = (f x v).
Proof. exact (h1). Qed.
Lemma lem3797085 {A B : Type'} (f : type1411 A B) (y : A) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem3797086 {A B : Type'} (y : A) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : c = (f x v)) : (f y c) = (term273 A B y f x v).
Proof. exact (MK_COMB (@lem3797085 A B f y) (@lem3797084 A B c f x v h1)). Qed.
Lemma lem3797087 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3797088 {A B : Type'} (y : A) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : c = (f x v)) : (term178 A B f y c) = (term274 A B y f x v).
Proof. exact (MK_COMB (@lem3797087 B) (@lem3797086 A B y c f x v h1)). Qed.
Lemma lem3797089 {A B : Type'} (x : A) (f : type1411 A B) (y : A) (v : B) : (term273 A B x f y v) = (term273 A B x f y v).
Proof. exact (eq_refl (term273 A B x f y v)). Qed.
Lemma lem3797090 {A B : Type'} (y : A) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : c = (f x v)) : ((f y c) = (term273 A B x f y v)) = ((term273 A B y f x v) = (term273 A B x f y v)).
Proof. exact (MK_COMB (@lem3797088 A B y c f x v h1) (@lem3797089 A B x f y v)). Qed.
Lemma lem3797093 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (y : A) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : c = (f x v)) : (term275 A B b s n c x f y v) = (term276 A B b s n x f y v).
Proof. exact (MK_COMB (@lem3797080 A B b s x n y v f) (@lem3797090 A B y c f x v h1)). Qed.
Lemma lem3797096 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (y : A) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : c = (f x v)) : (term276 A B b s n x f y v) = (term275 A B b s n c x f y v).
Proof. exact (SYM (@lem3797093 A B b s n y c f x v h1)). Qed.
Lemma lem3797102 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term1 A s x y) = (term1 A s y x).
Proof. exact (EQ_MP (@lem3794833 A s y x) (@lem3795938 A s y x)). Qed.
Lemma lem3797103 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term1 A s x y) = (term1 A s y x).
Proof. exact (@lem3797102 A s y x). Qed.
Lemma lem3797104 {A B : Type'} (f : type1411 A B) (b : B) : (@FINREC A B f b) = (@FINREC A B f b).
Proof. exact (eq_refl (@FINREC A B f b)). Qed.
Lemma lem3797105 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) : (term277 A B f b s x y) = (term277 A B f b s y x).
Proof. exact (MK_COMB (@lem3797104 A B f b) (@lem3797103 A s y x)). Qed.
Lemma lem3797106 {B : Type'} (v : B) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem3797107 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) : (term278 A B f b s x y v) = (term278 A B f b s y x v).
Proof. exact (MK_COMB (@lem3797105 A B f b s y x) (@lem3797106 B v)). Qed.
Lemma lem3797108 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3797109 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) : (term268 A B f b s x y v n) = (term268 A B f b s y x v n).
Proof. exact (MK_COMB (@lem3797107 A B f b s y x v) (@lem3797108 n)). Qed.
Lemma lem3797110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797111 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) : (term279 A B f b s x y v n) = (term279 A B f b s y x v n).
Proof. exact (MK_COMB (@lem3797110) (@lem3797109 A B f b s y x v n)). Qed.
Lemma lem3797113 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3797114 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3797113 B x). Qed.
Lemma lem3797115 {A B : Type'} (f : type1411 A B) (y : A) (v : B) : ((f y v) = (f y v)) = True.
Proof. exact (@lem3797114 B (f y v)). Qed.
Lemma lem3797116 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) : (term280 A B b s x n f y v) = (term281 A B f b s y x v n).
Proof. exact (MK_COMB (@lem3797111 A B f b s y x v n) (@lem3797115 A B f y v)). Qed.
Lemma lem3797117 {A : Type'} (y : A) (s : A -> Prop) (x : A) : (term11 A y s x) = (term11 A y s x).
Proof. exact (eq_refl (term11 A y s x)). Qed.
Lemma lem3797118 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) : (term282 A B b s x n f y v) = (term283 A B f b s y x v n).
Proof. exact (MK_COMB (@lem3797117 A y s x) (@lem3797116 A B f b s y x v n)). Qed.
Lemma lem3797119 {A B : Type'} (b : B) (s : A -> Prop) (x : A) (n : nat) (f : type1411 A B) (y : A) (v : B) : (term283 A B f b s y x v n) = (term282 A B b s x n f y v).
Proof. exact (SYM (@lem3797118 A B f b s y x v n)). Qed.
Lemma lem3797120 {A : Type'} (s : A -> Prop) : term254 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3797121 {A : Type'} (s : A -> Prop) : (term254 A s) = (term255 A s).
Proof. exact (eq_refl (term254 A s)). Qed.
Lemma lem3797122 {A : Type'} (s : A -> Prop) : term255 A s.
Proof. exact (EQ_MP (@lem3797121 A s) (@lem3797120 A s)). Qed.
Lemma lem3797123 {A : Type'} (s : A -> Prop) (x : A) : term256 A s x.
Proof. exact (@lem3797122 A s x). Qed.
Lemma lem3797124 {A : Type'} (s : A -> Prop) (x : A) : (term256 A s x) = (term257 A s x).
Proof. exact (eq_refl (term256 A s x)). Qed.
Lemma lem3797125 {A : Type'} (s : A -> Prop) (x : A) : term257 A s x.
Proof. exact (EQ_MP (@lem3797124 A s x) (@lem3797123 A s x)). Qed.
Lemma lem3797126 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term258 A s x y.
Proof. exact (@lem3797125 A s x y). Qed.
Lemma lem3797127 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term258 A s x y) = ((term3 A x s y) = (term4 A s x y)).
Proof. exact (eq_refl (term258 A s x y)). Qed.
Lemma lem3797148 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = ((@IN A y s) = True).
Proof. exact (@lem7 (@IN A y s)). Qed.
Lemma lem3797155 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3797156 {A : Type'} (x : A) (y : A) (h1 : x = y) : y = x.
Proof. exact (SYM (@lem3797155 A x y h1)). Qed.
Lemma lem3797157 {A : Type'} (y : A) (x : A) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem3797158 {A : Type'} (y : A) (x : A) (h1 : y = x) : x = y.
Proof. exact (SYM (@lem3797157 A y x h1)). Qed.
Lemma lem3797159 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (prop_ext (fun h1 : x = y => @lem3797156 A x y h1) (fun h1 : y = x => @lem3797158 A y x h1)). Qed.
Lemma lem3797160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797161 {A : Type'} (y : A) (x : A) : (term9 A x y) = (term9 A y x).
Proof. exact (MK_COMB (@lem3797160) (@lem3797159 A y x)). Qed.
Lemma lem3797162 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : term9 A y x.
Proof. exact (EQ_MP (@lem3797161 A y x) (@lem3795944 A x y h1)). Qed.
Lemma lem3797163 {A : Type'} (y : A) (x : A) : term259 A y x.
Proof. exact (@lem82 (y = x)). Qed.
Lemma lem3797165 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) : (term268 A B f b s y x v n) = ((term268 A B f b s y x v n) = True).
Proof. exact (@lem7 (term268 A B f b s y x v n)). Qed.
Lemma lem3797170 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (EQ_MP (@lem3797127 A s x y) (@lem3797126 A s x y)). Qed.
Lemma lem3797171 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term3 A x s y) = (term4 A s x y).
Proof. exact (@lem3797170 A s x y). Qed.
Lemma lem3797172 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term3 A y s x) = (term4 A s y x).
Proof. exact (@lem3797171 A s y x). Qed.
Lemma lem3797176 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : (@IN A y s) = True.
Proof. exact (EQ_MP (@lem3797148 A y s) (@lem3796653 A y s h1)). Qed.
Lemma lem3797177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797178 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : (term7 A y s) = (and True).
Proof. exact (MK_COMB (@lem3797177) (@lem3797176 A y s h1)). Qed.
Lemma lem3797180 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (y = x) = False.
Proof. exact (@lem3797163 A y x (@lem3797162 A x y h1)). Qed.
Lemma lem3797181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797182 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (term9 A y x) = (~ False).
Proof. exact (MK_COMB (@lem3797181) (@lem3797180 A x y h1)). Qed.
Lemma lem3797184 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3797185 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (term9 A y x) = True.
Proof. exact (TRANS (@lem3797182 A x y h1) (@lem3797184)). Qed.
Lemma lem3797186 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A y s) : (term4 A s y x) = (True /\ True).
Proof. exact (MK_COMB (@lem3797178 A y s h2) (@lem3797185 A x y h1)). Qed.
Lemma lem3797188 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3797189 : (True /\ True) = True.
Proof. exact (@lem3797188 True). Qed.
Lemma lem3797190 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A y s) : (term4 A s y x) = True.
Proof. exact (TRANS (@lem3797186 A x y s h1 h2) (@lem3797189)). Qed.
Lemma lem3797191 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A y s) : (term3 A y s x) = True.
Proof. exact (TRANS (@lem3797172 A s y x) (@lem3797190 A x y s h1 h2)). Qed.
Lemma lem3797192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797193 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : term9 A x y) (h2 : @IN A y s) : (term11 A y s x) = (and True).
Proof. exact (MK_COMB (@lem3797192) (@lem3797191 A x y s h1 h2)). Qed.
Lemma lem3797195 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3797196 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) : (term281 A B f b s y x v n) = (term268 A B f b s y x v n).
Proof. exact (@lem3797195 (term268 A B f b s y x v n)). Qed.
Lemma lem3797198 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term268 A B f b s y x v n) : (term268 A B f b s y x v n) = True.
Proof. exact (EQ_MP (@lem3797165 A B f b s y x v n) (@lem3796989 A B f b s y x v n h1)). Qed.
Lemma lem3797199 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term268 A B f b s y x v n) : (term281 A B f b s y x v n) = True.
Proof. exact (TRANS (@lem3797196 A B f b s y x v n) (@lem3797198 A B f b s y x v n h1)). Qed.
Lemma lem3797200 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term9 A x y) (h2 : @IN A y s) (h3 : term268 A B f b s y x v n) : (term283 A B f b s y x v n) = (True /\ True).
Proof. exact (MK_COMB (@lem3797193 A x y s h1 h2) (@lem3797199 A B f b s y x v n h3)). Qed.
Lemma lem3797202 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3797203 : (True /\ True) = True.
Proof. exact (@lem3797202 True). Qed.
Lemma lem3797204 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term9 A x y) (h2 : @IN A y s) (h3 : term268 A B f b s y x v n) : (term283 A B f b s y x v n) = True.
Proof. exact (TRANS (@lem3797200 A B f b s y x v n h1 h2 h3) (@lem3797203)). Qed.
Lemma lem3797205 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term9 A x y) (h2 : @IN A y s) (h3 : term268 A B f b s y x v n) : True = (term283 A B f b s y x v n).
Proof. exact (SYM (@lem3797204 A B f b s y x v n h1 h2 h3)). Qed.
Lemma lem3797206 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term9 A x y) (h2 : @IN A y s) (h3 : term268 A B f b s y x v n) : term283 A B f b s y x v n.
Proof. exact (EQ_MP (@lem3797205 A B f b s y x v n h1 h2 h3) (@lem0)). Qed.
Lemma lem3797207 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term9 A x y) (h2 : @IN A y s) (h3 : term268 A B f b s y x v n) : term282 A B b s x n f y v.
Proof. exact (EQ_MP (@lem3797119 A B b s x n f y v) (@lem3797206 A B f b s y x v n h1 h2 h3)). Qed.
Lemma lem3797208 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term9 A x y) (h2 : @IN A y s) (h3 : term268 A B f b s y x v n) : term284 A B b s x n v f y.
Proof. exact (ex_intro (term285 A B b s x n v f y) v (@lem3797207 A B f b s y x v n h1 h2 h3)). Qed.
Lemma lem3797209 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term9 A x y) (h2 : @IN A y s) (h3 : term268 A B f b s y x v n) : term270 A B b s x n y v f.
Proof. exact (ex_intro (term286 A B b s x n y v f) y (@lem3797208 A B f b s y x v n h1 h2 h3)). Qed.
Lemma lem3797235 {A B : Type'} (f : type1411 A B) (h1 : term89 A B f) : term89 A B f.
Proof. exact (h1). Qed.
Lemma lem3797236 {A B : Type'} (x : A) (f : type1411 A B) (h1 : term89 A B f) : term287 A B f x.
Proof. exact (@lem3797235 A B f h1 x). Qed.
Lemma lem3797237 {A B : Type'} (f : type1411 A B) (x : A) : (term287 A B f x) = (term288 A B f x).
Proof. exact (eq_refl (term287 A B f x)). Qed.
Lemma lem3797238 {A B : Type'} (x : A) (f : type1411 A B) (h1 : term89 A B f) : term288 A B f x.
Proof. exact (EQ_MP (@lem3797237 A B f x) (@lem3797236 A B x f h1)). Qed.
Lemma lem3797239 {A B : Type'} (x : A) (y : A) (f : type1411 A B) (h1 : term89 A B f) : term289 A B f x y.
Proof. exact (@lem3797238 A B x f h1 y). Qed.
Lemma lem3797240 {A B : Type'} (y : A) (f : type1411 A B) (x : A) : (term289 A B f x y) = (term290 A B y f x).
Proof. exact (eq_refl (term289 A B f x y)). Qed.
Lemma lem3797241 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term89 A B f) : term290 A B y f x.
Proof. exact (EQ_MP (@lem3797240 A B y f x) (@lem3797239 A B x y f h1)). Qed.
Lemma lem3797242 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term89 A B f) : term291 A B y f x s.
Proof. exact (@lem3797241 A B y x f h1 s). Qed.
Lemma lem3797243 {A B : Type'} (y : A) (f : type1411 A B) (x : A) (s : B) : (term291 A B y f x s) = (term292 A B y f x s).
Proof. exact (eq_refl (term291 A B y f x s)). Qed.
Lemma lem3797244 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term89 A B f) : term292 A B y f x s.
Proof. exact (EQ_MP (@lem3797243 A B y f x s) (@lem3797242 A B y x s f h1)). Qed.
Lemma lem3797245 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : term9 A x y.
Proof. exact (h1). Qed.
Lemma lem3797246 {A B : Type'} (s : B) (f : type1411 A B) (x : A) (y : A) (h1 : term89 A B f) (h2 : term9 A x y) : (term273 A B x f y s) = (term273 A B y f x s).
Proof. exact (@lem3797244 A B y x s f h1 (@lem3797245 A x y h2)). Qed.
Lemma lem3797247 {A B : Type'} (f : type1411 A B) (s : B) (x : A) (y : A) (h1 : term9 A x y) : term293 A B y f x s.
Proof. exact (fun h0 : term89 A B f => @lem3797246 A B s f x y h0 h1). Qed.
Lemma lem3797248 {A B : Type'} (f : type1411 A B) (h1 : term89 A B f) : term89 A B f.
Proof. exact (h1). Qed.
Lemma lem3797249 {A B : Type'} (s : B) (f : type1411 A B) (x : A) (y : A) (h1 : term89 A B f) (h2 : term9 A x y) : (term273 A B x f y s) = (term273 A B y f x s).
Proof. exact (@lem3797247 A B f s x y h2 (@lem3797248 A B f h1)). Qed.
Lemma lem3797250 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term89 A B f) : term292 A B y f x s.
Proof. exact (fun h0 : term9 A x y => @lem3797249 A B s f x y h1 h0). Qed.
Lemma lem3797251 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term89 A B f) : term290 A B y f x.
Proof. exact (fun s : B => @lem3797250 A B y x s f h1). Qed.
Lemma lem3797252 {A B : Type'} (y : A) (f : type1411 A B) (h1 : term89 A B f) : term294 A B y f.
Proof. exact (fun x : A => @lem3797251 A B y x f h1). Qed.
Lemma lem3797253 {A B : Type'} (f : type1411 A B) (h1 : term89 A B f) : term295 A B f.
Proof. exact (fun y : A => @lem3797252 A B y f h1). Qed.
Lemma lem3797254 {A B : Type'} (f : type1411 A B) : term296 A B f.
Proof. exact (fun h0 : term89 A B f => @lem3797253 A B f h0). Qed.
Lemma lem3797255 {A B : Type'} (f : type1411 A B) (h1 : term89 A B f) : term295 A B f.
Proof. exact (@lem3797254 A B f (@lem3795971 A B f h1)). Qed.
Lemma lem3797256 {A B : Type'} (y : A) (f : type1411 A B) (h1 : term89 A B f) : term297 A B f y.
Proof. exact (@lem3797255 A B f h1 y). Qed.
Lemma lem3797257 {A B : Type'} (y : A) (f : type1411 A B) : (term297 A B f y) = (term294 A B y f).
Proof. exact (eq_refl (term297 A B f y)). Qed.
Lemma lem3797258 {A B : Type'} (y : A) (f : type1411 A B) (h1 : term89 A B f) : term294 A B y f.
Proof. exact (EQ_MP (@lem3797257 A B y f) (@lem3797256 A B y f h1)). Qed.
Lemma lem3797259 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term89 A B f) : term298 A B y f x.
Proof. exact (@lem3797258 A B y f h1 x). Qed.
Lemma lem3797260 {A B : Type'} (y : A) (f : type1411 A B) (x : A) : (term298 A B y f x) = (term290 A B y f x).
Proof. exact (eq_refl (term298 A B y f x)). Qed.
Lemma lem3797261 {A B : Type'} (y : A) (x : A) (f : type1411 A B) (h1 : term89 A B f) : term290 A B y f x.
Proof. exact (EQ_MP (@lem3797260 A B y f x) (@lem3797259 A B y x f h1)). Qed.
Lemma lem3797262 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term89 A B f) : term291 A B y f x s.
Proof. exact (@lem3797261 A B y x f h1 s). Qed.
Lemma lem3797263 {A B : Type'} (y : A) (f : type1411 A B) (x : A) (s : B) : (term291 A B y f x s) = (term292 A B y f x s).
Proof. exact (eq_refl (term291 A B y f x s)). Qed.
Lemma lem3797266 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term89 A B f) : term292 A B y f x s.
Proof. exact (EQ_MP (@lem3797263 A B y f x s) (@lem3797262 A B y x s f h1)). Qed.
Lemma lem3797267 {A B : Type'} (y : A) (x : A) (s : B) (f : type1411 A B) (h1 : term89 A B f) : term292 A B y f x s.
Proof. exact (@lem3797266 A B y x s f h1). Qed.
Lemma lem3797268 {A B : Type'} (x : A) (y : A) (v : B) (f : type1411 A B) (h1 : term89 A B f) : term292 A B x f y v.
Proof. exact (@lem3797267 A B x y v f h1). Qed.
Lemma lem3797295 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3797296 {A : Type'} (x : A) (y : A) (h1 : x = y) : y = x.
Proof. exact (SYM (@lem3797295 A x y h1)). Qed.
Lemma lem3797297 {A : Type'} (y : A) (x : A) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem3797298 {A : Type'} (y : A) (x : A) (h1 : y = x) : x = y.
Proof. exact (SYM (@lem3797297 A y x h1)). Qed.
Lemma lem3797299 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (prop_ext (fun h1 : x = y => @lem3797296 A x y h1) (fun h1 : y = x => @lem3797298 A y x h1)). Qed.
Lemma lem3797300 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797301 {A : Type'} (y : A) (x : A) : (term9 A x y) = (term9 A y x).
Proof. exact (MK_COMB (@lem3797300) (@lem3797299 A y x)). Qed.
Lemma lem3797302 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : term9 A y x.
Proof. exact (EQ_MP (@lem3797301 A y x) (@lem3795944 A x y h1)). Qed.
Lemma lem3797303 {A : Type'} (y : A) (x : A) : term259 A y x.
Proof. exact (@lem82 (y = x)). Qed.
Lemma lem3797308 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (y = x) = False.
Proof. exact (@lem3797303 A y x (@lem3797302 A x y h1)). Qed.
Lemma lem3797309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797310 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (term9 A y x) = (~ False).
Proof. exact (MK_COMB (@lem3797309) (@lem3797308 A x y h1)). Qed.
Lemma lem3797312 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3797313 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : (term9 A y x) = True.
Proof. exact (TRANS (@lem3797310 A x y h1) (@lem3797312)). Qed.
Lemma lem3797314 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : True = (term9 A y x).
Proof. exact (SYM (@lem3797313 A x y h1)). Qed.
Lemma lem3797315 {A : Type'} (x : A) (y : A) (h1 : term9 A x y) : term9 A y x.
Proof. exact (EQ_MP (@lem3797314 A x y h1) (@lem0)). Qed.
Lemma lem3797316 {A B : Type'} (v : B) (f : type1411 A B) (x : A) (y : A) (h1 : term89 A B f) (h2 : term9 A x y) : (term273 A B y f x v) = (term273 A B x f y v).
Proof. exact (@lem3797268 A B x y v f h1 (@lem3797315 A x y h2)). Qed.
Lemma lem3797317 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : @IN A y s) (h4 : term268 A B f b s y x v n) : term276 A B b s n x f y v.
Proof. exact (conj (@lem3797209 A B f b s y x v n h2 h3 h4) (@lem3797316 A B v f x y h1 h2)). Qed.
Lemma lem3797318 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : c = (f x v)) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : term275 A B b s n c x f y v.
Proof. exact (EQ_MP (@lem3797096 A B b s n y c f x v h3) (@lem3797317 A B f b s y x v n h1 h2 h4 h5)). Qed.
Lemma lem3797319 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : c = (f x v)) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : term244 A B b s n y c f x.
Proof. exact (ex_intro (term243 A B b s n y c f x) (f y v) (@lem3797318 A B c f b s y x v n h1 h2 h3 h4 h5)). Qed.
Lemma lem3797320 {A B : Type'} (b : B) (s : A -> Prop) (y : A) (n : nat) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : term267 A B b s y n c f x v) : c = (f x v).
Proof. exact (proj2 (@lem3796987 A B b s y n c f x v h1)). Qed.
Lemma lem3797321 {A B : Type'} (b : B) (s : A -> Prop) (y : A) (n : nat) (c : B) (f : type1411 A B) (x : A) (v : B) (h1 : term267 A B b s y n c f x v) : term268 A B f b s y x v n.
Proof. exact (proj1 (@lem3796987 A B b s y n c f x v h1)). Qed.
Lemma lem3797322 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : c = (f x v)) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : (c = (f x v)) = (term244 A B b s n y c f x).
Proof. exact (prop_ext (fun h6 : c = (f x v) => @lem3797319 A B c f b s y x v n h1 h2 h3 h4 h5) (fun h6 : term244 A B b s n y c f x => @lem3796988 A B c f x v h3)). Qed.
Lemma lem3797323 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : c = (f x v)) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : term244 A B b s n y c f x.
Proof. exact (EQ_MP (@lem3797322 A B c f b s y x v n h1 h2 h3 h4 h5) (@lem3796988 A B c f x v h3)). Qed.
Lemma lem3797324 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : c = (f x v)) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : (term268 A B f b s y x v n) = (term244 A B b s n y c f x).
Proof. exact (prop_ext (fun h6 : term268 A B f b s y x v n => @lem3797323 A B c f b s y x v n h1 h2 h3 h4 h5) (fun h6 : term244 A B b s n y c f x => @lem3796989 A B f b s y x v n h5)). Qed.
Lemma lem3797325 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : c = (f x v)) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : term244 A B b s n y c f x.
Proof. exact (EQ_MP (@lem3797324 A B c f b s y x v n h1 h2 h3 h4 h5) (@lem3796989 A B f b s y x v n h5)). Qed.
Lemma lem3797326 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : term267 A B b s y n c f x v) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : (c = (f x v)) = (term244 A B b s n y c f x).
Proof. exact (prop_ext (fun h6 : c = (f x v) => @lem3797325 A B c f b s y x v n h1 h2 h6 h4 h5) (fun h6 : term244 A B b s n y c f x => @lem3797320 A B b s y n c f x v h3)). Qed.
Lemma lem3797327 {A B : Type'} (c : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (x : A) (v : B) (n : nat) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : term267 A B b s y n c f x v) (h4 : @IN A y s) (h5 : term268 A B f b s y x v n) : term244 A B b s n y c f x.
Proof. exact (EQ_MP (@lem3797326 A B c f b s y x v n h1 h2 h3 h4 h5) (@lem3797320 A B b s y n c f x v h3)). Qed.
Lemma lem3797328 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (x : A) (v : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : term267 A B b s y n c f x v) (h4 : @IN A y s) : (term268 A B f b s y x v n) = (term244 A B b s n y c f x).
Proof. exact (prop_ext (fun h5 : term268 A B f b s y x v n => @lem3797327 A B c f b s y x v n h1 h2 h3 h4 h5) (fun h5 : term244 A B b s n y c f x => @lem3797321 A B b s y n c f x v h3)). Qed.
Lemma lem3797329 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (x : A) (v : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : term267 A B b s y n c f x v) (h4 : @IN A y s) : term244 A B b s n y c f x.
Proof. exact (EQ_MP (@lem3797328 A B b n c f x v y s h1 h2 h3 h4) (@lem3797321 A B b s y n c f x v h3)). Qed.
Lemma lem3797330 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (x : A) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term261 A B b s y n c f x) (h3 : term9 A x y) (h4 : @IN A y s) : term244 A B b s n y c f x.
Proof. exact (ex_elim (@lem3796986 A B b s y n c f x h2) (fun v : B => fun h0 : term299 A B b s y n c f x v => @lem3797329 A B b n c f x v y s h1 h3 h0 h4)). Qed.
Lemma lem3797331 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (x : A) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : @IN A y s) : term266 A B b s n y c f x.
Proof. exact (fun h0 : term261 A B b s y n c f x => @lem3797330 A B b n c f x y s h1 h0 h2 h3). Qed.
Lemma lem3797332 {A B : Type'} (b : B) (n : nat) (c : B) (f : type1411 A B) (x : A) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term9 A x y) (h3 : @IN A x s) (h4 : @IN A y s) : term265 A B b s n y c f x.
Proof. exact (EQ_MP (@lem3796985 A B b n c f y x s h2 h3) (@lem3797331 A B b n c f x y s h1 h2 h4)). Qed.
Lemma lem3797333 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term9 A x y) (h4 : @IN A x s) (h5 : @IN A y s) (h6 : term233 A B f b s y c n) : term244 A B b s n y c f x.
Proof. exact (@lem3797332 A B b n c f x y s h1 h3 h4 h5 (@lem3796875 A B x f b s y c n h2 h6)). Qed.
Lemma lem3797334 {A B : Type'} (c : B) (b : B) (n : nat) (f : type1411 A B) (x : A) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term9 A x y) (h4 : @IN A x s) (h5 : @IN A y s) : term300 A B b s n y c f x.
Proof. exact (fun h0 : term233 A B f b s y c n => @lem3797333 A B x f b s y c n h1 h2 h3 h4 h5 h0). Qed.
Lemma lem3797335 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term9 A x y) (h4 : @IN A x s) (h5 : @IN A y s) (h6 : term233 A B f b s y c n) : term244 A B b s n y c f x.
Proof. exact (@lem3797334 A B c b n f x y s h1 h2 h3 h4 h5 (@lem3796655 A B f b s y c n h6)). Qed.
Lemma lem3797336 {A B : Type'} (z : B) (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term9 A x y) (h4 : z = (f y c)) (h5 : @IN A x s) (h6 : @IN A y s) (h7 : term233 A B f b s y c n) : term240 A B b s n z f x.
Proof. exact (EQ_MP (@lem3796791 A B b s n x z f y c h4) (@lem3797335 A B x f b s y c n h1 h2 h3 h5 h6 h7)). Qed.
Lemma lem3797337 {A B : Type'} (x : A) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : x = y) (h2 : z = (f y c)) (h3 : term233 A B f b s y c n) : term240 A B b s n z f x.
Proof. exact (EQ_MP (@lem3796725 A B b s n x z f y c h1 h2) (@lem3796834 A B f b s y c n h3)). Qed.
Lemma lem3797338 {A B : Type'} (z : B) (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : z = (f y c)) (h4 : @IN A x s) (h5 : @IN A y s) (h6 : term233 A B f b s y c n) : term240 A B b s n z f x.
Proof. exact (or_elim (@lem3795942 A x y) (fun h0 : x = y => @lem3797337 A B x z f b s y c n h0 h3 h6) (fun h0 : term9 A x y => @lem3797336 A B z x f b s y c n h1 h2 h0 h3 h4 h5 h6)). Qed.
Lemma lem3797339 {A B : Type'} (x : A) (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : z = (f y c)) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : term301 A B b s n z f x.
Proof. exact (fun h0 : @IN A x s => @lem3797338 A B z x f b s y c n h1 h2 h3 h0 h4 h5). Qed.
Lemma lem3797344 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : z = (f y c)) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : term227 A B b s n z f.
Proof. exact (fun x : A => @lem3797339 A B x z f b s y c n h1 h2 h3 h4 h5). Qed.
Lemma lem3797345 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term231 A B b s n z f y c) : term232 A B b s n z f y c.
Proof. exact (proj2 (@lem3796651 A B b s n z f y c h1)). Qed.
Lemma lem3797346 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term231 A B b s n z f y c) : @IN A y s.
Proof. exact (proj1 (@lem3796651 A B b s n z f y c h1)). Qed.
Lemma lem3797347 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term232 A B b s n z f y c) : z = (f y c).
Proof. exact (proj2 (@lem3796652 A B b s n z f y c h1)). Qed.
Lemma lem3797348 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term232 A B b s n z f y c) : term233 A B f b s y c n.
Proof. exact (proj1 (@lem3796652 A B b s n z f y c h1)). Qed.
Lemma lem3797349 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : z = (f y c)) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : (z = (f y c)) = (term227 A B b s n z f).
Proof. exact (prop_ext (fun h6 : z = (f y c) => @lem3797344 A B z f b s y c n h1 h2 h3 h4 h5) (fun h6 : term227 A B b s n z f => @lem3796654 A B z f y c h3)). Qed.
Lemma lem3797350 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : z = (f y c)) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : term227 A B b s n z f.
Proof. exact (EQ_MP (@lem3797349 A B z f b s y c n h1 h2 h3 h4 h5) (@lem3796654 A B z f y c h3)). Qed.
Lemma lem3797351 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : z = (f y c)) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : (term233 A B f b s y c n) = (term227 A B b s n z f).
Proof. exact (prop_ext (fun h6 : term233 A B f b s y c n => @lem3797350 A B z f b s y c n h1 h2 h3 h4 h5) (fun h6 : term227 A B b s n z f => @lem3796655 A B f b s y c n h5)). Qed.
Lemma lem3797352 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : z = (f y c)) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : term227 A B b s n z f.
Proof. exact (EQ_MP (@lem3797351 A B z f b s y c n h1 h2 h3 h4 h5) (@lem3796655 A B f b s y c n h5)). Qed.
Lemma lem3797353 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term232 A B b s n z f y c) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : (z = (f y c)) = (term227 A B b s n z f).
Proof. exact (prop_ext (fun h6 : z = (f y c) => @lem3797352 A B z f b s y c n h1 h2 h6 h4 h5) (fun h6 : term227 A B b s n z f => @lem3797347 A B b s n z f y c h3)). Qed.
Lemma lem3797354 {A B : Type'} (z : B) (f : type1411 A B) (b : B) (s : A -> Prop) (y : A) (c : B) (n : nat) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term232 A B b s n z f y c) (h4 : @IN A y s) (h5 : term233 A B f b s y c n) : term227 A B b s n z f.
Proof. exact (EQ_MP (@lem3797353 A B z f b s y c n h1 h2 h3 h4 h5) (@lem3797347 A B b s n z f y c h3)). Qed.
Lemma lem3797355 {A B : Type'} (b : B) (n : nat) (z : B) (f : type1411 A B) (c : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term232 A B b s n z f y c) (h4 : @IN A y s) : (term233 A B f b s y c n) = (term227 A B b s n z f).
Proof. exact (prop_ext (fun h5 : term233 A B f b s y c n => @lem3797354 A B z f b s y c n h1 h2 h3 h4 h5) (fun h5 : term227 A B b s n z f => @lem3797348 A B b s n z f y c h3)). Qed.
Lemma lem3797356 {A B : Type'} (b : B) (n : nat) (z : B) (f : type1411 A B) (c : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term232 A B b s n z f y c) (h4 : @IN A y s) : term227 A B b s n z f.
Proof. exact (EQ_MP (@lem3797355 A B b n z f c y s h1 h2 h3 h4) (@lem3797348 A B b s n z f y c h3)). Qed.
Lemma lem3797357 {A B : Type'} (b : B) (n : nat) (z : B) (f : type1411 A B) (c : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term232 A B b s n z f y c) (h4 : @IN A y s) : (@IN A y s) = (term227 A B b s n z f).
Proof. exact (prop_ext (fun h5 : @IN A y s => @lem3797356 A B b n z f c y s h1 h2 h3 h4) (fun h5 : term227 A B b s n z f => @lem3796653 A y s h4)). Qed.
Lemma lem3797358 {A B : Type'} (b : B) (n : nat) (z : B) (f : type1411 A B) (c : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term232 A B b s n z f y c) (h4 : @IN A y s) : term227 A B b s n z f.
Proof. exact (EQ_MP (@lem3797357 A B b n z f c y s h1 h2 h3 h4) (@lem3796653 A y s h4)). Qed.
Lemma lem3797359 {A B : Type'} (b : B) (n : nat) (z : B) (f : type1411 A B) (c : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term231 A B b s n z f y c) (h4 : @IN A y s) : (term232 A B b s n z f y c) = (term227 A B b s n z f).
Proof. exact (prop_ext (fun h5 : term232 A B b s n z f y c => @lem3797358 A B b n z f c y s h1 h2 h5 h4) (fun h5 : term227 A B b s n z f => @lem3797345 A B b s n z f y c h3)). Qed.
Lemma lem3797360 {A B : Type'} (b : B) (n : nat) (z : B) (f : type1411 A B) (c : B) (y : A) (s : A -> Prop) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term231 A B b s n z f y c) (h4 : @IN A y s) : term227 A B b s n z f.
Proof. exact (EQ_MP (@lem3797359 A B b n z f c y s h1 h2 h3 h4) (@lem3797345 A B b s n z f y c h3)). Qed.
Lemma lem3797361 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term231 A B b s n z f y c) : (@IN A y s) = (term227 A B b s n z f).
Proof. exact (prop_ext (fun h4 : @IN A y s => @lem3797360 A B b n z f c y s h1 h2 h3 h4) (fun h4 : term227 A B b s n z f => @lem3797346 A B b s n z f y c h3)). Qed.
Lemma lem3797362 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (c : B) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term231 A B b s n z f y c) : term227 A B b s n z f.
Proof. exact (EQ_MP (@lem3797361 A B b s n z f y c h1 h2 h3) (@lem3797346 A B b s n z f y c h3)). Qed.
Lemma lem3797363 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term230 A B b s n z f y) : term227 A B b s n z f.
Proof. exact (ex_elim (@lem3796650 A B b s n z f y h3) (fun c : B => fun h0 : term302 A B b s n z f y c => @lem3797362 A B b s n z f y c h1 h2 h0)). Qed.
Lemma lem3797364 {A B : Type'} (y : A) (s : A -> Prop) (z : B) (b : B) (n : nat) (f : type1411 A B) (h1 : term89 A B f) (h2 : term98 A B b n f) : term303 A B y b s n z f.
Proof. exact (fun h0 : term230 A B b s n z f y => @lem3797363 A B b s n z f y h1 h2 h0). Qed.
Lemma lem3797365 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (y : A) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term230 A B b s n z f y) : term227 A B b s n z f.
Proof. exact (@lem3797364 A B y s z b n f h1 h2 (@lem3796649 A B b s n z f y h3)). Qed.
Lemma lem3797366 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term89 A B f) (h2 : term98 A B b n f) (h3 : term224 A B b s n z f) : term227 A B b s n z f.
Proof. exact (ex_elim (@lem3796648 A B b s n z f h3) (fun y : A => fun h0 : term304 A B b s n z f y => @lem3797365 A B b s n z f y h1 h2 h0)). Qed.
Lemma lem3797367 {A B : Type'} (s : A -> Prop) (z : B) (b : B) (n : nat) (f : type1411 A B) (h1 : term89 A B f) (h2 : term98 A B b n f) : term229 A B b s n z f.
Proof. exact (fun h0 : term224 A B b s n z f => @lem3797366 A B b s n z f h1 h2 h0). Qed.
Lemma lem3797368 {A B : Type'} (s : A -> Prop) (z : B) (b : B) (n : nat) (f : type1411 A B) (h1 : term89 A B f) (h2 : term98 A B b n f) : term228 A B b s n z f.
Proof. exact (EQ_MP (@lem3796647 A B b s n z f) (@lem3797367 A B s z b n f h1 h2)). Qed.
Lemma lem3797373 {A B : Type'} (s : A -> Prop) (b : B) (n : nat) (f : type1411 A B) (h1 : term89 A B f) (h2 : term98 A B b n f) : term305 A B b s n f.
Proof. exact (fun z : B => @lem3797368 A B s z b n f h1 h2). Qed.
Lemma lem3797378 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term89 A B f) (h2 : term98 A B b n f) : term102 A B b n f.
Proof. exact (fun s : A -> Prop => @lem3797373 A B s b n f h1 h2). Qed.
Lemma lem3797379 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term89 A B f) : term104 A B b n f.
Proof. exact (fun h0 : term98 A B b n f => @lem3797378 A B b n f h1 h0). Qed.
Lemma lem3797384 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term89 A B f) : term108 A B b f.
Proof. exact (fun n : nat => @lem3797379 A B b n f h1). Qed.
Lemma lem3797385 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term89 A B f) : term110 A B b f.
Proof. exact (conj (@lem3796638 A B b f) (@lem3797384 A B b f h1)). Qed.
Lemma lem3797386 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term89 A B f) : term115 A B b f.
Proof. exact (@lem3795994 A B b f (@lem3797385 A B b f h1)). Qed.
Lemma lem3797387 {A B : Type'} (b : B) (f : type1411 A B) : term306 A B b f.
Proof. exact (fun h0 : term89 A B f => @lem3797386 A B b f h0). Qed.
Lemma lem3797392 {A B : Type'} (f : type1411 A B) : term307 A B f.
Proof. exact (fun b : B => @lem3797387 A B b f). Qed.
Lemma lem3797397 {A B : Type'} : term308 A B.
Proof. exact (fun f : type1411 A B => @lem3797392 A B f). Qed.
