Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_UNCURRY_term_abbrevs.
Require Import ETA_AX_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm7_spec.
Lemma lem52764 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem52765 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem52766 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem52765 A B t) (@lem52764 A B t)). Qed.
Lemma lem52770 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term2 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem52771 (p : Prop) (q : Prop) (p' : Prop) : term3 p q p'.
Proof. exact (fun q' : Prop => @lem52770 p q p' q'). Qed.
Lemma lem52772 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun p' : Prop => @lem52771 p q p'). Qed.
Lemma lem52773 {A B C : Type'} (P : type443 A B C) : term5 A B C P.
Proof. exact (@lem52772 (term6 A B C P) (term7 A B C P)). Qed.
Lemma lem52774 {A B C : Type'} (P : type443 A B C) (p' : Prop) : term8 A B C P p'.
Proof. exact (@lem52773 A B C P p'). Qed.
Lemma lem52775 {A B C : Type'} (P : type443 A B C) (p' : Prop) : (term8 A B C P p') = (term9 A B C P p').
Proof. exact (eq_refl (term8 A B C P p')). Qed.
Lemma lem52776 {A B C : Type'} (P : type443 A B C) (p' : Prop) : term9 A B C P p'.
Proof. exact (EQ_MP (@lem52775 A B C P p') (@lem52774 A B C P p')). Qed.
Lemma lem52777 {A B C : Type'} (P : type443 A B C) (p' : Prop) (q' : Prop) : term10 A B C P p' q'.
Proof. exact (@lem52776 A B C P p' q'). Qed.
Lemma lem52778 {A B C : Type'} (P : type443 A B C) (p' : Prop) (q' : Prop) : (term10 A B C P p' q') = (term11 A B C P p' q').
Proof. exact (eq_refl (term10 A B C P p' q')). Qed.
Lemma lem52779 {A B C : Type'} (P : type443 A B C) (p' : Prop) (q' : Prop) : term11 A B C P p' q'.
Proof. exact (EQ_MP (@lem52778 A B C P p' q') (@lem52777 A B C P p' q')). Qed.
Lemma lem52784 {A B C : Type'} (P : type443 A B C) : (term6 A B C P) = (term6 A B C P).
Proof. exact (eq_refl (term6 A B C P)). Qed.
Lemma lem52785 {A B C : Type'} (P : type443 A B C) (q' : Prop) : term12 A B C P q'.
Proof. exact (@lem52779 A B C P (term6 A B C P) q'). Qed.
Lemma lem52786 {A B C : Type'} (P : type443 A B C) (q' : Prop) : term13 A B C P q'.
Proof. exact (@lem52785 A B C P q' (@lem52784 A B C P)). Qed.
Lemma lem52787 {A B C : Type'} (P : type443 A B C) (h1 : term6 A B C P) : term6 A B C P.
Proof. exact (h1). Qed.
Lemma lem52788 {A B C : Type'} (f : type1412 A B C) (P : type443 A B C) (h1 : term6 A B C P) : term14 A B C P f.
Proof. exact (@lem52787 A B C P h1 f). Qed.
Lemma lem52789 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term14 A B C P f) = (P f).
Proof. exact (eq_refl (term14 A B C P f)). Qed.
Lemma lem52790 {A B C : Type'} (f : type1412 A B C) (P : type443 A B C) (h1 : term6 A B C P) : P f.
Proof. exact (EQ_MP (@lem52789 A B C P f) (@lem52788 A B C f P h1)). Qed.
Lemma lem52791 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (P f) = ((P f) = True).
Proof. exact (@lem7 (P f)). Qed.
Lemma lem52798 {A B C : Type'} (f : type1412 A B C) (P : type443 A B C) (h1 : term6 A B C P) : (P f) = True.
Proof. exact (EQ_MP (@lem52791 A B C P f) (@lem52790 A B C f P h1)). Qed.
Lemma lem52799 {A B C : Type'} (f : type1412 A B C) (P : type443 A B C) (h1 : term6 A B C P) : (P f) = True.
Proof. exact (@lem52798 A B C f P h1). Qed.
Lemma lem52800 {A B C : Type'} (f : type1209 A B C) (P : type443 A B C) (h1 : term6 A B C P) : (term15 A B C P f) = True.
Proof. exact (@lem52799 A B C (term16 A B C f) P h1). Qed.
Lemma lem52801 {A B C : Type'} (P : type443 A B C) (h1 : term6 A B C P) : (term17 A B C P) = (term18 A B C).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem52800 A B C f P h1)). Qed.
Lemma lem52802 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem52803 {A B C : Type'} (P : type443 A B C) (h1 : term6 A B C P) : (term7 A B C P) = (term19 A B C).
Proof. exact (MK_COMB (@lem52802 A B C) (@lem52801 A B C P h1)). Qed.
Lemma lem52805 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52806 {A B C : Type'} (t : Prop) : (term21 A B C t) = t.
Proof. exact (@lem52805 (type1209 A B C) t). Qed.
Lemma lem52807 {A B C : Type'} : (term19 A B C) = True.
Proof. exact (@lem52806 A B C True). Qed.
Lemma lem52808 {A B C : Type'} (P : type443 A B C) (h1 : term6 A B C P) : (term7 A B C P) = True.
Proof. exact (TRANS (@lem52803 A B C P h1) (@lem52807 A B C)). Qed.
Lemma lem52809 {A B C : Type'} (P : type443 A B C) : term22 A B C P.
Proof. exact (fun h0 : term6 A B C P => @lem52808 A B C P h0). Qed.
Lemma lem52810 {A B C : Type'} (P : type443 A B C) : term23 A B C P.
Proof. exact (@lem52786 A B C P True). Qed.
Lemma lem52811 {A B C : Type'} (P : type443 A B C) : (term24 A B C P) = (term25 A B C P).
Proof. exact (@lem52810 A B C P (@lem52809 A B C P)). Qed.
Lemma lem52813 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem52814 {A B C : Type'} (P : type443 A B C) : (term25 A B C P) = True.
Proof. exact (@lem52813 (term6 A B C P)). Qed.
Lemma lem52815 {A B C : Type'} (P : type443 A B C) : (term24 A B C P) = True.
Proof. exact (TRANS (@lem52811 A B C P) (@lem52814 A B C P)). Qed.
Lemma lem52816 {A B C : Type'} (P : type443 A B C) : True = (term24 A B C P).
Proof. exact (SYM (@lem52815 A B C P)). Qed.
Lemma lem52817 {A B C : Type'} (P : type443 A B C) : term24 A B C P.
Proof. exact (EQ_MP (@lem52816 A B C P) (@lem0)). Qed.
Lemma lem52862 {A B C : Type'} (P : type443 A B C) (h1 : term7 A B C P) : term7 A B C P.
Proof. exact (h1). Qed.
Lemma lem52863 {A B C : Type'} (f : type1412 A B C) (P : type443 A B C) (h1 : term7 A B C P) : term26 A B C P f.
Proof. exact (@lem52862 A B C P h1 (term27 A B C f)). Qed.
Lemma lem52864 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term26 A B C P f) = (term28 A B C P f).
Proof. exact (eq_refl (term26 A B C P f)). Qed.
Lemma lem52865 {A B C : Type'} (f : type1412 A B C) (P : type443 A B C) (h1 : term7 A B C P) : term28 A B C P f.
Proof. exact (EQ_MP (@lem52864 A B C P f) (@lem52863 A B C f P h1)). Qed.
Lemma lem52869 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term2 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem52870 (p : Prop) (q : Prop) (p' : Prop) : term3 p q p'.
Proof. exact (fun q' : Prop => @lem52869 p q p' q'). Qed.
Lemma lem52871 (p : Prop) (q : Prop) : term4 p q.
Proof. exact (fun p' : Prop => @lem52870 p q p'). Qed.
Lemma lem52872 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : term29 A B C P f.
Proof. exact (@lem52871 (term28 A B C P f) (P f)). Qed.
Lemma lem52873 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (p' : Prop) : term30 A B C P f p'.
Proof. exact (@lem52872 A B C P f p'). Qed.
Lemma lem52874 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (p' : Prop) : (term30 A B C P f p') = (term31 A B C P f p').
Proof. exact (eq_refl (term30 A B C P f p')). Qed.
Lemma lem52875 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (p' : Prop) : term31 A B C P f p'.
Proof. exact (EQ_MP (@lem52874 A B C P f p') (@lem52873 A B C P f p')). Qed.
Lemma lem52876 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term32 A B C P f p' q'.
Proof. exact (@lem52875 A B C P f p' q'). Qed.
Lemma lem52877 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (p' : Prop) (q' : Prop) : (term32 A B C P f p' q') = (term33 A B C P f p' q').
Proof. exact (eq_refl (term32 A B C P f p' q')). Qed.
Lemma lem52878 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term33 A B C P f p' q'.
Proof. exact (EQ_MP (@lem52877 A B C P f p' q') (@lem52876 A B C P f p' q')). Qed.
Lemma lem52879 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term34 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem52880 {A B : Type'} (a : A) (b : B) : a = (term34 A B a b).
Proof. exact (@lem52879 A B a b). Qed.
Lemma lem52881 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term35 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem52882 {A B : Type'} (a : A) (b : B) : b = (term35 A B a b).
Proof. exact (@lem52881 A B a b). Qed.
Lemma lem52883 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem52884 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (eq_refl (term36 A)). Qed.
Lemma lem52885 {A B : Type'} (a : A) (b : B) : (term37 A a) = (term38 A B a b).
Proof. exact (MK_COMB (@lem52884 A) (@lem52880 A B a b)). Qed.
Lemma lem52886 {A B : Type'} (a : A) (b : B) : (term38 A B a b) = (term34 A B a b).
Proof. exact (eq_refl (term38 A B a b)). Qed.
Lemma lem52887 {A : Type'} (a : A) : (term39 A a) = (term39 A a).
Proof. exact (eq_refl (term39 A a)). Qed.
Lemma lem52888 {A B : Type'} (a : A) (b : B) : ((term37 A a) = (term38 A B a b)) = ((term37 A a) = (term34 A B a b)).
Proof. exact (MK_COMB (@lem52887 A a) (@lem52886 A B a b)). Qed.
Lemma lem52889 {A : Type'} (a : A) : (term37 A a) = a.
Proof. exact (eq_refl (term37 A a)). Qed.
Lemma lem52890 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem52891 {A : Type'} (a : A) : (term39 A a) = (@eq A a).
Proof. exact (MK_COMB (@lem52890 A) (@lem52889 A a)). Qed.
Lemma lem52892 {A B : Type'} (a : A) (b : B) : (term34 A B a b) = (term34 A B a b).
Proof. exact (eq_refl (term34 A B a b)). Qed.
Lemma lem52893 {A B : Type'} (a : A) (b : B) : ((term37 A a) = (term34 A B a b)) = (a = (term34 A B a b)).
Proof. exact (MK_COMB (@lem52891 A a) (@lem52892 A B a b)). Qed.
Lemma lem52894 {A B : Type'} (a : A) (b : B) : ((term37 A a) = (term38 A B a b)) = (a = (term34 A B a b)).
Proof. exact (TRANS (@lem52888 A B a b) (@lem52893 A B a b)). Qed.
Lemma lem52895 {A B : Type'} (a : A) (b : B) : a = (term34 A B a b).
Proof. exact (EQ_MP (@lem52894 A B a b) (@lem52885 A B a b)). Qed.
Lemma lem52896 {A : Type'} (a : A) : (@eq A a) = (@eq A a).
Proof. exact (eq_refl (@eq A a)). Qed.
Lemma lem52897 {A B : Type'} (a : A) (b : B) : (a = a) = (a = (term34 A B a b)).
Proof. exact (MK_COMB (@lem52896 A a) (@lem52895 A B a b)). Qed.
Lemma lem52898 {A B : Type'} (a : A) (b : B) : a = (term34 A B a b).
Proof. exact (EQ_MP (@lem52897 A B a b) (@lem52883 A a)). Qed.
Lemma lem52899 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem52900 {B : Type'} : (term36 B) = (term36 B).
Proof. exact (eq_refl (term36 B)). Qed.
Lemma lem52901 {A B : Type'} (a : A) (b : B) : (term37 B b) = (term40 A B a b).
Proof. exact (MK_COMB (@lem52900 B) (@lem52882 A B a b)). Qed.
Lemma lem52902 {A B : Type'} (a : A) (b : B) : (term40 A B a b) = (term35 A B a b).
Proof. exact (eq_refl (term40 A B a b)). Qed.
Lemma lem52903 {B : Type'} (b : B) : (term39 B b) = (term39 B b).
Proof. exact (eq_refl (term39 B b)). Qed.
Lemma lem52904 {A B : Type'} (a : A) (b : B) : ((term37 B b) = (term40 A B a b)) = ((term37 B b) = (term35 A B a b)).
Proof. exact (MK_COMB (@lem52903 B b) (@lem52902 A B a b)). Qed.
Lemma lem52905 {B : Type'} (b : B) : (term37 B b) = b.
Proof. exact (eq_refl (term37 B b)). Qed.
Lemma lem52906 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem52907 {B : Type'} (b : B) : (term39 B b) = (@eq B b).
Proof. exact (MK_COMB (@lem52906 B) (@lem52905 B b)). Qed.
Lemma lem52908 {A B : Type'} (a : A) (b : B) : (term35 A B a b) = (term35 A B a b).
Proof. exact (eq_refl (term35 A B a b)). Qed.
Lemma lem52909 {A B : Type'} (a : A) (b : B) : ((term37 B b) = (term35 A B a b)) = (b = (term35 A B a b)).
Proof. exact (MK_COMB (@lem52907 B b) (@lem52908 A B a b)). Qed.
Lemma lem52910 {A B : Type'} (a : A) (b : B) : ((term37 B b) = (term40 A B a b)) = (b = (term35 A B a b)).
Proof. exact (TRANS (@lem52904 A B a b) (@lem52909 A B a b)). Qed.
Lemma lem52911 {A B : Type'} (a : A) (b : B) : b = (term35 A B a b).
Proof. exact (EQ_MP (@lem52910 A B a b) (@lem52901 A B a b)). Qed.
Lemma lem52912 {B : Type'} (b : B) : (@eq B b) = (@eq B b).
Proof. exact (eq_refl (@eq B b)). Qed.
Lemma lem52913 {A B : Type'} (a : A) (b : B) : (b = b) = (b = (term35 A B a b)).
Proof. exact (MK_COMB (@lem52912 B b) (@lem52911 A B a b)). Qed.
Lemma lem52914 {A B : Type'} (a : A) (b : B) : b = (term35 A B a b).
Proof. exact (EQ_MP (@lem52913 A B a b) (@lem52899 B b)). Qed.
Lemma lem52915 {A B C : Type'} (f : type1412 A B C) : (term41 A B C f) = (term41 A B C f).
Proof. exact (eq_refl (term41 A B C f)). Qed.
Lemma lem52916 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term42 A B C f a) = (term43 A B C f a b).
Proof. exact (MK_COMB (@lem52915 A B C f) (@lem52898 A B a b)). Qed.
Lemma lem52917 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term43 A B C f a b) = (term44 A B C f a b).
Proof. exact (eq_refl (term43 A B C f a b)). Qed.
Lemma lem52918 {A B C : Type'} (f : type1412 A B C) (a : A) : (term45 A B C f a) = (term45 A B C f a).
Proof. exact (eq_refl (term45 A B C f a)). Qed.
Lemma lem52919 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : ((term42 A B C f a) = (term43 A B C f a b)) = ((term42 A B C f a) = (term44 A B C f a b)).
Proof. exact (MK_COMB (@lem52918 A B C f a) (@lem52917 A B C f a b)). Qed.
Lemma lem52920 {A B C : Type'} (f : type1412 A B C) (a : A) : (term42 A B C f a) = (term46 A B C f a).
Proof. exact (eq_refl (term42 A B C f a)). Qed.
Lemma lem52921 {B C : Type'} : (@eq (B -> C)) = (@eq (B -> C)).
Proof. exact (eq_refl (@eq (B -> C))). Qed.
Lemma lem52922 {A B C : Type'} (f : type1412 A B C) (a : A) : (term45 A B C f a) = (term47 A B C f a).
Proof. exact (MK_COMB (@lem52921 B C) (@lem52920 A B C f a)). Qed.
Lemma lem52923 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term44 A B C f a b) = (term44 A B C f a b).
Proof. exact (eq_refl (term44 A B C f a b)). Qed.
Lemma lem52924 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : ((term42 A B C f a) = (term44 A B C f a b)) = ((term46 A B C f a) = (term44 A B C f a b)).
Proof. exact (MK_COMB (@lem52922 A B C f a) (@lem52923 A B C f a b)). Qed.
Lemma lem52925 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : ((term42 A B C f a) = (term43 A B C f a b)) = ((term46 A B C f a) = (term44 A B C f a b)).
Proof. exact (TRANS (@lem52919 A B C f a b) (@lem52924 A B C f a b)). Qed.
Lemma lem52926 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term46 A B C f a) = (term44 A B C f a b).
Proof. exact (EQ_MP (@lem52925 A B C f a b) (@lem52916 A B C f a b)). Qed.
Lemma lem52927 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term48 A B C f a b) = (term49 A B C f a b).
Proof. exact (MK_COMB (@lem52926 A B C f a b) (@lem52914 A B a b)). Qed.
Lemma lem52928 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term49 A B C f a b) = (term50 A B C f a b).
Proof. exact (eq_refl (term49 A B C f a b)). Qed.
Lemma lem52929 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term51 A B C f a b) = (term51 A B C f a b).
Proof. exact (eq_refl (term51 A B C f a b)). Qed.
Lemma lem52930 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : ((term48 A B C f a b) = (term49 A B C f a b)) = ((term48 A B C f a b) = (term50 A B C f a b)).
Proof. exact (MK_COMB (@lem52929 A B C f a b) (@lem52928 A B C f a b)). Qed.
Lemma lem52931 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term48 A B C f a b) = (f a b).
Proof. exact (eq_refl (term48 A B C f a b)). Qed.
Lemma lem52932 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem52933 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term51 A B C f a b) = (term52 A B C f a b).
Proof. exact (MK_COMB (@lem52932 C) (@lem52931 A B C f a b)). Qed.
Lemma lem52934 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term50 A B C f a b) = (term50 A B C f a b).
Proof. exact (eq_refl (term50 A B C f a b)). Qed.
Lemma lem52935 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : ((term48 A B C f a b) = (term50 A B C f a b)) = ((f a b) = (term50 A B C f a b)).
Proof. exact (MK_COMB (@lem52933 A B C f a b) (@lem52934 A B C f a b)). Qed.
Lemma lem52936 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : ((term48 A B C f a b) = (term49 A B C f a b)) = ((f a b) = (term50 A B C f a b)).
Proof. exact (TRANS (@lem52930 A B C f a b) (@lem52935 A B C f a b)). Qed.
Lemma lem52937 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (f a b) = (term50 A B C f a b).
Proof. exact (EQ_MP (@lem52936 A B C f a b) (@lem52927 A B C f a b)). Qed.
Lemma lem52938 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term50 A B C f a b) = (f a b).
Proof. exact (SYM (@lem52937 A B C f a b)). Qed.
Lemma lem52939 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term53 A B C f a b) = (term50 A B C f a b).
Proof. exact (eq_refl (term53 A B C f a b)). Qed.
Lemma lem52940 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term53 A B C f a b) = (f a b).
Proof. exact (TRANS (@lem52939 A B C f a b) (@lem52938 A B C f a b)). Qed.
Lemma lem52941 {A B C : Type'} (f : type1412 A B C) (a : A) : term54 A B C f a.
Proof. exact (fun b : B => @lem52940 A B C f a b). Qed.
Lemma lem52942 {A B C : Type'} (f : type1412 A B C) : term55 A B C f.
Proof. exact (fun a : A => @lem52941 A B C f a). Qed.
Lemma lem52943 {A B C : Type'} (f : type1412 A B C) : term56 A B C f.
Proof. exact (ex_intro (term57 A B C f) (term58 A B C f) (@lem52942 A B C f)). Qed.
Lemma lem52945 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem52946 {C : Type'} (a : C) (b : C) : (a = b) = (@GEQ C a b).
Proof. exact (@lem52945 C a b). Qed.
Lemma lem52947 {A B C : Type'} (_1500 : type1209 A B C) (f : type1412 A B C) (a : A) (b : B) : ((term59 A B C _1500 a b) = (f a b)) = (term60 A B C _1500 f a b).
Proof. exact (@lem52946 C (term59 A B C _1500 a b) (f a b)). Qed.
Lemma lem52948 {A B C : Type'} (_1500 : type1209 A B C) (f : type1412 A B C) (a : A) : (term61 A B C _1500 f a) = (term62 A B C _1500 f a).
Proof. exact (fun_ext (fun b : B => @lem52947 A B C _1500 f a b)). Qed.
Lemma lem52949 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem52950 {A B C : Type'} (_1500 : type1209 A B C) (f : type1412 A B C) (a : A) : (term63 A B C _1500 f a) = (term64 A B C _1500 f a).
Proof. exact (MK_COMB (@lem52949 B) (@lem52948 A B C _1500 f a)). Qed.
Lemma lem52951 {A B C : Type'} (_1500 : type1209 A B C) (f : type1412 A B C) : (term65 A B C _1500 f) = (term66 A B C _1500 f).
Proof. exact (fun_ext (fun a : A => @lem52950 A B C _1500 f a)). Qed.
Lemma lem52952 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem52953 {A B C : Type'} (_1500 : type1209 A B C) (f : type1412 A B C) : (term67 A B C _1500 f) = (term68 A B C _1500 f).
Proof. exact (MK_COMB (@lem52952 A) (@lem52951 A B C _1500 f)). Qed.
Lemma lem52954 {A B C : Type'} (f : type1412 A B C) : (term57 A B C f) = (term69 A B C f).
Proof. exact (fun_ext (fun _1500 : type1209 A B C => @lem52953 A B C _1500 f)). Qed.
Lemma lem52955 {A B C : Type'} : (@ex ((prod A B) -> C)) = (@ex ((prod A B) -> C)).
Proof. exact (eq_refl (@ex ((prod A B) -> C))). Qed.
Lemma lem52956 {A B C : Type'} (f : type1412 A B C) : (term56 A B C f) = (term70 A B C f).
Proof. exact (MK_COMB (@lem52955 A B C) (@lem52954 A B C f)). Qed.
Lemma lem52957 {A B C : Type'} (f : type1412 A B C) : term70 A B C f.
Proof. exact (EQ_MP (@lem52956 A B C f) (@lem52943 A B C f)). Qed.
Lemma lem52959 {_5076 : Type'} (P : _5076 -> Prop) : term71 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem52960 {A B C : Type'} (P : type322 A B C) : term72 A B C P.
Proof. exact (@lem52959 (type1209 A B C) P). Qed.
Lemma lem52961 {A B C : Type'} (f : type1412 A B C) : term73 A B C f.
Proof. exact (@lem52960 A B C (term69 A B C f)). Qed.
Lemma lem52962 {A B C : Type'} (f : type1412 A B C) : term74 A B C f.
Proof. exact (@lem52961 A B C f (@lem52957 A B C f)). Qed.
Lemma lem52963 {A B C : Type'} (f : type1412 A B C) : (term74 A B C f) = (term75 A B C f).
Proof. exact (eq_refl (term74 A B C f)). Qed.
Lemma lem52964 {A B C : Type'} (f : type1412 A B C) : term75 A B C f.
Proof. exact (EQ_MP (@lem52963 A B C f) (@lem52962 A B C f)). Qed.
Lemma lem52965 {A B C : Type'} (f : type1412 A B C) (a : A) : term76 A B C f a.
Proof. exact (@lem52964 A B C f a). Qed.
Lemma lem52966 {A B C : Type'} (f : type1412 A B C) (a : A) : (term76 A B C f a) = (term77 A B C f a).
Proof. exact (eq_refl (term76 A B C f a)). Qed.
Lemma lem52967 {A B C : Type'} (f : type1412 A B C) (a : A) : term77 A B C f a.
Proof. exact (EQ_MP (@lem52966 A B C f a) (@lem52965 A B C f a)). Qed.
Lemma lem52968 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : term78 A B C f a b.
Proof. exact (@lem52967 A B C f a b). Qed.
Lemma lem52969 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term78 A B C f a b) = (term79 A B C f a b).
Proof. exact (eq_refl (term78 A B C f a b)). Qed.
Lemma lem52970 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : term79 A B C f a b.
Proof. exact (EQ_MP (@lem52969 A B C f a b) (@lem52968 A B C f a b)). Qed.
Lemma lem52972 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem52973 {C : Type'} (a : C) (b : C) : (@GEQ C a b) = (a = b).
Proof. exact (@lem52972 C a b). Qed.
Lemma lem52974 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term79 A B C f a b) = ((term80 A B C f a b) = (f a b)).
Proof. exact (@lem52973 C (term80 A B C f a b) (f a b)). Qed.
Lemma lem52975 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term80 A B C f a b) = (f a b).
Proof. exact (EQ_MP (@lem52974 A B C f a b) (@lem52970 A B C f a b)). Qed.
Lemma lem52976 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term80 A B C f a b) = (f a b).
Proof. exact (@lem52975 A B C f a b). Qed.
Lemma lem52977 {A B C : Type'} (f : type1412 A B C) (a : A) : (term81 A B C f a) = (term46 A B C f a).
Proof. exact (fun_ext (fun b : B => @lem52976 A B C f a b)). Qed.
Lemma lem52978 {B C : Type'} (t : B -> C) : (term1 B C t) = t.
Proof. exact (@lem52766 B C t). Qed.
Lemma lem52979 {A B C : Type'} (f : type1412 A B C) (a : A) : (term46 A B C f a) = (f a).
Proof. exact (@lem52978 B C (f a)). Qed.
Lemma lem52980 {A B C : Type'} (f : type1412 A B C) (a : A) : (term81 A B C f a) = (f a).
Proof. exact (TRANS (@lem52977 A B C f a) (@lem52979 A B C f a)). Qed.
Lemma lem52981 {A B C : Type'} (f : type1412 A B C) : (term82 A B C f) = (term83 A B C f).
Proof. exact (fun_ext (fun a : A => @lem52980 A B C f a)). Qed.
Lemma lem52982 {A B C : Type'} (t : type1412 A B C) : (term83 A B C t) = t.
Proof. exact (@lem52766 A (B -> C) t). Qed.
Lemma lem52983 {A B C : Type'} (f : type1412 A B C) : (term83 A B C f) = f.
Proof. exact (@lem52982 A B C f). Qed.
Lemma lem52984 {A B C : Type'} (f : type1412 A B C) : (term82 A B C f) = f.
Proof. exact (TRANS (@lem52981 A B C f) (@lem52983 A B C f)). Qed.
Lemma lem52985 {A B C : Type'} (P : type443 A B C) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem52986 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term28 A B C P f) = (P f).
Proof. exact (MK_COMB (@lem52985 A B C P) (@lem52984 A B C f)). Qed.
Lemma lem52987 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (q' : Prop) : term84 A B C P f q'.
Proof. exact (@lem52878 A B C P f (P f) q'). Qed.
Lemma lem52988 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (q' : Prop) : term85 A B C P f q'.
Proof. exact (@lem52987 A B C P f q' (@lem52986 A B C P f)). Qed.
Lemma lem52989 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : P f.
Proof. exact (h1). Qed.
Lemma lem52990 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (P f) = ((P f) = True).
Proof. exact (@lem7 (P f)). Qed.
Lemma lem52993 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : (P f) = True.
Proof. exact (EQ_MP (@lem52990 A B C P f) (@lem52989 A B C P f h1)). Qed.
Lemma lem52994 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : term86 A B C P f.
Proof. exact (fun h0 : P f => @lem52993 A B C P f h0). Qed.
Lemma lem52995 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : term87 A B C P f.
Proof. exact (@lem52988 A B C P f True). Qed.
Lemma lem52996 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term88 A B C P f) = (term89 A B C P f).
Proof. exact (@lem52995 A B C P f (@lem52994 A B C P f)). Qed.
Lemma lem52998 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem52999 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term89 A B C P f) = True.
Proof. exact (@lem52998 (P f)). Qed.
Lemma lem53000 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term88 A B C P f) = True.
Proof. exact (TRANS (@lem52996 A B C P f) (@lem52999 A B C P f)). Qed.
Lemma lem53001 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : True = (term88 A B C P f).
Proof. exact (SYM (@lem53000 A B C P f)). Qed.
Lemma lem53002 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : term88 A B C P f.
Proof. exact (EQ_MP (@lem53001 A B C P f) (@lem0)). Qed.
Lemma lem53003 {A B C : Type'} (f : type1412 A B C) (P : type443 A B C) (h1 : term7 A B C P) : P f.
Proof. exact (@lem53002 A B C P f (@lem52865 A B C f P h1)). Qed.
Lemma lem53008 {A B C : Type'} (P : type443 A B C) (h1 : term7 A B C P) : term6 A B C P.
Proof. exact (fun f : type1412 A B C => @lem53003 A B C f P h1). Qed.
Lemma lem53010 {A B C : Type'} (P : type443 A B C) : term90 A B C P.
Proof. exact (fun h0 : term7 A B C P => @lem53008 A B C P h0). Qed.
Lemma lem53011 {A B C : Type'} (P : type443 A B C) : term91 A B C P.
Proof. exact (conj (@lem52817 A B C P) (@lem53010 A B C P)). Qed.
Lemma lem53012 {A B C : Type'} (P : type443 A B C) : (term91 A B C P) = ((term6 A B C P) = (term7 A B C P)).
Proof. exact (@lem32 (term6 A B C P) (term7 A B C P)). Qed.
Lemma lem53013 {A B C : Type'} (P : type443 A B C) : (term6 A B C P) = (term7 A B C P).
Proof. exact (EQ_MP (@lem53012 A B C P) (@lem53011 A B C P)). Qed.
Lemma lem53018 {A B C : Type'} : term92 A B C.
Proof. exact (fun P : type443 A B C => @lem53013 A B C P). Qed.
