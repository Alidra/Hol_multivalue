Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_DIFF_INJ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3373799 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3373800 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3373801 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3373800 t1) (@lem3373799 t1)). Qed.
Lemma lem3373802 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3373801 t1 t2). Qed.
Lemma lem3373803 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3373804 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3373803 t1 t2) (@lem3373802 t1 t2)). Qed.
Lemma lem3373805 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3373804 t1 t2 t3). Qed.
Lemma lem3373806 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3373807 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3373806 t1 t2 t3) (@lem3373805 t1 t2 t3)). Qed.
Lemma lem3373808 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3373807 t1 t2 t3)). Qed.
Lemma lem3373848 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3373849 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term7 B s t).
Proof. exact (@lem3373848 B s t). Qed.
Lemma lem3373850 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term8 A B f s t) = (term9 A B s f t)) = (term10 A B s f t).
Proof. exact (@lem3373849 B (term8 A B f s t) (term9 A B s f t)). Qed.
Lemma lem3373859 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term11 A B s t f) = (term11 A B s t f).
Proof. exact (eq_refl (term11 A B s t f)). Qed.
Lemma lem3373860 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term12 A B s f t) = (term13 A B s f t).
Proof. exact (MK_COMB (@lem3373859 A B s t f) (@lem3373850 A B s f t)). Qed.
Lemma lem3373863 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B s f) = (term15 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3373860 A B s f t)). Qed.
Lemma lem3373864 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3373865 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term16 A B s f) = (term17 A B s f).
Proof. exact (MK_COMB (@lem3373864 A) (@lem3373863 A B s f)). Qed.
Lemma lem3373870 {A B : Type'} (f : A -> B) : (term18 A B f) = (term19 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3373865 A B s f)). Qed.
Lemma lem3373871 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3373872 {A B : Type'} (f : A -> B) : (term20 A B f) = (term21 A B f).
Proof. exact (MK_COMB (@lem3373871 A) (@lem3373870 A B f)). Qed.
Lemma lem3373877 {A B : Type'} : (term22 A B) = (term23 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3373872 A B f)). Qed.
Lemma lem3373878 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3373879 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem3373878 A B) (@lem3373877 A B)). Qed.
Lemma lem3373884 {A B : Type'} : (term25 A B) = (term24 A B).
Proof. exact (SYM (@lem3373879 A B)). Qed.
Lemma lem3373912 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3373913 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3373912 A P x). Qed.
Lemma lem3373914 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3373913 A s x). Qed.
Lemma lem3373915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3373916 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3373915) (@lem3373914 A s x)). Qed.
Lemma lem3373920 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3373921 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3373920 A P x). Qed.
Lemma lem3373922 {A : Type'} (t : A -> Prop) (y : A) : (@IN A y t) = (t y).
Proof. exact (@lem3373921 A t y). Qed.
Lemma lem3373923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3373924 {A : Type'} (t : A -> Prop) (y : A) : (term26 A y t) = (term27 A t y).
Proof. exact (MK_COMB (@lem3373923) (@lem3373922 A t y)). Qed.
Lemma lem3373927 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3373928 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term28 A B t x f y) = (term29 A B t x f y).
Proof. exact (MK_COMB (@lem3373924 A t y) (@lem3373927 A B x f y)). Qed.
Lemma lem3373931 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term30 A B s t x f y) = (term31 A B s t x f y).
Proof. exact (MK_COMB (@lem3373916 A s x) (@lem3373928 A B t x f y)). Qed.
Lemma lem3373934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3373935 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term32 A B s t x f y) = (term33 A B s t x f y).
Proof. exact (MK_COMB (@lem3373934) (@lem3373931 A B s t x f y)). Qed.
Lemma lem3373938 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3373939 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (y : A) : (term34 A B s t f x y) = (term35 A B s t f x y).
Proof. exact (MK_COMB (@lem3373935 A B s t x f y) (@lem3373938 A x y)). Qed.
Lemma lem3373942 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term36 A B s t f x) = (term37 A B s t f x).
Proof. exact (fun_ext (fun y : A => @lem3373939 A B s t f x y)). Qed.
Lemma lem3373943 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3373944 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term38 A B s t f x) = (term39 A B s t f x).
Proof. exact (MK_COMB (@lem3373943 A) (@lem3373942 A B s t f x)). Qed.
Lemma lem3373949 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term40 A B s t f) = (term41 A B s t f).
Proof. exact (fun_ext (fun x : A => @lem3373944 A B s t f x)). Qed.
Lemma lem3373950 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3373951 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term42 A B s t f) = (term43 A B s t f).
Proof. exact (MK_COMB (@lem3373950 A) (@lem3373949 A B s t f)). Qed.
Lemma lem3373956 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3373957 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term11 A B s t f) = (term44 A B s t f).
Proof. exact (MK_COMB (@lem3373956) (@lem3373951 A B s t f)). Qed.
Lemma lem3373965 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y f s) = (term46 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3373966 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y f s) = (term46 A B y f s).
Proof. exact (@lem3373965 A B y f s). Qed.
Lemma lem3373967 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term47 A B x f s t) = (term48 A B x f s t).
Proof. exact (@lem3373966 A B x f (@DIFF A s t)). Qed.
Lemma lem3373977 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term49 A x s t) = (term50 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3373978 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term49 A x s t) = (term50 A s x t).
Proof. exact (@lem3373977 A s x t). Qed.
Lemma lem3373982 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3373983 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3373982 A P x). Qed.
Lemma lem3373984 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3373983 A s x). Qed.
Lemma lem3373985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3373986 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3373985) (@lem3373984 A s x)). Qed.
Lemma lem3373988 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3373989 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3373988 A P x). Qed.
Lemma lem3373990 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3373989 A t x). Qed.
Lemma lem3373991 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3373992 {A : Type'} (t : A -> Prop) (x : A) : (term51 A x t) = (term52 A t x).
Proof. exact (MK_COMB (@lem3373991) (@lem3373990 A t x)). Qed.
Lemma lem3373993 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term50 A s x t) = (term53 A s t x).
Proof. exact (MK_COMB (@lem3373986 A s x) (@lem3373992 A t x)). Qed.
Lemma lem3373996 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term49 A x s t) = (term53 A s t x).
Proof. exact (TRANS (@lem3373978 A s x t) (@lem3373993 A s t x)). Qed.
Lemma lem3373997 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term54 A B x f x') = (term54 A B x f x').
Proof. exact (eq_refl (term54 A B x f x')). Qed.
Lemma lem3373998 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term55 A B x f x' s t) = (term56 A B x f s t x').
Proof. exact (MK_COMB (@lem3373997 A B x f x') (@lem3373996 A s t x')). Qed.
Lemma lem3374001 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term57 A B x f s t) = (term58 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3373998 A B x f s t x')). Qed.
Lemma lem3374002 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374003 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term48 A B x f s t) = (term59 A B x f s t).
Proof. exact (MK_COMB (@lem3374002 A) (@lem3374001 A B x f s t)). Qed.
Lemma lem3374008 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term47 A B x f s t) = (term59 A B x f s t).
Proof. exact (TRANS (@lem3373967 A B x f s t) (@lem3374003 A B x f s t)). Qed.
Lemma lem3374009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3374010 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term60 A B x f s t) = (term61 A B x f s t).
Proof. exact (MK_COMB (@lem3374009) (@lem3374008 A B x f s t)). Qed.
Lemma lem3374012 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term49 A x s t) = (term50 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3374013 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term49 B x s t) = (term50 B s x t).
Proof. exact (@lem3374012 B s x t). Qed.
Lemma lem3374014 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term62 A B x s f t) = (term63 A B s x f t).
Proof. exact (@lem3374013 B (@IMAGE A B f s) x (@IMAGE A B f t)). Qed.
Lemma lem3374018 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y f s) = (term46 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3374019 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y f s) = (term46 A B y f s).
Proof. exact (@lem3374018 A B y f s). Qed.
Lemma lem3374020 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term45 A B x f s) = (term46 A B x f s).
Proof. exact (@lem3374019 A B x f s). Qed.
Lemma lem3374030 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3374031 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3374030 A P x). Qed.
Lemma lem3374032 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3374031 A s x). Qed.
Lemma lem3374033 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term54 A B x f x') = (term54 A B x f x').
Proof. exact (eq_refl (term54 A B x f x')). Qed.
Lemma lem3374034 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term64 A B x f x' s) = (term65 A B x f s x').
Proof. exact (MK_COMB (@lem3374033 A B x f x') (@lem3374032 A s x')). Qed.
Lemma lem3374037 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term66 A B x f s) = (term67 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3374034 A B x f s x')). Qed.
Lemma lem3374038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374039 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term46 A B x f s) = (term68 A B x f s).
Proof. exact (MK_COMB (@lem3374038 A) (@lem3374037 A B x f s)). Qed.
Lemma lem3374044 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term45 A B x f s) = (term68 A B x f s).
Proof. exact (TRANS (@lem3374020 A B x f s) (@lem3374039 A B x f s)). Qed.
Lemma lem3374045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374046 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term69 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3374045) (@lem3374044 A B x f s)). Qed.
Lemma lem3374048 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y f s) = (term46 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3374049 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term45 A B y f s) = (term46 A B y f s).
Proof. exact (@lem3374048 A B y f s). Qed.
Lemma lem3374050 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term45 A B x f t) = (term46 A B x f t).
Proof. exact (@lem3374049 A B x f t). Qed.
Lemma lem3374060 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3374061 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3374060 A P x). Qed.
Lemma lem3374062 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3374061 A t x). Qed.
Lemma lem3374063 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term54 A B x f x') = (term54 A B x f x').
Proof. exact (eq_refl (term54 A B x f x')). Qed.
Lemma lem3374064 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term64 A B x f x' t) = (term65 A B x f t x').
Proof. exact (MK_COMB (@lem3374063 A B x f x') (@lem3374062 A t x')). Qed.
Lemma lem3374067 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term66 A B x f t) = (term67 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374064 A B x f t x')). Qed.
Lemma lem3374068 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374069 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term46 A B x f t) = (term68 A B x f t).
Proof. exact (MK_COMB (@lem3374068 A) (@lem3374067 A B x f t)). Qed.
Lemma lem3374074 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term45 A B x f t) = (term68 A B x f t).
Proof. exact (TRANS (@lem3374050 A B x f t) (@lem3374069 A B x f t)). Qed.
Lemma lem3374075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3374076 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term71 A B x f t) = (term72 A B x f t).
Proof. exact (MK_COMB (@lem3374075) (@lem3374074 A B x f t)). Qed.
Lemma lem3374077 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term63 A B s x f t) = (term73 A B s x f t).
Proof. exact (MK_COMB (@lem3374046 A B x f s) (@lem3374076 A B x f t)). Qed.
Lemma lem3374080 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term62 A B x s f t) = (term73 A B s x f t).
Proof. exact (TRANS (@lem3374014 A B s x f t) (@lem3374077 A B s x f t)). Qed.
Lemma lem3374081 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term47 A B x f s t) = (term62 A B x s f t)) = ((term59 A B x f s t) = (term73 A B s x f t)).
Proof. exact (MK_COMB (@lem3374010 A B x f s t) (@lem3374080 A B s x f t)). Qed.
Lemma lem3374084 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term74 A B s f t) = (term75 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3374081 A B s x f t)). Qed.
Lemma lem3374085 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3374086 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term10 A B s f t) = (term76 A B s f t).
Proof. exact (MK_COMB (@lem3374085 B) (@lem3374084 A B s f t)). Qed.
Lemma lem3374091 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term13 A B s f t) = (term77 A B s f t).
Proof. exact (MK_COMB (@lem3373957 A B s t f) (@lem3374086 A B s f t)). Qed.
Lemma lem3374094 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term15 A B s f) = (term78 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3374091 A B s f t)). Qed.
Lemma lem3374095 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3374096 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term17 A B s f) = (term79 A B s f).
Proof. exact (MK_COMB (@lem3374095 A) (@lem3374094 A B s f)). Qed.
Lemma lem3374101 {A B : Type'} (f : A -> B) : (term19 A B f) = (term80 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3374096 A B s f)). Qed.
Lemma lem3374102 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3374103 {A B : Type'} (f : A -> B) : (term21 A B f) = (term81 A B f).
Proof. exact (MK_COMB (@lem3374102 A) (@lem3374101 A B f)). Qed.
Lemma lem3374108 {A B : Type'} : (term23 A B) = (term82 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3374103 A B f)). Qed.
Lemma lem3374109 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3374110 {A B : Type'} : (term25 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem3374109 A B) (@lem3374108 A B)). Qed.
Lemma lem3374115 {A B : Type'} : (term83 A B) = (term25 A B).
Proof. exact (SYM (@lem3374110 A B)). Qed.
Lemma lem3374117 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3374118 {A B : Type'} : (term83 A B) = (term85 A B).
Proof. exact (@lem3374117 (term83 A B)). Qed.
Lemma lem3374119 {A B : Type'} : (term85 A B) = (term83 A B).
Proof. exact (SYM (@lem3374118 A B)). Qed.
Lemma lem3374120 {A B : Type'} (h1 : term86 A B) : term86 A B.
Proof. exact (h1). Qed.
Lemma lem3374123 {A B : Type'} (h1 : term85 A B) : term85 A B.
Proof. exact (h1). Qed.
Lemma lem3374124 {A B : Type'} : term87 A B.
Proof. exact (fun h0 : term85 A B => @lem3374123 A B h0). Qed.
Lemma lem3374125 {A B : Type'} (h1 : term87 A B) : term87 A B.
Proof. exact (h1). Qed.
Lemma lem3374126 {A B : Type'} (h1 : term85 A B) : term85 A B.
Proof. exact (h1). Qed.
Lemma lem3374127 {A B : Type'} (h1 : term85 A B) (h2 : term87 A B) : term85 A B.
Proof. exact (@lem3374125 A B h2 (@lem3374126 A B h1)). Qed.
Lemma lem3374128 {A B : Type'} (h1 : term85 A B) : term88 A B.
Proof. exact (fun h0 : term87 A B => @lem3374127 A B h1 h0). Qed.
Lemma lem3374129 {A B : Type'} (h1 : term87 A B) : term87 A B.
Proof. exact (h1). Qed.
Lemma lem3374130 {A B : Type'} (h1 : term85 A B) (h2 : term87 A B) : term85 A B.
Proof. exact (@lem3374128 A B h1 (@lem3374129 A B h2)). Qed.
Lemma lem3374131 {A B : Type'} (h1 : term87 A B) : term87 A B.
Proof. exact (fun h0 : term85 A B => @lem3374130 A B h0 h1). Qed.
Lemma lem3374132 {A B : Type'} : term89 A B.
Proof. exact (fun h0 : term87 A B => @lem3374131 A B h0). Qed.
Lemma lem3374135 {A B : Type'} : term87 A B.
Proof. exact (@lem3374132 A B (@lem3374124 A B)). Qed.
Lemma lem3374136 {A B : Type'} : term87 A B.
Proof. exact (@lem3374135 A B). Qed.
Lemma lem3374138 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3374139 {A B : Type'} : (term85 A B) = (term90 A B).
Proof. exact (@lem3374138 (term86 A B)). Qed.
Lemma lem3374141 (t : Prop) : (term91 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3374142 {A B : Type'} : (term90 A B) = (term83 A B).
Proof. exact (@lem3374141 (term83 A B)). Qed.
Lemma lem3374301 {A B : Type'} : (term85 A B) = (term83 A B).
Proof. exact (TRANS (@lem3374139 A B) (@lem3374142 A B)). Qed.
Lemma lem3374306 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term65 A B x f t x') = (term65 A B x f t x').
Proof. exact (eq_refl (term65 A B x f t x')). Qed.
Lemma lem3374307 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term67 A B x f t) = (term67 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374306 A B x f t x')). Qed.
Lemma lem3374308 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374309 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term68 A B x f t) = (term68 A B x f t).
Proof. exact (MK_COMB (@lem3374308 A) (@lem3374307 A B x f t)). Qed.
Lemma lem3374310 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3374311 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term72 A B x f t) = (term72 A B x f t).
Proof. exact (MK_COMB (@lem3374310) (@lem3374309 A B x f t)). Qed.
Lemma lem3374316 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term65 A B x f s x') = (term65 A B x f s x').
Proof. exact (eq_refl (term65 A B x f s x')). Qed.
Lemma lem3374317 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term67 A B x f s) = (term67 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3374316 A B x f s x')). Qed.
Lemma lem3374318 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374319 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term68 A B x f s) = (term68 A B x f s).
Proof. exact (MK_COMB (@lem3374318 A) (@lem3374317 A B x f s)). Qed.
Lemma lem3374320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374321 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3374320) (@lem3374319 A B x f s)). Qed.
Lemma lem3374322 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term73 A B s x f t) = (term73 A B s x f t).
Proof. exact (MK_COMB (@lem3374321 A B x f s) (@lem3374311 A B x f t)). Qed.
Lemma lem3374333 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term56 A B x f s t x') = (term56 A B x f s t x').
Proof. exact (eq_refl (term56 A B x f s t x')). Qed.
Lemma lem3374334 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term58 A B x f s t) = (term58 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3374333 A B x f s t x')). Qed.
Lemma lem3374335 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374336 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term59 A B x f s t) = (term59 A B x f s t).
Proof. exact (MK_COMB (@lem3374335 A) (@lem3374334 A B x f s t)). Qed.
Lemma lem3374337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3374338 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term61 A B x f s t) = (term61 A B x f s t).
Proof. exact (MK_COMB (@lem3374337) (@lem3374336 A B x f s t)). Qed.
Lemma lem3374339 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term59 A B x f s t) = (term73 A B s x f t)) = ((term59 A B x f s t) = (term73 A B s x f t)).
Proof. exact (MK_COMB (@lem3374338 A B x f s t) (@lem3374322 A B s x f t)). Qed.
Lemma lem3374340 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term75 A B s f t) = (term75 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem3374339 A B s x f t)). Qed.
Lemma lem3374341 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3374342 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term76 A B s f t) = (term76 A B s f t).
Proof. exact (MK_COMB (@lem3374341 B) (@lem3374340 A B s f t)). Qed.
Lemma lem3374355 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (y : A) : (term35 A B s t f x y) = (term35 A B s t f x y).
Proof. exact (eq_refl (term35 A B s t f x y)). Qed.
Lemma lem3374356 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term37 A B s t f x) = (term37 A B s t f x).
Proof. exact (fun_ext (fun y : A => @lem3374355 A B s t f x y)). Qed.
Lemma lem3374357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3374358 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term39 A B s t f x) = (term39 A B s t f x).
Proof. exact (MK_COMB (@lem3374357 A) (@lem3374356 A B s t f x)). Qed.
Lemma lem3374359 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term41 A B s t f) = (term41 A B s t f).
Proof. exact (fun_ext (fun x : A => @lem3374358 A B s t f x)). Qed.
Lemma lem3374360 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3374361 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term43 A B s t f) = (term43 A B s t f).
Proof. exact (MK_COMB (@lem3374360 A) (@lem3374359 A B s t f)). Qed.
Lemma lem3374362 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3374363 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term44 A B s t f) = (term44 A B s t f).
Proof. exact (MK_COMB (@lem3374362) (@lem3374361 A B s t f)). Qed.
Lemma lem3374364 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term77 A B s f t) = (term77 A B s f t).
Proof. exact (MK_COMB (@lem3374363 A B s t f) (@lem3374342 A B s f t)). Qed.
Lemma lem3374365 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term78 A B s f) = (term78 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3374364 A B s f t)). Qed.
Lemma lem3374366 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3374367 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term79 A B s f) = (term79 A B s f).
Proof. exact (MK_COMB (@lem3374366 A) (@lem3374365 A B s f)). Qed.
Lemma lem3374368 {A B : Type'} (f : A -> B) : (term80 A B f) = (term80 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3374367 A B s f)). Qed.
Lemma lem3374369 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3374370 {A B : Type'} (f : A -> B) : (term81 A B f) = (term81 A B f).
Proof. exact (MK_COMB (@lem3374369 A) (@lem3374368 A B f)). Qed.
Lemma lem3374371 {A B : Type'} : (term82 A B) = (term82 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3374370 A B f)). Qed.
Lemma lem3374372 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3374373 {A B : Type'} : (term83 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem3374372 A B) (@lem3374371 A B)). Qed.
Lemma lem3374448 {A B : Type'} : (term85 A B) = (term83 A B).
Proof. exact (TRANS (@lem3374301 A B) (@lem3374373 A B)). Qed.
Lemma lem3374449 {A B : Type'} : (term83 A B) = (term85 A B).
Proof. exact (SYM (@lem3374448 A B)). Qed.
Lemma lem3374450 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term43 A B s t f.
Proof. exact (h1). Qed.
Lemma lem3374452 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3374453 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term59 A B x f s t) = (term73 A B s x f t)) = (term92 A B s x f t).
Proof. exact (@lem3374452 ((term59 A B x f s t) = (term73 A B s x f t))). Qed.
Lemma lem3374454 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term92 A B s x f t) = ((term59 A B x f s t) = (term73 A B s x f t)).
Proof. exact (SYM (@lem3374453 A B s x f t)). Qed.
Lemma lem3374455 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term93 A B s x f t) : term93 A B s x f t.
Proof. exact (h1). Qed.
Lemma lem3374463 {A B : Type'} (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term94 A B t x f y) = (term95 A B t x f y).
Proof. exact (@lem17045 (t y) ((f x) = (f y))). Qed.
Lemma lem3374465 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term96 A s x).
Proof. exact (eq_refl (term96 A s x)). Qed.
Lemma lem3374466 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term97 A B s t x f y) = (term98 A B s t x f y).
Proof. exact (MK_COMB (@lem3374465 A s x) (@lem3374463 A B t x f y)). Qed.
Lemma lem3374467 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term99 A B s t x f y) = (term97 A B s t x f y).
Proof. exact (@lem17045 (s x) (term29 A B t x f y)). Qed.
Lemma lem3374468 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term99 A B s t x f y) = (term98 A B s t x f y).
Proof. exact (TRANS (@lem3374467 A B s t x f y) (@lem3374466 A B s t x f y)). Qed.
Lemma lem3374469 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3374470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3374471 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : A -> B) (y : A) : (term100 A B s t x f y) = (term101 A B s t x f y).
Proof. exact (MK_COMB (@lem3374470) (@lem3374468 A B s t x f y)). Qed.
Lemma lem3374472 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (y : A) : (term102 A B s t f x y) = (term103 A B s t f x y).
Proof. exact (MK_COMB (@lem3374471 A B s t x f y) (@lem3374469 A x y)). Qed.
Lemma lem3374473 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (y : A) : (term35 A B s t f x y) = (term102 A B s t f x y).
Proof. exact (@lem17265 (term31 A B s t x f y) (x = y)). Qed.
Lemma lem3374474 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (y : A) : (term35 A B s t f x y) = (term103 A B s t f x y).
Proof. exact (TRANS (@lem3374473 A B s t f x y) (@lem3374472 A B s t f x y)). Qed.
Lemma lem3374475 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term37 A B s t f x) = (term104 A B s t f x).
Proof. exact (fun_ext (fun y : A => @lem3374474 A B s t f x y)). Qed.
Lemma lem3374476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3374477 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term39 A B s t f x) = (term105 A B s t f x).
Proof. exact (MK_COMB (@lem3374476 A) (@lem3374475 A B s t f x)). Qed.
Lemma lem3374478 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term41 A B s t f) = (term106 A B s t f).
Proof. exact (fun_ext (fun x : A => @lem3374477 A B s t f x)). Qed.
Lemma lem3374479 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3374536 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term43 A B s t f) = (term107 A B s t f).
Proof. exact (MK_COMB (@lem3374479 A) (@lem3374478 A B s t f)). Qed.
Lemma lem3374537 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term107 A B s t f.
Proof. exact (EQ_MP (@lem3374536 A B s t f) (@lem3374450 A B s t f h1)). Qed.
Lemma lem3374545 {A : Type'} (t : A -> Prop) (x : A) : (term108 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3374547 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term96 A s x).
Proof. exact (eq_refl (term96 A s x)). Qed.
Lemma lem3374548 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term109 A s t x) = (term110 A s t x).
Proof. exact (MK_COMB (@lem3374547 A s x) (@lem3374545 A t x)). Qed.
Lemma lem3374549 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term111 A s t x) = (term109 A s t x).
Proof. exact (@lem17045 (s x) (term52 A t x)). Qed.
Lemma lem3374550 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term111 A s t x) = (term110 A s t x).
Proof. exact (TRANS (@lem3374549 A s t x) (@lem3374548 A s t x)). Qed.
Lemma lem3374555 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term112 A B x f x') = (term112 A B x f x').
Proof. exact (eq_refl (term112 A B x f x')). Qed.
Lemma lem3374556 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term113 A B x f s t x') = (term114 A B x f s t x').
Proof. exact (MK_COMB (@lem3374555 A B x f x') (@lem3374550 A s t x')). Qed.
Lemma lem3374557 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term115 A B x f s t x') = (term113 A B x f s t x').
Proof. exact (@lem17045 (x = (f x')) (term53 A s t x')). Qed.
Lemma lem3374558 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term115 A B x f s t x') = (term114 A B x f s t x').
Proof. exact (TRANS (@lem3374557 A B x f s t x') (@lem3374556 A B x f s t x')). Qed.
Lemma lem3374561 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term56 A B x f s t x') = (term56 A B x f s t x').
Proof. exact (eq_refl (term56 A B x f s t x')). Qed.
Lemma lem3374562 {A : Type'} (P : A -> Prop) : (term116 A P) = (term117 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3374563 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term118 A B x f s t) = (term119 A B x f s t).
Proof. exact (@lem3374562 A (term58 A B x f s t)). Qed.
Lemma lem3374564 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term120 A B x f s t x') = (term56 A B x f s t x').
Proof. exact (eq_refl (term120 A B x f s t x')). Qed.
Lemma lem3374565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3374566 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term121 A B x f s t x') = (term115 A B x f s t x').
Proof. exact (MK_COMB (@lem3374565) (@lem3374564 A B x f s t x')). Qed.
Lemma lem3374567 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term121 A B x f s t x') = (term114 A B x f s t x').
Proof. exact (TRANS (@lem3374566 A B x f s t x') (@lem3374558 A B x f s t x')). Qed.
Lemma lem3374568 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term122 A B x f s t) = (term123 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3374567 A B x f s t x')). Qed.
Lemma lem3374569 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3374570 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term119 A B x f s t) = (term124 A B x f s t).
Proof. exact (MK_COMB (@lem3374569 A) (@lem3374568 A B x f s t)). Qed.
Lemma lem3374571 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term118 A B x f s t) = (term124 A B x f s t).
Proof. exact (TRANS (@lem3374563 A B x f s t) (@lem3374570 A B x f s t)). Qed.
Lemma lem3374572 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term58 A B x f s t) = (term58 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3374561 A B x f s t x')). Qed.
Lemma lem3374573 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374574 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term59 A B x f s t) = (term59 A B x f s t).
Proof. exact (MK_COMB (@lem3374573 A) (@lem3374572 A B x f s t)). Qed.
Lemma lem3374583 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term125 A B x f s x') = (term126 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3374586 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term65 A B x f s x') = (term65 A B x f s x').
Proof. exact (eq_refl (term65 A B x f s x')). Qed.
Lemma lem3374587 {A : Type'} (P : A -> Prop) : (term116 A P) = (term117 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3374588 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term72 A B x f s) = (term127 A B x f s).
Proof. exact (@lem3374587 A (term67 A B x f s)). Qed.
Lemma lem3374589 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term65 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem3374590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3374591 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term129 A B x f s x') = (term125 A B x f s x').
Proof. exact (MK_COMB (@lem3374590) (@lem3374589 A B x f s x')). Qed.
Lemma lem3374592 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term129 A B x f s x') = (term126 A B x f s x').
Proof. exact (TRANS (@lem3374591 A B x f s x') (@lem3374583 A B x f s x')). Qed.
Lemma lem3374593 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term130 A B x f s) = (term131 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3374592 A B x f s x')). Qed.
Lemma lem3374594 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3374595 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term127 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem3374594 A) (@lem3374593 A B x f s)). Qed.
Lemma lem3374596 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term72 A B x f s) = (term132 A B x f s).
Proof. exact (TRANS (@lem3374588 A B x f s) (@lem3374595 A B x f s)). Qed.
Lemma lem3374597 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term67 A B x f s) = (term67 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3374586 A B x f s x')). Qed.
Lemma lem3374598 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374599 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term68 A B x f s) = (term68 A B x f s).
Proof. exact (MK_COMB (@lem3374598 A) (@lem3374597 A B x f s)). Qed.
Lemma lem3374608 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term125 A B x f t x') = (term126 A B x f t x').
Proof. exact (@lem17045 (x = (f x')) (t x')). Qed.
Lemma lem3374611 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term65 A B x f t x') = (term65 A B x f t x').
Proof. exact (eq_refl (term65 A B x f t x')). Qed.
Lemma lem3374612 {A : Type'} (P : A -> Prop) : (term116 A P) = (term117 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3374613 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term72 A B x f t) = (term127 A B x f t).
Proof. exact (@lem3374612 A (term67 A B x f t)). Qed.
Lemma lem3374614 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term128 A B x f t x') = (term65 A B x f t x').
Proof. exact (eq_refl (term128 A B x f t x')). Qed.
Lemma lem3374615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3374616 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term129 A B x f t x') = (term125 A B x f t x').
Proof. exact (MK_COMB (@lem3374615) (@lem3374614 A B x f t x')). Qed.
Lemma lem3374617 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term129 A B x f t x') = (term126 A B x f t x').
Proof. exact (TRANS (@lem3374616 A B x f t x') (@lem3374608 A B x f t x')). Qed.
Lemma lem3374618 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term130 A B x f t) = (term131 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374617 A B x f t x')). Qed.
Lemma lem3374619 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3374620 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term127 A B x f t) = (term132 A B x f t).
Proof. exact (MK_COMB (@lem3374619 A) (@lem3374618 A B x f t)). Qed.
Lemma lem3374621 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term72 A B x f t) = (term132 A B x f t).
Proof. exact (TRANS (@lem3374613 A B x f t) (@lem3374620 A B x f t)). Qed.
Lemma lem3374622 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term67 A B x f t) = (term67 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374611 A B x f t x')). Qed.
Lemma lem3374623 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374624 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term68 A B x f t) = (term68 A B x f t).
Proof. exact (MK_COMB (@lem3374623 A) (@lem3374622 A B x f t)). Qed.
Lemma lem3374625 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term133 A B x f t) = (term68 A B x f t).
Proof. exact (@lem16933 (term68 A B x f t)). Qed.
Lemma lem3374626 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term133 A B x f t) = (term68 A B x f t).
Proof. exact (TRANS (@lem3374625 A B x f t) (@lem3374624 A B x f t)). Qed.
Lemma lem3374627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3374628 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term134 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem3374627) (@lem3374596 A B x f s)). Qed.
Lemma lem3374629 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term136 A B s x f t) = (term137 A B s x f t).
Proof. exact (MK_COMB (@lem3374628 A B x f s) (@lem3374626 A B x f t)). Qed.
Lemma lem3374630 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term138 A B s x f t) = (term136 A B s x f t).
Proof. exact (@lem17045 (term68 A B x f s) (term72 A B x f t)). Qed.
Lemma lem3374631 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term138 A B s x f t) = (term137 A B s x f t).
Proof. exact (TRANS (@lem3374630 A B s x f t) (@lem3374629 A B s x f t)). Qed.
Lemma lem3374632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374633 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term70 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3374632) (@lem3374599 A B x f s)). Qed.
Lemma lem3374634 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term73 A B s x f t) = (term139 A B s x f t).
Proof. exact (MK_COMB (@lem3374633 A B x f s) (@lem3374621 A B x f t)). Qed.
Lemma lem3374635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374636 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term140 A B x f s t) = (term141 A B x f s t).
Proof. exact (MK_COMB (@lem3374635) (@lem3374571 A B x f s t)). Qed.
Lemma lem3374637 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term142 A B s x f t) = (term143 A B s x f t).
Proof. exact (MK_COMB (@lem3374636 A B x f s t) (@lem3374634 A B s x f t)). Qed.
Lemma lem3374638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374639 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term144 A B x f s t) = (term144 A B x f s t).
Proof. exact (MK_COMB (@lem3374638) (@lem3374574 A B x f s t)). Qed.
Lemma lem3374640 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term145 A B s x f t) = (term146 A B s x f t).
Proof. exact (MK_COMB (@lem3374639 A B x f s t) (@lem3374631 A B s x f t)). Qed.
Lemma lem3374641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3374642 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term147 A B s x f t) = (term148 A B s x f t).
Proof. exact (MK_COMB (@lem3374641) (@lem3374640 A B s x f t)). Qed.
Lemma lem3374643 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term149 A B s x f t) = (term150 A B s x f t).
Proof. exact (MK_COMB (@lem3374642 A B s x f t) (@lem3374637 A B s x f t)). Qed.
Lemma lem3374644 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term93 A B s x f t) = (term149 A B s x f t).
Proof. exact (@lem17646 (term59 A B x f s t) (term73 A B s x f t)). Qed.
Lemma lem3374645 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term93 A B s x f t) = (term150 A B s x f t).
Proof. exact (TRANS (@lem3374644 A B s x f t) (@lem3374643 A B s x f t)). Qed.
Lemma lem3374904 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3374905 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem3374904 A P Q). Qed.
Lemma lem3374906 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term153 A B s x f t) = (term154 A B s x f t).
Proof. exact (@lem3374905 A (term132 A B x f s) (term67 A B x f t)). Qed.
Lemma lem3374907 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term128 A B x f t x') = (term65 A B x f t x').
Proof. exact (eq_refl (term128 A B x f t x')). Qed.
Lemma lem3374908 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term155 A B x f t) = (term67 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374907 A B x f t x')). Qed.
Lemma lem3374909 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374910 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term156 A B x f t) = (term68 A B x f t).
Proof. exact (MK_COMB (@lem3374909 A) (@lem3374908 A B x f t)). Qed.
Lemma lem3374911 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term135 A B x f s) = (term135 A B x f s).
Proof. exact (eq_refl (term135 A B x f s)). Qed.
Lemma lem3374912 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term153 A B s x f t) = (term137 A B s x f t).
Proof. exact (MK_COMB (@lem3374911 A B x f s) (@lem3374910 A B x f t)). Qed.
Lemma lem3374913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3374914 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term157 A B s x f t) = (term158 A B s x f t).
Proof. exact (MK_COMB (@lem3374913) (@lem3374912 A B s x f t)). Qed.
Lemma lem3374915 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term128 A B x f t x') = (term65 A B x f t x').
Proof. exact (eq_refl (term128 A B x f t x')). Qed.
Lemma lem3374916 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term135 A B x f s) = (term135 A B x f s).
Proof. exact (eq_refl (term135 A B x f s)). Qed.
Lemma lem3374917 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term159 A B s x f t x') = (term160 A B s x f t x').
Proof. exact (MK_COMB (@lem3374916 A B x f s) (@lem3374915 A B x f t x')). Qed.
Lemma lem3374918 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term161 A B s x f t) = (term162 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374917 A B s x f t x')). Qed.
Lemma lem3374919 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374920 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term154 A B s x f t) = (term163 A B s x f t).
Proof. exact (MK_COMB (@lem3374919 A) (@lem3374918 A B s x f t)). Qed.
Lemma lem3374921 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term153 A B s x f t) = (term154 A B s x f t)) = ((term137 A B s x f t) = (term163 A B s x f t)).
Proof. exact (MK_COMB (@lem3374914 A B s x f t) (@lem3374920 A B s x f t)). Qed.
Lemma lem3374922 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term137 A B s x f t) = (term163 A B s x f t).
Proof. exact (EQ_MP (@lem3374921 A B s x f t) (@lem3374906 A B s x f t)). Qed.
Lemma lem3374923 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term144 A B x f s t) = (term144 A B x f s t).
Proof. exact (eq_refl (term144 A B x f s t)). Qed.
Lemma lem3374924 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term146 A B s x f t) = (term164 A B s x f t).
Proof. exact (MK_COMB (@lem3374923 A B x f s t) (@lem3374922 A B s x f t)). Qed.
Lemma lem3374926 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3374927 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (@lem3374926 A P Q). Qed.
Lemma lem3374928 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term167 A B s x f t) = (term168 A B s x f t).
Proof. exact (@lem3374927 A (term58 A B x f s t) (term163 A B s x f t)). Qed.
Lemma lem3374929 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term120 A B x f s t x') = (term56 A B x f s t x').
Proof. exact (eq_refl (term120 A B x f s t x')). Qed.
Lemma lem3374930 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term169 A B x f s t) = (term58 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3374929 A B x f s t x')). Qed.
Lemma lem3374931 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374932 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term170 A B x f s t) = (term59 A B x f s t).
Proof. exact (MK_COMB (@lem3374931 A) (@lem3374930 A B x f s t)). Qed.
Lemma lem3374933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374934 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term171 A B x f s t) = (term144 A B x f s t).
Proof. exact (MK_COMB (@lem3374933) (@lem3374932 A B x f s t)). Qed.
Lemma lem3374935 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term163 A B s x f t) = (term163 A B s x f t).
Proof. exact (eq_refl (term163 A B s x f t)). Qed.
Lemma lem3374936 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term167 A B s x f t) = (term164 A B s x f t).
Proof. exact (MK_COMB (@lem3374934 A B x f s t) (@lem3374935 A B s x f t)). Qed.
Lemma lem3374937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3374938 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term172 A B s x f t) = (term173 A B s x f t).
Proof. exact (MK_COMB (@lem3374937) (@lem3374936 A B s x f t)). Qed.
Lemma lem3374939 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term120 A B x f s t x') = (term56 A B x f s t x').
Proof. exact (eq_refl (term120 A B x f s t x')). Qed.
Lemma lem3374940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374941 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term174 A B x f s t x') = (term175 A B x f s t x').
Proof. exact (MK_COMB (@lem3374940) (@lem3374939 A B x f s t x')). Qed.
Lemma lem3374942 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term163 A B s x f t) = (term163 A B s x f t).
Proof. exact (eq_refl (term163 A B s x f t)). Qed.
Lemma lem3374943 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term176 A B x s x' f t) = (term177 A B x s x' f t).
Proof. exact (MK_COMB (@lem3374941 A B x' f s t x) (@lem3374942 A B s x' f t)). Qed.
Lemma lem3374944 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term178 A B s x f t) = (term179 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374943 A B x' s x f t)). Qed.
Lemma lem3374945 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374946 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term168 A B s x f t) = (term180 A B s x f t).
Proof. exact (MK_COMB (@lem3374945 A) (@lem3374944 A B s x f t)). Qed.
Lemma lem3374947 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term167 A B s x f t) = (term168 A B s x f t)) = ((term164 A B s x f t) = (term180 A B s x f t)).
Proof. exact (MK_COMB (@lem3374938 A B s x f t) (@lem3374946 A B s x f t)). Qed.
Lemma lem3374948 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term164 A B s x f t) = (term180 A B s x f t).
Proof. exact (EQ_MP (@lem3374947 A B s x f t) (@lem3374928 A B s x f t)). Qed.
Lemma lem3374950 {A : Type'} (P : Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3374951 {A : Type'} (P : Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (@lem3374950 A P Q). Qed.
Lemma lem3374952 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term183 A B x s x' f t) = (term184 A B x s x' f t).
Proof. exact (@lem3374951 A (term56 A B x' f s t x) (term162 A B s x' f t)). Qed.
Lemma lem3374953 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term185 A B s x f t x') = (term160 A B s x f t x').
Proof. exact (eq_refl (term185 A B s x f t x')). Qed.
Lemma lem3374954 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term186 A B s x f t) = (term162 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374953 A B s x f t x')). Qed.
Lemma lem3374955 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374956 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term187 A B s x f t) = (term163 A B s x f t).
Proof. exact (MK_COMB (@lem3374955 A) (@lem3374954 A B s x f t)). Qed.
Lemma lem3374957 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term175 A B x f s t x') = (term175 A B x f s t x').
Proof. exact (eq_refl (term175 A B x f s t x')). Qed.
Lemma lem3374958 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term183 A B x s x' f t) = (term177 A B x s x' f t).
Proof. exact (MK_COMB (@lem3374957 A B x' f s t x) (@lem3374956 A B s x' f t)). Qed.
Lemma lem3374959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3374960 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term188 A B x s x' f t) = (term189 A B x s x' f t).
Proof. exact (MK_COMB (@lem3374959) (@lem3374958 A B x s x' f t)). Qed.
Lemma lem3374961 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term185 A B s x f t x') = (term160 A B s x f t x').
Proof. exact (eq_refl (term185 A B s x f t x')). Qed.
Lemma lem3374962 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term175 A B x f s t x') = (term175 A B x f s t x').
Proof. exact (eq_refl (term175 A B x f s t x')). Qed.
Lemma lem3374963 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term190 A B x s x' f t x'') = (term191 A B x s x' f t x'').
Proof. exact (MK_COMB (@lem3374962 A B x' f s t x) (@lem3374961 A B s x' f t x'')). Qed.
Lemma lem3374964 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term192 A B x s x' f t) = (term193 A B x s x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3374963 A B x s x' f t x'')). Qed.
Lemma lem3374965 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374966 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term184 A B x s x' f t) = (term194 A B x s x' f t).
Proof. exact (MK_COMB (@lem3374965 A) (@lem3374964 A B x s x' f t)). Qed.
Lemma lem3374967 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : ((term183 A B x s x' f t) = (term184 A B x s x' f t)) = ((term177 A B x s x' f t) = (term194 A B x s x' f t)).
Proof. exact (MK_COMB (@lem3374960 A B x s x' f t) (@lem3374966 A B x s x' f t)). Qed.
Lemma lem3374968 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term177 A B x s x' f t) = (term194 A B x s x' f t).
Proof. exact (EQ_MP (@lem3374967 A B x s x' f t) (@lem3374952 A B x s x' f t)). Qed.
Lemma lem3374969 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term179 A B s x f t) = (term195 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374968 A B x' s x f t)). Qed.
Lemma lem3374970 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374971 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term180 A B s x f t) = (term196 A B s x f t).
Proof. exact (MK_COMB (@lem3374970 A) (@lem3374969 A B s x f t)). Qed.
Lemma lem3374972 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term164 A B s x f t) = (term196 A B s x f t).
Proof. exact (TRANS (@lem3374948 A B s x f t) (@lem3374971 A B s x f t)). Qed.
Lemma lem3374973 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term146 A B s x f t) = (term196 A B s x f t).
Proof. exact (TRANS (@lem3374924 A B s x f t) (@lem3374972 A B s x f t)). Qed.
Lemma lem3374974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3374975 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term148 A B s x f t) = (term197 A B s x f t).
Proof. exact (MK_COMB (@lem3374974) (@lem3374973 A B s x f t)). Qed.
Lemma lem3374977 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3374978 {A : Type'} (P : A -> Prop) (Q : Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (@lem3374977 A P Q). Qed.
Lemma lem3374979 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term198 A B s x f t) = (term199 A B s x f t).
Proof. exact (@lem3374978 A (term67 A B x f s) (term132 A B x f t)). Qed.
Lemma lem3374980 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term65 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem3374981 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term155 A B x f s) = (term67 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3374980 A B x f s x')). Qed.
Lemma lem3374982 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374983 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term156 A B x f s) = (term68 A B x f s).
Proof. exact (MK_COMB (@lem3374982 A) (@lem3374981 A B x f s)). Qed.
Lemma lem3374984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374985 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B x f s) = (term70 A B x f s).
Proof. exact (MK_COMB (@lem3374984) (@lem3374983 A B x f s)). Qed.
Lemma lem3374986 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term132 A B x f t) = (term132 A B x f t).
Proof. exact (eq_refl (term132 A B x f t)). Qed.
Lemma lem3374987 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term198 A B s x f t) = (term139 A B s x f t).
Proof. exact (MK_COMB (@lem3374985 A B x f s) (@lem3374986 A B x f t)). Qed.
Lemma lem3374988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3374989 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term201 A B s x f t) = (term202 A B s x f t).
Proof. exact (MK_COMB (@lem3374988) (@lem3374987 A B s x f t)). Qed.
Lemma lem3374990 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term128 A B x f s x') = (term65 A B x f s x').
Proof. exact (eq_refl (term128 A B x f s x')). Qed.
Lemma lem3374991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3374992 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term203 A B x f s x') = (term204 A B x f s x').
Proof. exact (MK_COMB (@lem3374991) (@lem3374990 A B x f s x')). Qed.
Lemma lem3374993 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term132 A B x f t) = (term132 A B x f t).
Proof. exact (eq_refl (term132 A B x f t)). Qed.
Lemma lem3374994 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term205 A B s x x' f t) = (term206 A B s x x' f t).
Proof. exact (MK_COMB (@lem3374992 A B x' f s x) (@lem3374993 A B x' f t)). Qed.
Lemma lem3374995 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term207 A B s x f t) = (term208 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3374994 A B s x' x f t)). Qed.
Lemma lem3374996 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3374997 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term199 A B s x f t) = (term209 A B s x f t).
Proof. exact (MK_COMB (@lem3374996 A) (@lem3374995 A B s x f t)). Qed.
Lemma lem3374998 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term198 A B s x f t) = (term199 A B s x f t)) = ((term139 A B s x f t) = (term209 A B s x f t)).
Proof. exact (MK_COMB (@lem3374989 A B s x f t) (@lem3374997 A B s x f t)). Qed.
Lemma lem3374999 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term139 A B s x f t) = (term209 A B s x f t).
Proof. exact (EQ_MP (@lem3374998 A B s x f t) (@lem3374979 A B s x f t)). Qed.
Lemma lem3375000 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term141 A B x f s t) = (term141 A B x f s t).
Proof. exact (eq_refl (term141 A B x f s t)). Qed.
Lemma lem3375001 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term143 A B s x f t) = (term210 A B s x f t).
Proof. exact (MK_COMB (@lem3375000 A B x f s t) (@lem3374999 A B s x f t)). Qed.
Lemma lem3375003 {A : Type'} (P : Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3375004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term181 A P Q) = (term182 A P Q).
Proof. exact (@lem3375003 A P Q). Qed.
Lemma lem3375005 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term211 A B s x f t) = (term212 A B s x f t).
Proof. exact (@lem3375004 A (term124 A B x f s t) (term208 A B s x f t)). Qed.
Lemma lem3375006 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term213 A B s x' f t x) = (term206 A B s x x' f t).
Proof. exact (eq_refl (term213 A B s x' f t x)). Qed.
Lemma lem3375007 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term214 A B s x f t) = (term208 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375006 A B s x' x f t)). Qed.
Lemma lem3375008 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375009 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term215 A B s x f t) = (term209 A B s x f t).
Proof. exact (MK_COMB (@lem3375008 A) (@lem3375007 A B s x f t)). Qed.
Lemma lem3375010 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term141 A B x f s t) = (term141 A B x f s t).
Proof. exact (eq_refl (term141 A B x f s t)). Qed.
Lemma lem3375011 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term211 A B s x f t) = (term210 A B s x f t).
Proof. exact (MK_COMB (@lem3375010 A B x f s t) (@lem3375009 A B s x f t)). Qed.
Lemma lem3375012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375013 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term216 A B s x f t) = (term217 A B s x f t).
Proof. exact (MK_COMB (@lem3375012) (@lem3375011 A B s x f t)). Qed.
Lemma lem3375014 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term213 A B s x' f t x) = (term206 A B s x x' f t).
Proof. exact (eq_refl (term213 A B s x' f t x)). Qed.
Lemma lem3375015 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term141 A B x f s t) = (term141 A B x f s t).
Proof. exact (eq_refl (term141 A B x f s t)). Qed.
Lemma lem3375016 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term218 A B s x' f t x) = (term219 A B s x x' f t).
Proof. exact (MK_COMB (@lem3375015 A B x' f s t) (@lem3375014 A B s x x' f t)). Qed.
Lemma lem3375017 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term220 A B s x f t) = (term221 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375016 A B s x' x f t)). Qed.
Lemma lem3375018 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375019 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term212 A B s x f t) = (term222 A B s x f t).
Proof. exact (MK_COMB (@lem3375018 A) (@lem3375017 A B s x f t)). Qed.
Lemma lem3375020 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term211 A B s x f t) = (term212 A B s x f t)) = ((term210 A B s x f t) = (term222 A B s x f t)).
Proof. exact (MK_COMB (@lem3375013 A B s x f t) (@lem3375019 A B s x f t)). Qed.
Lemma lem3375021 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term210 A B s x f t) = (term222 A B s x f t).
Proof. exact (EQ_MP (@lem3375020 A B s x f t) (@lem3375005 A B s x f t)). Qed.
Lemma lem3375022 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term143 A B s x f t) = (term222 A B s x f t).
Proof. exact (TRANS (@lem3375001 A B s x f t) (@lem3375021 A B s x f t)). Qed.
Lemma lem3375023 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term150 A B s x f t) = (term223 A B s x f t).
Proof. exact (MK_COMB (@lem3374975 A B s x f t) (@lem3375022 A B s x f t)). Qed.
Lemma lem3375025 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3375026 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3375025 A P Q). Qed.
Lemma lem3375027 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term226 A B s x f t) = (term227 A B s x f t).
Proof. exact (@lem3375026 A (term195 A B s x f t) (term221 A B s x f t)). Qed.
Lemma lem3375028 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term228 A B s x' f t x) = (term194 A B x s x' f t).
Proof. exact (eq_refl (term228 A B s x' f t x)). Qed.
Lemma lem3375029 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term229 A B s x f t) = (term195 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375028 A B x' s x f t)). Qed.
Lemma lem3375030 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375031 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term230 A B s x f t) = (term196 A B s x f t).
Proof. exact (MK_COMB (@lem3375030 A) (@lem3375029 A B s x f t)). Qed.
Lemma lem3375032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3375033 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term231 A B s x f t) = (term197 A B s x f t).
Proof. exact (MK_COMB (@lem3375032) (@lem3375031 A B s x f t)). Qed.
Lemma lem3375034 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term232 A B s x' f t x) = (term219 A B s x x' f t).
Proof. exact (eq_refl (term232 A B s x' f t x)). Qed.
Lemma lem3375035 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term233 A B s x f t) = (term221 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375034 A B s x' x f t)). Qed.
Lemma lem3375036 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375037 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term234 A B s x f t) = (term222 A B s x f t).
Proof. exact (MK_COMB (@lem3375036 A) (@lem3375035 A B s x f t)). Qed.
Lemma lem3375038 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term226 A B s x f t) = (term223 A B s x f t).
Proof. exact (MK_COMB (@lem3375033 A B s x f t) (@lem3375037 A B s x f t)). Qed.
Lemma lem3375039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375040 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term235 A B s x f t) = (term236 A B s x f t).
Proof. exact (MK_COMB (@lem3375039) (@lem3375038 A B s x f t)). Qed.
Lemma lem3375041 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term228 A B s x' f t x) = (term194 A B x s x' f t).
Proof. exact (eq_refl (term228 A B s x' f t x)). Qed.
Lemma lem3375042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3375043 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term237 A B s x' f t x) = (term238 A B x s x' f t).
Proof. exact (MK_COMB (@lem3375042) (@lem3375041 A B x s x' f t)). Qed.
Lemma lem3375044 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term232 A B s x' f t x) = (term219 A B s x x' f t).
Proof. exact (eq_refl (term232 A B s x' f t x)). Qed.
Lemma lem3375045 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term239 A B s x' f t x) = (term240 A B s x x' f t).
Proof. exact (MK_COMB (@lem3375043 A B x s x' f t) (@lem3375044 A B s x x' f t)). Qed.
Lemma lem3375046 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term241 A B s x f t) = (term242 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375045 A B s x' x f t)). Qed.
Lemma lem3375047 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375048 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term227 A B s x f t) = (term243 A B s x f t).
Proof. exact (MK_COMB (@lem3375047 A) (@lem3375046 A B s x f t)). Qed.
Lemma lem3375049 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term226 A B s x f t) = (term227 A B s x f t)) = ((term223 A B s x f t) = (term243 A B s x f t)).
Proof. exact (MK_COMB (@lem3375040 A B s x f t) (@lem3375048 A B s x f t)). Qed.
Lemma lem3375050 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term223 A B s x f t) = (term243 A B s x f t).
Proof. exact (EQ_MP (@lem3375049 A B s x f t) (@lem3375027 A B s x f t)). Qed.
Lemma lem3375052 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3375053 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (@lem3375052 A P Q). Qed.
Lemma lem3375054 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term246 A B s x x' f t) = (term247 A B s x x' f t).
Proof. exact (@lem3375053 A (term193 A B x s x' f t) (term219 A B s x x' f t)). Qed.
Lemma lem3375055 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term248 A B x s x' f t x'') = (term191 A B x s x' f t x'').
Proof. exact (eq_refl (term248 A B x s x' f t x'')). Qed.
Lemma lem3375056 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term249 A B x s x' f t) = (term193 A B x s x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3375055 A B x s x' f t x'')). Qed.
Lemma lem3375057 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375058 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term250 A B x s x' f t) = (term194 A B x s x' f t).
Proof. exact (MK_COMB (@lem3375057 A) (@lem3375056 A B x s x' f t)). Qed.
Lemma lem3375059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3375060 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) : (term251 A B x s x' f t) = (term238 A B x s x' f t).
Proof. exact (MK_COMB (@lem3375059) (@lem3375058 A B x s x' f t)). Qed.
Lemma lem3375061 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term219 A B s x x' f t) = (term219 A B s x x' f t).
Proof. exact (eq_refl (term219 A B s x x' f t)). Qed.
Lemma lem3375062 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term246 A B s x x' f t) = (term240 A B s x x' f t).
Proof. exact (MK_COMB (@lem3375060 A B x s x' f t) (@lem3375061 A B s x x' f t)). Qed.
Lemma lem3375063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375064 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term252 A B s x x' f t) = (term253 A B s x x' f t).
Proof. exact (MK_COMB (@lem3375063) (@lem3375062 A B s x x' f t)). Qed.
Lemma lem3375065 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term248 A B x s x' f t x'') = (term191 A B x s x' f t x'').
Proof. exact (eq_refl (term248 A B x s x' f t x'')). Qed.
Lemma lem3375066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3375067 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term254 A B x s x' f t x'') = (term255 A B x s x' f t x'').
Proof. exact (MK_COMB (@lem3375066) (@lem3375065 A B x s x' f t x'')). Qed.
Lemma lem3375068 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term219 A B s x x' f t) = (term219 A B s x x' f t).
Proof. exact (eq_refl (term219 A B s x x' f t)). Qed.
Lemma lem3375069 {A B : Type'} (x' : A) (s : A -> Prop) (x : A) (x'' : B) (f : A -> B) (t : A -> Prop) : (term256 A B x' s x x'' f t) = (term257 A B x' s x x'' f t).
Proof. exact (MK_COMB (@lem3375067 A B x s x'' f t x') (@lem3375068 A B s x x'' f t)). Qed.
Lemma lem3375070 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term258 A B s x x' f t) = (term259 A B s x x' f t).
Proof. exact (fun_ext (fun x'' : A => @lem3375069 A B x'' s x x' f t)). Qed.
Lemma lem3375071 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375072 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term247 A B s x x' f t) = (term260 A B s x x' f t).
Proof. exact (MK_COMB (@lem3375071 A) (@lem3375070 A B s x x' f t)). Qed.
Lemma lem3375073 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : ((term246 A B s x x' f t) = (term247 A B s x x' f t)) = ((term240 A B s x x' f t) = (term260 A B s x x' f t)).
Proof. exact (MK_COMB (@lem3375064 A B s x x' f t) (@lem3375072 A B s x x' f t)). Qed.
Lemma lem3375074 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term240 A B s x x' f t) = (term260 A B s x x' f t).
Proof. exact (EQ_MP (@lem3375073 A B s x x' f t) (@lem3375054 A B s x x' f t)). Qed.
Lemma lem3375075 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term242 A B s x f t) = (term261 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375074 A B s x' x f t)). Qed.
Lemma lem3375076 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3375077 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term243 A B s x f t) = (term262 A B s x f t).
Proof. exact (MK_COMB (@lem3375076 A) (@lem3375075 A B s x f t)). Qed.
Lemma lem3375078 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term223 A B s x f t) = (term262 A B s x f t).
Proof. exact (TRANS (@lem3375050 A B s x f t) (@lem3375077 A B s x f t)). Qed.
Lemma lem3375080 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term150 A B s x f t) = (term262 A B s x f t).
Proof. exact (TRANS (@lem3375023 A B s x f t) (@lem3375078 A B s x f t)). Qed.
Lemma lem3375081 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term93 A B s x f t) = (term262 A B s x f t).
Proof. exact (TRANS (@lem3374645 A B s x f t) (@lem3375080 A B s x f t)). Qed.
Lemma lem3375082 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term93 A B s x f t) : term262 A B s x f t.
Proof. exact (EQ_MP (@lem3375081 A B s x f t) (@lem3374455 A B s x f t h1)). Qed.
Lemma lem3375083 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term260 A B s x' x f t) : term260 A B s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3375084 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term257 A B x'' s x' x f t) : term257 A B x'' s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3375119 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (y : A) : (term103 A B s t f x y) = (term103 A B s t f x y).
Proof. exact (eq_refl (term103 A B s t f x y)). Qed.
Lemma lem3375120 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term104 A B s t f x) = (term104 A B s t f x).
Proof. exact (fun_ext (fun y : A => @lem3375119 A B s t f x y)). Qed.
Lemma lem3375121 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375122 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term105 A B s t f x) = (term105 A B s t f x).
Proof. exact (MK_COMB (@lem3375121 A) (@lem3375120 A B s t f x)). Qed.
Lemma lem3375123 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term106 A B s t f) = (term106 A B s t f).
Proof. exact (fun_ext (fun x : A => @lem3375122 A B s t f x)). Qed.
Lemma lem3375124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375125 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term107 A B s t f) = (term107 A B s t f).
Proof. exact (MK_COMB (@lem3375124 A) (@lem3375123 A B s t f)). Qed.
Lemma lem3375126 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term107 A B s t f.
Proof. exact (EQ_MP (@lem3375125 A B s t f) (@lem3374537 A B s t f h1)). Qed.
Lemma lem3375143 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term126 A B x f t x') = (term126 A B x f t x').
Proof. exact (eq_refl (term126 A B x f t x')). Qed.
Lemma lem3375144 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term131 A B x f t) = (term131 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375143 A B x f t x')). Qed.
Lemma lem3375145 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375146 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term132 A B x f t) = (term132 A B x f t).
Proof. exact (MK_COMB (@lem3375145 A) (@lem3375144 A B x f t)). Qed.
Lemma lem3375161 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term204 A B x f s x') = (term204 A B x f s x').
Proof. exact (eq_refl (term204 A B x f s x')). Qed.
Lemma lem3375162 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) : (term206 A B s x' x f t) = (term206 A B s x' x f t).
Proof. exact (MK_COMB (@lem3375161 A B x f s x') (@lem3375146 A B x f t)). Qed.
Lemma lem3375185 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term114 A B x f s t x') = (term114 A B x f s t x').
Proof. exact (eq_refl (term114 A B x f s t x')). Qed.
Lemma lem3375186 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term123 A B x f s t) = (term123 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3375185 A B x f s t x')). Qed.
Lemma lem3375187 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375188 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term124 A B x f s t) = (term124 A B x f s t).
Proof. exact (MK_COMB (@lem3375187 A) (@lem3375186 A B x f s t)). Qed.
Lemma lem3375189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3375190 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term141 A B x f s t) = (term141 A B x f s t).
Proof. exact (MK_COMB (@lem3375189) (@lem3375188 A B x f s t)). Qed.
Lemma lem3375191 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) : (term219 A B s x' x f t) = (term219 A B s x' x f t).
Proof. exact (MK_COMB (@lem3375190 A B x f s t) (@lem3375162 A B s x' x f t)). Qed.
Lemma lem3375204 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term65 A B x f t x'') = (term65 A B x f t x'').
Proof. exact (eq_refl (term65 A B x f t x'')). Qed.
Lemma lem3375221 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term126 A B x f s x') = (term126 A B x f s x').
Proof. exact (eq_refl (term126 A B x f s x')). Qed.
Lemma lem3375222 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term131 A B x f s) = (term131 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3375221 A B x f s x')). Qed.
Lemma lem3375223 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375224 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem3375223 A) (@lem3375222 A B x f s)). Qed.
Lemma lem3375225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3375226 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term135 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem3375225) (@lem3375224 A B x f s)). Qed.
Lemma lem3375227 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term160 A B s x f t x'') = (term160 A B s x f t x'').
Proof. exact (MK_COMB (@lem3375226 A B x f s) (@lem3375204 A B x f t x'')). Qed.
Lemma lem3375250 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term175 A B x f s t x') = (term175 A B x f s t x').
Proof. exact (eq_refl (term175 A B x f s t x')). Qed.
Lemma lem3375251 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term191 A B x' s x f t x'') = (term191 A B x' s x f t x'').
Proof. exact (MK_COMB (@lem3375250 A B x f s t x') (@lem3375227 A B s x f t x'')). Qed.
Lemma lem3375252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3375253 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term255 A B x' s x f t x'') = (term255 A B x' s x f t x'').
Proof. exact (MK_COMB (@lem3375252) (@lem3375251 A B x' s x f t x'')). Qed.
Lemma lem3375254 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) : (term257 A B x'' s x' x f t) = (term257 A B x'' s x' x f t).
Proof. exact (MK_COMB (@lem3375253 A B x' s x f t x'') (@lem3375191 A B s x' x f t)). Qed.
Lemma lem3375255 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term257 A B x'' s x' x f t) : term257 A B x'' s x' x f t.
Proof. exact (EQ_MP (@lem3375254 A B x'' s x' x f t) (@lem3375084 A B x'' s x' x f t h1)). Qed.
Lemma lem3375256 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term191 A B x' s x f t x''.
Proof. exact (h1). Qed.
Lemma lem3375257 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term219 A B s x' x f t.
Proof. exact (h1). Qed.
Lemma lem3375258 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term160 A B s x f t x''.
Proof. exact (proj2 (@lem3375256 A B x' s x f t x'' h1)). Qed.
Lemma lem3375259 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term56 A B x f s t x'.
Proof. exact (proj1 (@lem3375256 A B x' s x f t x'' h1)). Qed.
Lemma lem3375260 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term53 A s t x'.
Proof. exact (proj2 (@lem3375259 A B x' s x f t x'' h1)). Qed.
Lemma lem3375264 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term132 A B x f s) : term132 A B x f s.
Proof. exact (h1). Qed.
Lemma lem3375265 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : term65 A B x f t x''.
Proof. exact (h1). Qed.
Lemma lem3375268 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term206 A B s x' x f t.
Proof. exact (proj2 (@lem3375257 A B s x' x f t h1)). Qed.
Lemma lem3375269 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term124 A B x f s t.
Proof. exact (proj1 (@lem3375257 A B s x' x f t h1)). Qed.
Lemma lem3375270 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term132 A B x f t.
Proof. exact (proj2 (@lem3375268 A B s x' x f t h1)). Qed.
Lemma lem3375271 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term65 A B x f s x'.
Proof. exact (proj1 (@lem3375268 A B s x' x f t h1)). Qed.
Lemma lem3375321 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term126 A B x f s x') = (term126 A B x f s x').
Proof. exact (eq_refl (term126 A B x f s x')). Qed.
Lemma lem3375322 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term131 A B x f s) = (term131 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3375321 A B x f s x')). Qed.
Lemma lem3375323 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375325 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem3375323 A) (@lem3375322 A B x f s)). Qed.
Lemma lem3375326 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term132 A B x f s) : term132 A B x f s.
Proof. exact (EQ_MP (@lem3375325 A B x f s) (@lem3375264 A B x f s h1)). Qed.
Lemma lem3375346 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) (y : A) : (term103 A B s t f x y) = (term103 A B s t f x y).
Proof. exact (eq_refl (term103 A B s t f x y)). Qed.
Lemma lem3375347 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term104 A B s t f x) = (term104 A B s t f x).
Proof. exact (fun_ext (fun y : A => @lem3375346 A B s t f x y)). Qed.
Lemma lem3375348 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375349 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (x : A) : (term105 A B s t f x) = (term105 A B s t f x).
Proof. exact (MK_COMB (@lem3375348 A) (@lem3375347 A B s t f x)). Qed.
Lemma lem3375350 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term106 A B s t f) = (term106 A B s t f).
Proof. exact (fun_ext (fun x : A => @lem3375349 A B s t f x)). Qed.
Lemma lem3375351 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375353 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term107 A B s t f) = (term107 A B s t f).
Proof. exact (MK_COMB (@lem3375351 A) (@lem3375350 A B s t f)). Qed.
Lemma lem3375354 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term107 A B s t f.
Proof. exact (EQ_MP (@lem3375353 A B s t f) (@lem3375126 A B s t f h1)). Qed.
Lemma lem3375416 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term114 A B x f s t x') = (term114 A B x f s t x').
Proof. exact (eq_refl (term114 A B x f s t x')). Qed.
Lemma lem3375417 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term123 A B x f s t) = (term123 A B x f s t).
Proof. exact (fun_ext (fun x' : A => @lem3375416 A B x f s t x')). Qed.
Lemma lem3375418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375420 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term124 A B x f s t) = (term124 A B x f s t).
Proof. exact (MK_COMB (@lem3375418 A) (@lem3375417 A B x f s t)). Qed.
Lemma lem3375421 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term124 A B x f s t.
Proof. exact (EQ_MP (@lem3375420 A B x f s t) (@lem3375269 A B s x' x f t h1)). Qed.
Lemma lem3375429 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term126 A B x f t x') = (term126 A B x f t x').
Proof. exact (eq_refl (term126 A B x f t x')). Qed.
Lemma lem3375430 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term131 A B x f t) = (term131 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem3375429 A B x f t x')). Qed.
Lemma lem3375431 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3375433 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term132 A B x f t) = (term132 A B x f t).
Proof. exact (MK_COMB (@lem3375431 A) (@lem3375430 A B x f t)). Qed.
Lemma lem3375434 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term132 A B x f t.
Proof. exact (EQ_MP (@lem3375433 A B x f t) (@lem3375270 A B s x' x f t h1)). Qed.
Lemma lem3375449 {A B : Type'} (_35321 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term132 A B x f s) : term263 A B x f s _35321.
Proof. exact (@lem3375326 A B x f s h1 _35321). Qed.
Lemma lem3375450 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term263 A B x f s _35321) = (term126 A B x f s _35321).
Proof. exact (eq_refl (term263 A B x f s _35321)). Qed.
Lemma lem3375452 {A B : Type'} (_35322 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term264 A B s t f _35322.
Proof. exact (@lem3375354 A B s t f h1 _35322). Qed.
Lemma lem3375453 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) : (term264 A B s t f _35322) = (term105 A B s t f _35322).
Proof. exact (eq_refl (term264 A B s t f _35322)). Qed.
Lemma lem3375454 {A B : Type'} (_35322 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term105 A B s t f _35322.
Proof. exact (EQ_MP (@lem3375453 A B s t f _35322) (@lem3375452 A B _35322 s t f h1)). Qed.
Lemma lem3375455 {A B : Type'} (_35322 : A) (_35323 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term265 A B s t f _35322 _35323.
Proof. exact (@lem3375454 A B _35322 s t f h1 _35323). Qed.
Lemma lem3375456 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term265 A B s t f _35322 _35323) = (term103 A B s t f _35322 _35323).
Proof. exact (eq_refl (term265 A B s t f _35322 _35323)). Qed.
Lemma lem3375457 {A B : Type'} (_35322 : A) (_35323 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term103 A B s t f _35322 _35323.
Proof. exact (EQ_MP (@lem3375456 A B s t f _35322 _35323) (@lem3375455 A B _35322 _35323 s t f h1)). Qed.
Lemma lem3375464 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term266 A B x f s t _35326.
Proof. exact (@lem3375421 A B s x' x f t h1 _35326). Qed.
Lemma lem3375465 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term266 A B x f s t _35326) = (term114 A B x f s t _35326).
Proof. exact (eq_refl (term266 A B x f s t _35326)). Qed.
Lemma lem3375467 {A B : Type'} (_35327 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term263 A B x f t _35327.
Proof. exact (@lem3375434 A B s x' x f t h1 _35327). Qed.
Lemma lem3375468 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term263 A B x f t _35327) = (term126 A B x f t _35327).
Proof. exact (eq_refl (term263 A B x f t _35327)). Qed.
Lemma lem3375489 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3375259 A B x' s x f t x'' h1)). Qed.
Lemma lem3375499 {A B : Type'} (_35321 : A) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term132 A B x f s) : term126 A B x f s _35321.
Proof. exact (EQ_MP (@lem3375450 A B x f s _35321) (@lem3375449 A B _35321 x f s h1)). Qed.
Lemma lem3375503 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term103 A B s t f _35322 _35323) = (term267 A B s t f _35322 _35323).
Proof. exact (@lem3373808 (term52 A s _35322) (term95 A B t _35322 f _35323) (_35322 = _35323)). Qed.
Lemma lem3375510 {A B : Type'} (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term268 A B t f _35322 _35323) = (term269 A B t f _35322 _35323).
Proof. exact (@lem3373808 (term52 A t _35323) (term270 A B _35322 f _35323) (_35322 = _35323)). Qed.
Lemma lem3375511 {A : Type'} (s : A -> Prop) (_35322 : A) : (term96 A s _35322) = (term96 A s _35322).
Proof. exact (eq_refl (term96 A s _35322)). Qed.
Lemma lem3375514 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term267 A B s t f _35322 _35323) = (term271 A B s t f _35322 _35323).
Proof. exact (MK_COMB (@lem3375511 A s _35322) (@lem3375510 A B t f _35322 _35323)). Qed.
Lemma lem3375516 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term103 A B s t f _35322 _35323) = (term271 A B s t f _35322 _35323).
Proof. exact (TRANS (@lem3375503 A B s t f _35322 _35323) (@lem3375514 A B s t f _35322 _35323)). Qed.
Lemma lem3375519 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : x = (f x').
Proof. exact (proj1 (@lem3375259 A B x' s x f t x'' h1)). Qed.
Lemma lem3375525 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : x = (f x'').
Proof. exact (proj1 (@lem3375265 A B x f t x'' h1)). Qed.
Lemma lem3375555 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term114 A B x f s t _35326.
Proof. exact (EQ_MP (@lem3375465 A B x f s t _35326) (@lem3375464 A B _35326 s x' x f t h1)). Qed.
Lemma lem3375561 {A B : Type'} (_35327 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term126 A B x f t _35327.
Proof. exact (EQ_MP (@lem3375468 A B x f t _35327) (@lem3375467 A B _35327 s x' x f t h1)). Qed.
Lemma lem3375563 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : x = (f x').
Proof. exact (proj1 (@lem3375271 A B s x' x f t h1)). Qed.
Lemma lem3375622 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35321 : A) : (term272 A B f s _35321) = (term272 A B f s _35321).
Proof. exact (eq_refl (term272 A B f s _35321)). Qed.
Lemma lem3375623 {A B : Type'} (_35321 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : (term273 A B f s _35321 x) = (term274 A B s _35321 f x').
Proof. exact (MK_COMB (@lem3375622 A B f s _35321) (@lem3375489 A B x' s x f t x'' h1)). Qed.
Lemma lem3375624 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term274 A B s _35321 f x') = (term275 A B x' f s _35321).
Proof. exact (eq_refl (term274 A B s _35321 f x')). Qed.
Lemma lem3375625 {A B : Type'} (f : A -> B) (s : A -> Prop) (_35321 : A) (x : B) : (term276 A B f s _35321 x) = (term276 A B f s _35321 x).
Proof. exact (eq_refl (term276 A B f s _35321 x)). Qed.
Lemma lem3375626 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : ((term273 A B f s _35321 x) = (term274 A B s _35321 f x')) = ((term273 A B f s _35321 x) = (term275 A B x' f s _35321)).
Proof. exact (MK_COMB (@lem3375625 A B f s _35321 x) (@lem3375624 A B x' f s _35321)). Qed.
Lemma lem3375627 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term273 A B f s _35321 x) = (term126 A B x f s _35321).
Proof. exact (eq_refl (term273 A B f s _35321 x)). Qed.
Lemma lem3375628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375629 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term276 A B f s _35321 x) = (term277 A B x f s _35321).
Proof. exact (MK_COMB (@lem3375628) (@lem3375627 A B x f s _35321)). Qed.
Lemma lem3375630 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term275 A B x' f s _35321) = (term275 A B x' f s _35321).
Proof. exact (eq_refl (term275 A B x' f s _35321)). Qed.
Lemma lem3375631 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : ((term273 A B f s _35321 x) = (term275 A B x' f s _35321)) = ((term126 A B x f s _35321) = (term275 A B x' f s _35321)).
Proof. exact (MK_COMB (@lem3375629 A B x f s _35321) (@lem3375630 A B x' f s _35321)). Qed.
Lemma lem3375632 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : ((term273 A B f s _35321 x) = (term274 A B s _35321 f x')) = ((term126 A B x f s _35321) = (term275 A B x' f s _35321)).
Proof. exact (TRANS (@lem3375626 A B x x' f s _35321) (@lem3375631 A B x x' f s _35321)). Qed.
Lemma lem3375633 {A B : Type'} (_35321 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : (term126 A B x f s _35321) = (term275 A B x' f s _35321).
Proof. exact (EQ_MP (@lem3375632 A B x x' f s _35321) (@lem3375623 A B _35321 x' s x f t x'' h1)). Qed.
Lemma lem3375634 {A B : Type'} (_35321 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : term275 A B x' f s _35321.
Proof. exact (EQ_MP (@lem3375633 A B _35321 x' s x f t x'' h2) (@lem3375499 A B _35321 x f s h1)). Qed.
Lemma lem3375662 {A B : Type'} (_35322 : A) (_35323 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term271 A B s t f _35322 _35323.
Proof. exact (EQ_MP (@lem3375516 A B s t f _35322 _35323) (@lem3375457 A B _35322 _35323 s t f h1)). Qed.
Lemma lem3375663 {A B : Type'} (f : A -> B) (x' : A) : (term278 A B f x') = (term278 A B f x').
Proof. exact (eq_refl (term278 A B f x')). Qed.
Lemma lem3375664 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : (term279 A B f x' x) = (term280 A B x' f x'').
Proof. exact (MK_COMB (@lem3375663 A B f x') (@lem3375525 A B x f t x'' h1)). Qed.
Lemma lem3375665 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : (term280 A B x' f x'') = ((f x'') = (f x')).
Proof. exact (eq_refl (term280 A B x' f x'')). Qed.
Lemma lem3375666 {A B : Type'} (f : A -> B) (x' : A) (x : B) : (term281 A B f x' x) = (term281 A B f x' x).
Proof. exact (eq_refl (term281 A B f x' x)). Qed.
Lemma lem3375667 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A) : ((term279 A B f x' x) = (term280 A B x' f x'')) = ((term279 A B f x' x) = ((f x'') = (f x'))).
Proof. exact (MK_COMB (@lem3375666 A B f x' x) (@lem3375665 A B x'' f x')). Qed.
Lemma lem3375668 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term279 A B f x' x) = (x = (f x')).
Proof. exact (eq_refl (term279 A B f x' x)). Qed.
Lemma lem3375669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375670 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term281 A B f x' x) = (term282 A B x f x').
Proof. exact (MK_COMB (@lem3375669) (@lem3375668 A B x f x')). Qed.
Lemma lem3375671 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : ((f x'') = (f x')) = ((f x'') = (f x')).
Proof. exact (eq_refl ((f x'') = (f x'))). Qed.
Lemma lem3375672 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A) : ((term279 A B f x' x) = ((f x'') = (f x'))) = ((x = (f x')) = ((f x'') = (f x'))).
Proof. exact (MK_COMB (@lem3375670 A B x f x') (@lem3375671 A B x'' f x')). Qed.
Lemma lem3375673 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A) : ((term279 A B f x' x) = (term280 A B x' f x'')) = ((x = (f x')) = ((f x'') = (f x'))).
Proof. exact (TRANS (@lem3375667 A B x x'' f x') (@lem3375672 A B x x'' f x')). Qed.
Lemma lem3375674 {A B : Type'} (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : (x = (f x')) = ((f x'') = (f x')).
Proof. exact (EQ_MP (@lem3375673 A B x x'' f x') (@lem3375664 A B x' x f t x'' h1)). Qed.
Lemma lem3375703 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term52 A t x'.
Proof. exact (proj2 (@lem3375260 A B x' s x f t x'' h1)). Qed.
Lemma lem3375746 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term283 A B f s t _35326) = (term283 A B f s t _35326).
Proof. exact (eq_refl (term283 A B f s t _35326)). Qed.
Lemma lem3375747 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : (term284 A B f s t _35326 x) = (term285 A B s t _35326 f x').
Proof. exact (MK_COMB (@lem3375746 A B f s t _35326) (@lem3375563 A B s x' x f t h1)). Qed.
Lemma lem3375748 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term285 A B s t _35326 f x') = (term286 A B x' f s t _35326).
Proof. exact (eq_refl (term285 A B s t _35326 f x')). Qed.
Lemma lem3375749 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) (x : B) : (term287 A B f s t _35326 x) = (term287 A B f s t _35326 x).
Proof. exact (eq_refl (term287 A B f s t _35326 x)). Qed.
Lemma lem3375750 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : ((term284 A B f s t _35326 x) = (term285 A B s t _35326 f x')) = ((term284 A B f s t _35326 x) = (term286 A B x' f s t _35326)).
Proof. exact (MK_COMB (@lem3375749 A B f s t _35326 x) (@lem3375748 A B x' f s t _35326)). Qed.
Lemma lem3375751 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term284 A B f s t _35326 x) = (term114 A B x f s t _35326).
Proof. exact (eq_refl (term284 A B f s t _35326 x)). Qed.
Lemma lem3375752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375753 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term287 A B f s t _35326 x) = (term288 A B x f s t _35326).
Proof. exact (MK_COMB (@lem3375752) (@lem3375751 A B x f s t _35326)). Qed.
Lemma lem3375754 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term286 A B x' f s t _35326) = (term286 A B x' f s t _35326).
Proof. exact (eq_refl (term286 A B x' f s t _35326)). Qed.
Lemma lem3375755 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : ((term284 A B f s t _35326 x) = (term286 A B x' f s t _35326)) = ((term114 A B x f s t _35326) = (term286 A B x' f s t _35326)).
Proof. exact (MK_COMB (@lem3375753 A B x f s t _35326) (@lem3375754 A B x' f s t _35326)). Qed.
Lemma lem3375756 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : ((term284 A B f s t _35326 x) = (term285 A B s t _35326 f x')) = ((term114 A B x f s t _35326) = (term286 A B x' f s t _35326)).
Proof. exact (TRANS (@lem3375750 A B x x' f s t _35326) (@lem3375755 A B x x' f s t _35326)). Qed.
Lemma lem3375757 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : (term114 A B x f s t _35326) = (term286 A B x' f s t _35326).
Proof. exact (EQ_MP (@lem3375756 A B x x' f s t _35326) (@lem3375747 A B _35326 s x' x f t h1)). Qed.
Lemma lem3375758 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term286 A B x' f s t _35326.
Proof. exact (EQ_MP (@lem3375757 A B _35326 s x' x f t h1) (@lem3375555 A B _35326 s x' x f t h1)). Qed.
Lemma lem3375759 {A B : Type'} (f : A -> B) (t : A -> Prop) (_35327 : A) : (term272 A B f t _35327) = (term272 A B f t _35327).
Proof. exact (eq_refl (term272 A B f t _35327)). Qed.
Lemma lem3375760 {A B : Type'} (_35327 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : (term273 A B f t _35327 x) = (term274 A B t _35327 f x').
Proof. exact (MK_COMB (@lem3375759 A B f t _35327) (@lem3375563 A B s x' x f t h1)). Qed.
Lemma lem3375761 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term274 A B t _35327 f x') = (term275 A B x' f t _35327).
Proof. exact (eq_refl (term274 A B t _35327 f x')). Qed.
Lemma lem3375762 {A B : Type'} (f : A -> B) (t : A -> Prop) (_35327 : A) (x : B) : (term276 A B f t _35327 x) = (term276 A B f t _35327 x).
Proof. exact (eq_refl (term276 A B f t _35327 x)). Qed.
Lemma lem3375763 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : ((term273 A B f t _35327 x) = (term274 A B t _35327 f x')) = ((term273 A B f t _35327 x) = (term275 A B x' f t _35327)).
Proof. exact (MK_COMB (@lem3375762 A B f t _35327 x) (@lem3375761 A B x' f t _35327)). Qed.
Lemma lem3375764 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term273 A B f t _35327 x) = (term126 A B x f t _35327).
Proof. exact (eq_refl (term273 A B f t _35327 x)). Qed.
Lemma lem3375765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375766 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term276 A B f t _35327 x) = (term277 A B x f t _35327).
Proof. exact (MK_COMB (@lem3375765) (@lem3375764 A B x f t _35327)). Qed.
Lemma lem3375767 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term275 A B x' f t _35327) = (term275 A B x' f t _35327).
Proof. exact (eq_refl (term275 A B x' f t _35327)). Qed.
Lemma lem3375768 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : ((term273 A B f t _35327 x) = (term275 A B x' f t _35327)) = ((term126 A B x f t _35327) = (term275 A B x' f t _35327)).
Proof. exact (MK_COMB (@lem3375766 A B x f t _35327) (@lem3375767 A B x' f t _35327)). Qed.
Lemma lem3375769 {A B : Type'} (x : B) (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : ((term273 A B f t _35327 x) = (term274 A B t _35327 f x')) = ((term126 A B x f t _35327) = (term275 A B x' f t _35327)).
Proof. exact (TRANS (@lem3375763 A B x x' f t _35327) (@lem3375768 A B x x' f t _35327)). Qed.
Lemma lem3375770 {A B : Type'} (_35327 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : (term126 A B x f t _35327) = (term275 A B x' f t _35327).
Proof. exact (EQ_MP (@lem3375769 A B x x' f t _35327) (@lem3375760 A B _35327 s x' x f t h1)). Qed.
Lemma lem3375771 {A B : Type'} (_35327 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term275 A B x' f t _35327.
Proof. exact (EQ_MP (@lem3375770 A B _35327 s x' x f t h1) (@lem3375561 A B _35327 s x' x f t h1)). Qed.
Lemma lem3375823 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3375824 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3375823 B x). Qed.
Lemma lem3375825 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3375824 B (f x')). Qed.
Lemma lem3375826 {A B : Type'} (f : A -> B) (x' : A) : term289 A B f x'.
Proof. exact (fun h0 : term290 A B f x' => @lem3375825 A B f x'). Qed.
Lemma lem3375828 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3375829 {A B : Type'} (f : A -> B) (x' : A) : (term289 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3375828 ((f x') = (f x'))). Qed.
Lemma lem3375830 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3375829 A B f x') (@lem3375826 A B f x')). Qed.
Lemma lem3375832 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : s x'.
Proof. exact (proj1 (@lem3375260 A B x' s x f t x'' h1)). Qed.
Lemma lem3375833 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term292 A s x'.
Proof. exact (fun h0 : term52 A s x' => @lem3375832 A B x' s x f t x'' h1). Qed.
Lemma lem3375835 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3375836 {A : Type'} (s : A -> Prop) (x' : A) : (term292 A s x') = (s x').
Proof. exact (@lem3375835 (s x')). Qed.
Lemma lem3375837 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3375836 A s x') (@lem3375833 A B x' s x f t x'' h1)). Qed.
Lemma lem3375839 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3375840 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term275 A B x' f s _35321) = (term295 A B x' f s _35321).
Proof. exact (@lem3375839 ((f x') = (f _35321)) (s _35321)). Qed.
Lemma lem3375842 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3375843 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term295 A B x' f s _35321) = (term296 A B x' f s _35321).
Proof. exact (@lem3375842 (term297 A B x' f s _35321)). Qed.
Lemma lem3375844 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35321 : A) : (term275 A B x' f s _35321) = (term296 A B x' f s _35321).
Proof. exact (TRANS (@lem3375840 A B x' f s _35321) (@lem3375843 A B x' f s _35321)). Qed.
Lemma lem3375846 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term298 A B f s x'.
Proof. exact (conj (@lem3375830 A B f x') (@lem3375837 A B x' s x f t x'' h1)). Qed.
Lemma lem3375848 {A B : Type'} (_35321 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : term296 A B x' f s _35321.
Proof. exact (EQ_MP (@lem3375844 A B x' f s _35321) (@lem3375634 A B _35321 x' s x f t x'' h1 h2)). Qed.
Lemma lem3375849 {A B : Type'} (_35321 : A) (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : term296 A B x' f s _35321.
Proof. exact (@lem3375848 A B _35321 x' s x f t x'' h1 h2). Qed.
Lemma lem3375850 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : term299 A B f s x'.
Proof. exact (@lem3375849 A B x' x' s x f t x'' h1 h2). Qed.
Lemma lem3375853 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : False.
Proof. exact (@lem3375850 A B x' s x f t x'' h1 h2 (@lem3375846 A B x' s x f t x'' h2)). Qed.
Lemma lem3375854 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : term300.
Proof. exact (fun h0 : ~ False => @lem3375853 A B x' s x f t x'' h1 h2). Qed.
Lemma lem3375856 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3375857 : term300 = False.
Proof. exact (@lem3375856 False). Qed.
Lemma lem3375871 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3375872 {A : Type'} (_35368 : A) (_35369 : A) (h1 : _35368 = _35369) : _35368 = _35369.
Proof. exact (h1). Qed.
Lemma lem3375873 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) (h1 : _35368 = _35369) : (t _35368) = (t _35369).
Proof. exact (MK_COMB (@lem3375871 A t) (@lem3375872 A _35368 _35369 h1)). Qed.
Lemma lem3375875 (b : Prop) (a : Prop) : term301 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3375876 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : term302 A _35369 t _35368.
Proof. exact (@lem3375875 (t _35369) (t _35368)). Qed.
Lemma lem3375877 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) (h1 : _35368 = _35369) : term303 A _35369 t _35368.
Proof. exact (@lem3375876 A _35369 t _35368 (@lem3375873 A t _35368 _35369 h1)). Qed.
Lemma lem3375878 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : term304 A _35369 t _35368.
Proof. exact (fun h0 : _35368 = _35369 => @lem3375877 A t _35368 _35369 h0). Qed.
Lemma lem3375880 (a : Prop) (b : Prop) : (a -> b) = (term305 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3375881 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : (term304 A _35369 t _35368) = (term306 A _35369 t _35368).
Proof. exact (@lem3375880 (_35368 = _35369) (term303 A _35369 t _35368)). Qed.
Lemma lem3375882 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : term306 A _35369 t _35368.
Proof. exact (EQ_MP (@lem3375881 A _35369 t _35368) (@lem3375878 A _35369 t _35368)). Qed.
Lemma lem3375892 {B : Type'} (x : B) (y : B) (z : B) : term307 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3375894 {A : Type'} (x : A) (y : A) (z : A) : term307 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem3375896 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : s x'.
Proof. exact (proj1 (@lem3375260 A B x' s x f t x'' h1)). Qed.
Lemma lem3375897 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term292 A s x'.
Proof. exact (fun h0 : term52 A s x' => @lem3375896 A B x' s x f t x'' h1). Qed.
Lemma lem3375899 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3375900 {A : Type'} (s : A -> Prop) (x' : A) : (term292 A s x') = (s x').
Proof. exact (@lem3375899 (s x')). Qed.
Lemma lem3375901 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : s x'.
Proof. exact (EQ_MP (@lem3375900 A s x') (@lem3375897 A B x' s x f t x'' h1)). Qed.
Lemma lem3375903 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : t x''.
Proof. exact (proj2 (@lem3375265 A B x f t x'' h1)). Qed.
Lemma lem3375904 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : term292 A t x''.
Proof. exact (fun h0 : term52 A t x'' => @lem3375903 A B x f t x'' h1). Qed.
Lemma lem3375906 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3375907 {A : Type'} (t : A -> Prop) (x'' : A) : (term292 A t x'') = (t x'').
Proof. exact (@lem3375906 (t x'')). Qed.
Lemma lem3375908 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3375907 A t x'') (@lem3375904 A B x f t x'' h1)). Qed.
Lemma lem3375910 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : (f x'') = (f x').
Proof. exact (EQ_MP (@lem3375674 A B x' x f t x'' h2) (@lem3375519 A B x' s x f t x'' h1)). Qed.
Lemma lem3375911 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : term308 A B x'' f x'.
Proof. exact (fun h0 : term270 A B x'' f x' => @lem3375910 A B x' s x f t x'' h1 h2). Qed.
Lemma lem3375913 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3375914 {A B : Type'} (x'' : A) (f : A -> B) (x' : A) : (term308 A B x'' f x') = ((f x'') = (f x')).
Proof. exact (@lem3375913 ((f x'') = (f x'))). Qed.
Lemma lem3375915 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : (f x'') = (f x').
Proof. exact (EQ_MP (@lem3375914 A B x'' f x') (@lem3375911 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3375917 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3375918 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3375917 B x). Qed.
Lemma lem3375919 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (@lem3375918 B (f x'')). Qed.
Lemma lem3375920 {A B : Type'} (f : A -> B) (x'' : A) : term289 A B f x''.
Proof. exact (fun h0 : term290 A B f x'' => @lem3375919 A B f x''). Qed.
Lemma lem3375922 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3375923 {A B : Type'} (f : A -> B) (x'' : A) : (term289 A B f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3375922 ((f x'') = (f x''))). Qed.
Lemma lem3375924 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3375923 A B f x'') (@lem3375920 A B f x'')). Qed.
Lemma lem3375942 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3375943 {B : Type'} (y : B) (x : B) (z : B) : (term309 B x y z) = (term310 B y x z).
Proof. exact (@lem3375942 (y = z) (term311 B x z)). Qed.
Lemma lem3375953 {B : Type'} (x : B) (y : B) : (term312 B x y) = (term312 B x y).
Proof. exact (eq_refl (term312 B x y)). Qed.
Lemma lem3375954 {B : Type'} (y : B) (x : B) (z : B) : (term307 B x y z) = (term313 B y x z).
Proof. exact (MK_COMB (@lem3375953 B x y) (@lem3375943 B y x z)). Qed.
Lemma lem3375958 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3375959 {B : Type'} (y : B) (x : B) (z : B) : (term313 B y x z) = (term314 B y x z).
Proof. exact (@lem3375958 (y = z) (term311 B x y) (term311 B x z)). Qed.
Lemma lem3375981 {B : Type'} (y : B) (x : B) (z : B) : (term307 B x y z) = (term314 B y x z).
Proof. exact (TRANS (@lem3375954 B y x z) (@lem3375959 B y x z)). Qed.
Lemma lem3375982 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3375983 {B : Type'} (y : B) (x : B) (z : B) : (term315 B x y z) = (term316 B y x z).
Proof. exact (MK_COMB (@lem3375982) (@lem3375981 B y x z)). Qed.
Lemma lem3376005 {B : Type'} (y : B) (x : B) (z : B) : (term314 B y x z) = (term314 B y x z).
Proof. exact (eq_refl (term314 B y x z)). Qed.
Lemma lem3376006 {B : Type'} (y : B) (x : B) (z : B) : ((term307 B x y z) = (term314 B y x z)) = ((term314 B y x z) = (term314 B y x z)).
Proof. exact (MK_COMB (@lem3375983 B y x z) (@lem3376005 B y x z)). Qed.
Lemma lem3376008 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3376009 (x : Prop) : (x = x) = True.
Proof. exact (@lem3376008 Prop x). Qed.
Lemma lem3376010 {B : Type'} (y : B) (x : B) (z : B) : ((term314 B y x z) = (term314 B y x z)) = True.
Proof. exact (@lem3376009 (term314 B y x z)). Qed.
Lemma lem3376011 {B : Type'} (y : B) (x : B) (z : B) : ((term307 B x y z) = (term314 B y x z)) = True.
Proof. exact (TRANS (@lem3376006 B y x z) (@lem3376010 B y x z)). Qed.
Lemma lem3376012 {B : Type'} (y : B) (x : B) (z : B) : True = ((term307 B x y z) = (term314 B y x z)).
Proof. exact (SYM (@lem3376011 B y x z)). Qed.
Lemma lem3376013 {B : Type'} (y : B) (x : B) (z : B) : (term307 B x y z) = (term314 B y x z).
Proof. exact (EQ_MP (@lem3376012 B y x z) (@lem0)). Qed.
Lemma lem3376014 {B : Type'} (y : B) (x : B) (z : B) : term314 B y x z.
Proof. exact (EQ_MP (@lem3376013 B y x z) (@lem3375892 B x y z)). Qed.
Lemma lem3376016 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3376017 {B : Type'} (x : B) (y : B) (z : B) : (term314 B y x z) = (term318 B x y z).
Proof. exact (@lem3376016 (term319 B y x z) (y = z)). Qed.
Lemma lem3376019 (a : Prop) (b : Prop) : (term320 a b) = (term321 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3376020 {B : Type'} (y : B) (x : B) (z : B) : (term322 B y x z) = (term323 B y x z).
Proof. exact (@lem3376019 (term311 B x y) (term311 B x z)). Qed.
Lemma lem3376022 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376023 {B : Type'} (x : B) (y : B) : (term324 B x y) = (x = y).
Proof. exact (@lem3376022 (x = y)). Qed.
Lemma lem3376024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376025 {B : Type'} (x : B) (y : B) : (term325 B x y) = (term326 B x y).
Proof. exact (MK_COMB (@lem3376024) (@lem3376023 B x y)). Qed.
Lemma lem3376027 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376028 {B : Type'} (x : B) (z : B) : (term324 B x z) = (x = z).
Proof. exact (@lem3376027 (x = z)). Qed.
Lemma lem3376029 {B : Type'} (y : B) (x : B) (z : B) : (term323 B y x z) = (term327 B y x z).
Proof. exact (MK_COMB (@lem3376025 B x y) (@lem3376028 B x z)). Qed.
Lemma lem3376030 {B : Type'} (y : B) (x : B) (z : B) : (term322 B y x z) = (term327 B y x z).
Proof. exact (TRANS (@lem3376020 B y x z) (@lem3376029 B y x z)). Qed.
Lemma lem3376031 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376032 {B : Type'} (y : B) (x : B) (z : B) : (term328 B y x z) = (term329 B y x z).
Proof. exact (MK_COMB (@lem3376031) (@lem3376030 B y x z)). Qed.
Lemma lem3376033 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3376034 {B : Type'} (x : B) (y : B) (z : B) : (term318 B x y z) = (term330 B x y z).
Proof. exact (MK_COMB (@lem3376032 B y x z) (@lem3376033 B y z)). Qed.
Lemma lem3376035 {B : Type'} (x : B) (y : B) (z : B) : (term314 B y x z) = (term330 B x y z).
Proof. exact (TRANS (@lem3376017 B x y z) (@lem3376034 B x y z)). Qed.
Lemma lem3376037 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : term331 A B x' f x''.
Proof. exact (conj (@lem3375915 A B x' s x f t x'' h1 h2) (@lem3375924 A B f x'')). Qed.
Lemma lem3376039 {B : Type'} (x : B) (y : B) (z : B) : term330 B x y z.
Proof. exact (EQ_MP (@lem3376035 B x y z) (@lem3376014 B y x z)). Qed.
Lemma lem3376040 {B : Type'} (x : B) (y : B) (z : B) : term330 B x y z.
Proof. exact (@lem3376039 B x y z). Qed.
Lemma lem3376041 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : term332 A B x' f x''.
Proof. exact (@lem3376040 B (f x'') (f x') (f x'')). Qed.
Lemma lem3376044 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : (f x') = (f x'').
Proof. exact (@lem3376041 A B x' f x'' (@lem3376037 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3376045 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : term308 A B x' f x''.
Proof. exact (fun h0 : term270 A B x' f x'' => @lem3376044 A B x' s x f t x'' h1 h2). Qed.
Lemma lem3376047 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376048 {A B : Type'} (x' : A) (f : A -> B) (x'' : A) : (term308 A B x' f x'') = ((f x') = (f x'')).
Proof. exact (@lem3376047 ((f x') = (f x''))). Qed.
Lemma lem3376049 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : (f x') = (f x'').
Proof. exact (EQ_MP (@lem3376048 A B x' f x'') (@lem3376045 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3376075 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3376076 {A B : Type'} (_35322 : A) (f : A -> B) (_35323 : A) : (term333 A B f _35322 _35323) = (term334 A B _35322 f _35323).
Proof. exact (@lem3376075 (_35322 = _35323) (term270 A B _35322 f _35323)). Qed.
Lemma lem3376086 {A : Type'} (t : A -> Prop) (_35323 : A) : (term96 A t _35323) = (term96 A t _35323).
Proof. exact (eq_refl (term96 A t _35323)). Qed.
Lemma lem3376087 {A B : Type'} (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term269 A B t f _35322 _35323) = (term335 A B t _35322 f _35323).
Proof. exact (MK_COMB (@lem3376086 A t _35323) (@lem3376076 A B _35322 f _35323)). Qed.
Lemma lem3376091 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3376092 {A B : Type'} (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term335 A B t _35322 f _35323) = (term336 A B t _35322 f _35323).
Proof. exact (@lem3376091 (_35322 = _35323) (term52 A t _35323) (term270 A B _35322 f _35323)). Qed.
Lemma lem3376112 {A B : Type'} (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term269 A B t f _35322 _35323) = (term336 A B t _35322 f _35323).
Proof. exact (TRANS (@lem3376087 A B t _35322 f _35323) (@lem3376092 A B t _35322 f _35323)). Qed.
Lemma lem3376113 {A : Type'} (s : A -> Prop) (_35322 : A) : (term96 A s _35322) = (term96 A s _35322).
Proof. exact (eq_refl (term96 A s _35322)). Qed.
Lemma lem3376114 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term271 A B s t f _35322 _35323) = (term337 A B s t _35322 f _35323).
Proof. exact (MK_COMB (@lem3376113 A s _35322) (@lem3376112 A B t _35322 f _35323)). Qed.
Lemma lem3376118 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3376119 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term337 A B s t _35322 f _35323) = (term338 A B s t _35322 f _35323).
Proof. exact (@lem3376118 (_35322 = _35323) (term52 A s _35322) (term95 A B t _35322 f _35323)). Qed.
Lemma lem3376149 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term271 A B s t f _35322 _35323) = (term338 A B s t _35322 f _35323).
Proof. exact (TRANS (@lem3376114 A B s t _35322 f _35323) (@lem3376119 A B s t _35322 f _35323)). Qed.
Lemma lem3376150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3376151 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term339 A B s t f _35322 _35323) = (term340 A B s t _35322 f _35323).
Proof. exact (MK_COMB (@lem3376150) (@lem3376149 A B s t _35322 f _35323)). Qed.
Lemma lem3376181 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term338 A B s t _35322 f _35323) = (term338 A B s t _35322 f _35323).
Proof. exact (eq_refl (term338 A B s t _35322 f _35323)). Qed.
Lemma lem3376182 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : ((term271 A B s t f _35322 _35323) = (term338 A B s t _35322 f _35323)) = ((term338 A B s t _35322 f _35323) = (term338 A B s t _35322 f _35323)).
Proof. exact (MK_COMB (@lem3376151 A B s t _35322 f _35323) (@lem3376181 A B s t _35322 f _35323)). Qed.
Lemma lem3376184 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3376185 (x : Prop) : (x = x) = True.
Proof. exact (@lem3376184 Prop x). Qed.
Lemma lem3376186 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : ((term338 A B s t _35322 f _35323) = (term338 A B s t _35322 f _35323)) = True.
Proof. exact (@lem3376185 (term338 A B s t _35322 f _35323)). Qed.
Lemma lem3376187 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : ((term271 A B s t f _35322 _35323) = (term338 A B s t _35322 f _35323)) = True.
Proof. exact (TRANS (@lem3376182 A B s t _35322 f _35323) (@lem3376186 A B s t _35322 f _35323)). Qed.
Lemma lem3376188 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : True = ((term271 A B s t f _35322 _35323) = (term338 A B s t _35322 f _35323)).
Proof. exact (SYM (@lem3376187 A B s t _35322 f _35323)). Qed.
Lemma lem3376189 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term271 A B s t f _35322 _35323) = (term338 A B s t _35322 f _35323).
Proof. exact (EQ_MP (@lem3376188 A B s t _35322 f _35323) (@lem0)). Qed.
Lemma lem3376190 {A B : Type'} (_35322 : A) (_35323 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term338 A B s t _35322 f _35323.
Proof. exact (EQ_MP (@lem3376189 A B s t _35322 f _35323) (@lem3375662 A B _35322 _35323 s t f h1)). Qed.
Lemma lem3376192 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3376193 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term338 A B s t _35322 f _35323) = (term341 A B s t f _35322 _35323).
Proof. exact (@lem3376192 (term98 A B s t _35322 f _35323) (_35322 = _35323)). Qed.
Lemma lem3376195 (a : Prop) (b : Prop) : (term320 a b) = (term321 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3376196 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term342 A B s t _35322 f _35323) = (term343 A B s t _35322 f _35323).
Proof. exact (@lem3376195 (term52 A s _35322) (term95 A B t _35322 f _35323)). Qed.
Lemma lem3376198 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376199 {A : Type'} (s : A -> Prop) (_35322 : A) : (term108 A s _35322) = (s _35322).
Proof. exact (@lem3376198 (s _35322)). Qed.
Lemma lem3376200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376201 {A : Type'} (s : A -> Prop) (_35322 : A) : (term344 A s _35322) = (term27 A s _35322).
Proof. exact (MK_COMB (@lem3376200) (@lem3376199 A s _35322)). Qed.
Lemma lem3376203 (a : Prop) (b : Prop) : (term320 a b) = (term321 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3376204 {A B : Type'} (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term345 A B t _35322 f _35323) = (term346 A B t _35322 f _35323).
Proof. exact (@lem3376203 (term52 A t _35323) (term270 A B _35322 f _35323)). Qed.
Lemma lem3376206 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376207 {A : Type'} (t : A -> Prop) (_35323 : A) : (term108 A t _35323) = (t _35323).
Proof. exact (@lem3376206 (t _35323)). Qed.
Lemma lem3376208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376209 {A : Type'} (t : A -> Prop) (_35323 : A) : (term344 A t _35323) = (term27 A t _35323).
Proof. exact (MK_COMB (@lem3376208) (@lem3376207 A t _35323)). Qed.
Lemma lem3376211 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376212 {A B : Type'} (_35322 : A) (f : A -> B) (_35323 : A) : (term347 A B _35322 f _35323) = ((f _35322) = (f _35323)).
Proof. exact (@lem3376211 ((f _35322) = (f _35323))). Qed.
Lemma lem3376213 {A B : Type'} (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term346 A B t _35322 f _35323) = (term29 A B t _35322 f _35323).
Proof. exact (MK_COMB (@lem3376209 A t _35323) (@lem3376212 A B _35322 f _35323)). Qed.
Lemma lem3376214 {A B : Type'} (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term345 A B t _35322 f _35323) = (term29 A B t _35322 f _35323).
Proof. exact (TRANS (@lem3376204 A B t _35322 f _35323) (@lem3376213 A B t _35322 f _35323)). Qed.
Lemma lem3376215 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term343 A B s t _35322 f _35323) = (term31 A B s t _35322 f _35323).
Proof. exact (MK_COMB (@lem3376201 A s _35322) (@lem3376214 A B t _35322 f _35323)). Qed.
Lemma lem3376216 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term342 A B s t _35322 f _35323) = (term31 A B s t _35322 f _35323).
Proof. exact (TRANS (@lem3376196 A B s t _35322 f _35323) (@lem3376215 A B s t _35322 f _35323)). Qed.
Lemma lem3376217 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376218 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (_35322 : A) (f : A -> B) (_35323 : A) : (term348 A B s t _35322 f _35323) = (term33 A B s t _35322 f _35323).
Proof. exact (MK_COMB (@lem3376217) (@lem3376216 A B s t _35322 f _35323)). Qed.
Lemma lem3376219 {A : Type'} (_35322 : A) (_35323 : A) : (_35322 = _35323) = (_35322 = _35323).
Proof. exact (eq_refl (_35322 = _35323)). Qed.
Lemma lem3376220 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term341 A B s t f _35322 _35323) = (term35 A B s t f _35322 _35323).
Proof. exact (MK_COMB (@lem3376218 A B s t _35322 f _35323) (@lem3376219 A _35322 _35323)). Qed.
Lemma lem3376221 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_35322 : A) (_35323 : A) : (term338 A B s t _35322 f _35323) = (term35 A B s t f _35322 _35323).
Proof. exact (TRANS (@lem3376193 A B s t f _35322 _35323) (@lem3376220 A B s t f _35322 _35323)). Qed.
Lemma lem3376223 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : term29 A B t x' f x''.
Proof. exact (conj (@lem3375908 A B x f t x'' h2) (@lem3376049 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3376224 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') (h2 : term65 A B x f t x'') : term31 A B s t x' f x''.
Proof. exact (conj (@lem3375901 A B x' s x f t x'' h1) (@lem3376223 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3376226 {A B : Type'} (_35322 : A) (_35323 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term35 A B s t f _35322 _35323.
Proof. exact (EQ_MP (@lem3376221 A B s t f _35322 _35323) (@lem3376190 A B _35322 _35323 s t f h1)). Qed.
Lemma lem3376227 {A B : Type'} (_35322 : A) (_35323 : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term35 A B s t f _35322 _35323.
Proof. exact (@lem3376226 A B _35322 _35323 s t f h1). Qed.
Lemma lem3376228 {A B : Type'} (x' : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term35 A B s t f x' x''.
Proof. exact (@lem3376227 A B x' x'' s t f h1). Qed.
Lemma lem3376231 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : x' = x''.
Proof. exact (@lem3376228 A B x' x'' s t f h1 (@lem3376224 A B x' s x f t x'' h2 h3)). Qed.
Lemma lem3376232 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : term349 A x' x''.
Proof. exact (fun h0 : term311 A x' x'' => @lem3376231 A B x' s x f t x'' h1 h2 h3). Qed.
Lemma lem3376234 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376235 {A : Type'} (x' : A) (x'' : A) : (term349 A x' x'') = (x' = x'').
Proof. exact (@lem3376234 (x' = x'')). Qed.
Lemma lem3376236 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : x' = x''.
Proof. exact (EQ_MP (@lem3376235 A x' x'') (@lem3376232 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3376238 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3376239 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3376238 A x). Qed.
Lemma lem3376240 {A : Type'} (x' : A) : x' = x'.
Proof. exact (@lem3376239 A x'). Qed.
Lemma lem3376241 {A : Type'} (x' : A) : term350 A x'.
Proof. exact (fun h0 : term351 A x' => @lem3376240 A x'). Qed.
Lemma lem3376243 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376244 {A : Type'} (x' : A) : (term350 A x') = (x' = x').
Proof. exact (@lem3376243 (x' = x')). Qed.
Lemma lem3376245 {A : Type'} (x' : A) : x' = x'.
Proof. exact (EQ_MP (@lem3376244 A x') (@lem3376241 A x')). Qed.
Lemma lem3376263 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3376264 {A : Type'} (y : A) (x : A) (z : A) : (term309 A x y z) = (term310 A y x z).
Proof. exact (@lem3376263 (y = z) (term311 A x z)). Qed.
Lemma lem3376274 {A : Type'} (x : A) (y : A) : (term312 A x y) = (term312 A x y).
Proof. exact (eq_refl (term312 A x y)). Qed.
Lemma lem3376275 {A : Type'} (y : A) (x : A) (z : A) : (term307 A x y z) = (term313 A y x z).
Proof. exact (MK_COMB (@lem3376274 A x y) (@lem3376264 A y x z)). Qed.
Lemma lem3376279 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3376280 {A : Type'} (y : A) (x : A) (z : A) : (term313 A y x z) = (term314 A y x z).
Proof. exact (@lem3376279 (y = z) (term311 A x y) (term311 A x z)). Qed.
Lemma lem3376302 {A : Type'} (y : A) (x : A) (z : A) : (term307 A x y z) = (term314 A y x z).
Proof. exact (TRANS (@lem3376275 A y x z) (@lem3376280 A y x z)). Qed.
Lemma lem3376303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3376304 {A : Type'} (y : A) (x : A) (z : A) : (term315 A x y z) = (term316 A y x z).
Proof. exact (MK_COMB (@lem3376303) (@lem3376302 A y x z)). Qed.
Lemma lem3376326 {A : Type'} (y : A) (x : A) (z : A) : (term314 A y x z) = (term314 A y x z).
Proof. exact (eq_refl (term314 A y x z)). Qed.
Lemma lem3376327 {A : Type'} (y : A) (x : A) (z : A) : ((term307 A x y z) = (term314 A y x z)) = ((term314 A y x z) = (term314 A y x z)).
Proof. exact (MK_COMB (@lem3376304 A y x z) (@lem3376326 A y x z)). Qed.
Lemma lem3376329 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3376330 (x : Prop) : (x = x) = True.
Proof. exact (@lem3376329 Prop x). Qed.
Lemma lem3376331 {A : Type'} (y : A) (x : A) (z : A) : ((term314 A y x z) = (term314 A y x z)) = True.
Proof. exact (@lem3376330 (term314 A y x z)). Qed.
Lemma lem3376332 {A : Type'} (y : A) (x : A) (z : A) : ((term307 A x y z) = (term314 A y x z)) = True.
Proof. exact (TRANS (@lem3376327 A y x z) (@lem3376331 A y x z)). Qed.
Lemma lem3376333 {A : Type'} (y : A) (x : A) (z : A) : True = ((term307 A x y z) = (term314 A y x z)).
Proof. exact (SYM (@lem3376332 A y x z)). Qed.
Lemma lem3376334 {A : Type'} (y : A) (x : A) (z : A) : (term307 A x y z) = (term314 A y x z).
Proof. exact (EQ_MP (@lem3376333 A y x z) (@lem0)). Qed.
Lemma lem3376335 {A : Type'} (y : A) (x : A) (z : A) : term314 A y x z.
Proof. exact (EQ_MP (@lem3376334 A y x z) (@lem3375894 A x y z)). Qed.
Lemma lem3376337 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3376338 {A : Type'} (x : A) (y : A) (z : A) : (term314 A y x z) = (term318 A x y z).
Proof. exact (@lem3376337 (term319 A y x z) (y = z)). Qed.
Lemma lem3376340 (a : Prop) (b : Prop) : (term320 a b) = (term321 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3376341 {A : Type'} (y : A) (x : A) (z : A) : (term322 A y x z) = (term323 A y x z).
Proof. exact (@lem3376340 (term311 A x y) (term311 A x z)). Qed.
Lemma lem3376343 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376344 {A : Type'} (x : A) (y : A) : (term324 A x y) = (x = y).
Proof. exact (@lem3376343 (x = y)). Qed.
Lemma lem3376345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376346 {A : Type'} (x : A) (y : A) : (term325 A x y) = (term326 A x y).
Proof. exact (MK_COMB (@lem3376345) (@lem3376344 A x y)). Qed.
Lemma lem3376348 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376349 {A : Type'} (x : A) (z : A) : (term324 A x z) = (x = z).
Proof. exact (@lem3376348 (x = z)). Qed.
Lemma lem3376350 {A : Type'} (y : A) (x : A) (z : A) : (term323 A y x z) = (term327 A y x z).
Proof. exact (MK_COMB (@lem3376346 A x y) (@lem3376349 A x z)). Qed.
Lemma lem3376351 {A : Type'} (y : A) (x : A) (z : A) : (term322 A y x z) = (term327 A y x z).
Proof. exact (TRANS (@lem3376341 A y x z) (@lem3376350 A y x z)). Qed.
Lemma lem3376352 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376353 {A : Type'} (y : A) (x : A) (z : A) : (term328 A y x z) = (term329 A y x z).
Proof. exact (MK_COMB (@lem3376352) (@lem3376351 A y x z)). Qed.
Lemma lem3376354 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3376355 {A : Type'} (x : A) (y : A) (z : A) : (term318 A x y z) = (term330 A x y z).
Proof. exact (MK_COMB (@lem3376353 A y x z) (@lem3376354 A y z)). Qed.
Lemma lem3376356 {A : Type'} (x : A) (y : A) (z : A) : (term314 A y x z) = (term330 A x y z).
Proof. exact (TRANS (@lem3376338 A x y z) (@lem3376355 A x y z)). Qed.
Lemma lem3376358 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : term352 A x'' x'.
Proof. exact (conj (@lem3376236 A B x' s x f t x'' h1 h2 h3) (@lem3376245 A x')). Qed.
Lemma lem3376360 {A : Type'} (x : A) (y : A) (z : A) : term330 A x y z.
Proof. exact (EQ_MP (@lem3376356 A x y z) (@lem3376335 A y x z)). Qed.
Lemma lem3376361 {A : Type'} (x : A) (y : A) (z : A) : term330 A x y z.
Proof. exact (@lem3376360 A x y z). Qed.
Lemma lem3376362 {A : Type'} (x'' : A) (x' : A) : term353 A x'' x'.
Proof. exact (@lem3376361 A x' x'' x'). Qed.
Lemma lem3376365 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : x'' = x'.
Proof. exact (@lem3376362 A x'' x' (@lem3376358 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3376366 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : term349 A x'' x'.
Proof. exact (fun h0 : term311 A x'' x' => @lem3376365 A B x' s x f t x'' h1 h2 h3). Qed.
Lemma lem3376368 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376369 {A : Type'} (x'' : A) (x' : A) : (term349 A x'' x') = (x'' = x').
Proof. exact (@lem3376368 (x'' = x')). Qed.
Lemma lem3376370 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : x'' = x'.
Proof. exact (EQ_MP (@lem3376369 A x'' x') (@lem3376366 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3376372 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : t x''.
Proof. exact (proj2 (@lem3375265 A B x f t x'' h1)). Qed.
Lemma lem3376373 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : term292 A t x''.
Proof. exact (fun h0 : term52 A t x'' => @lem3376372 A B x f t x'' h1). Qed.
Lemma lem3376375 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376376 {A : Type'} (t : A -> Prop) (x'' : A) : (term292 A t x'') = (t x'').
Proof. exact (@lem3376375 (t x'')). Qed.
Lemma lem3376377 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term65 A B x f t x'') : t x''.
Proof. exact (EQ_MP (@lem3376376 A t x'') (@lem3376373 A B x f t x'' h1)). Qed.
Lemma lem3376383 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3376384 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : (term306 A _35369 t _35368) = (term354 A _35369 t _35368).
Proof. exact (@lem3376383 (t _35369) (term311 A _35368 _35369) (term52 A t _35368)). Qed.
Lemma lem3376398 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3376399 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : (term355 A _35369 t _35368) = (term356 A t _35368 _35369).
Proof. exact (@lem3376398 (term52 A t _35368) (term311 A _35368 _35369)). Qed.
Lemma lem3376407 {A : Type'} (t : A -> Prop) (_35369 : A) : (term357 A t _35369) = (term357 A t _35369).
Proof. exact (eq_refl (term357 A t _35369)). Qed.
Lemma lem3376408 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : (term354 A _35369 t _35368) = (term358 A t _35368 _35369).
Proof. exact (MK_COMB (@lem3376407 A t _35369) (@lem3376399 A t _35368 _35369)). Qed.
Lemma lem3376419 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : (term306 A _35369 t _35368) = (term358 A t _35368 _35369).
Proof. exact (TRANS (@lem3376384 A _35369 t _35368) (@lem3376408 A t _35368 _35369)). Qed.
Lemma lem3376420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3376421 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : (term359 A _35369 t _35368) = (term360 A t _35368 _35369).
Proof. exact (MK_COMB (@lem3376420) (@lem3376419 A t _35368 _35369)). Qed.
Lemma lem3376435 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3376436 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : (term355 A _35369 t _35368) = (term356 A t _35368 _35369).
Proof. exact (@lem3376435 (term52 A t _35368) (term311 A _35368 _35369)). Qed.
Lemma lem3376444 {A : Type'} (t : A -> Prop) (_35369 : A) : (term357 A t _35369) = (term357 A t _35369).
Proof. exact (eq_refl (term357 A t _35369)). Qed.
Lemma lem3376445 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : (term354 A _35369 t _35368) = (term358 A t _35368 _35369).
Proof. exact (MK_COMB (@lem3376444 A t _35369) (@lem3376436 A t _35368 _35369)). Qed.
Lemma lem3376456 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : ((term306 A _35369 t _35368) = (term354 A _35369 t _35368)) = ((term358 A t _35368 _35369) = (term358 A t _35368 _35369)).
Proof. exact (MK_COMB (@lem3376421 A t _35368 _35369) (@lem3376445 A t _35368 _35369)). Qed.
Lemma lem3376458 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3376459 (x : Prop) : (x = x) = True.
Proof. exact (@lem3376458 Prop x). Qed.
Lemma lem3376460 {A : Type'} (t : A -> Prop) (_35368 : A) (_35369 : A) : ((term358 A t _35368 _35369) = (term358 A t _35368 _35369)) = True.
Proof. exact (@lem3376459 (term358 A t _35368 _35369)). Qed.
Lemma lem3376461 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : ((term306 A _35369 t _35368) = (term354 A _35369 t _35368)) = True.
Proof. exact (TRANS (@lem3376456 A t _35368 _35369) (@lem3376460 A t _35368 _35369)). Qed.
Lemma lem3376462 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : True = ((term306 A _35369 t _35368) = (term354 A _35369 t _35368)).
Proof. exact (SYM (@lem3376461 A _35369 t _35368)). Qed.
Lemma lem3376463 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : (term306 A _35369 t _35368) = (term354 A _35369 t _35368).
Proof. exact (EQ_MP (@lem3376462 A _35369 t _35368) (@lem0)). Qed.
Lemma lem3376464 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : term354 A _35369 t _35368.
Proof. exact (EQ_MP (@lem3376463 A _35369 t _35368) (@lem3375882 A _35369 t _35368)). Qed.
Lemma lem3376466 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3376467 {A : Type'} (_35368 : A) (t : A -> Prop) (_35369 : A) : (term354 A _35369 t _35368) = (term361 A _35368 t _35369).
Proof. exact (@lem3376466 (term355 A _35369 t _35368) (t _35369)). Qed.
Lemma lem3376469 (a : Prop) (b : Prop) : (term320 a b) = (term321 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3376470 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : (term362 A _35369 t _35368) = (term363 A _35369 t _35368).
Proof. exact (@lem3376469 (term311 A _35368 _35369) (term52 A t _35368)). Qed.
Lemma lem3376472 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376473 {A : Type'} (_35368 : A) (_35369 : A) : (term324 A _35368 _35369) = (_35368 = _35369).
Proof. exact (@lem3376472 (_35368 = _35369)). Qed.
Lemma lem3376474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376475 {A : Type'} (_35368 : A) (_35369 : A) : (term325 A _35368 _35369) = (term326 A _35368 _35369).
Proof. exact (MK_COMB (@lem3376474) (@lem3376473 A _35368 _35369)). Qed.
Lemma lem3376477 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376478 {A : Type'} (t : A -> Prop) (_35368 : A) : (term108 A t _35368) = (t _35368).
Proof. exact (@lem3376477 (t _35368)). Qed.
Lemma lem3376479 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : (term363 A _35369 t _35368) = (term364 A _35369 t _35368).
Proof. exact (MK_COMB (@lem3376475 A _35368 _35369) (@lem3376478 A t _35368)). Qed.
Lemma lem3376480 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : (term362 A _35369 t _35368) = (term364 A _35369 t _35368).
Proof. exact (TRANS (@lem3376470 A _35369 t _35368) (@lem3376479 A _35369 t _35368)). Qed.
Lemma lem3376481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376482 {A : Type'} (_35369 : A) (t : A -> Prop) (_35368 : A) : (term365 A _35369 t _35368) = (term366 A _35369 t _35368).
Proof. exact (MK_COMB (@lem3376481) (@lem3376480 A _35369 t _35368)). Qed.
Lemma lem3376483 {A : Type'} (t : A -> Prop) (_35369 : A) : (t _35369) = (t _35369).
Proof. exact (eq_refl (t _35369)). Qed.
Lemma lem3376484 {A : Type'} (_35368 : A) (t : A -> Prop) (_35369 : A) : (term361 A _35368 t _35369) = (term367 A _35368 t _35369).
Proof. exact (MK_COMB (@lem3376482 A _35369 t _35368) (@lem3376483 A t _35369)). Qed.
Lemma lem3376485 {A : Type'} (_35368 : A) (t : A -> Prop) (_35369 : A) : (term354 A _35369 t _35368) = (term367 A _35368 t _35369).
Proof. exact (TRANS (@lem3376467 A _35368 t _35369) (@lem3376484 A _35368 t _35369)). Qed.
Lemma lem3376487 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : term364 A x' t x''.
Proof. exact (conj (@lem3376370 A B x' s x f t x'' h1 h2 h3) (@lem3376377 A B x f t x'' h3)). Qed.
Lemma lem3376489 {A : Type'} (_35368 : A) (t : A -> Prop) (_35369 : A) : term367 A _35368 t _35369.
Proof. exact (EQ_MP (@lem3376485 A _35368 t _35369) (@lem3376464 A _35369 t _35368)). Qed.
Lemma lem3376490 {A : Type'} (_35368 : A) (t : A -> Prop) (_35369 : A) : term367 A _35368 t _35369.
Proof. exact (@lem3376489 A _35368 t _35369). Qed.
Lemma lem3376491 {A : Type'} (x'' : A) (t : A -> Prop) (x' : A) : term367 A x'' t x'.
Proof. exact (@lem3376490 A x'' t x'). Qed.
Lemma lem3376494 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : t x'.
Proof. exact (@lem3376491 A x'' t x' (@lem3376487 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3376495 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : term292 A t x'.
Proof. exact (fun h0 : term52 A t x' => @lem3376494 A B x' s x f t x'' h1 h2 h3). Qed.
Lemma lem3376497 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376498 {A : Type'} (t : A -> Prop) (x' : A) : (term292 A t x') = (t x').
Proof. exact (@lem3376497 (t x')). Qed.
Lemma lem3376499 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : t x'.
Proof. exact (EQ_MP (@lem3376498 A t x') (@lem3376495 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3376502 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3376504 {A : Type'} (t : A -> Prop) (x' : A) : (term52 A t x') = (term368 A t x').
Proof. exact (@lem3376502 (t x')). Qed.
Lemma lem3376507 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term191 A B x' s x f t x'') : term368 A t x'.
Proof. exact (EQ_MP (@lem3376504 A t x') (@lem3375703 A B x' s x f t x'' h1)). Qed.
Lemma lem3376510 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : False.
Proof. exact (@lem3376507 A B x' s x f t x'' h2 (@lem3376499 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3376511 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : term300.
Proof. exact (fun h0 : ~ False => @lem3376510 A B x' s x f t x'' h1 h2 h3). Qed.
Lemma lem3376513 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376514 : term300 = False.
Proof. exact (@lem3376513 False). Qed.
Lemma lem3376553 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3376554 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3376553 B x). Qed.
Lemma lem3376555 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3376554 B (f x')). Qed.
Lemma lem3376556 {A B : Type'} (f : A -> B) (x' : A) : term289 A B f x'.
Proof. exact (fun h0 : term290 A B f x' => @lem3376555 A B f x'). Qed.
Lemma lem3376558 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376559 {A B : Type'} (f : A -> B) (x' : A) : (term289 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3376558 ((f x') = (f x'))). Qed.
Lemma lem3376560 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3376559 A B f x') (@lem3376556 A B f x')). Qed.
Lemma lem3376562 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3376563 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3376562 B x). Qed.
Lemma lem3376564 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3376563 B (f x')). Qed.
Lemma lem3376565 {A B : Type'} (f : A -> B) (x' : A) : term289 A B f x'.
Proof. exact (fun h0 : term290 A B f x' => @lem3376564 A B f x'). Qed.
Lemma lem3376567 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376568 {A B : Type'} (f : A -> B) (x' : A) : (term289 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3376567 ((f x') = (f x'))). Qed.
Lemma lem3376569 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3376568 A B f x') (@lem3376565 A B f x')). Qed.
Lemma lem3376571 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : s x'.
Proof. exact (proj2 (@lem3375271 A B s x' x f t h1)). Qed.
Lemma lem3376572 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term292 A s x'.
Proof. exact (fun h0 : term52 A s x' => @lem3376571 A B s x' x f t h1). Qed.
Lemma lem3376574 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376575 {A : Type'} (s : A -> Prop) (x' : A) : (term292 A s x') = (s x').
Proof. exact (@lem3376574 (s x')). Qed.
Lemma lem3376576 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : s x'.
Proof. exact (EQ_MP (@lem3376575 A s x') (@lem3376572 A B s x' x f t h1)). Qed.
Lemma lem3376582 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3376583 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (t : A -> Prop) (_35326 : A) : (term286 A B x' f s t _35326) = (term369 A B s x' f t _35326).
Proof. exact (@lem3376582 (term52 A s _35326) (term270 A B x' f _35326) (t _35326)). Qed.
Lemma lem3376597 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3376598 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term370 A B x' f t _35326) = (term371 A B t x' f _35326).
Proof. exact (@lem3376597 (t _35326) (term270 A B x' f _35326)). Qed.
Lemma lem3376606 {A : Type'} (s : A -> Prop) (_35326 : A) : (term96 A s _35326) = (term96 A s _35326).
Proof. exact (eq_refl (term96 A s _35326)). Qed.
Lemma lem3376607 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term369 A B s x' f t _35326) = (term372 A B s t x' f _35326).
Proof. exact (MK_COMB (@lem3376606 A s _35326) (@lem3376598 A B t x' f _35326)). Qed.
Lemma lem3376611 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3376612 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term372 A B s t x' f _35326) = (term373 A B t s x' f _35326).
Proof. exact (@lem3376611 (t _35326) (term52 A s _35326) (term270 A B x' f _35326)). Qed.
Lemma lem3376630 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term369 A B s x' f t _35326) = (term373 A B t s x' f _35326).
Proof. exact (TRANS (@lem3376607 A B s t x' f _35326) (@lem3376612 A B t s x' f _35326)). Qed.
Lemma lem3376631 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term286 A B x' f s t _35326) = (term373 A B t s x' f _35326).
Proof. exact (TRANS (@lem3376583 A B s x' f t _35326) (@lem3376630 A B t s x' f _35326)). Qed.
Lemma lem3376632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3376633 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term374 A B x' f s t _35326) = (term375 A B t s x' f _35326).
Proof. exact (MK_COMB (@lem3376632) (@lem3376631 A B t s x' f _35326)). Qed.
Lemma lem3376647 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3376648 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term275 A B x' f s _35326) = (term95 A B s x' f _35326).
Proof. exact (@lem3376647 (term52 A s _35326) (term270 A B x' f _35326)). Qed.
Lemma lem3376656 {A : Type'} (t : A -> Prop) (_35326 : A) : (term357 A t _35326) = (term357 A t _35326).
Proof. exact (eq_refl (term357 A t _35326)). Qed.
Lemma lem3376657 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : (term376 A B t x' f s _35326) = (term373 A B t s x' f _35326).
Proof. exact (MK_COMB (@lem3376656 A t _35326) (@lem3376648 A B s x' f _35326)). Qed.
Lemma lem3376668 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : ((term286 A B x' f s t _35326) = (term376 A B t x' f s _35326)) = ((term373 A B t s x' f _35326) = (term373 A B t s x' f _35326)).
Proof. exact (MK_COMB (@lem3376633 A B t s x' f _35326) (@lem3376657 A B t s x' f _35326)). Qed.
Lemma lem3376670 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3376671 (x : Prop) : (x = x) = True.
Proof. exact (@lem3376670 Prop x). Qed.
Lemma lem3376672 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (f : A -> B) (_35326 : A) : ((term373 A B t s x' f _35326) = (term373 A B t s x' f _35326)) = True.
Proof. exact (@lem3376671 (term373 A B t s x' f _35326)). Qed.
Lemma lem3376673 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_35326 : A) : ((term286 A B x' f s t _35326) = (term376 A B t x' f s _35326)) = True.
Proof. exact (TRANS (@lem3376668 A B t s x' f _35326) (@lem3376672 A B t s x' f _35326)). Qed.
Lemma lem3376674 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_35326 : A) : True = ((term286 A B x' f s t _35326) = (term376 A B t x' f s _35326)).
Proof. exact (SYM (@lem3376673 A B t x' f s _35326)). Qed.
Lemma lem3376675 {A B : Type'} (t : A -> Prop) (x' : A) (f : A -> B) (s : A -> Prop) (_35326 : A) : (term286 A B x' f s t _35326) = (term376 A B t x' f s _35326).
Proof. exact (EQ_MP (@lem3376674 A B t x' f s _35326) (@lem0)). Qed.
Lemma lem3376676 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term376 A B t x' f s _35326.
Proof. exact (EQ_MP (@lem3376675 A B t x' f s _35326) (@lem3375758 A B _35326 s x' x f t h1)). Qed.
Lemma lem3376678 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3376679 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term376 A B t x' f s _35326) = (term377 A B x' f s t _35326).
Proof. exact (@lem3376678 (term275 A B x' f s _35326) (t _35326)). Qed.
Lemma lem3376681 (a : Prop) (b : Prop) : (term320 a b) = (term321 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3376682 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35326 : A) : (term378 A B x' f s _35326) = (term379 A B x' f s _35326).
Proof. exact (@lem3376681 (term270 A B x' f _35326) (term52 A s _35326)). Qed.
Lemma lem3376684 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376685 {A B : Type'} (x' : A) (f : A -> B) (_35326 : A) : (term347 A B x' f _35326) = ((f x') = (f _35326)).
Proof. exact (@lem3376684 ((f x') = (f _35326))). Qed.
Lemma lem3376686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3376687 {A B : Type'} (x' : A) (f : A -> B) (_35326 : A) : (term380 A B x' f _35326) = (term381 A B x' f _35326).
Proof. exact (MK_COMB (@lem3376686) (@lem3376685 A B x' f _35326)). Qed.
Lemma lem3376689 (a : Prop) : (term91 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3376690 {A : Type'} (s : A -> Prop) (_35326 : A) : (term108 A s _35326) = (s _35326).
Proof. exact (@lem3376689 (s _35326)). Qed.
Lemma lem3376691 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35326 : A) : (term379 A B x' f s _35326) = (term297 A B x' f s _35326).
Proof. exact (MK_COMB (@lem3376687 A B x' f _35326) (@lem3376690 A s _35326)). Qed.
Lemma lem3376692 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35326 : A) : (term378 A B x' f s _35326) = (term297 A B x' f s _35326).
Proof. exact (TRANS (@lem3376682 A B x' f s _35326) (@lem3376691 A B x' f s _35326)). Qed.
Lemma lem3376693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3376694 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_35326 : A) : (term382 A B x' f s _35326) = (term383 A B x' f s _35326).
Proof. exact (MK_COMB (@lem3376693) (@lem3376692 A B x' f s _35326)). Qed.
Lemma lem3376695 {A : Type'} (t : A -> Prop) (_35326 : A) : (t _35326) = (t _35326).
Proof. exact (eq_refl (t _35326)). Qed.
Lemma lem3376696 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term377 A B x' f s t _35326) = (term384 A B x' f s t _35326).
Proof. exact (MK_COMB (@lem3376694 A B x' f s _35326) (@lem3376695 A t _35326)). Qed.
Lemma lem3376697 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (_35326 : A) : (term376 A B t x' f s _35326) = (term384 A B x' f s t _35326).
Proof. exact (TRANS (@lem3376679 A B x' f s t _35326) (@lem3376696 A B x' f s t _35326)). Qed.
Lemma lem3376699 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term298 A B f s x'.
Proof. exact (conj (@lem3376569 A B f x') (@lem3376576 A B s x' x f t h1)). Qed.
Lemma lem3376701 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term384 A B x' f s t _35326.
Proof. exact (EQ_MP (@lem3376697 A B x' f s t _35326) (@lem3376676 A B _35326 s x' x f t h1)). Qed.
Lemma lem3376702 {A B : Type'} (_35326 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term384 A B x' f s t _35326.
Proof. exact (@lem3376701 A B _35326 s x' x f t h1). Qed.
Lemma lem3376703 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term385 A B f s t x'.
Proof. exact (@lem3376702 A B x' s x' x f t h1). Qed.
Lemma lem3376706 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : t x'.
Proof. exact (@lem3376703 A B s x' x f t h1 (@lem3376699 A B s x' x f t h1)). Qed.
Lemma lem3376707 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term292 A t x'.
Proof. exact (fun h0 : term52 A t x' => @lem3376706 A B s x' x f t h1). Qed.
Lemma lem3376709 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376710 {A : Type'} (t : A -> Prop) (x' : A) : (term292 A t x') = (t x').
Proof. exact (@lem3376709 (t x')). Qed.
Lemma lem3376711 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : t x'.
Proof. exact (EQ_MP (@lem3376710 A t x') (@lem3376707 A B s x' x f t h1)). Qed.
Lemma lem3376713 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3376714 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term275 A B x' f t _35327) = (term295 A B x' f t _35327).
Proof. exact (@lem3376713 ((f x') = (f _35327)) (t _35327)). Qed.
Lemma lem3376716 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3376717 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term295 A B x' f t _35327) = (term296 A B x' f t _35327).
Proof. exact (@lem3376716 (term297 A B x' f t _35327)). Qed.
Lemma lem3376718 {A B : Type'} (x' : A) (f : A -> B) (t : A -> Prop) (_35327 : A) : (term275 A B x' f t _35327) = (term296 A B x' f t _35327).
Proof. exact (TRANS (@lem3376714 A B x' f t _35327) (@lem3376717 A B x' f t _35327)). Qed.
Lemma lem3376720 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term298 A B f t x'.
Proof. exact (conj (@lem3376560 A B f x') (@lem3376711 A B s x' x f t h1)). Qed.
Lemma lem3376722 {A B : Type'} (_35327 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term296 A B x' f t _35327.
Proof. exact (EQ_MP (@lem3376718 A B x' f t _35327) (@lem3375771 A B _35327 s x' x f t h1)). Qed.
Lemma lem3376723 {A B : Type'} (_35327 : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term296 A B x' f t _35327.
Proof. exact (@lem3376722 A B _35327 s x' x f t h1). Qed.
Lemma lem3376724 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term299 A B f t x'.
Proof. exact (@lem3376723 A B x' s x' x f t h1). Qed.
Lemma lem3376727 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : False.
Proof. exact (@lem3376724 A B s x' x f t h1 (@lem3376720 A B s x' x f t h1)). Qed.
Lemma lem3376728 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : term300.
Proof. exact (fun h0 : ~ False => @lem3376727 A B s x' x f t h1). Qed.
Lemma lem3376730 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3376731 : term300 = False.
Proof. exact (@lem3376730 False). Qed.
Lemma lem3376733 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term219 A B s x' x f t) : False.
Proof. exact (EQ_MP (@lem3376731) (@lem3376728 A B s x' x f t h1)). Qed.
Lemma lem3376734 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') (h3 : term65 A B x f t x'') : False.
Proof. exact (EQ_MP (@lem3376514) (@lem3376511 A B x' s x f t x'' h1 h2 h3)). Qed.
Lemma lem3376735 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : False.
Proof. exact (EQ_MP (@lem3375857) (@lem3375854 A B x' s x f t x'' h1 h2)). Qed.
Lemma lem3376736 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : (term132 A B x f s) = False.
Proof. exact (prop_ext (fun h3 : term132 A B x f s => @lem3376735 A B x' s x f t x'' h1 h2) (fun h3 : False => @lem3375326 A B x f s h1)). Qed.
Lemma lem3376737 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term132 A B x f s) (h2 : term191 A B x' s x f t x'') : False.
Proof. exact (EQ_MP (@lem3376736 A B x' s x f t x'' h1 h2) (@lem3375326 A B x f s h1)). Qed.
Lemma lem3376738 {A B : Type'} (x' : A) (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) (h1 : term43 A B s t f) (h2 : term191 A B x' s x f t x'') : False.
Proof. exact (or_elim (@lem3375258 A B x' s x f t x'' h2) (fun h0 : term132 A B x f s => @lem3376737 A B x' s x f t x'' h0 h2) (fun h0 : term65 A B x f t x'' => @lem3376734 A B x' s x f t x'' h1 h2 h0)). Qed.
Lemma lem3376739 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term43 A B s t f) (h2 : term257 A B x'' s x' x f t) : False.
Proof. exact (or_elim (@lem3375255 A B x'' s x' x f t h2) (fun h0 : term191 A B x' s x f t x'' => @lem3376738 A B x' s x f t x'' h1 h0) (fun h0 : term219 A B s x' x f t => @lem3376733 A B s x' x f t h0)). Qed.
Lemma lem3376740 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term43 A B s t f) (h2 : term257 A B x'' s x' x f t) : (term257 A B x'' s x' x f t) = False.
Proof. exact (prop_ext (fun h3 : term257 A B x'' s x' x f t => @lem3376739 A B x'' s x' x f t h1 h2) (fun h3 : False => @lem3375255 A B x'' s x' x f t h2)). Qed.
Lemma lem3376741 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term43 A B s t f) (h2 : term257 A B x'' s x' x f t) : False.
Proof. exact (EQ_MP (@lem3376740 A B x'' s x' x f t h1 h2) (@lem3375255 A B x'' s x' x f t h2)). Qed.
Lemma lem3376742 {A B : Type'} (s : A -> Prop) (x' : A) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term43 A B s t f) (h2 : term260 A B s x' x f t) : False.
Proof. exact (ex_elim (@lem3375083 A B s x' x f t h2) (fun x'' : A => fun h0 : term259 A B s x' x f t x'' => @lem3376741 A B x'' s x' x f t h1 h0)). Qed.
Lemma lem3376743 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term43 A B s t f) (h2 : term93 A B s x f t) : False.
Proof. exact (ex_elim (@lem3375082 A B s x f t h2) (fun x' : A => fun h0 : term261 A B s x f t x' => @lem3376742 A B s x' x f t h1 h0)). Qed.
Lemma lem3376744 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term43 A B s t f) (h2 : term93 A B s x f t) : (term93 A B s x f t) = False.
Proof. exact (prop_ext (fun h3 : term93 A B s x f t => @lem3376743 A B s x f t h1 h2) (fun h3 : False => @lem3374455 A B s x f t h2)). Qed.
Lemma lem3376745 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (h1 : term43 A B s t f) (h2 : term93 A B s x f t) : False.
Proof. exact (EQ_MP (@lem3376744 A B s x f t h1 h2) (@lem3374455 A B s x f t h2)). Qed.
Lemma lem3376746 {A B : Type'} (x : B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term92 A B s x f t.
Proof. exact (fun h0 : term93 A B s x f t => @lem3376745 A B s x f t h1 h0). Qed.
Lemma lem3376747 {A B : Type'} (x : B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : (term59 A B x f s t) = (term73 A B s x f t).
Proof. exact (EQ_MP (@lem3374454 A B s x f t) (@lem3376746 A B x s t f h1)). Qed.
Lemma lem3376752 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term43 A B s t f) : term76 A B s f t.
Proof. exact (fun x : B => @lem3376747 A B x s t f h1). Qed.
Lemma lem3376753 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : term77 A B s f t.
Proof. exact (fun h0 : term43 A B s t f => @lem3376752 A B s t f h0). Qed.
Lemma lem3376758 {A B : Type'} (s : A -> Prop) (f : A -> B) : term79 A B s f.
Proof. exact (fun t : A -> Prop => @lem3376753 A B s f t). Qed.
Lemma lem3376763 {A B : Type'} (f : A -> B) : term81 A B f.
Proof. exact (fun s : A -> Prop => @lem3376758 A B s f). Qed.
Lemma lem3376768 {A B : Type'} : term83 A B.
Proof. exact (fun f : A -> B => @lem3376763 A B f). Qed.
Lemma lem3376769 {A B : Type'} : term85 A B.
Proof. exact (EQ_MP (@lem3374449 A B) (@lem3376768 A B)). Qed.
Lemma lem3376771 {A B : Type'} : term85 A B.
Proof. exact (@lem3374136 A B (@lem3376769 A B)). Qed.
Lemma lem3376772 {A B : Type'} (h1 : term86 A B) : False.
Proof. exact (@lem3376771 A B (@lem3374120 A B h1)). Qed.
Lemma lem3376773 {A B : Type'} (h1 : term86 A B) : (term86 A B) = False.
Proof. exact (prop_ext (fun h2 : term86 A B => @lem3376772 A B h1) (fun h2 : False => @lem3374120 A B h1)). Qed.
Lemma lem3376774 {A B : Type'} (h1 : term86 A B) : False.
Proof. exact (EQ_MP (@lem3376773 A B h1) (@lem3374120 A B h1)). Qed.
Lemma lem3376775 {A B : Type'} : term85 A B.
Proof. exact (fun h0 : term86 A B => @lem3376774 A B h0). Qed.
Lemma lem3376776 {A B : Type'} : term83 A B.
Proof. exact (EQ_MP (@lem3374119 A B) (@lem3376775 A B)). Qed.
Lemma lem3376777 {A B : Type'} : term25 A B.
Proof. exact (EQ_MP (@lem3374115 A B) (@lem3376776 A B)). Qed.
Lemma lem3376778 {A B : Type'} : term24 A B.
Proof. exact (EQ_MP (@lem3373884 A B) (@lem3376777 A B)). Qed.
