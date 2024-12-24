Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_RECURSION_LEMMA_term_abbrevs.
Require Import ABSORPTION_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_RULES_spec.
Require Import FINREC_FUN_spec.
Require Import IN_INSERT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
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
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem3812802 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3812803 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3812804 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3812803 A x) (@lem3812802 A x)). Qed.
Lemma lem3812805 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem3812804 A x y). Qed.
Lemma lem3812806 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem3812807 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem3812806 A y x) (@lem3812805 A x y)). Qed.
Lemma lem3812808 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem3812807 A y x s). Qed.
Lemma lem3812809 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A y x s) = ((term5 A x y s) = (term6 A y x s)).
Proof. exact (eq_refl (term4 A y x s)). Qed.
Lemma lem3812813 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = ((@INSERT A x s) = s)) : (@IN A x s) = ((@INSERT A x s) = s).
Proof. exact (h1). Qed.
Lemma lem3812814 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = ((@INSERT A x s) = s)) : ((@INSERT A x s) = s) = (@IN A x s).
Proof. exact (SYM (@lem3812813 A x s h1)). Qed.
Lemma lem3812815 {A : Type'} (x : A) (s : A -> Prop) (h1 : ((@INSERT A x s) = s) = (@IN A x s)) : ((@INSERT A x s) = s) = (@IN A x s).
Proof. exact (h1). Qed.
Lemma lem3812816 {A : Type'} (x : A) (s : A -> Prop) (h1 : ((@INSERT A x s) = s) = (@IN A x s)) : (@IN A x s) = ((@INSERT A x s) = s).
Proof. exact (SYM (@lem3812815 A x s h1)). Qed.
Lemma lem3812817 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = ((@INSERT A x s) = s)) = (((@INSERT A x s) = s) = (@IN A x s)).
Proof. exact (prop_ext (fun h1 : (@IN A x s) = ((@INSERT A x s) = s) => @lem3812814 A x s h1) (fun h1 : ((@INSERT A x s) = s) = (@IN A x s) => @lem3812816 A x s h1)). Qed.
Lemma lem3812818 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3812817 A x s)). Qed.
Lemma lem3812819 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3812820 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (MK_COMB (@lem3812819 A) (@lem3812818 A x)). Qed.
Lemma lem3812821 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (fun_ext (fun x : A => @lem3812820 A x)). Qed.
Lemma lem3812822 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3812823 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3812822 A) (@lem3812821 A)). Qed.
Lemma lem3812824 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3812823 A) (@lem3276312 A)). Qed.
Lemma lem3812825 {A : Type'} (x : A) : term15 A x.
Proof. exact (@lem3812824 A x). Qed.
Lemma lem3812826 {A : Type'} (x : A) : (term15 A x) = (term10 A x).
Proof. exact (eq_refl (term15 A x)). Qed.
Lemma lem3812827 {A : Type'} (x : A) : term10 A x.
Proof. exact (EQ_MP (@lem3812826 A x) (@lem3812825 A x)). Qed.
Lemma lem3812828 {A : Type'} (x : A) (s : A -> Prop) : term16 A x s.
Proof. exact (@lem3812827 A x s). Qed.
Lemma lem3812829 {A : Type'} (x : A) (s : A -> Prop) : (term16 A x s) = (((@INSERT A x s) = s) = (@IN A x s)).
Proof. exact (eq_refl (term16 A x s)). Qed.
Lemma lem3812831 {A B : Type'} (h1 : term17 A B) : term17 A B.
Proof. exact (h1). Qed.
Lemma lem3812832 {A B : Type'} (f : type1411 A B) (h1 : term17 A B) : term18 A B f.
Proof. exact (@lem3812831 A B h1 f). Qed.
Lemma lem3812833 {A B : Type'} (f : type1411 A B) : (term18 A B f) = (term19 A B f).
Proof. exact (eq_refl (term18 A B f)). Qed.
Lemma lem3812834 {A B : Type'} (f : type1411 A B) (h1 : term17 A B) : term19 A B f.
Proof. exact (EQ_MP (@lem3812833 A B f) (@lem3812832 A B f h1)). Qed.
Lemma lem3812835 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term17 A B) : term20 A B f b.
Proof. exact (@lem3812834 A B f h1 b). Qed.
Lemma lem3812836 {A B : Type'} (b : B) (f : type1411 A B) : (term20 A B f b) = (term21 A B b f).
Proof. exact (eq_refl (term20 A B f b)). Qed.
Lemma lem3812837 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term17 A B) : term21 A B b f.
Proof. exact (EQ_MP (@lem3812836 A B b f) (@lem3812835 A B f b h1)). Qed.
Lemma lem3812838 {A B : Type'} (f : type1411 A B) (h1 : term22 A B f) : term22 A B f.
Proof. exact (h1). Qed.
Lemma lem3812839 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term22 A B f) (h2 : term17 A B) : term23 A B b f.
Proof. exact (@lem3812837 A B b f h2 (@lem3812838 A B f h1)). Qed.
Lemma lem3812840 {A B : Type'} (f : type1411 A B) (h1 : term22 A B f) (h2 : term17 A B) : term24 A B f.
Proof. exact (fun b : B => @lem3812839 A B b f h1 h2). Qed.
Lemma lem3812841 {A B : Type'} (f : type1411 A B) (h1 : term17 A B) : term25 A B f.
Proof. exact (fun h0 : term22 A B f => @lem3812840 A B f h0 h1). Qed.
Lemma lem3812842 {A B : Type'} (h1 : term17 A B) : term26 A B.
Proof. exact (fun f : type1411 A B => @lem3812841 A B f h1). Qed.
Lemma lem3812843 {A B : Type'} : term27 A B.
Proof. exact (fun h0 : term17 A B => @lem3812842 A B h0). Qed.
Lemma lem3812844 {A B : Type'} : term26 A B.
Proof. exact (@lem3812843 A B (@lem3812781 A B)). Qed.
Lemma lem3812845 {A B : Type'} (f : type1411 A B) : term28 A B f.
Proof. exact (@lem3812844 A B f). Qed.
Lemma lem3812846 {A B : Type'} (f : type1411 A B) : (term28 A B f) = (term25 A B f).
Proof. exact (eq_refl (term28 A B f)). Qed.
Lemma lem3812848 {A B : Type'} (f : type1411 A B) (h1 : term22 A B f) : term22 A B f.
Proof. exact (h1). Qed.
Lemma lem3812850 {A B : Type'} (f : type1411 A B) : term25 A B f.
Proof. exact (EQ_MP (@lem3812846 A B f) (@lem3812845 A B f)). Qed.
Lemma lem3812851 {A B : Type'} (f : type1411 A B) : term25 A B f.
Proof. exact (@lem3812850 A B f). Qed.
Lemma lem3812852 {A B : Type'} (f : type1411 A B) (h1 : term22 A B f) : term24 A B f.
Proof. exact (@lem3812851 A B f (@lem3812848 A B f h1)). Qed.
Lemma lem3812853 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term22 A B f) : term29 A B f b.
Proof. exact (@lem3812852 A B f h1 b). Qed.
Lemma lem3812854 {A B : Type'} (b : B) (f : type1411 A B) : (term29 A B f b) = (term23 A B b f).
Proof. exact (eq_refl (term29 A B f b)). Qed.
Lemma lem3812855 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term22 A B f) : term23 A B b f.
Proof. exact (EQ_MP (@lem3812854 A B b f) (@lem3812853 A B b f h1)). Qed.
Lemma lem3812856 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term23 A B b f) : term23 A B b f.
Proof. exact (h1). Qed.
Lemma lem3812857 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (h1 : term30 A B b f g) : term30 A B b f g.
Proof. exact (h1). Qed.
Lemma lem3812858 {A B : Type'} (f : type1411 A B) (g : type685 A B) (h1 : term31 A B f g) : term31 A B f g.
Proof. exact (h1). Qed.
Lemma lem3812859 {A B : Type'} (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : (g (@EMPTY A)) = b.
Proof. exact (h1). Qed.
Lemma lem3812873 {A B : Type'} (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : (g (@EMPTY A)) = b.
Proof. exact (h1). Qed.
Lemma lem3812874 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3812875 {A B : Type'} (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : (term32 A B g) = (@eq B b).
Proof. exact (MK_COMB (@lem3812874 B) (@lem3812873 A B g b h1)). Qed.
Lemma lem3812876 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3812877 {A B : Type'} (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : ((g (@EMPTY A)) = b) = (b = b).
Proof. exact (MK_COMB (@lem3812875 A B g b h1) (@lem3812876 B b)). Qed.
Lemma lem3812879 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3812880 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3812879 B x). Qed.
Lemma lem3812881 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem3812880 B b). Qed.
Lemma lem3812882 {A B : Type'} (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : ((g (@EMPTY A)) = b) = True.
Proof. exact (TRANS (@lem3812877 A B g b h1) (@lem3812881 B b)). Qed.
Lemma lem3812883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3812884 {A B : Type'} (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : (term33 A B g b) = (and True).
Proof. exact (MK_COMB (@lem3812883) (@lem3812882 A B g b h1)). Qed.
Lemma lem3812897 {A B : Type'} (f : type1411 A B) (g : type685 A B) : (term34 A B f g) = (term34 A B f g).
Proof. exact (eq_refl (term34 A B f g)). Qed.
Lemma lem3812898 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : (term35 A B b f g) = (term36 A B f g).
Proof. exact (MK_COMB (@lem3812884 A B g b h1) (@lem3812897 A B f g)). Qed.
Lemma lem3812900 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3812901 {A B : Type'} (f : type1411 A B) (g : type685 A B) : (term36 A B f g) = (term34 A B f g).
Proof. exact (@lem3812900 (term34 A B f g)). Qed.
Lemma lem3812914 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : (term35 A B b f g) = (term34 A B f g).
Proof. exact (TRANS (@lem3812898 A B f g b h1) (@lem3812901 A B f g)). Qed.
Lemma lem3812915 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : (term34 A B f g) = (term35 A B b f g).
Proof. exact (SYM (@lem3812914 A B f g b h1)). Qed.
Lemma lem3812916 {B : Type'} (_474 : B) (_475 : Prop) (_476 : B -> Prop) (_477 : B) : (term37 B _476 _475 _474 _477) = (term38 B _474 _475 _476 _477).
Proof. exact (@lem13473 B _474 _475 _476 _477). Qed.
Lemma lem3812917 {A B : Type'} (_474 : B) (_475 : Prop) (g : type685 A B) (x : A) (s : A -> Prop) (_477 : B) : (term39 A B g x s _475 _474 _477) = (term40 A B _474 _475 g x s _477).
Proof. exact (@lem3812916 B _474 _475 (term41 A B g x s) _477). Qed.
Lemma lem3812918 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term42 A B f x g s) = (term43 A B f x g s).
Proof. exact (@lem3812917 A B (g s) (@IN A x s) g x s (term44 A B f x g s)). Qed.
Lemma lem3812919 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term45 A B f x g s) = (term46 A B f x g s).
Proof. exact (eq_refl (term45 A B f x g s)). Qed.
Lemma lem3812920 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem3812921 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term48 A B f x g s) = (term49 A B f x g s).
Proof. exact (MK_COMB (@lem3812920 A x s) (@lem3812919 A B f x g s)). Qed.
Lemma lem3812922 {A B : Type'} (x : A) (g : type685 A B) (s : A -> Prop) : (term50 A B x g s) = (term51 A B x g s).
Proof. exact (eq_refl (term50 A B x g s)). Qed.
Lemma lem3812923 {A : Type'} (x : A) (s : A -> Prop) : (term52 A x s) = (term52 A x s).
Proof. exact (eq_refl (term52 A x s)). Qed.
Lemma lem3812924 {A B : Type'} (x : A) (g : type685 A B) (s : A -> Prop) : (term53 A B x g s) = (term54 A B x g s).
Proof. exact (MK_COMB (@lem3812923 A x s) (@lem3812922 A B x g s)). Qed.
Lemma lem3812925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3812926 {A B : Type'} (x : A) (g : type685 A B) (s : A -> Prop) : (term55 A B x g s) = (term56 A B x g s).
Proof. exact (MK_COMB (@lem3812925) (@lem3812924 A B x g s)). Qed.
Lemma lem3812927 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term43 A B f x g s) = (term57 A B f x g s).
Proof. exact (MK_COMB (@lem3812926 A B x g s) (@lem3812921 A B f x g s)). Qed.
Lemma lem3812928 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term42 A B f x g s) = (term58 A B f x g s).
Proof. exact (eq_refl (term42 A B f x g s)). Qed.
Lemma lem3812929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3812930 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term59 A B f x g s) = (term60 A B f x g s).
Proof. exact (MK_COMB (@lem3812929) (@lem3812928 A B f x g s)). Qed.
Lemma lem3812931 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : ((term42 A B f x g s) = (term43 A B f x g s)) = ((term58 A B f x g s) = (term57 A B f x g s)).
Proof. exact (MK_COMB (@lem3812930 A B f x g s) (@lem3812927 A B f x g s)). Qed.
Lemma lem3812932 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term58 A B f x g s) = (term57 A B f x g s).
Proof. exact (EQ_MP (@lem3812931 A B f x g s) (@lem3812918 A B f x g s)). Qed.
Lemma lem3812933 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term57 A B f x g s) = (term58 A B f x g s).
Proof. exact (SYM (@lem3812932 A B f x g s)). Qed.
Lemma lem3812934 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3812951 {A : Type'} (x : A) (s : A -> Prop) (h1 : term61 A x s) : term61 A x s.
Proof. exact (h1). Qed.
Lemma lem3813001 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3813002 {A B : Type'} (g : type685 A B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3813004 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = s) = (@IN A x s).
Proof. exact (EQ_MP (@lem3812829 A x s) (@lem3812828 A x s)). Qed.
Lemma lem3813005 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = s) = (@IN A x s).
Proof. exact (@lem3813004 A x s). Qed.
Lemma lem3813006 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@INSERT A x s) = s).
Proof. exact (SYM (@lem3813005 A x s)). Qed.
Lemma lem3813015 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem3813020 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem3813015 A x s) (@lem3812934 A x s h1)). Qed.
Lemma lem3813021 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem3813020 A x s h1)). Qed.
Lemma lem3813022 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem3813021 A x s h1) (@lem0)). Qed.
Lemma lem3813023 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@INSERT A x s) = s.
Proof. exact (EQ_MP (@lem3813006 A x s) (@lem3813022 A x s h1)). Qed.
Lemma lem3813024 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term62 A B g x s) = (g s).
Proof. exact (MK_COMB (@lem3813002 A B g) (@lem3813023 A x s h1)). Qed.
Lemma lem3813025 {A : Type'} (x : A) (s : A -> Prop) (h1 : term63 A x s) : term63 A x s.
Proof. exact (h1). Qed.
Lemma lem3813029 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem3812809 A y x s) (@lem3812808 A y x s)). Qed.
Lemma lem3813030 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (@lem3813029 A y x s). Qed.
Lemma lem3813031 {A : Type'} (x : A) (s : A -> Prop) : (term64 A x s) = (term65 A x s).
Proof. exact (@lem3813030 A x x s). Qed.
Lemma lem3813035 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3813036 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3813035 A x). Qed.
Lemma lem3813037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3813038 {A : Type'} (x : A) : (term66 A x) = (or True).
Proof. exact (MK_COMB (@lem3813037) (@lem3813036 A x)). Qed.
Lemma lem3813039 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem3813040 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = (term67 A x s).
Proof. exact (MK_COMB (@lem3813038 A x) (@lem3813039 A x s)). Qed.
Lemma lem3813042 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3813043 {A : Type'} (x : A) (s : A -> Prop) : (term67 A x s) = True.
Proof. exact (@lem3813042 (@IN A x s)). Qed.
Lemma lem3813044 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = True.
Proof. exact (TRANS (@lem3813040 A x s) (@lem3813043 A x s)). Qed.
Lemma lem3813045 {A : Type'} (x : A) (s : A -> Prop) : (term64 A x s) = True.
Proof. exact (TRANS (@lem3813031 A x s) (@lem3813044 A x s)). Qed.
Lemma lem3813046 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term68 A x s).
Proof. exact (eq_refl (term68 A x s)). Qed.
Lemma lem3813047 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term69 A x s).
Proof. exact (MK_COMB (@lem3813046 A x s) (@lem3813045 A x s)). Qed.
Lemma lem3813049 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3813050 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (term70 A x s).
Proof. exact (@lem3813049 (term70 A x s)). Qed.
Lemma lem3813051 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term70 A x s).
Proof. exact (TRANS (@lem3813047 A x s) (@lem3813050 A x s)). Qed.
Lemma lem3813052 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term63 A x s).
Proof. exact (SYM (@lem3813051 A x s)). Qed.
Lemma lem3813054 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3813055 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term72 A x s).
Proof. exact (@lem3813054 (term70 A x s)). Qed.
Lemma lem3813056 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term70 A x s).
Proof. exact (SYM (@lem3813055 A x s)). Qed.
Lemma lem3813057 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term73 A x s.
Proof. exact (h1). Qed.
Lemma lem3813058 {A : Type'} : term74 A.
Proof. exact (@lem3197565 A). Qed.
Lemma lem3813063 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term75 A B b f g x s) : term75 A B b f g x s.
Proof. exact (h1). Qed.
Lemma lem3813064 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term76 A B b f g x s.
Proof. exact (fun h0 : term75 A B b f g x s => @lem3813063 A B b f g x s h0). Qed.
Lemma lem3813065 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term76 A B b f g x s) : term76 A B b f g x s.
Proof. exact (h1). Qed.
Lemma lem3813066 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term75 A B b f g x s) : term75 A B b f g x s.
Proof. exact (h1). Qed.
Lemma lem3813067 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term75 A B b f g x s) (h2 : term76 A B b f g x s) : term75 A B b f g x s.
Proof. exact (@lem3813065 A B b f g x s h2 (@lem3813066 A B b f g x s h1)). Qed.
Lemma lem3813068 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term75 A B b f g x s) : term77 A B b f g x s.
Proof. exact (fun h0 : term76 A B b f g x s => @lem3813067 A B b f g x s h1 h0). Qed.
Lemma lem3813069 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term76 A B b f g x s) : term76 A B b f g x s.
Proof. exact (h1). Qed.
Lemma lem3813070 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term75 A B b f g x s) (h2 : term76 A B b f g x s) : term75 A B b f g x s.
Proof. exact (@lem3813068 A B b f g x s h1 (@lem3813069 A B b f g x s h2)). Qed.
Lemma lem3813071 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term76 A B b f g x s) : term76 A B b f g x s.
Proof. exact (fun h0 : term75 A B b f g x s => @lem3813070 A B b f g x s h0 h1). Qed.
Lemma lem3813072 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term78 A B b f g x s.
Proof. exact (fun h0 : term76 A B b f g x s => @lem3813071 A B b f g x s h0). Qed.
Lemma lem3813075 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term76 A B b f g x s.
Proof. exact (@lem3813072 A B b f g x s (@lem3813064 A B b f g x s)). Qed.
Lemma lem3813076 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term76 A B b f g x s.
Proof. exact (@lem3813075 A B b f g x s). Qed.
Lemma lem3813120 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3813121 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (@lem3813120 (term74 A)). Qed.
Lemma lem3813134 {A : Type'} (x : A) (s : A -> Prop) : (term81 A x s) = (term81 A x s).
Proof. exact (eq_refl (term81 A x s)). Qed.
Lemma lem3813135 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term83 A x s).
Proof. exact (MK_COMB (@lem3813134 A x s) (@lem3813121 A)). Qed.
Lemma lem3813138 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem3813139 {A : Type'} (x : A) (s : A -> Prop) : (term85 A x s) = (term86 A x s).
Proof. exact (MK_COMB (@lem3813138 A s) (@lem3813135 A x s)). Qed.
Lemma lem3813142 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem3813143 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = (term88 A x s).
Proof. exact (MK_COMB (@lem3813142 A x s) (@lem3813139 A x s)). Qed.
Lemma lem3813146 {A B : Type'} (f : type1411 A B) (g : type685 A B) : (term89 A B f g) = (term89 A B f g).
Proof. exact (eq_refl (term89 A B f g)). Qed.
Lemma lem3813147 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term90 A B f g x s) = (term91 A B f g x s).
Proof. exact (MK_COMB (@lem3813146 A B f g) (@lem3813143 A x s)). Qed.
Lemma lem3813150 {A B : Type'} (g : type685 A B) (b : B) : (term92 A B g b) = (term92 A B g b).
Proof. exact (eq_refl (term92 A B g b)). Qed.
Lemma lem3813151 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term75 A B b f g x s) = (term93 A B b f g x s).
Proof. exact (MK_COMB (@lem3813150 A B g b) (@lem3813147 A B f g x s)). Qed.
Lemma lem3813154 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term94 A B f g x s) = (term95 A B f g x s).
Proof. exact (fun_ext (fun b : B => @lem3813151 A B b f g x s)). Qed.
Lemma lem3813155 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3813156 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term96 A B f g x s) = (term97 A B f g x s).
Proof. exact (MK_COMB (@lem3813155 B) (@lem3813154 A B f g x s)). Qed.
Lemma lem3813161 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) : (term98 A B g x s) = (term99 A B g x s).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3813156 A B f g x s)). Qed.
Lemma lem3813162 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3813163 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) : (term100 A B g x s) = (term101 A B g x s).
Proof. exact (MK_COMB (@lem3813162 A B) (@lem3813161 A B g x s)). Qed.
Lemma lem3813168 {A B : Type'} (x : A) (s : A -> Prop) : (term102 A B x s) = (term103 A B x s).
Proof. exact (fun_ext (fun g : type685 A B => @lem3813163 A B g x s)). Qed.
Lemma lem3813169 {A B : Type'} : (@all ((A -> Prop) -> B)) = (@all ((A -> Prop) -> B)).
Proof. exact (eq_refl (@all ((A -> Prop) -> B))). Qed.
Lemma lem3813170 {A B : Type'} (x : A) (s : A -> Prop) : (term104 A B x s) = (term105 A B x s).
Proof. exact (MK_COMB (@lem3813169 A B) (@lem3813168 A B x s)). Qed.
Lemma lem3813175 {A B : Type'} (s : A -> Prop) : (term106 A B s) = (term107 A B s).
Proof. exact (fun_ext (fun x : A => @lem3813170 A B x s)). Qed.
Lemma lem3813176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3813177 {A B : Type'} (s : A -> Prop) : (term108 A B s) = (term109 A B s).
Proof. exact (MK_COMB (@lem3813176 A) (@lem3813175 A B s)). Qed.
Lemma lem3813182 {A B : Type'} : (term110 A B) = (term111 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3813177 A B s)). Qed.
Lemma lem3813183 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3813192 {A B : Type'} : (term112 A B) = (term113 A B).
Proof. exact (MK_COMB (@lem3813183 A) (@lem3813182 A B)). Qed.
Lemma lem3813197 {A : Type'} (x : A) (s : A -> Prop) : (term114 A x s) = (term114 A x s).
Proof. exact (eq_refl (term114 A x s)). Qed.
Lemma lem3813198 {A : Type'} (x : A) : (term115 A x) = (term115 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3813197 A x s)). Qed.
Lemma lem3813199 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3813200 {A : Type'} (x : A) : (term116 A x) = (term116 A x).
Proof. exact (MK_COMB (@lem3813199 A) (@lem3813198 A x)). Qed.
Lemma lem3813201 {A : Type'} : (term117 A) = (term117 A).
Proof. exact (fun_ext (fun x : A => @lem3813200 A x)). Qed.
Lemma lem3813202 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3813203 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (MK_COMB (@lem3813202 A) (@lem3813201 A)). Qed.
Lemma lem3813206 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (eq_refl (term119 A)). Qed.
Lemma lem3813207 {A : Type'} : (term74 A) = (term74 A).
Proof. exact (MK_COMB (@lem3813206 A) (@lem3813203 A)). Qed.
Lemma lem3813208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3813209 {A : Type'} : (term80 A) = (term80 A).
Proof. exact (MK_COMB (@lem3813208) (@lem3813207 A)). Qed.
Lemma lem3813214 {A : Type'} (x : A) (s : A -> Prop) : (term81 A x s) = (term81 A x s).
Proof. exact (eq_refl (term81 A x s)). Qed.
Lemma lem3813215 {A : Type'} (x : A) (s : A -> Prop) : (term83 A x s) = (term83 A x s).
Proof. exact (MK_COMB (@lem3813214 A x s) (@lem3813209 A)). Qed.
Lemma lem3813218 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem3813219 {A : Type'} (x : A) (s : A -> Prop) : (term86 A x s) = (term86 A x s).
Proof. exact (MK_COMB (@lem3813218 A s) (@lem3813215 A x s)). Qed.
Lemma lem3813224 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem3813225 {A : Type'} (x : A) (s : A -> Prop) : (term88 A x s) = (term88 A x s).
Proof. exact (MK_COMB (@lem3813224 A x s) (@lem3813219 A x s)). Qed.
Lemma lem3813234 {A B : Type'} (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term120 A B f g s x) = (term120 A B f g s x).
Proof. exact (eq_refl (term120 A B f g s x)). Qed.
Lemma lem3813235 {A B : Type'} (f : type1411 A B) (g : type685 A B) (s : A -> Prop) : (term121 A B f g s) = (term121 A B f g s).
Proof. exact (fun_ext (fun x : A => @lem3813234 A B f g s x)). Qed.
Lemma lem3813236 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3813237 {A B : Type'} (f : type1411 A B) (g : type685 A B) (s : A -> Prop) : (term122 A B f g s) = (term122 A B f g s).
Proof. exact (MK_COMB (@lem3813236 A) (@lem3813235 A B f g s)). Qed.
Lemma lem3813238 {A B : Type'} (f : type1411 A B) (g : type685 A B) : (term123 A B f g) = (term123 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3813237 A B f g s)). Qed.
Lemma lem3813239 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3813240 {A B : Type'} (f : type1411 A B) (g : type685 A B) : (term31 A B f g) = (term31 A B f g).
Proof. exact (MK_COMB (@lem3813239 A) (@lem3813238 A B f g)). Qed.
Lemma lem3813241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3813242 {A B : Type'} (f : type1411 A B) (g : type685 A B) : (term89 A B f g) = (term89 A B f g).
Proof. exact (MK_COMB (@lem3813241) (@lem3813240 A B f g)). Qed.
Lemma lem3813243 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term91 A B f g x s) = (term91 A B f g x s).
Proof. exact (MK_COMB (@lem3813242 A B f g) (@lem3813225 A x s)). Qed.
Lemma lem3813246 {A B : Type'} (g : type685 A B) (b : B) : (term92 A B g b) = (term92 A B g b).
Proof. exact (eq_refl (term92 A B g b)). Qed.
Lemma lem3813247 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term93 A B b f g x s) = (term93 A B b f g x s).
Proof. exact (MK_COMB (@lem3813246 A B g b) (@lem3813243 A B f g x s)). Qed.
Lemma lem3813248 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term95 A B f g x s) = (term95 A B f g x s).
Proof. exact (fun_ext (fun b : B => @lem3813247 A B b f g x s)). Qed.
Lemma lem3813249 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3813250 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term97 A B f g x s) = (term97 A B f g x s).
Proof. exact (MK_COMB (@lem3813249 B) (@lem3813248 A B f g x s)). Qed.
Lemma lem3813251 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) : (term99 A B g x s) = (term99 A B g x s).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3813250 A B f g x s)). Qed.
Lemma lem3813252 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3813253 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) : (term101 A B g x s) = (term101 A B g x s).
Proof. exact (MK_COMB (@lem3813252 A B) (@lem3813251 A B g x s)). Qed.
Lemma lem3813254 {A B : Type'} (x : A) (s : A -> Prop) : (term103 A B x s) = (term103 A B x s).
Proof. exact (fun_ext (fun g : type685 A B => @lem3813253 A B g x s)). Qed.
Lemma lem3813255 {A B : Type'} : (@all ((A -> Prop) -> B)) = (@all ((A -> Prop) -> B)).
Proof. exact (eq_refl (@all ((A -> Prop) -> B))). Qed.
Lemma lem3813256 {A B : Type'} (x : A) (s : A -> Prop) : (term105 A B x s) = (term105 A B x s).
Proof. exact (MK_COMB (@lem3813255 A B) (@lem3813254 A B x s)). Qed.
Lemma lem3813257 {A B : Type'} (s : A -> Prop) : (term107 A B s) = (term107 A B s).
Proof. exact (fun_ext (fun x : A => @lem3813256 A B x s)). Qed.
Lemma lem3813258 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3813259 {A B : Type'} (s : A -> Prop) : (term109 A B s) = (term109 A B s).
Proof. exact (MK_COMB (@lem3813258 A) (@lem3813257 A B s)). Qed.
Lemma lem3813260 {A B : Type'} : (term111 A B) = (term111 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3813259 A B s)). Qed.
Lemma lem3813261 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3813262 {A B : Type'} : (term113 A B) = (term113 A B).
Proof. exact (MK_COMB (@lem3813261 A) (@lem3813260 A B)). Qed.
Lemma lem3813337 {A B : Type'} : (term112 A B) = (term113 A B).
Proof. exact (TRANS (@lem3813192 A B) (@lem3813262 A B)). Qed.
Lemma lem3813338 {A B : Type'} : (term113 A B) = (term112 A B).
Proof. exact (SYM (@lem3813337 A B)). Qed.
Lemma lem3813344 {A : Type'} (h1 : term74 A) : term74 A.
Proof. exact (h1). Qed.
Lemma lem3813438 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3813444 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term73 A x s.
Proof. exact (h1). Qed.
Lemma lem3813452 {A : Type'} (x : A) (s : A -> Prop) : (term114 A x s) = (term124 A x s).
Proof. exact (@lem17265 (@FINITE A s) (term70 A x s)). Qed.
Lemma lem3813453 {A : Type'} (x : A) : (term115 A x) = (term125 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3813452 A x s)). Qed.
Lemma lem3813454 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3813455 {A : Type'} (x : A) : (term116 A x) = (term126 A x).
Proof. exact (MK_COMB (@lem3813454 A) (@lem3813453 A x)). Qed.
Lemma lem3813456 {A : Type'} : (term117 A) = (term127 A).
Proof. exact (fun_ext (fun x : A => @lem3813455 A x)). Qed.
Lemma lem3813457 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3813458 {A : Type'} : (term118 A) = (term128 A).
Proof. exact (MK_COMB (@lem3813457 A) (@lem3813456 A)). Qed.
Lemma lem3813460 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (eq_refl (term119 A)). Qed.
Lemma lem3813517 {A : Type'} : (term74 A) = (term129 A).
Proof. exact (MK_COMB (@lem3813460 A) (@lem3813458 A)). Qed.
Lemma lem3813518 {A : Type'} (h1 : term74 A) : term129 A.
Proof. exact (EQ_MP (@lem3813517 A) (@lem3813344 A h1)). Qed.
Lemma lem3813580 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3813590 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term73 A x s.
Proof. exact (h1). Qed.
Lemma lem3813605 {A : Type'} (x : A) (s : A -> Prop) : (term124 A x s) = (term124 A x s).
Proof. exact (eq_refl (term124 A x s)). Qed.
Lemma lem3813606 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3813605 A x s)). Qed.
Lemma lem3813607 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3813608 {A : Type'} (x : A) : (term126 A x) = (term126 A x).
Proof. exact (MK_COMB (@lem3813607 A) (@lem3813606 A x)). Qed.
Lemma lem3813609 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (fun_ext (fun x : A => @lem3813608 A x)). Qed.
Lemma lem3813610 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3813611 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (MK_COMB (@lem3813610 A) (@lem3813609 A)). Qed.
Lemma lem3813616 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (eq_refl (term119 A)). Qed.
Lemma lem3813617 {A : Type'} : (term129 A) = (term129 A).
Proof. exact (MK_COMB (@lem3813616 A) (@lem3813611 A)). Qed.
Lemma lem3813618 {A : Type'} (h1 : term74 A) : term129 A.
Proof. exact (EQ_MP (@lem3813617 A) (@lem3813518 A h1)). Qed.
Lemma lem3813619 {A : Type'} (h1 : term74 A) : term128 A.
Proof. exact (proj2 (@lem3813618 A h1)). Qed.
Lemma lem3813654 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3813658 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term73 A x s.
Proof. exact (h1). Qed.
Lemma lem3813670 {A : Type'} (x : A) (s : A -> Prop) : (term124 A x s) = (term124 A x s).
Proof. exact (eq_refl (term124 A x s)). Qed.
Lemma lem3813671 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3813670 A x s)). Qed.
Lemma lem3813672 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3813673 {A : Type'} (x : A) : (term126 A x) = (term126 A x).
Proof. exact (MK_COMB (@lem3813672 A) (@lem3813671 A x)). Qed.
Lemma lem3813674 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (fun_ext (fun x : A => @lem3813673 A x)). Qed.
Lemma lem3813675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3813677 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (MK_COMB (@lem3813675 A) (@lem3813674 A)). Qed.
Lemma lem3813678 {A : Type'} (h1 : term74 A) : term128 A.
Proof. exact (EQ_MP (@lem3813677 A) (@lem3813619 A h1)). Qed.
Lemma lem3813685 {A : Type'} (_44278 : A) (h1 : term74 A) : term130 A _44278.
Proof. exact (@lem3813678 A h1 _44278). Qed.
Lemma lem3813686 {A : Type'} (_44278 : A) : (term130 A _44278) = (term126 A _44278).
Proof. exact (eq_refl (term130 A _44278)). Qed.
Lemma lem3813687 {A : Type'} (_44278 : A) (h1 : term74 A) : term126 A _44278.
Proof. exact (EQ_MP (@lem3813686 A _44278) (@lem3813685 A _44278 h1)). Qed.
Lemma lem3813688 {A : Type'} (_44278 : A) (_44279 : A -> Prop) (h1 : term74 A) : term131 A _44278 _44279.
Proof. exact (@lem3813687 A _44278 h1 _44279). Qed.
Lemma lem3813689 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term131 A _44278 _44279) = (term124 A _44278 _44279).
Proof. exact (eq_refl (term131 A _44278 _44279)). Qed.
Lemma lem3813708 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3813710 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term73 A x s.
Proof. exact (h1). Qed.
Lemma lem3813775 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3813789 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term73 A x s.
Proof. exact (h1). Qed.
Lemma lem3813817 {A : Type'} (_44278 : A) (_44279 : A -> Prop) (h1 : term74 A) : term124 A _44278 _44279.
Proof. exact (EQ_MP (@lem3813689 A _44278 _44279) (@lem3813688 A _44278 _44279 h1)). Qed.
Lemma lem3813909 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3813910 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term132 A s.
Proof. exact (fun h0 : term133 A s => @lem3813909 A s h1). Qed.
Lemma lem3813912 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3813913 {A : Type'} (s : A -> Prop) : (term132 A s) = (@FINITE A s).
Proof. exact (@lem3813912 (@FINITE A s)). Qed.
Lemma lem3813914 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3813913 A s) (@lem3813910 A s h1)). Qed.
Lemma lem3813920 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3813921 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term124 A _44278 _44279) = (term135 A _44278 _44279).
Proof. exact (@lem3813920 (term70 A _44278 _44279) (term133 A _44279)). Qed.
Lemma lem3813927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3813928 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term136 A _44278 _44279) = (term137 A _44278 _44279).
Proof. exact (MK_COMB (@lem3813927) (@lem3813921 A _44278 _44279)). Qed.
Lemma lem3813934 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term135 A _44278 _44279) = (term135 A _44278 _44279).
Proof. exact (eq_refl (term135 A _44278 _44279)). Qed.
Lemma lem3813935 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : ((term124 A _44278 _44279) = (term135 A _44278 _44279)) = ((term135 A _44278 _44279) = (term135 A _44278 _44279)).
Proof. exact (MK_COMB (@lem3813928 A _44278 _44279) (@lem3813934 A _44278 _44279)). Qed.
Lemma lem3813937 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3813938 (x : Prop) : (x = x) = True.
Proof. exact (@lem3813937 Prop x). Qed.
Lemma lem3813939 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : ((term135 A _44278 _44279) = (term135 A _44278 _44279)) = True.
Proof. exact (@lem3813938 (term135 A _44278 _44279)). Qed.
Lemma lem3813940 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : ((term124 A _44278 _44279) = (term135 A _44278 _44279)) = True.
Proof. exact (TRANS (@lem3813935 A _44278 _44279) (@lem3813939 A _44278 _44279)). Qed.
Lemma lem3813941 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : True = ((term124 A _44278 _44279) = (term135 A _44278 _44279)).
Proof. exact (SYM (@lem3813940 A _44278 _44279)). Qed.
Lemma lem3813942 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term124 A _44278 _44279) = (term135 A _44278 _44279).
Proof. exact (EQ_MP (@lem3813941 A _44278 _44279) (@lem0)). Qed.
Lemma lem3813943 {A : Type'} (_44278 : A) (_44279 : A -> Prop) (h1 : term74 A) : term135 A _44278 _44279.
Proof. exact (EQ_MP (@lem3813942 A _44278 _44279) (@lem3813817 A _44278 _44279 h1)). Qed.
Lemma lem3813945 (b : Prop) (a : Prop) : (a \/ b) = (term138 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3813946 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term135 A _44278 _44279) = (term139 A _44278 _44279).
Proof. exact (@lem3813945 (term133 A _44279) (term70 A _44278 _44279)). Qed.
Lemma lem3813948 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3813949 {A : Type'} (_44279 : A -> Prop) : (term141 A _44279) = (@FINITE A _44279).
Proof. exact (@lem3813948 (@FINITE A _44279)). Qed.
Lemma lem3813950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3813951 {A : Type'} (_44279 : A -> Prop) : (term142 A _44279) = (term84 A _44279).
Proof. exact (MK_COMB (@lem3813950) (@lem3813949 A _44279)). Qed.
Lemma lem3813952 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term70 A _44278 _44279) = (term70 A _44278 _44279).
Proof. exact (eq_refl (term70 A _44278 _44279)). Qed.
Lemma lem3813953 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term139 A _44278 _44279) = (term114 A _44278 _44279).
Proof. exact (MK_COMB (@lem3813951 A _44279) (@lem3813952 A _44278 _44279)). Qed.
Lemma lem3813954 {A : Type'} (_44278 : A) (_44279 : A -> Prop) : (term135 A _44278 _44279) = (term114 A _44278 _44279).
Proof. exact (TRANS (@lem3813946 A _44278 _44279) (@lem3813953 A _44278 _44279)). Qed.
Lemma lem3813957 {A : Type'} (_44278 : A) (_44279 : A -> Prop) (h1 : term74 A) : term114 A _44278 _44279.
Proof. exact (EQ_MP (@lem3813954 A _44278 _44279) (@lem3813943 A _44278 _44279 h1)). Qed.
Lemma lem3813958 {A : Type'} (_44278 : A) (_44279 : A -> Prop) (h1 : term74 A) : term114 A _44278 _44279.
Proof. exact (@lem3813957 A _44278 _44279 h1). Qed.
Lemma lem3813959 {A : Type'} (_44278 : A) (s : A -> Prop) (h1 : term74 A) : term114 A _44278 s.
Proof. exact (@lem3813958 A _44278 s h1). Qed.
Lemma lem3813962 {A : Type'} (_44278 : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term74 A) : term70 A _44278 s.
Proof. exact (@lem3813959 A _44278 s h2 (@lem3813914 A s h1)). Qed.
Lemma lem3813963 {A : Type'} (_44278 : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term74 A) : term70 A _44278 s.
Proof. exact (@lem3813962 A _44278 s h1 h2). Qed.
Lemma lem3813964 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term74 A) : term70 A x s.
Proof. exact (@lem3813963 A x s h1 h2). Qed.
Lemma lem3813965 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term74 A) : term143 A x s.
Proof. exact (fun h0 : term73 A x s => @lem3813964 A x s h1 h2). Qed.
Lemma lem3813967 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3813968 {A : Type'} (x : A) (s : A -> Prop) : (term143 A x s) = (term70 A x s).
Proof. exact (@lem3813967 (term70 A x s)). Qed.
Lemma lem3813969 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term74 A) : term70 A x s.
Proof. exact (EQ_MP (@lem3813968 A x s) (@lem3813965 A x s h1 h2)). Qed.
Lemma lem3813972 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3813974 {A : Type'} (x : A) (s : A -> Prop) : (term73 A x s) = (term144 A x s).
Proof. exact (@lem3813972 (term70 A x s)). Qed.
Lemma lem3813977 {A : Type'} (x : A) (s : A -> Prop) (h1 : term73 A x s) : term144 A x s.
Proof. exact (EQ_MP (@lem3813974 A x s) (@lem3813789 A x s h1)). Qed.
Lemma lem3813980 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (@lem3813977 A x s h2 (@lem3813969 A x s h1 h3)). Qed.
Lemma lem3813981 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : term145.
Proof. exact (fun h0 : ~ False => @lem3813980 A x s h1 h2 h3). Qed.
Lemma lem3813983 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3813984 : term145 = False.
Proof. exact (@lem3813983 False). Qed.
Lemma lem3813985 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813984) (@lem3813981 A x s h1 h2 h3)). Qed.
Lemma lem3813986 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (term73 A x s) = False.
Proof. exact (prop_ext (fun h4 : term73 A x s => @lem3813985 A x s h1 h2 h3) (fun h4 : False => @lem3813789 A x s h2)). Qed.
Lemma lem3813987 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813986 A x s h1 h2 h3) (@lem3813789 A x s h2)). Qed.
Lemma lem3813988 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3813987 A x s h1 h2 h3) (fun h4 : False => @lem3813775 A s h1)). Qed.
Lemma lem3813990 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813988 A x s h1 h2 h3) (@lem3813775 A s h1)). Qed.
Lemma lem3813991 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (term73 A x s) = False.
Proof. exact (prop_ext (fun h4 : term73 A x s => @lem3813990 A x s h1 h2 h3) (fun h4 : False => @lem3813710 A x s h2)). Qed.
Lemma lem3813992 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813991 A x s h1 h2 h3) (@lem3813710 A x s h2)). Qed.
Lemma lem3813993 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3813992 A x s h1 h2 h3) (fun h4 : False => @lem3813708 A s h1)). Qed.
Lemma lem3813994 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813993 A x s h1 h2 h3) (@lem3813708 A s h1)). Qed.
Lemma lem3813995 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (term73 A x s) = False.
Proof. exact (prop_ext (fun h4 : term73 A x s => @lem3813994 A x s h1 h2 h3) (fun h4 : False => @lem3813658 A x s h2)). Qed.
Lemma lem3813996 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813995 A x s h1 h2 h3) (@lem3813658 A x s h2)). Qed.
Lemma lem3813997 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3813996 A x s h1 h2 h3) (fun h4 : False => @lem3813654 A s h1)). Qed.
Lemma lem3813998 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813997 A x s h1 h2 h3) (@lem3813654 A s h1)). Qed.
Lemma lem3813999 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (term73 A x s) = False.
Proof. exact (prop_ext (fun h4 : term73 A x s => @lem3813998 A x s h1 h2 h3) (fun h4 : False => @lem3813658 A x s h2)). Qed.
Lemma lem3814000 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3813999 A x s h1 h2 h3) (@lem3813658 A x s h2)). Qed.
Lemma lem3814001 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3814000 A x s h1 h2 h3) (fun h4 : False => @lem3813654 A s h1)). Qed.
Lemma lem3814002 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3814001 A x s h1 h2 h3) (@lem3813654 A s h1)). Qed.
Lemma lem3814003 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (term73 A x s) = False.
Proof. exact (prop_ext (fun h4 : term73 A x s => @lem3814002 A x s h1 h2 h3) (fun h4 : False => @lem3813590 A x s h2)). Qed.
Lemma lem3814004 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3814003 A x s h1 h2 h3) (@lem3813590 A x s h2)). Qed.
Lemma lem3814005 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3814004 A x s h1 h2 h3) (fun h4 : False => @lem3813580 A s h1)). Qed.
Lemma lem3814006 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3814005 A x s h1 h2 h3) (@lem3813580 A s h1)). Qed.
Lemma lem3814007 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (term73 A x s) = False.
Proof. exact (prop_ext (fun h4 : term73 A x s => @lem3814006 A x s h1 h2 h3) (fun h4 : False => @lem3813444 A x s h2)). Qed.
Lemma lem3814008 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3814007 A x s h1 h2 h3) (@lem3813444 A x s h2)). Qed.
Lemma lem3814009 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3814008 A x s h1 h2 h3) (fun h4 : False => @lem3813438 A s h1)). Qed.
Lemma lem3814010 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) (h3 : term74 A) : False.
Proof. exact (EQ_MP (@lem3814009 A x s h1 h2 h3) (@lem3813438 A s h1)). Qed.
Lemma lem3814011 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) : term79 A.
Proof. exact (fun h0 : term74 A => @lem3814010 A x s h1 h2 h0). Qed.
Lemma lem3814012 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (@lem69 (term74 A)). Qed.
Lemma lem3814013 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term73 A x s) : term80 A.
Proof. exact (EQ_MP (@lem3814012 A) (@lem3814011 A x s h1 h2)). Qed.
Lemma lem3814014 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term83 A x s.
Proof. exact (fun h0 : term73 A x s => @lem3814013 A x s h1 h0). Qed.
Lemma lem3814015 {A : Type'} (x : A) (s : A -> Prop) : term86 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3814014 A x s h0). Qed.
Lemma lem3814016 {A : Type'} (x : A) (s : A -> Prop) : term88 A x s.
Proof. exact (fun h0 : term61 A x s => @lem3814015 A x s). Qed.
Lemma lem3814017 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term91 A B f g x s.
Proof. exact (fun h0 : term31 A B f g => @lem3814016 A x s). Qed.
Lemma lem3814018 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term93 A B b f g x s.
Proof. exact (fun h0 : (g (@EMPTY A)) = b => @lem3814017 A B f g x s). Qed.
Lemma lem3814023 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term97 A B f g x s.
Proof. exact (fun b : B => @lem3814018 A B b f g x s). Qed.
Lemma lem3814028 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) : term101 A B g x s.
Proof. exact (fun f : type1411 A B => @lem3814023 A B f g x s). Qed.
Lemma lem3814033 {A B : Type'} (x : A) (s : A -> Prop) : term105 A B x s.
Proof. exact (fun g : type685 A B => @lem3814028 A B g x s). Qed.
Lemma lem3814038 {A B : Type'} (s : A -> Prop) : term109 A B s.
Proof. exact (fun x : A => @lem3814033 A B x s). Qed.
Lemma lem3814043 {A B : Type'} : term113 A B.
Proof. exact (fun s : A -> Prop => @lem3814038 A B s). Qed.
Lemma lem3814044 {A B : Type'} : term112 A B.
Proof. exact (EQ_MP (@lem3813338 A B) (@lem3814043 A B)). Qed.
Lemma lem3814045 {A B : Type'} (s : A -> Prop) : term146 A B s.
Proof. exact (@lem3814044 A B s). Qed.
Lemma lem3814046 {A B : Type'} (s : A -> Prop) : (term146 A B s) = (term108 A B s).
Proof. exact (eq_refl (term146 A B s)). Qed.
Lemma lem3814047 {A B : Type'} (s : A -> Prop) : term108 A B s.
Proof. exact (EQ_MP (@lem3814046 A B s) (@lem3814045 A B s)). Qed.
Lemma lem3814048 {A B : Type'} (s : A -> Prop) (x : A) : term147 A B s x.
Proof. exact (@lem3814047 A B s x). Qed.
Lemma lem3814049 {A B : Type'} (x : A) (s : A -> Prop) : (term147 A B s x) = (term104 A B x s).
Proof. exact (eq_refl (term147 A B s x)). Qed.
Lemma lem3814050 {A B : Type'} (x : A) (s : A -> Prop) : term104 A B x s.
Proof. exact (EQ_MP (@lem3814049 A B x s) (@lem3814048 A B s x)). Qed.
Lemma lem3814051 {A B : Type'} (x : A) (s : A -> Prop) (g : type685 A B) : term148 A B x s g.
Proof. exact (@lem3814050 A B x s g). Qed.
Lemma lem3814052 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) : (term148 A B x s g) = (term100 A B g x s).
Proof. exact (eq_refl (term148 A B x s g)). Qed.
Lemma lem3814053 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) : term100 A B g x s.
Proof. exact (EQ_MP (@lem3814052 A B g x s) (@lem3814051 A B x s g)). Qed.
Lemma lem3814054 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) (f : type1411 A B) : term149 A B g x s f.
Proof. exact (@lem3814053 A B g x s f). Qed.
Lemma lem3814055 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term149 A B g x s f) = (term96 A B f g x s).
Proof. exact (eq_refl (term149 A B g x s f)). Qed.
Lemma lem3814056 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term96 A B f g x s.
Proof. exact (EQ_MP (@lem3814055 A B f g x s) (@lem3814054 A B g x s f)). Qed.
Lemma lem3814057 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (b : B) : term150 A B f g x s b.
Proof. exact (@lem3814056 A B f g x s b). Qed.
Lemma lem3814058 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term150 A B f g x s b) = (term75 A B b f g x s).
Proof. exact (eq_refl (term150 A B f g x s b)). Qed.
Lemma lem3814059 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term75 A B b f g x s.
Proof. exact (EQ_MP (@lem3814058 A B b f g x s) (@lem3814057 A B f g x s b)). Qed.
Lemma lem3814061 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : term75 A B b f g x s.
Proof. exact (@lem3813076 A B b f g x s (@lem3814059 A B b f g x s)). Qed.
Lemma lem3814062 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : (g (@EMPTY A)) = b) : term90 A B f g x s.
Proof. exact (@lem3814061 A B b f g x s (@lem3812859 A B g b h1)). Qed.
Lemma lem3814063 {A B : Type'} (x : A) (s : A -> Prop) (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term87 A x s.
Proof. exact (@lem3814062 A B f x s g b h2 (@lem3812858 A B f g h1)). Qed.
Lemma lem3814064 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : term61 A x s) (h3 : (g (@EMPTY A)) = b) : term85 A x s.
Proof. exact (@lem3814063 A B x s f g b h1 h3 (@lem3812951 A x s h2)). Qed.
Lemma lem3814065 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term61 A x s) (h4 : (g (@EMPTY A)) = b) : term82 A x s.
Proof. exact (@lem3814064 A B f x s g b h1 h3 h4 (@lem3813001 A s h2)). Qed.
Lemma lem3814066 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term73 A x s) (h4 : term61 A x s) (h5 : (g (@EMPTY A)) = b) : term79 A.
Proof. exact (@lem3814065 A B f x s g b h1 h2 h4 h5 (@lem3813057 A x s h3)). Qed.
Lemma lem3814067 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term73 A x s) (h4 : term61 A x s) (h5 : (g (@EMPTY A)) = b) : False.
Proof. exact (@lem3814066 A B f x s g b h1 h2 h3 h4 h5 (@lem3813058 A)). Qed.
Lemma lem3814068 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term73 A x s) (h4 : term61 A x s) (h5 : (g (@EMPTY A)) = b) : (term73 A x s) = False.
Proof. exact (prop_ext (fun h6 : term73 A x s => @lem3814067 A B f x s g b h1 h2 h3 h4 h5) (fun h6 : False => @lem3813057 A x s h3)). Qed.
Lemma lem3814069 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term73 A x s) (h4 : term61 A x s) (h5 : (g (@EMPTY A)) = b) : False.
Proof. exact (EQ_MP (@lem3814068 A B f x s g b h1 h2 h3 h4 h5) (@lem3813057 A x s h3)). Qed.
Lemma lem3814070 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term61 A x s) (h4 : (g (@EMPTY A)) = b) : term72 A x s.
Proof. exact (fun h0 : term73 A x s => @lem3814069 A B f x s g b h1 h2 h0 h3 h4). Qed.
Lemma lem3814071 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term61 A x s) (h4 : (g (@EMPTY A)) = b) : term70 A x s.
Proof. exact (EQ_MP (@lem3813056 A x s) (@lem3814070 A B f x s g b h1 h2 h3 h4)). Qed.
Lemma lem3814072 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term61 A x s) (h4 : (g (@EMPTY A)) = b) : term63 A x s.
Proof. exact (EQ_MP (@lem3813052 A x s) (@lem3814071 A B f x s g b h1 h2 h3 h4)). Qed.
Lemma lem3814073 {A : Type'} (x : A) (s : A -> Prop) (h1 : term63 A x s) : term63 A x s.
Proof. exact (h1). Qed.
Lemma lem3814074 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (g : type685 A B) (h1 : term31 A B f g) : term151 A B f g s.
Proof. exact (@lem3812858 A B f g h1 s). Qed.
Lemma lem3814075 {A B : Type'} (f : type1411 A B) (g : type685 A B) (s : A -> Prop) : (term151 A B f g s) = (term122 A B f g s).
Proof. exact (eq_refl (term151 A B f g s)). Qed.
Lemma lem3814076 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (g : type685 A B) (h1 : term31 A B f g) : term122 A B f g s.
Proof. exact (EQ_MP (@lem3814075 A B f g s) (@lem3814074 A B s f g h1)). Qed.
Lemma lem3814077 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (g : type685 A B) (h1 : term31 A B f g) : term152 A B f g s x.
Proof. exact (@lem3814076 A B s f g h1 x). Qed.
Lemma lem3814078 {A B : Type'} (f : type1411 A B) (g : type685 A B) (s : A -> Prop) (x : A) : (term152 A B f g s x) = (term120 A B f g s x).
Proof. exact (eq_refl (term152 A B f g s x)). Qed.
Lemma lem3814081 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (g : type685 A B) (h1 : term31 A B f g) : term120 A B f g s x.
Proof. exact (EQ_MP (@lem3814078 A B f g s x) (@lem3814077 A B s x f g h1)). Qed.
Lemma lem3814082 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (g : type685 A B) (h1 : term31 A B f g) : term120 A B f g s x.
Proof. exact (@lem3814081 A B s x f g h1). Qed.
Lemma lem3814083 {A B : Type'} (s : A -> Prop) (x : A) (f : type1411 A B) (g : type685 A B) (h1 : term31 A B f g) : term153 A B f g s x.
Proof. exact (@lem3814082 A B (@INSERT A x s) x f g h1). Qed.
Lemma lem3814084 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term31 A B f g) (h2 : term63 A x s) : (term62 A B g x s) = (term154 A B f g s x).
Proof. exact (@lem3814083 A B s x f g h1 (@lem3814073 A x s h2)). Qed.
Lemma lem3814085 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term155 A B f x g s) = (term155 A B f x g s).
Proof. exact (eq_refl (term155 A B f x g s)). Qed.
Lemma lem3814086 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term31 A B f g) (h2 : term63 A x s) : (term156 A B f g x s) = (term157 A B f g s x).
Proof. exact (MK_COMB (@lem3814085 A B f x g s) (@lem3814084 A B f g x s h1 h2)). Qed.
Lemma lem3814087 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term157 A B f g s x) = ((term154 A B f g s x) = (term44 A B f x g s)).
Proof. exact (eq_refl (term157 A B f g s x)). Qed.
Lemma lem3814088 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) : (term158 A B f g x s) = (term158 A B f g x s).
Proof. exact (eq_refl (term158 A B f g x s)). Qed.
Lemma lem3814089 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : ((term156 A B f g x s) = (term157 A B f g s x)) = ((term156 A B f g x s) = ((term154 A B f g s x) = (term44 A B f x g s))).
Proof. exact (MK_COMB (@lem3814088 A B f g x s) (@lem3814087 A B f x g s)). Qed.
Lemma lem3814090 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term156 A B f g x s) = ((term62 A B g x s) = (term44 A B f x g s)).
Proof. exact (eq_refl (term156 A B f g x s)). Qed.
Lemma lem3814091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3814092 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : (term158 A B f g x s) = (term159 A B f x g s).
Proof. exact (MK_COMB (@lem3814091) (@lem3814090 A B f x g s)). Qed.
Lemma lem3814093 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : ((term154 A B f g s x) = (term44 A B f x g s)) = ((term154 A B f g s x) = (term44 A B f x g s)).
Proof. exact (eq_refl ((term154 A B f g s x) = (term44 A B f x g s))). Qed.
Lemma lem3814094 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : ((term156 A B f g x s) = ((term154 A B f g s x) = (term44 A B f x g s))) = (((term62 A B g x s) = (term44 A B f x g s)) = ((term154 A B f g s x) = (term44 A B f x g s))).
Proof. exact (MK_COMB (@lem3814092 A B f x g s) (@lem3814093 A B f x g s)). Qed.
Lemma lem3814095 {A B : Type'} (f : type1411 A B) (x : A) (g : type685 A B) (s : A -> Prop) : ((term156 A B f g x s) = (term157 A B f g s x)) = (((term62 A B g x s) = (term44 A B f x g s)) = ((term154 A B f g s x) = (term44 A B f x g s))).
Proof. exact (TRANS (@lem3814089 A B f x g s) (@lem3814094 A B f x g s)). Qed.
Lemma lem3814096 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term31 A B f g) (h2 : term63 A x s) : ((term62 A B g x s) = (term44 A B f x g s)) = ((term154 A B f g s x) = (term44 A B f x g s)).
Proof. exact (EQ_MP (@lem3814095 A B f x g s) (@lem3814086 A B f g x s h1 h2)). Qed.
Lemma lem3814097 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term31 A B f g) (h2 : term63 A x s) : ((term154 A B f g s x) = (term44 A B f x g s)) = ((term62 A B g x s) = (term44 A B f x g s)).
Proof. exact (SYM (@lem3814096 A B f g x s h1 h2)). Qed.
Lemma lem3814098 {A B : Type'} (f : type1411 A B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3814099 {A B : Type'} (g : type685 A B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3814105 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term160 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3814106 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term160 A s t).
Proof. exact (@lem3814105 A s t). Qed.
Lemma lem3814107 {A : Type'} (x : A) (s : A -> Prop) : ((term161 A s x) = s) = (term162 A x s).
Proof. exact (@lem3814106 A (term161 A s x) s). Qed.
Lemma lem3814116 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem3814117 {A : Type'} (x : A) (s : A -> Prop) : (term163 A x s) = (term164 A x s).
Proof. exact (MK_COMB (@lem3814116 A x s) (@lem3814107 A x s)). Qed.
Lemma lem3814120 {A : Type'} (x : A) (s : A -> Prop) : (term164 A x s) = (term163 A x s).
Proof. exact (SYM (@lem3814117 A x s)). Qed.
Lemma lem3814124 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3814125 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3814124 A P x). Qed.
Lemma lem3814126 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3814125 A s x). Qed.
Lemma lem3814127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3814128 {A : Type'} (s : A -> Prop) (x : A) : (term61 A x s) = (term165 A s x).
Proof. exact (MK_COMB (@lem3814127) (@lem3814126 A s x)). Qed.
Lemma lem3814129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3814130 {A : Type'} (s : A -> Prop) (x : A) : (term47 A x s) = (term166 A s x).
Proof. exact (MK_COMB (@lem3814129) (@lem3814128 A s x)). Qed.
Lemma lem3814138 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term167 A x s y) = (term168 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3814139 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term167 A x s y) = (term168 A s x y).
Proof. exact (@lem3814138 A s x y). Qed.
Lemma lem3814140 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term169 A x' s x) = (term170 A s x' x).
Proof. exact (@lem3814139 A (@INSERT A x s) x' x). Qed.
Lemma lem3814144 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3814145 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (@lem3814144 A y x s). Qed.
Lemma lem3814146 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term5 A x' x s) = (term6 A x x' s).
Proof. exact (@lem3814145 A x x' s). Qed.
Lemma lem3814152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3814153 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3814152 A P x). Qed.
Lemma lem3814154 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3814153 A s x'). Qed.
Lemma lem3814155 {A : Type'} (x' : A) (x : A) : (term171 A x' x) = (term171 A x' x).
Proof. exact (eq_refl (term171 A x' x)). Qed.
Lemma lem3814156 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term6 A x x' s) = (term172 A x s x').
Proof. exact (MK_COMB (@lem3814155 A x' x) (@lem3814154 A s x')). Qed.
Lemma lem3814159 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term5 A x' x s) = (term172 A x s x').
Proof. exact (TRANS (@lem3814146 A x x' s) (@lem3814156 A x s x')). Qed.
Lemma lem3814160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3814161 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term173 A x' x s) = (term174 A x s x').
Proof. exact (MK_COMB (@lem3814160) (@lem3814159 A x s x')). Qed.
Lemma lem3814164 {A : Type'} (x' : A) (x : A) : (term175 A x' x) = (term175 A x' x).
Proof. exact (eq_refl (term175 A x' x)). Qed.
Lemma lem3814165 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term170 A s x' x) = (term176 A s x' x).
Proof. exact (MK_COMB (@lem3814161 A x s x') (@lem3814164 A x' x)). Qed.
Lemma lem3814168 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term169 A x' s x) = (term176 A s x' x).
Proof. exact (TRANS (@lem3814140 A s x' x) (@lem3814165 A s x' x)). Qed.
Lemma lem3814169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3814170 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term177 A x' s x) = (term178 A s x' x).
Proof. exact (MK_COMB (@lem3814169) (@lem3814168 A s x' x)). Qed.
Lemma lem3814172 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3814173 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3814172 A P x). Qed.
Lemma lem3814174 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3814173 A s x'). Qed.
Lemma lem3814175 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term169 A x' s x) = (@IN A x' s)) = ((term176 A s x' x) = (s x')).
Proof. exact (MK_COMB (@lem3814170 A s x' x) (@lem3814174 A s x')). Qed.
Lemma lem3814178 {A : Type'} (x : A) (s : A -> Prop) : (term179 A x s) = (term180 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3814175 A x s x')). Qed.
Lemma lem3814179 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3814180 {A : Type'} (x : A) (s : A -> Prop) : (term162 A x s) = (term181 A x s).
Proof. exact (MK_COMB (@lem3814179 A) (@lem3814178 A x s)). Qed.
Lemma lem3814185 {A : Type'} (x : A) (s : A -> Prop) : (term164 A x s) = (term182 A x s).
Proof. exact (MK_COMB (@lem3814130 A s x) (@lem3814180 A x s)). Qed.
Lemma lem3814188 {A : Type'} (x : A) (s : A -> Prop) : (term182 A x s) = (term164 A x s).
Proof. exact (SYM (@lem3814185 A x s)). Qed.
Lemma lem3814190 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3814191 {A : Type'} (x : A) (s : A -> Prop) : (term182 A x s) = (term183 A x s).
Proof. exact (@lem3814190 (term182 A x s)). Qed.
Lemma lem3814192 {A : Type'} (x : A) (s : A -> Prop) : (term183 A x s) = (term182 A x s).
Proof. exact (SYM (@lem3814191 A x s)). Qed.
Lemma lem3814193 {A : Type'} (x : A) (s : A -> Prop) (h1 : term184 A x s) : term184 A x s.
Proof. exact (h1). Qed.
Lemma lem3814196 {A : Type'} (x : A) (s : A -> Prop) (h1 : term183 A x s) : term183 A x s.
Proof. exact (h1). Qed.
Lemma lem3814197 {A : Type'} (x : A) (s : A -> Prop) : term185 A x s.
Proof. exact (fun h0 : term183 A x s => @lem3814196 A x s h0). Qed.
Lemma lem3814198 {A : Type'} (x : A) (s : A -> Prop) (h1 : term185 A x s) : term185 A x s.
Proof. exact (h1). Qed.
Lemma lem3814199 {A : Type'} (x : A) (s : A -> Prop) (h1 : term183 A x s) : term183 A x s.
Proof. exact (h1). Qed.
Lemma lem3814200 {A : Type'} (x : A) (s : A -> Prop) (h1 : term183 A x s) (h2 : term185 A x s) : term183 A x s.
Proof. exact (@lem3814198 A x s h2 (@lem3814199 A x s h1)). Qed.
Lemma lem3814201 {A : Type'} (x : A) (s : A -> Prop) (h1 : term183 A x s) : term186 A x s.
Proof. exact (fun h0 : term185 A x s => @lem3814200 A x s h1 h0). Qed.
Lemma lem3814202 {A : Type'} (x : A) (s : A -> Prop) (h1 : term185 A x s) : term185 A x s.
Proof. exact (h1). Qed.
Lemma lem3814203 {A : Type'} (x : A) (s : A -> Prop) (h1 : term183 A x s) (h2 : term185 A x s) : term183 A x s.
Proof. exact (@lem3814201 A x s h1 (@lem3814202 A x s h2)). Qed.
Lemma lem3814204 {A : Type'} (x : A) (s : A -> Prop) (h1 : term185 A x s) : term185 A x s.
Proof. exact (fun h0 : term183 A x s => @lem3814203 A x s h0 h1). Qed.
Lemma lem3814205 {A : Type'} (x : A) (s : A -> Prop) : term187 A x s.
Proof. exact (fun h0 : term185 A x s => @lem3814204 A x s h0). Qed.
Lemma lem3814208 {A : Type'} (x : A) (s : A -> Prop) : term185 A x s.
Proof. exact (@lem3814205 A x s (@lem3814197 A x s)). Qed.
Lemma lem3814209 {A : Type'} (x : A) (s : A -> Prop) : term185 A x s.
Proof. exact (@lem3814208 A x s). Qed.
Lemma lem3814219 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3814220 {A : Type'} (x : A) (s : A -> Prop) : (term183 A x s) = (term188 A x s).
Proof. exact (@lem3814219 (term184 A x s)). Qed.
Lemma lem3814222 (t : Prop) : (term140 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3814223 {A : Type'} (x : A) (s : A -> Prop) : (term188 A x s) = (term182 A x s).
Proof. exact (@lem3814222 (term182 A x s)). Qed.
Lemma lem3814226 {A : Type'} (x : A) (s : A -> Prop) : (term183 A x s) = (term182 A x s).
Proof. exact (TRANS (@lem3814220 A x s) (@lem3814223 A x s)). Qed.
Lemma lem3814235 {A : Type'} (s : A -> Prop) : (term189 A s) = (term190 A s).
Proof. exact (fun_ext (fun x : A => @lem3814226 A x s)). Qed.
Lemma lem3814236 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3814237 {A : Type'} (s : A -> Prop) : (term191 A s) = (term192 A s).
Proof. exact (MK_COMB (@lem3814236 A) (@lem3814235 A s)). Qed.
Lemma lem3814242 {A : Type'} : (term193 A) = (term194 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3814237 A s)). Qed.
Lemma lem3814243 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3814252 {A : Type'} : (term195 A) = (term196 A).
Proof. exact (MK_COMB (@lem3814243 A) (@lem3814242 A)). Qed.
Lemma lem3814267 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term176 A s x' x) = (s x')) = ((term176 A s x' x) = (s x')).
Proof. exact (eq_refl ((term176 A s x' x) = (s x'))). Qed.
Lemma lem3814268 {A : Type'} (x : A) (s : A -> Prop) : (term180 A x s) = (term180 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3814267 A x s x')). Qed.
Lemma lem3814269 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3814270 {A : Type'} (x : A) (s : A -> Prop) : (term181 A x s) = (term181 A x s).
Proof. exact (MK_COMB (@lem3814269 A) (@lem3814268 A x s)). Qed.
Lemma lem3814275 {A : Type'} (s : A -> Prop) (x : A) : (term166 A s x) = (term166 A s x).
Proof. exact (eq_refl (term166 A s x)). Qed.
Lemma lem3814276 {A : Type'} (x : A) (s : A -> Prop) : (term182 A x s) = (term182 A x s).
Proof. exact (MK_COMB (@lem3814275 A s x) (@lem3814270 A x s)). Qed.
Lemma lem3814277 {A : Type'} (s : A -> Prop) : (term190 A s) = (term190 A s).
Proof. exact (fun_ext (fun x : A => @lem3814276 A x s)). Qed.
Lemma lem3814278 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3814279 {A : Type'} (s : A -> Prop) : (term192 A s) = (term192 A s).
Proof. exact (MK_COMB (@lem3814278 A) (@lem3814277 A s)). Qed.
Lemma lem3814280 {A : Type'} : (term194 A) = (term194 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3814279 A s)). Qed.
Lemma lem3814281 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3814282 {A : Type'} : (term196 A) = (term196 A).
Proof. exact (MK_COMB (@lem3814281 A) (@lem3814280 A)). Qed.
Lemma lem3814309 {A : Type'} : (term195 A) = (term196 A).
Proof. exact (TRANS (@lem3814252 A) (@lem3814282 A)). Qed.
Lemma lem3814310 {A : Type'} : (term196 A) = (term195 A).
Proof. exact (SYM (@lem3814309 A)). Qed.
Lemma lem3814313 (p : Prop) : p = (term71 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3814314 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term176 A s x' x) = (s x')) = (term197 A x s x').
Proof. exact (@lem3814313 ((term176 A s x' x) = (s x'))). Qed.
Lemma lem3814315 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term197 A x s x') = ((term176 A s x' x) = (s x')).
Proof. exact (SYM (@lem3814314 A x s x')). Qed.
Lemma lem3814316 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term198 A x s x') : term198 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3814322 {A : Type'} (s : A -> Prop) (x : A) (h1 : term165 A s x) : term165 A s x.
Proof. exact (h1). Qed.
Lemma lem3814331 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term199 A x s x') = (term200 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3814338 {A : Type'} (x' : A) (x : A) : (term201 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3814339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3814340 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term202 A x s x') = (term203 A x s x').
Proof. exact (MK_COMB (@lem3814339) (@lem3814331 A x s x')). Qed.
Lemma lem3814341 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term204 A s x' x) = (term205 A s x' x).
Proof. exact (MK_COMB (@lem3814340 A x s x') (@lem3814338 A x' x)). Qed.
Lemma lem3814342 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term206 A s x' x) = (term204 A s x' x).
Proof. exact (@lem17045 (term172 A x s x') (term175 A x' x)). Qed.
Lemma lem3814343 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term206 A s x' x) = (term205 A s x' x).
Proof. exact (TRANS (@lem3814342 A s x' x) (@lem3814341 A s x' x)). Qed.
Lemma lem3814348 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3814349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3814350 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term207 A s x' x) = (term208 A s x' x).
Proof. exact (MK_COMB (@lem3814349) (@lem3814343 A s x' x)). Qed.
Lemma lem3814351 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term209 A x s x') = (term210 A x s x').
Proof. exact (MK_COMB (@lem3814350 A s x' x) (@lem3814348 A s x')). Qed.
Lemma lem3814356 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term211 A x s x') = (term211 A x s x').
Proof. exact (eq_refl (term211 A x s x')). Qed.
Lemma lem3814357 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term212 A x s x') = (term213 A x s x').
Proof. exact (MK_COMB (@lem3814356 A x s x') (@lem3814351 A x s x')). Qed.
Lemma lem3814358 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term198 A x s x') = (term212 A x s x').
Proof. exact (@lem17646 (term176 A s x' x) (s x')). Qed.
Lemma lem3814363 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term198 A x s x') = (term213 A x s x').
Proof. exact (TRANS (@lem3814358 A x s x') (@lem3814357 A x s x')). Qed.
Lemma lem3814370 {A : Type'} (s : A -> Prop) (x : A) (h1 : term165 A s x) : term165 A s x.
Proof. exact (h1). Qed.
Lemma lem3814432 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term198 A x s x') : term213 A x s x'.
Proof. exact (EQ_MP (@lem3814363 A x s x') (@lem3814316 A x s x' h1)). Qed.
Lemma lem3814433 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term214 A x s x') : term214 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3814434 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term210 A x s x') : term210 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3814436 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term214 A x s x') : term176 A s x' x.
Proof. exact (proj1 (@lem3814433 A x s x' h1)). Qed.
Lemma lem3814438 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term214 A x s x') : term172 A x s x'.
Proof. exact (proj1 (@lem3814436 A x s x' h1)). Qed.
Lemma lem3814442 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term210 A x s x') : term205 A s x' x.
Proof. exact (proj1 (@lem3814434 A x s x' h1)). Qed.
Lemma lem3814443 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term200 A x s x') : term200 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3814462 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3814478 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3814498 {A : Type'} (s : A -> Prop) (x : A) (h1 : term165 A s x) : term165 A s x.
Proof. exact (h1). Qed.
Lemma lem3814506 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3814512 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term214 A x s x') : term175 A x' x.
Proof. exact (proj2 (@lem3814436 A x s x' h1)). Qed.
Lemma lem3814514 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3814518 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term214 A x s x') : term165 A s x'.
Proof. exact (proj2 (@lem3814433 A x s x' h1)). Qed.
Lemma lem3814522 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3814530 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term200 A x s x') : term165 A s x'.
Proof. exact (proj2 (@lem3814443 A x s x' h1)). Qed.
Lemma lem3814532 {A : Type'} (s : A -> Prop) (x : A) (h1 : term165 A s x) : term165 A s x.
Proof. exact (h1). Qed.
Lemma lem3814534 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term210 A x s x') : s x'.
Proof. exact (proj2 (@lem3814434 A x s x' h1)). Qed.
Lemma lem3814536 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3814578 {A : Type'} (x : A) : (term215 A x) = (term215 A x).
Proof. exact (eq_refl (term215 A x)). Qed.
Lemma lem3814579 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term216 A x x') = (term217 A x).
Proof. exact (MK_COMB (@lem3814578 A x) (@lem3814514 A x' x h1)). Qed.
Lemma lem3814580 {A : Type'} (x : A) : (term217 A x) = (term218 A x).
Proof. exact (eq_refl (term217 A x)). Qed.
Lemma lem3814581 {A : Type'} (x : A) (x' : A) : (term219 A x x') = (term219 A x x').
Proof. exact (eq_refl (term219 A x x')). Qed.
Lemma lem3814582 {A : Type'} (x' : A) (x : A) : ((term216 A x x') = (term217 A x)) = ((term216 A x x') = (term218 A x)).
Proof. exact (MK_COMB (@lem3814581 A x x') (@lem3814580 A x)). Qed.
Lemma lem3814583 {A : Type'} (x' : A) (x : A) : (term216 A x x') = (term175 A x' x).
Proof. exact (eq_refl (term216 A x x')). Qed.
Lemma lem3814584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3814585 {A : Type'} (x' : A) (x : A) : (term219 A x x') = (term220 A x' x).
Proof. exact (MK_COMB (@lem3814584) (@lem3814583 A x' x)). Qed.
Lemma lem3814586 {A : Type'} (x : A) : (term218 A x) = (term218 A x).
Proof. exact (eq_refl (term218 A x)). Qed.
Lemma lem3814587 {A : Type'} (x' : A) (x : A) : ((term216 A x x') = (term218 A x)) = ((term175 A x' x) = (term218 A x)).
Proof. exact (MK_COMB (@lem3814585 A x' x) (@lem3814586 A x)). Qed.
Lemma lem3814588 {A : Type'} (x' : A) (x : A) : ((term216 A x x') = (term217 A x)) = ((term175 A x' x) = (term218 A x)).
Proof. exact (TRANS (@lem3814582 A x' x) (@lem3814587 A x' x)). Qed.
Lemma lem3814589 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term175 A x' x) = (term218 A x).
Proof. exact (EQ_MP (@lem3814588 A x' x) (@lem3814579 A x' x h1)). Qed.
Lemma lem3814590 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : term218 A x.
Proof. exact (EQ_MP (@lem3814589 A x' x h2) (@lem3814512 A x s x' h1)). Qed.
Lemma lem3814618 {A : Type'} (s : A -> Prop) (x : A) (h1 : term165 A s x) : term165 A s x.
Proof. exact (h1). Qed.
Lemma lem3814619 {A : Type'} (s : A -> Prop) : (term221 A s) = (term221 A s).
Proof. exact (eq_refl (term221 A s)). Qed.
Lemma lem3814620 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term222 A s x') = (term222 A s x).
Proof. exact (MK_COMB (@lem3814619 A s) (@lem3814536 A x' x h1)). Qed.
Lemma lem3814621 {A : Type'} (s : A -> Prop) (x : A) : (term222 A s x) = (s x).
Proof. exact (eq_refl (term222 A s x)). Qed.
Lemma lem3814622 {A : Type'} (s : A -> Prop) (x' : A) : (term223 A s x') = (term223 A s x').
Proof. exact (eq_refl (term223 A s x')). Qed.
Lemma lem3814623 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term222 A s x') = (term222 A s x)) = ((term222 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3814622 A s x') (@lem3814621 A s x)). Qed.
Lemma lem3814624 {A : Type'} (s : A -> Prop) (x' : A) : (term222 A s x') = (s x').
Proof. exact (eq_refl (term222 A s x')). Qed.
Lemma lem3814625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3814626 {A : Type'} (s : A -> Prop) (x' : A) : (term223 A s x') = (term224 A s x').
Proof. exact (MK_COMB (@lem3814625) (@lem3814624 A s x')). Qed.
Lemma lem3814627 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3814628 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term222 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3814626 A s x') (@lem3814627 A s x)). Qed.
Lemma lem3814629 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term222 A s x') = (term222 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3814623 A x' s x) (@lem3814628 A x' s x)). Qed.
Lemma lem3814630 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3814629 A x' s x) (@lem3814620 A s x' x h1)). Qed.
Lemma lem3814647 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3814648 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3814647 A x). Qed.
Lemma lem3814649 {A : Type'} (x : A) : term225 A x.
Proof. exact (fun h0 : term218 A x => @lem3814648 A x). Qed.
Lemma lem3814651 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814652 {A : Type'} (x : A) : (term225 A x) = (x = x).
Proof. exact (@lem3814651 (x = x)). Qed.
Lemma lem3814653 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3814652 A x) (@lem3814649 A x)). Qed.
Lemma lem3814656 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3814658 {A : Type'} (x : A) : (term218 A x) = (term226 A x).
Proof. exact (@lem3814656 (x = x)). Qed.
Lemma lem3814661 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : term226 A x.
Proof. exact (EQ_MP (@lem3814658 A x) (@lem3814590 A s x' x h1 h2)). Qed.
Lemma lem3814664 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3814661 A s x' x h1 h2 (@lem3814653 A x)). Qed.
Lemma lem3814665 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : term145.
Proof. exact (fun h0 : ~ False => @lem3814664 A s x' x h1 h2). Qed.
Lemma lem3814667 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814668 : term145 = False.
Proof. exact (@lem3814667 False). Qed.
Lemma lem3814685 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3814686 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term227 A s x'.
Proof. exact (fun h0 : term165 A s x' => @lem3814685 A s x' h1). Qed.
Lemma lem3814688 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814689 {A : Type'} (s : A -> Prop) (x' : A) : (term227 A s x') = (s x').
Proof. exact (@lem3814688 (s x')). Qed.
Lemma lem3814690 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3814689 A s x') (@lem3814686 A s x' h1)). Qed.
Lemma lem3814693 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3814695 {A : Type'} (s : A -> Prop) (x' : A) : (term165 A s x') = (term228 A s x').
Proof. exact (@lem3814693 (s x')). Qed.
Lemma lem3814698 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term214 A x s x') : term228 A s x'.
Proof. exact (EQ_MP (@lem3814695 A s x') (@lem3814518 A x s x' h1)). Qed.
Lemma lem3814701 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : False.
Proof. exact (@lem3814698 A x s x' h2 (@lem3814690 A s x' h1)). Qed.
Lemma lem3814702 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : term145.
Proof. exact (fun h0 : ~ False => @lem3814701 A x s x' h1 h2). Qed.
Lemma lem3814704 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814705 : term145 = False.
Proof. exact (@lem3814704 False). Qed.
Lemma lem3814706 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : False.
Proof. exact (EQ_MP (@lem3814705) (@lem3814702 A x s x' h1 h2)). Qed.
Lemma lem3814722 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term210 A x s x') : s x'.
Proof. exact (proj2 (@lem3814434 A x s x' h1)). Qed.
Lemma lem3814723 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term210 A x s x') : term227 A s x'.
Proof. exact (fun h0 : term165 A s x' => @lem3814722 A x s x' h1). Qed.
Lemma lem3814725 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814726 {A : Type'} (s : A -> Prop) (x' : A) : (term227 A s x') = (s x').
Proof. exact (@lem3814725 (s x')). Qed.
Lemma lem3814727 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term210 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3814726 A s x') (@lem3814723 A x s x' h1)). Qed.
Lemma lem3814730 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3814732 {A : Type'} (s : A -> Prop) (x' : A) : (term165 A s x') = (term228 A s x').
Proof. exact (@lem3814730 (s x')). Qed.
Lemma lem3814735 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term200 A x s x') : term228 A s x'.
Proof. exact (EQ_MP (@lem3814732 A s x') (@lem3814530 A x s x' h1)). Qed.
Lemma lem3814738 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term200 A x s x') (h2 : term210 A x s x') : False.
Proof. exact (@lem3814735 A x s x' h1 (@lem3814727 A x s x' h2)). Qed.
Lemma lem3814739 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term200 A x s x') (h2 : term210 A x s x') : term145.
Proof. exact (fun h0 : ~ False => @lem3814738 A x s x' h1 h2). Qed.
Lemma lem3814741 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814742 : term145 = False.
Proof. exact (@lem3814741 False). Qed.
Lemma lem3814743 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term200 A x s x') (h2 : term210 A x s x') : False.
Proof. exact (EQ_MP (@lem3814742) (@lem3814739 A x s x' h1 h2)). Qed.
Lemma lem3814745 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term210 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3814630 A s x' x h2) (@lem3814534 A x s x' h1)). Qed.
Lemma lem3814746 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term210 A x s x') (h2 : x' = x) : term227 A s x.
Proof. exact (fun h0 : term165 A s x => @lem3814745 A s x' x h1 h2). Qed.
Lemma lem3814748 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814749 {A : Type'} (s : A -> Prop) (x : A) : (term227 A s x) = (s x).
Proof. exact (@lem3814748 (s x)). Qed.
Lemma lem3814750 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term210 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3814749 A s x) (@lem3814746 A s x' x h1 h2)). Qed.
Lemma lem3814753 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3814755 {A : Type'} (s : A -> Prop) (x : A) : (term165 A s x) = (term228 A s x).
Proof. exact (@lem3814753 (s x)). Qed.
Lemma lem3814758 {A : Type'} (s : A -> Prop) (x : A) (h1 : term165 A s x) : term228 A s x.
Proof. exact (EQ_MP (@lem3814755 A s x) (@lem3814618 A s x h1)). Qed.
Lemma lem3814761 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3814758 A s x h1 (@lem3814750 A s x' x h2 h3)). Qed.
Lemma lem3814762 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : term145.
Proof. exact (fun h0 : ~ False => @lem3814761 A s x' x h1 h2 h3). Qed.
Lemma lem3814764 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3814765 : term145 = False.
Proof. exact (@lem3814764 False). Qed.
Lemma lem3814766 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814765) (@lem3814762 A s x' x h1 h2 h3)). Qed.
Lemma lem3814767 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : (term165 A s x) = False.
Proof. exact (prop_ext (fun h4 : term165 A s x => @lem3814766 A s x' x h1 h2 h3) (fun h4 : False => @lem3814618 A s x h1)). Qed.
Lemma lem3814769 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814767 A s x' x h1 h2 h3) (@lem3814618 A s x h1)). Qed.
Lemma lem3814770 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814668) (@lem3814665 A s x' x h1 h2)). Qed.
Lemma lem3814771 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3814769 A s x' x h1 h2 h3) (fun h4 : False => @lem3814536 A x' x h3)). Qed.
Lemma lem3814772 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814771 A s x' x h1 h2 h3) (@lem3814536 A x' x h3)). Qed.
Lemma lem3814773 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : (term165 A s x) = False.
Proof. exact (prop_ext (fun h4 : term165 A s x => @lem3814772 A s x' x h1 h2 h3) (fun h4 : False => @lem3814532 A s x h1)). Qed.
Lemma lem3814774 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814773 A s x' x h1 h2 h3) (@lem3814532 A s x h1)). Qed.
Lemma lem3814775 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3814706 A x s x' h1 h2) (fun h3 : False => @lem3814522 A s x' h1)). Qed.
Lemma lem3814776 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : False.
Proof. exact (EQ_MP (@lem3814775 A x s x' h1 h2) (@lem3814522 A s x' h1)). Qed.
Lemma lem3814777 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3814770 A s x' x h1 h2) (fun h3 : False => @lem3814514 A x' x h2)). Qed.
Lemma lem3814778 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814777 A s x' x h1 h2) (@lem3814514 A x' x h2)). Qed.
Lemma lem3814779 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3814774 A s x' x h1 h2 h3) (fun h4 : False => @lem3814506 A x' x h3)). Qed.
Lemma lem3814780 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814779 A s x' x h1 h2 h3) (@lem3814506 A x' x h3)). Qed.
Lemma lem3814781 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : (term165 A s x) = False.
Proof. exact (prop_ext (fun h4 : term165 A s x => @lem3814780 A s x' x h1 h2 h3) (fun h4 : False => @lem3814498 A s x h1)). Qed.
Lemma lem3814782 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814781 A s x' x h1 h2 h3) (@lem3814498 A s x h1)). Qed.
Lemma lem3814783 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3814776 A x s x' h1 h2) (fun h3 : False => @lem3814478 A s x' h1)). Qed.
Lemma lem3814784 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : False.
Proof. exact (EQ_MP (@lem3814783 A x s x' h1 h2) (@lem3814478 A s x' h1)). Qed.
Lemma lem3814785 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3814778 A s x' x h1 h2) (fun h3 : False => @lem3814462 A x' x h2)). Qed.
Lemma lem3814786 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814785 A s x' x h1 h2) (@lem3814462 A x' x h2)). Qed.
Lemma lem3814787 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3814782 A s x' x h1 h2 h3) (fun h4 : False => @lem3814506 A x' x h3)). Qed.
Lemma lem3814788 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814787 A s x' x h1 h2 h3) (@lem3814506 A x' x h3)). Qed.
Lemma lem3814789 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : (term165 A s x) = False.
Proof. exact (prop_ext (fun h4 : term165 A s x => @lem3814788 A s x' x h1 h2 h3) (fun h4 : False => @lem3814498 A s x h1)). Qed.
Lemma lem3814790 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term165 A s x) (h2 : term210 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814789 A s x' x h1 h2 h3) (@lem3814498 A s x h1)). Qed.
Lemma lem3814791 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3814784 A x s x' h1 h2) (fun h3 : False => @lem3814478 A s x' h1)). Qed.
Lemma lem3814792 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term214 A x s x') : False.
Proof. exact (EQ_MP (@lem3814791 A x s x' h1 h2) (@lem3814478 A s x' h1)). Qed.
Lemma lem3814793 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3814786 A s x' x h1 h2) (fun h3 : False => @lem3814462 A x' x h2)). Qed.
Lemma lem3814794 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term214 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3814793 A s x' x h1 h2) (@lem3814462 A x' x h2)). Qed.
Lemma lem3814795 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term210 A x s x') : False.
Proof. exact (or_elim (@lem3814442 A x s x' h2) (fun h0 : term200 A x s x' => @lem3814743 A x s x' h0 h2) (fun h0 : x' = x => @lem3814790 A s x' x h1 h2 h0)). Qed.
Lemma lem3814796 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term214 A x s x') : False.
Proof. exact (or_elim (@lem3814438 A x s x' h1) (fun h0 : x' = x => @lem3814794 A s x' x h1 h0) (fun h0 : s x' => @lem3814792 A x s x' h0 h1)). Qed.
Lemma lem3814797 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term198 A x s x') : False.
Proof. exact (or_elim (@lem3814432 A x s x' h2) (fun h0 : term214 A x s x' => @lem3814796 A x s x' h0) (fun h0 : term210 A x s x' => @lem3814795 A x s x' h1 h0)). Qed.
Lemma lem3814798 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term198 A x s x') : (term165 A s x) = False.
Proof. exact (prop_ext (fun h3 : term165 A s x => @lem3814797 A x s x' h1 h2) (fun h3 : False => @lem3814370 A s x h1)). Qed.
Lemma lem3814799 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term198 A x s x') : False.
Proof. exact (EQ_MP (@lem3814798 A x s x' h1 h2) (@lem3814370 A s x h1)). Qed.
Lemma lem3814800 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term198 A x s x') : (term165 A s x) = False.
Proof. exact (prop_ext (fun h3 : term165 A s x => @lem3814799 A x s x' h1 h2) (fun h3 : False => @lem3814322 A s x h1)). Qed.
Lemma lem3814801 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term198 A x s x') : False.
Proof. exact (EQ_MP (@lem3814800 A x s x' h1 h2) (@lem3814322 A s x h1)). Qed.
Lemma lem3814802 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term198 A x s x') : (term198 A x s x') = False.
Proof. exact (prop_ext (fun h3 : term198 A x s x' => @lem3814801 A x s x' h1 h2) (fun h3 : False => @lem3814316 A x s x' h2)). Qed.
Lemma lem3814803 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term165 A s x) (h2 : term198 A x s x') : False.
Proof. exact (EQ_MP (@lem3814802 A x s x' h1 h2) (@lem3814316 A x s x' h2)). Qed.
Lemma lem3814804 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term165 A s x) : term197 A x s x'.
Proof. exact (fun h0 : term198 A x s x' => @lem3814803 A x s x' h1 h0). Qed.
Lemma lem3814805 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term165 A s x) : (term176 A s x' x) = (s x').
Proof. exact (EQ_MP (@lem3814315 A x s x') (@lem3814804 A x' s x h1)). Qed.
Lemma lem3814810 {A : Type'} (s : A -> Prop) (x : A) (h1 : term165 A s x) : term181 A x s.
Proof. exact (fun x' : A => @lem3814805 A x' s x h1). Qed.
Lemma lem3814811 {A : Type'} (x : A) (s : A -> Prop) : term182 A x s.
Proof. exact (fun h0 : term165 A s x => @lem3814810 A s x h0). Qed.
Lemma lem3814816 {A : Type'} (s : A -> Prop) : term192 A s.
Proof. exact (fun x : A => @lem3814811 A x s). Qed.
Lemma lem3814821 {A : Type'} : term196 A.
Proof. exact (fun s : A -> Prop => @lem3814816 A s). Qed.
Lemma lem3814822 {A : Type'} : term195 A.
Proof. exact (EQ_MP (@lem3814310 A) (@lem3814821 A)). Qed.
Lemma lem3814823 {A : Type'} (s : A -> Prop) : term229 A s.
Proof. exact (@lem3814822 A s). Qed.
Lemma lem3814824 {A : Type'} (s : A -> Prop) : (term229 A s) = (term191 A s).
Proof. exact (eq_refl (term229 A s)). Qed.
Lemma lem3814825 {A : Type'} (s : A -> Prop) : term191 A s.
Proof. exact (EQ_MP (@lem3814824 A s) (@lem3814823 A s)). Qed.
Lemma lem3814826 {A : Type'} (s : A -> Prop) (x : A) : term230 A s x.
Proof. exact (@lem3814825 A s x). Qed.
Lemma lem3814827 {A : Type'} (x : A) (s : A -> Prop) : (term230 A s x) = (term183 A x s).
Proof. exact (eq_refl (term230 A s x)). Qed.
Lemma lem3814828 {A : Type'} (x : A) (s : A -> Prop) : term183 A x s.
Proof. exact (EQ_MP (@lem3814827 A x s) (@lem3814826 A s x)). Qed.
Lemma lem3814830 {A : Type'} (x : A) (s : A -> Prop) : term183 A x s.
Proof. exact (@lem3814209 A x s (@lem3814828 A x s)). Qed.
Lemma lem3814831 {A : Type'} (x : A) (s : A -> Prop) (h1 : term184 A x s) : False.
Proof. exact (@lem3814830 A x s (@lem3814193 A x s h1)). Qed.
Lemma lem3814832 {A : Type'} (x : A) (s : A -> Prop) (h1 : term184 A x s) : (term184 A x s) = False.
Proof. exact (prop_ext (fun h2 : term184 A x s => @lem3814831 A x s h1) (fun h2 : False => @lem3814193 A x s h1)). Qed.
Lemma lem3814833 {A : Type'} (x : A) (s : A -> Prop) (h1 : term184 A x s) : False.
Proof. exact (EQ_MP (@lem3814832 A x s h1) (@lem3814193 A x s h1)). Qed.
Lemma lem3814834 {A : Type'} (x : A) (s : A -> Prop) : term183 A x s.
Proof. exact (fun h0 : term184 A x s => @lem3814833 A x s h0). Qed.
Lemma lem3814835 {A : Type'} (x : A) (s : A -> Prop) : term182 A x s.
Proof. exact (EQ_MP (@lem3814192 A x s) (@lem3814834 A x s)). Qed.
Lemma lem3814836 {A : Type'} (x : A) (s : A -> Prop) : term164 A x s.
Proof. exact (EQ_MP (@lem3814188 A x s) (@lem3814835 A x s)). Qed.
Lemma lem3814837 {A : Type'} (x : A) (s : A -> Prop) : term163 A x s.
Proof. exact (EQ_MP (@lem3814120 A x s) (@lem3814836 A x s)). Qed.
Lemma lem3814838 {A : Type'} (x : A) (s : A -> Prop) (h1 : term61 A x s) : (term161 A s x) = s.
Proof. exact (@lem3814837 A x s (@lem3812951 A x s h1)). Qed.
Lemma lem3814839 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term61 A x s) : (term231 A B g s x) = (g s).
Proof. exact (MK_COMB (@lem3814099 A B g) (@lem3814838 A x s h1)). Qed.
Lemma lem3814840 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term61 A x s) : (term154 A B f g s x) = (term44 A B f x g s).
Proof. exact (MK_COMB (@lem3814098 A B f x) (@lem3814839 A B g x s h1)). Qed.
Lemma lem3814841 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term31 A B f g) (h2 : term61 A x s) (h3 : term63 A x s) : (term62 A B g x s) = (term44 A B f x g s).
Proof. exact (EQ_MP (@lem3814097 A B f g x s h1 h3) (@lem3814840 A B f g x s h2)). Qed.
Lemma lem3814842 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term31 A B f g) (h2 : term61 A x s) : term232 A B f x g s.
Proof. exact (fun h0 : term63 A x s => @lem3814841 A B f g x s h1 h2 h0). Qed.
Lemma lem3814843 {A B : Type'} (f : type1411 A B) (g : type685 A B) (x : A) (s : A -> Prop) (h1 : term31 A B f g) (h2 : term61 A x s) (h3 : term63 A x s) : (term62 A B g x s) = (term44 A B f x g s).
Proof. exact (@lem3814842 A B f g x s h1 h2 (@lem3813025 A x s h3)). Qed.
Lemma lem3814844 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term61 A x s) (h4 : (g (@EMPTY A)) = b) : (term63 A x s) = ((term62 A B g x s) = (term44 A B f x g s)).
Proof. exact (prop_ext (fun h5 : term63 A x s => @lem3814843 A B f g x s h1 h3 h5) (fun h5 : (term62 A B g x s) = (term44 A B f x g s) => @lem3814072 A B f x s g b h1 h2 h3 h4)). Qed.
Lemma lem3814845 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : @FINITE A s) (h3 : term61 A x s) (h4 : (g (@EMPTY A)) = b) : (term62 A B g x s) = (term44 A B f x g s).
Proof. exact (EQ_MP (@lem3814844 A B f x s g b h1 h2 h3 h4) (@lem3814072 A B f x s g b h1 h2 h3 h4)). Qed.
Lemma lem3814850 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : term61 A x s) (h3 : (g (@EMPTY A)) = b) : term46 A B f x g s.
Proof. exact (fun h0 : @FINITE A s => @lem3814845 A B f x s g b h1 h0 h2 h3). Qed.
Lemma lem3814851 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : term61 A x s) (h3 : (g (@EMPTY A)) = b) : (term61 A x s) = (term46 A B f x g s).
Proof. exact (prop_ext (fun h4 : term61 A x s => @lem3814850 A B f x s g b h1 h2 h3) (fun h4 : term46 A B f x g s => @lem3812951 A x s h2)). Qed.
Lemma lem3814852 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : term61 A x s) (h3 : (g (@EMPTY A)) = b) : term46 A B f x g s.
Proof. exact (EQ_MP (@lem3814851 A B f x s g b h1 h2 h3) (@lem3812951 A x s h2)). Qed.
Lemma lem3814853 {A B : Type'} (x : A) (s : A -> Prop) (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term49 A B f x g s.
Proof. exact (fun h0 : term61 A x s => @lem3814852 A B f x s g b h1 h0 h2). Qed.
Lemma lem3814854 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term51 A B x g s.
Proof. exact (fun h0 : @FINITE A s => @lem3813024 A B g x s h1). Qed.
Lemma lem3814855 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = (term51 A B x g s).
Proof. exact (prop_ext (fun h2 : @IN A x s => @lem3814854 A B g x s h1) (fun h2 : term51 A B x g s => @lem3812934 A x s h1)). Qed.
Lemma lem3814856 {A B : Type'} (g : type685 A B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term51 A B x g s.
Proof. exact (EQ_MP (@lem3814855 A B g x s h1) (@lem3812934 A x s h1)). Qed.
Lemma lem3814857 {A B : Type'} (x : A) (g : type685 A B) (s : A -> Prop) : term54 A B x g s.
Proof. exact (fun h0 : @IN A x s => @lem3814856 A B g x s h0). Qed.
Lemma lem3814858 {A B : Type'} (x : A) (s : A -> Prop) (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term57 A B f x g s.
Proof. exact (conj (@lem3814857 A B x g s) (@lem3814853 A B x s f g b h1 h2)). Qed.
Lemma lem3814859 {A B : Type'} (x : A) (s : A -> Prop) (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term58 A B f x g s.
Proof. exact (EQ_MP (@lem3812933 A B f x g s) (@lem3814858 A B x s f g b h1 h2)). Qed.
Lemma lem3814864 {A B : Type'} (x : A) (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term233 A B f x g.
Proof. exact (fun s : A -> Prop => @lem3814859 A B x s f g b h1 h2). Qed.
Lemma lem3814869 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term34 A B f g.
Proof. exact (fun x : A => @lem3814864 A B x f g b h1 h2). Qed.
Lemma lem3814870 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term35 A B b f g.
Proof. exact (EQ_MP (@lem3812915 A B f g b h2) (@lem3814869 A B f g b h1 h2)). Qed.
Lemma lem3814871 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term234 A B b f.
Proof. exact (ex_intro (term235 A B b f) g (@lem3814870 A B f g b h1 h2)). Qed.
Lemma lem3814872 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (h1 : term30 A B b f g) : term31 A B f g.
Proof. exact (proj2 (@lem3812857 A B b f g h1)). Qed.
Lemma lem3814873 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (h1 : term30 A B b f g) : (g (@EMPTY A)) = b.
Proof. exact (proj1 (@lem3812857 A B b f g h1)). Qed.
Lemma lem3814874 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : (term31 A B f g) = (term234 A B b f).
Proof. exact (prop_ext (fun h3 : term31 A B f g => @lem3814871 A B f g b h1 h2) (fun h3 : term234 A B b f => @lem3812858 A B f g h1)). Qed.
Lemma lem3814875 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term234 A B b f.
Proof. exact (EQ_MP (@lem3814874 A B f g b h1 h2) (@lem3812858 A B f g h1)). Qed.
Lemma lem3814876 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : ((g (@EMPTY A)) = b) = (term234 A B b f).
Proof. exact (prop_ext (fun h3 : (g (@EMPTY A)) = b => @lem3814875 A B f g b h1 h2) (fun h3 : term234 A B b f => @lem3812859 A B g b h2)). Qed.
Lemma lem3814877 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term31 A B f g) (h2 : (g (@EMPTY A)) = b) : term234 A B b f.
Proof. exact (EQ_MP (@lem3814876 A B f g b h1 h2) (@lem3812859 A B g b h2)). Qed.
Lemma lem3814878 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term30 A B b f g) (h2 : (g (@EMPTY A)) = b) : (term31 A B f g) = (term234 A B b f).
Proof. exact (prop_ext (fun h3 : term31 A B f g => @lem3814877 A B f g b h3 h2) (fun h3 : term234 A B b f => @lem3814872 A B b f g h1)). Qed.
Lemma lem3814879 {A B : Type'} (f : type1411 A B) (g : type685 A B) (b : B) (h1 : term30 A B b f g) (h2 : (g (@EMPTY A)) = b) : term234 A B b f.
Proof. exact (EQ_MP (@lem3814878 A B f g b h1 h2) (@lem3814872 A B b f g h1)). Qed.
Lemma lem3814880 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (h1 : term30 A B b f g) : ((g (@EMPTY A)) = b) = (term234 A B b f).
Proof. exact (prop_ext (fun h2 : (g (@EMPTY A)) = b => @lem3814879 A B f g b h1 h2) (fun h2 : term234 A B b f => @lem3814873 A B b f g h1)). Qed.
Lemma lem3814881 {A B : Type'} (b : B) (f : type1411 A B) (g : type685 A B) (h1 : term30 A B b f g) : term234 A B b f.
Proof. exact (EQ_MP (@lem3814880 A B b f g h1) (@lem3814873 A B b f g h1)). Qed.
Lemma lem3814882 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term23 A B b f) : term234 A B b f.
Proof. exact (ex_elim (@lem3812856 A B b f h1) (fun g : type685 A B => fun h0 : term236 A B b f g => @lem3814881 A B b f g h0)). Qed.
Lemma lem3814883 {A B : Type'} (b : B) (f : type1411 A B) : term237 A B b f.
Proof. exact (fun h0 : term23 A B b f => @lem3814882 A B b f h0). Qed.
Lemma lem3814884 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term22 A B f) : term234 A B b f.
Proof. exact (@lem3814883 A B b f (@lem3812855 A B b f h1)). Qed.
Lemma lem3814885 {A B : Type'} (b : B) (f : type1411 A B) : term238 A B b f.
Proof. exact (fun h0 : term22 A B f => @lem3814884 A B b f h0). Qed.
Lemma lem3814890 {A B : Type'} (f : type1411 A B) : term239 A B f.
Proof. exact (fun b : B => @lem3814885 A B b f). Qed.
Lemma lem3814895 {A B : Type'} : term240 A B.
Proof. exact (fun f : type1411 A B => @lem3814890 A B f). Qed.
